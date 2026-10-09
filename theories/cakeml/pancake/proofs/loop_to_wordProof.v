(** * Pancake [loop_to_wordProof]: correctness of [loop_to_word]

    Port of [cakeml/pancake/proofs/loop_to_wordProofScript.sml].

    Naming: [wordLang] and [wordSem] are imported, so unqualified program
    constructors, [state], [evaluate], [get_var], ... are wordLang's and
    wordSem's; loopLang's and loopSem's are written [loopLang.X],
    [loopSem.X].  HOL's [t with clock := k] is [set_clock k t] and
    [t with <|stack := xs; handler := h|>] is [set_handler h (set_stack xs t)].

    [compile_correct] (HOL: [recInduct evaluate_ind] with one [Resume] per
    statement) is well-founded induction on [loopSem.eval_lt]; each
    statement is handled by a Galette-only lemma [cc_<Stmt>] about the
    predicate [cc_P] (the theorem's conclusion, with [cc_post] its case
    analysis on the result).  [state_rel_imp_semantics] goes through
    [crep_to_loopProof.semantics_wrapper_eq] (the word semantics is put in
    wrapper form by the Galette-only [word_sem_is_wrapper]).  Other untagged
    lemmas are Galette-only helpers; [tick_loop_tick] plays the role of the
    HOL [local] lemmas [evaluate_tick_unfold] and
    [evaluate_tick_loop_tick_unfold], and [loopProps.acc_vars_acc_iff] that
    of [acc_vars_acc'].  HOL's boolean [EVERY] predicates ([λ(q,r). q = FST l
    ∧ ...]) are written with [=?], [<=?], [<?].

    Not ported: [env_to_list_IMP] (needs wordProps'
    [env_to_list_lookup_equiv], not ported); [mem_prog_mem_compile_prog]
    (HOL's [MEM] on programs needs [EqDecision] on [loopLang.prog] and
    [wordLang.prog], which have none); [loop_to_word_compile_not_created]
    and the [local] [loop_to_word_compile_not_created_MEM] (HOL's [EVERY]
    of the [Prop]-valued [not_created_subprogs]); [loop_compile_no_install_code],
    [loop_compile_no_alloc_code], [loop_compile_no_mt_code] (need wordProps'
    [no_install_code], [no_alloc_code], [no_mt_code], not ported);
    [full_imp_inst_ok_less], [loop_inst_ok_def] and the
    [loop_to_word_*every_inst_ok_less] theorems (instruction-encoding side
    conditions for the later passes). *)

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
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.misc.misc Require Import fromList2.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require stackLang.
Import stackLang(store_name(..)).
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require consts clock.
From Galette.cakeml.pancake Require loopLang panLang.
From Galette.cakeml.pancake Require Import loop_to_word.
From Galette.cakeml.pancake.semantics Require loopSem loopProps.
From Galette.cakeml.pancake.proofs Require crep_to_loopProof.
Open Scope N_scope.

(** ** Relations *)

Section Rel.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_def" *)
Definition locals_rel {B} (ctxt : num_map N) (l1 l2 : num_map B) : Prop :=
  INJ (find_var ctxt) (domain ctxt) UNIV /\
  (forall n m, lookup n ctxt = SOME m -> m <> 0 /\ EVEN m) /\
  forall n v, lookup n l1 = SOME v ->
    exists m, lookup n ctxt = SOME m /\ lookup m l2 = SOME v.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "globals_rel_def" *)
Definition globals_rel {B} (g1 : fmap (word 5) B) (g2 : fmap store_name B) : Prop :=
  forall n v, FLOOKUP g1 n = SOME v -> FLOOKUP g2 (Temp n) = SOME v.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "code_rel_def" *)
Definition code_rel (s_code : num_map (list N * loopLang.prog a))
    (t_code : num_map (N * prog a)) : Prop :=
  forall name params body,
    lookup name s_code = SOME (params, body) ->
    lookup name t_code = SOME (LENGTH params + 1, comp_func name params body) /\
    ALL_DISTINCT params.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_def" *)
Definition state_rel (s : loopSem.state a ffi_t) (t : state a c ffi_t) : Prop :=
  exists len,
    memory t = loopSem.memory s /\
    mdomain t = loopSem.mdomain s /\
    sh_mdomain t = loopSem.sh_mdomain s /\
    clock t = loopSem.clock s /\
    be t = loopSem.be s /\
    ffi t = loopSem.ffi s /\
    ALOOKUP (fmap_to_alist (store t)) CurrHeap = SOME (Word (loopSem.base_addr s)) /\
    ALOOKUP (fmap_to_alist (store t)) HeapLength = SOME (Word len) /\
    loopSem.top_addr s = (loopSem.base_addr s + n2w 2 * len)%w /\
    globals_rel (loopSem.globals s) (store t) /\
    code_rel (loopSem.code s) (code t).

End Rel.

(** ** Basic lemmas *)

Section Basic.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : loopSem.state a ffi_t) (t : state a c ffi_t).

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_intro" *)
Theorem locals_rel_intro : forall {B} ctxt (l1 l2 : num_map B),
  locals_rel ctxt l1 l2 ->
  INJ (find_var ctxt) (domain ctxt) UNIV /\
  (forall n m, lookup n ctxt = SOME m -> m <> 0 /\ EVEN m) /\
  forall n v, lookup n l1 = SOME v ->
    exists m, lookup n ctxt = SOME m /\ lookup m l2 = SOME v.
Proof. intros B ctxt l1 l2 H; exact H. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "globals_rel_intro" *)
Theorem globals_rel_intro : forall {B} (g1 : fmap (word 5) B) g2,
  globals_rel g1 g2 ->
  forall n v, FLOOKUP g1 n = SOME v -> FLOOKUP g2 (Temp n) = SOME v.
Proof. intros B g1 g2 H; exact H. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "code_rel_intro" *)
Theorem code_rel_intro : forall (s_code : num_map (list N * loopLang.prog a)) t_code,
  code_rel s_code t_code ->
  forall name params body,
    lookup name s_code = SOME (params, body) ->
    lookup name t_code = SOME (LENGTH params + 1, comp_func name params body) /\
    ALL_DISTINCT params.
Proof. intros s_code t_code H; exact H. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_intro" *)
Theorem state_rel_intro : forall s t,
  state_rel s t ->
  memory t = loopSem.memory s /\
  mdomain t = loopSem.mdomain s /\
  clock t = loopSem.clock s /\
  be t = loopSem.be s /\
  ffi t = loopSem.ffi s /\
  ALOOKUP (fmap_to_alist (store t)) CurrHeap = SOME (Word (loopSem.base_addr s)) /\
  globals_rel (loopSem.globals s) (store t) /\
  code_rel (loopSem.code s) (code t).
Proof.
  intros s t (len & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  repeat (split; [assumption|]); assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "find_var_neq_0" *)
Theorem find_var_neq_0 : forall {B} v ctxt (lcl lcl' : num_map B),
  v IN domain ctxt /\ locals_rel ctxt lcl lcl' ->
  find_var ctxt v <> 0.
Proof.
  intros B v ctxt lcl lcl' [Hv (_ & Hc & _)].
  apply domain_lookup in Hv as [m Hm]. unfold find_var; rewrite Hm.
  exact (proj1 (Hc _ _ Hm)).
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "find_var_neq_0_ctxt" *)
Theorem find_var_neq_0_ctxt : forall ctxt v,
  (forall n m, lookup n ctxt = SOME m -> m <> 0 /\ EVEN m) /\ v IN domain ctxt ->
  find_var ctxt v <> 0.
Proof.
  intros ctxt v [Hc Hv]. apply domain_lookup in Hv as [m Hm].
  unfold find_var; rewrite Hm. exact (proj1 (Hc _ _ Hm)).
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "find_var_neq_odd" *)
Theorem find_var_neq_odd : forall ctxt k v,
  (forall n m, lookup n ctxt = SOME m -> m <> 0 /\ EVEN m) /\ ~ EVEN k ->
  find_var ctxt v <> k.
Proof.
  intros ctxt k v [Hc Hk]. unfold find_var. destruct (lookup v ctxt) as [m|] eqn:E.
  - intros ->. apply Hk. exact (proj2 (Hc _ _ E)).
  - intros <-. apply Hk. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_insert" *)
Theorem locals_rel_insert : forall {B} ctxt (lcl lcl' : num_map B) v w,
  locals_rel ctxt lcl lcl' /\ v IN domain ctxt ->
  locals_rel ctxt (insert v w lcl) (insert (find_var ctxt v) w lcl').
Proof.
  intros B ctxt lcl lcl' v w [(Hinj & Hc & Hl) Hv].
  split; [exact Hinj|]. split; [exact Hc|].
  intros n x Hn. rewrite lookup_insert in Hn.
  destruct (decide (n = v)) as [->|Hne].
  - injection Hn as <-. apply domain_lookup in Hv as [m Hm].
    exists m. split; [exact Hm|]. rewrite lookup_insert.
    unfold find_var; rewrite Hm. destruct (decide (m = m)); [reflexivity|congruence].
  - destruct (Hl _ _ Hn) as (m & Hm & Hm').
    exists m. split; [exact Hm|]. rewrite lookup_insert.
    destruct (decide (m = find_var ctxt v)) as [Heq|]; [|exact Hm'].
    exfalso. apply Hne. apply (proj2 Hinj).
    + split; apply domain_lookup; eauto.
      apply domain_lookup in Hv; exact Hv.
    + unfold find_var at 1; rewrite Hm; exact Heq.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_insert_unmapped" *)
Theorem locals_rel_insert_unmapped : forall {B} ctxt (lcl lcl' : num_map B) k x,
  locals_rel ctxt lcl lcl' /\
  (forall n, n IN domain ctxt -> find_var ctxt n <> k) ->
  locals_rel ctxt lcl (insert k x lcl').
Proof.
  intros B ctxt lcl lcl' k x [(Hinj & Hc & Hl) Hk].
  split; [exact Hinj|]. split; [exact Hc|].
  intros n v Hn. destruct (Hl _ _ Hn) as (m & Hm & Hm').
  exists m. split; [exact Hm|]. rewrite lookup_insert.
  destruct (decide (m = k)) as [->|]; [|exact Hm'].
  exfalso. apply (Hk n); [apply domain_lookup; eauto|]. unfold find_var; rewrite Hm; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_alist_insert" *)
Theorem locals_rel_alist_insert : forall {B} ctxt (vs : list N) (ws : list B) lcl lcl',
  locals_rel ctxt lcl lcl' /\ set vs SUBSET domain ctxt ->
  locals_rel ctxt (alist_insert vs ws lcl)
    (alist_insert (MAP (find_var ctxt) vs) ws lcl').
Proof.
  intros B ctxt vs; induction vs as [|v vs IH]; intros ws lcl lcl' [Hr Hs];
    [destruct ws; exact Hr|].
  destruct ws as [|w ws]; [exact Hr|]. cbn [MAP alist_insert].
  apply locals_rel_insert. split.
  - apply IH. split; [exact Hr|]. intros x Hx; apply Hs; right; exact Hx.
  - apply Hs; left; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_ALL_DISTINCT_MAP" *)
Theorem locals_rel_ALL_DISTINCT_MAP : forall {B} ctxt (lcl lcl' : num_map B) xs,
  locals_rel ctxt lcl lcl' /\ set xs SUBSET domain ctxt /\ ALL_DISTINCT xs ->
  ALL_DISTINCT (MAP (find_var ctxt) xs).
Proof.
  intros B ctxt lcl lcl' xs ((Hinj & _) & Hs & Hd). revert Hs Hd.
  induction xs as [|x xs IH]; intros Hs Hd; [reflexivity|].
  cbn [MAP ALL_DISTINCT] in *. apply andb_prop in Hd as [Hn Hd].
  apply andb_true_intro; split.
  - apply negb_true_iff. apply negb_true_iff in Hn.
    destruct (MEM (find_var ctxt x) (MAP (find_var ctxt) xs)) eqn:E; [|reflexivity].
    exfalso. apply MEM_In in E. apply in_map_iff in E as (y & Hy & Hin).
    assert (x = y).
    { apply (proj2 Hinj); [split; apply Hs; [left; reflexivity|right; apply IN_set; exact Hin]|].
      symmetry; exact Hy. }
    subst y. apply MEM_In in Hin. rewrite Hin in Hn. discriminate.
  - apply IH; [intros z Hz; apply Hs; right; exact Hz|exact Hd].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_alist_insert_toAList" *)
Theorem locals_rel_alist_insert_toAList : forall {B} ctxt (vs : list N) (ws : list B) lcl env,
  locals_rel ctxt lcl env /\ set vs SUBSET domain ctxt ->
  locals_rel ctxt (alist_insert vs ws lcl)
    (alist_insert (MAP (find_var ctxt) vs) ws (fromAList (toAList env))).
Proof.
  intros B ctxt vs ws lcl env [(H1 & H2 & H3) Hs]. apply locals_rel_alist_insert.
  split; [|exact Hs]. split; [exact H1|]. split; [exact H2|].
  intros n v Hn. destruct (H3 _ _ Hn) as (m & Hm & Hm'). exists m.
  rewrite lookup_fromAList_toAList. split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_get_var" *)
Theorem locals_rel_get_var : forall ctxt l t n w,
  locals_rel ctxt l (locals t) /\ lookup n l = SOME w ->
  get_var (find_var ctxt n) t = SOME w.
Proof.
  intros ctxt l t n w [(_ & _ & H) Hn]. destruct (H _ _ Hn) as (m & Hm & Hm').
  unfold get_var, find_var; rewrite Hm; exact Hm'.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_get_vars" *)
Theorem locals_rel_get_vars : forall ctxt s t argvars argvals,
  locals_rel ctxt (loopSem.locals s) (locals t) /\
  loopSem.get_vars argvars s = SOME argvals ->
  get_vars (MAP (find_var ctxt) argvars) t = SOME argvals /\
  LENGTH argvals = LENGTH argvars.
Proof.
  intros ctxt s t argvars; induction argvars as [|v vs IH]; intros argvals [Hr Hg].
  - injection Hg as <-; split; reflexivity.
  - cbn [loopSem.get_vars] in Hg.
    destruct (lookup v (loopSem.locals s)) as [x|] eqn:E; [|discriminate].
    destruct (loopSem.get_vars vs s) as [xs|] eqn:E'; [|discriminate].
    injection Hg as <-. destruct (IH xs (conj Hr eq_refl)) as [H1 H2].
    cbn [MAP get_vars]. rewrite (locals_rel_get_var ctxt _ t v x (conj Hr E)), H1.
    split; [reflexivity|cbn [LENGTH]; rewrite H2; reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_IMP" *)
Local Theorem state_rel_IMP : forall s t, state_rel s t -> clock t = loopSem.clock s.
Proof. intros s t (len & _ & _ & _ & H & _); exact H. Qed.

End Basic.

(** ** Contexts *)

Section Ctxt.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "set_fromNumSet" *)
Theorem set_fromNumSet : forall t, set (fromNumSet t) = domain t.
Proof.
  intros t. apply set_ext; intros x. unfold fromNumSet. change (set (MAP FST (toAList t)) x)
    with (x IN set (MAP FST (toAList t))).
  rewrite IN_set, domain_lookup. split.
  - intros Hx. apply in_map_iff in Hx as ([k []] & <- & Hin). exists tt.
    apply MEM_toAList, MEM_In, Hin.
  - intros [[] Hv]. apply in_map_iff. exists (x, tt). split; [reflexivity|].
    apply MEM_In, MEM_toAList, Hv.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "domain_toNumSet" *)
Theorem domain_toNumSet : forall ps, domain (toNumSet ps) = set ps.
Proof.
  induction ps as [|p ps IH]; cbn [toNumSet].
  - apply set_ext; intros x; cbn; tauto.
  - rewrite domain_insert, IH. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "domain_make_ctxt" *)
Theorem domain_make_ctxt : forall n ps (l : num_map N),
  domain (make_ctxt n ps l) = domain l UNION set ps.
Proof.
  intros n ps; revert n; induction ps as [|p ps IH]; intros n l; cbn [make_ctxt].
  - apply set_ext; intros x; unfold pred_set.UNION, pred_set.IN; cbn; tauto.
  - rewrite IH, domain_insert. apply set_ext; intros x; unfold pred_set.UNION, pred_set.IN; cbn; tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "make_ctxt_inj" *)
Theorem make_ctxt_inj : forall xs (l : num_map N) n,
  (forall x y v, lookup x l = SOME v /\ lookup y l = SOME v -> x = y /\ v < n) ->
  (forall x y v, lookup x (make_ctxt n xs l) = SOME v /\
                 lookup y (make_ctxt n xs l) = SOME v -> x = y).
Proof.
  induction xs as [|h xs IH]; intros l n Hl; cbn [make_ctxt].
  - intros x y v H; exact (proj1 (Hl x y v H)).
  - apply IH. intros x y v [Hx Hy]. rewrite lookup_insert in Hx, Hy.
    destruct (decide (x = h)), (decide (y = h)); subst.
    + injection Hx as <-. split; [reflexivity|lia].
    + injection Hx as <-. destruct (Hl y y n (conj Hy Hy)); lia.
    + injection Hy as <-. destruct (Hl x x n (conj Hx Hx)); lia.
    + destruct (Hl x y v (conj Hx Hy)). split; [assumption|lia].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "make_ctxt_APPEND" *)
Local Theorem make_ctxt_APPEND : forall xs ys n (l : num_map N),
  make_ctxt n (xs ++ ys) l = make_ctxt (n + 2 * LENGTH xs) ys (make_ctxt n xs l).
Proof.
  induction xs as [|x xs IH]; intros ys n l; cbn [make_ctxt app LENGTH].
  - rewrite N.add_0_r; reflexivity.
  - rewrite IH. f_equal. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "make_ctxt_NOT_MEM" *)
Local Theorem make_ctxt_NOT_MEM : forall xs n (l : num_map N) x,
  ~ MEM x xs -> lookup x (make_ctxt n xs l) = lookup x l.
Proof.
  induction xs as [|y xs IH]; intros n l x Hx; cbn [make_ctxt]; [reflexivity|].
  cbn [MEM] in Hx. rewrite IH.
  - rewrite lookup_insert. destruct (decide (x = y)) as [->|]; [|reflexivity].
    exfalso; apply Hx. apply orb_true_intro; left; apply bool_decide_spec; reflexivity.
  - intros H; apply Hx; rewrite H, orb_true_r; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_EL_make_ctxt" *)
Theorem lookup_EL_make_ctxt : forall params k n (l : num_map N),
  k < LENGTH params /\ ALL_DISTINCT params ->
  lookup (EL k params) (make_ctxt n params l) = SOME (2 * k + n).
Proof.
  induction params as [|p ps IH]; intros k n l [Hk Hd]; cbn [LENGTH] in Hk; [lia|].
  cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hn Hd]. cbn [make_ctxt].
  destruct (N.eq_dec k 0) as [->|Hk0].
  - change (EL 0 (p :: ps)) with p. rewrite make_ctxt_NOT_MEM.
    + rewrite lookup_insert. destruct (decide (p = p)); [f_equal; lia|congruence].
    + intros H; rewrite H in Hn; discriminate.
  - replace k with (SUC (k - 1)) by lia. rewrite EL_SUC. cbn [TL].
    rewrite IH by (split; [lia|exact Hd]). f_equal; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_make_ctxt_range" *)
Theorem lookup_make_ctxt_range : forall xs m (l : num_map N) n y,
  lookup n (make_ctxt m xs l) = SOME y ->
  lookup n l = SOME y \/ m <= y.
Proof.
  induction xs as [|x xs IH]; intros m l n y H; cbn [make_ctxt] in H; [left; exact H|].
  destruct (IH _ _ _ _ H) as [H1|H1]; [|right; lia].
  rewrite lookup_insert in H1. destruct (decide (n = x)); [injection H1 as <-; right; lia|].
  left; exact H1.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_make_ctxt_EVEN" *)
Theorem lookup_make_ctxt_EVEN : forall xs m (l : num_map N) n y,
  EVEN m /\ (forall k v, lookup k l = SOME v -> EVEN v) /\
  lookup n (make_ctxt m xs l) = SOME y -> EVEN y.
Proof.
  induction xs as [|x xs IH]; intros m l n y (Hm & Hl & H); cbn [make_ctxt] in H;
    [exact (Hl _ _ H)|].
  apply (IH (m + 2) (insert x m l) n y). split; [|split; [|exact H]].
  - rewrite N.even_add; rewrite Hm; reflexivity.
  - intros k v Hk. rewrite lookup_insert in Hk. destruct (decide (k = x));
      [injection Hk as <-; exact Hm|exact (Hl _ _ Hk)].
Qed.

Lemma fromList2_aux {A} : forall (l : list A) i (t : num_map A) n,
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

Lemma lookup_fromList2_EL {A} `{Inhabited A} (l : list A) k :
  k < LENGTH l -> lookup (2 * k) (fromList2 l) = SOME (EL k l).
Proof.
  intros Hk. unfold fromList2. rewrite fromList2_aux. rewrite N.sub_0_r.
  destruct (decide _) as [_|Hn].
  - rewrite N.mul_comm, N.div_mul by lia. rewrite EL_nth by exact Hk.
    apply nth_error_nth'. rewrite LENGTH_length in Hk. lia.
  - exfalso; apply Hn. split; [lia|]. split.
    + rewrite N.even_mul; reflexivity.
    + rewrite N.mul_comm, N.div_mul by lia. exact Hk.
Qed.

Lemma ALOOKUP_ZIP_EL {B} `{IB : Inhabited B} : forall (params : list N) (l : list B) n v,
  LENGTH params = LENGTH l ->
  ALOOKUP (ZIP (params, l)) n = SOME v ->
  exists k, k < LENGTH params /\ n = EL k params /\ v = EL k l.
Proof.
  induction params as [|p ps IH]; intros [|x l] n v Hl H; cbn [LENGTH] in Hl; try lia;
    try discriminate H.
  cbn [ZIP ALOOKUP] in H. destruct (decide (p = n)) as [->|Hne].
  - injection H as <-. exists 0. cbn [LENGTH]. split; [lia|split; reflexivity].
  - destruct (IH l n v ltac:(lia) H) as (k & Hk & -> & ->).
    exists (SUC k). cbn [LENGTH]. rewrite !EL_SUC. split; [lia|split; reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_make_ctxt" *)
Theorem locals_rel_make_ctxt : forall {B} `{Inhabited B} params xs (l : list B) (retv : B),
  ALL_DISTINCT params /\ DISJOINT (set params) (set xs) /\
  LENGTH params = LENGTH l ->
  locals_rel (make_ctxt 2 (params ++ xs) LN)
    (fromAList (ZIP (params, l))) (fromList2 (retv :: l)).
Proof.
  intros B IB params xs l retv (Hd & Hdj & Hl).
  assert (Hinj : forall x y v, lookup x (make_ctxt 2 (params ++ xs) LN) = SOME v /\
                    lookup y (make_ctxt 2 (params ++ xs) LN) = SOME v -> x = y).
  { apply make_ctxt_inj. intros x y v [Hx _]; discriminate Hx. }
  split; [|split].
  - split; [intros; exact Logic.I|]. intros x y [Hx Hy] He.
    apply domain_lookup in Hx as [vx Hx], Hy as [vy Hy].
    unfold find_var in He; rewrite Hx, Hy in He; subst vy.
    exact (Hinj x y vx (conj Hx Hy)).
  - intros n m Hn. split.
    + destruct (lookup_make_ctxt_range _ _ _ _ _ Hn) as [H1|H1]; [discriminate H1|lia].
    + apply (lookup_make_ctxt_EVEN (params ++ xs) 2 LN n m).
      split; [reflexivity|]. split; [intros k v Hk; discriminate Hk|exact Hn].
  - intros n v Hn. rewrite lookup_fromAList in Hn.
    destruct (ALOOKUP_ZIP_EL params l n v Hl Hn) as (k & Hk & -> & ->).
    exists (2 * k + 2). split.
    + rewrite make_ctxt_APPEND, make_ctxt_NOT_MEM.
      * apply lookup_EL_make_ctxt; split; assumption.
      * intros Hm. apply MEM_set in Hm. apply IN_DISJOINT in Hdj. apply Hdj.
        exists (EL k params). split; [|exact Hm].
        apply IN_set. rewrite EL_nth by exact Hk. apply nth_In. rewrite LENGTH_length in Hk. lia.
    + replace (2 * k + 2) with (2 * SUC k) by lia.
      rewrite lookup_fromList2_EL by (cbn [LENGTH]; lia). rewrite EL_SUC; reflexivity.
Qed.

End Ctxt.

(** ** Cut sets *)

Section Cutsets.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "domain_mk_new_cutset_not_empty" *)
Theorem domain_mk_new_cutset_not_empty : forall ctxt x1,
  domain (mk_new_cutset ctxt x1) <> EMPTY.
Proof.
  intros ctxt x1 H. unfold mk_new_cutset in H. rewrite domain_insert in H.
  assert (H0 : (fun x => x = 0 \/ domain (toNumSet (MAP (find_var ctxt) (fromNumSet x1))) x) 0)
    by (left; reflexivity).
  rewrite H in H0. exact H0.
Qed.

Lemma lookup_mk_new_cutset ctxt x1 n :
  domain (mk_new_cutset ctxt x1) n <->
  n = 0 \/ exists v, domain x1 v /\ n = find_var ctxt v.
Proof.
  unfold mk_new_cutset. rewrite domain_insert, domain_toNumSet.
  change (set (MAP (find_var ctxt) (fromNumSet x1)) n)
    with (n IN set (MAP (find_var ctxt) (fromNumSet x1))).
  rewrite IN_set, in_map_iff. split; intros [H|H]; auto; right.
  - destruct H as (v & <- & Hv). exists v. split; [|reflexivity].
    rewrite <- set_fromNumSet. apply IN_set, Hv.
  - destruct H as (v & Hv & ->). exists v. split; [reflexivity|].
    apply IN_set. rewrite set_fromNumSet. exact Hv.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_mk_new_cutset" *)
Theorem cut_env_mk_new_cutset : forall {B} ctxt (l1 l2 : num_map B) x1 y,
  locals_rel ctxt l1 l2 /\ domain x1 SUBSET domain l1 /\ lookup 0 l2 = SOME y ->
  exists env1, cut_env (mk_new_cutset ctxt x1, LN) l2 = SOME env1 /\
    locals_rel ctxt (inter l1 x1) env1.
Proof.
  intros B ctxt l1 l2 x1 y ((Hinj & Hc & Hl) & Hs & H0).
  unfold cut_env, cut_envs, cut_names. cbn [FST SND fst snd].
  destruct (classical_dec (domain (mk_new_cutset ctxt x1) SUBSET domain l2)) as [Hsub|Hsub].
  2:{ exfalso; apply Hsub. intros n Hn. unfold pred_set.IN in Hn.
      apply lookup_mk_new_cutset in Hn as [->|(v & Hv & ->)].
      - apply domain_lookup; eauto.
      - apply Hs in Hv. apply domain_lookup in Hv as [w Hw].
        destruct (Hl _ _ Hw) as (m & Hm & Hm'). unfold pred_set.IN, find_var; rewrite Hm.
        apply domain_lookup; eauto. }
  destruct (classical_dec (domain (@LN unit) SUBSET domain l2)) as [_|Hn].
  2:{ exfalso; apply Hn; intros n Hn'; destruct Hn'. }
  eexists; split; [reflexivity|].
  split; [exact Hinj|]. split; [exact Hc|].
  intros n v Hn. rewrite lookup_inter_alt in Hn. destruct (decide (domain x1 n)) as [Hd|]; [|discriminate].
  destruct (Hl _ _ Hn) as (m & Hm & Hm'). exists m. split; [exact Hm|].
  rewrite (proj1 (@inter_LN _ _ unit l2)). rewrite (proj2 (union_LN _)).
  rewrite lookup_inter_alt. destruct (decide _) as [|Hn']; [exact Hm'|].
  exfalso; apply Hn'. apply lookup_mk_new_cutset. right. exists n. split; [exact Hd|].
  unfold find_var; rewrite Hm; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_LN_IMP" *)
Theorem cut_env_LN_IMP : forall {B} s (l env : num_map B),
  cut_env (s, LN) l = SOME env ->
  cut_envs (s, LN) l = SOME (env, LN).
Proof.
  intros B s l env. unfold cut_env, cut_envs, cut_names. cbn [FST SND fst snd].
  destruct (classical_dec (domain s SUBSET domain l)); [|discriminate].
  destruct (classical_dec (domain (@LN unit) SUBSET domain l)) as [_|Hn];
    [|exfalso; apply Hn; intros n Hn'; destruct Hn'].
  rewrite (proj1 (@inter_LN _ _ unit l)), (proj2 (union_LN _)). intros H; injection H as <-. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "env_to_list_LN_IMP" *)
Theorem env_to_list_LN_IMP : forall (l : N -> N -> N) x p,
  env_to_list (a := a) LN l = (x, p) -> x = [].
Proof.
  intros l x p H. unfold env_to_list in H. injection H as <- _.
  unfold list_rearrange. destruct (classical_dec _); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "cut_env_mk_new_cutset_IMP" *)
Theorem cut_env_mk_new_cutset_IMP : forall {B} ctxt x1 (l1 l2 : num_map B),
  cut_env (mk_new_cutset ctxt x1, LN) l1 = SOME l2 ->
  lookup 0 l2 = lookup 0 l1.
Proof.
  intros B ctxt x1 l1 l2 H. apply cut_env_LN_IMP in H. unfold cut_envs, cut_names in H.
  cbn [FST SND fst snd] in H.
  destruct (classical_dec _); [|discriminate].
  destruct (classical_dec _); [|discriminate].
  injection H as <- _. rewrite lookup_inter_alt. destruct (decide _) as [|Hn]; [reflexivity|].
  exfalso; apply Hn. apply lookup_mk_new_cutset. left; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "LASTN_ADD_CONS" *)
Local Theorem LASTN_ADD_CONS : forall {A} (xs : list A) n x,
  ~ (LENGTH xs <= n) -> LASTN (n + 1) (x :: xs) = LASTN (n + 1) xs.
Proof.
  intros A xs n x H. unfold LASTN. cbn [List.rev]. rewrite !TAKE_firstn, firstn_app.
  rewrite length_rev. rewrite LENGTH_length in H.
  replace (N.to_nat (n + 1) - length xs)%nat with 0%nat by lia. rewrite app_nil_r. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "word_sh_SOME_MOD_dimword" *)
Local Theorem word_sh_SOME_MOD_dimword : forall sh (w : word a) n z,
  good_dimindex a /\ word_sh sh w n = SOME z -> n MOD dimword a = n.
Proof.
  intros sh w n z [Hg H]. unfold word_sh in H.
  destruct (n =? 0) eqn:E0; cbn [negb andb] in H.
  - apply N.eqb_eq in E0; subst. apply N.Div0.mod_0_l.
  - destruct (dimindex a <=? n) eqn:E1; [discriminate|]. apply N.leb_gt in E1.
    apply N.mod_small. unfold dimword. destruct Hg as [Hg|Hg]; rewrite Hg in *;
      [change (2 ^ 32) with 4294967296|change (2 ^ 64) with 18446744073709551616]; lia.
Qed.

End Cutsets.

(** ** Expressions *)

Lemma ALOOKUP_fmap {K V} `{EqDecision K} (fm : fmap K V) k :
  ALOOKUP (fmap_to_alist fm) k = FLOOKUP fm k.
Proof. rewrite (proj2 (ALOOKUP_EQ_FLOOKUP [] fm)). reflexivity. Qed.

Section Exp.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "comp_exp_preserves_eval" *)
Theorem comp_exp_preserves_eval : forall (s : loopSem.state a ffi_t) (e : loopLang.exp a) v
    (t : state a c ffi_t) ctxt,
  loopSem.eval s e = SOME v /\ good_dimindex a /\
  state_rel s t /\ locals_rel ctxt (loopSem.locals s) (locals t) ->
  word_exp t (comp_exp ctxt e) = SOME v.
Proof.
  intros s e; induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2| |]
    using loopProps.exp_nested_ind; intros v t ctxt (He & Hg & Hs & Hl);
    cbn [loopSem.eval comp_exp word_exp] in *.
  - exact He.
  - exact (locals_rel_get_var ctxt _ t n v (conj Hl He)).
  - destruct Hs as (len & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgl & _).
    unfold get_store. exact (Hgl _ _ He).
  - destruct (loopSem.eval s e) as [[w|]|] eqn:E; try discriminate.
    rewrite (IH _ t ctxt (conj eq_refl (conj Hg (conj Hs Hl)))).
    destruct Hs as (len & Hm & Hd & _).
    unfold loopSem.mem_load in He; unfold mem_load. rewrite Hm, Hd. exact He.
  - destruct (loopSem.the_words (MAP (loopSem.eval s) es)) as [ws|] eqn:E; [|discriminate].
    enough (Hw : the_words (MAP (word_exp t) (MAP (comp_exp ctxt) es)) = SOME ws)
      by (rewrite Hw; exact He).
    clear He. revert ws E. induction IH as [|x es Hx Hes IHes]; intros ws E; [exact E|].
    cbn [MAP loopSem.the_words the_words] in *.
    destruct (loopSem.eval s x) as [[w|]|] eqn:Ex; try discriminate.
    destruct (loopSem.the_words (MAP (loopSem.eval s) es)) as [ws'|] eqn:Ews; [|discriminate].
    rewrite (Hx _ t ctxt (conj eq_refl (conj Hg (conj Hs Hl)))), (IHes ws' eq_refl). exact E.
  - destruct (loopSem.eval s e1) as [[w1|]|] eqn:E1; try discriminate.
    destruct (loopSem.eval s e2) as [[w2|]|] eqn:E2; try discriminate.
    rewrite (IH1 _ t ctxt (conj eq_refl (conj Hg (conj Hs Hl)))),
      (IH2 _ t ctxt (conj eq_refl (conj Hg (conj Hs Hl)))). exact He.
  - injection He as <-. destruct Hs as (len & _ & _ & _ & _ & _ & _ & Hc & _).
    unfold get_store. rewrite ALOOKUP_fmap in Hc. exact Hc.
  - injection He as <-.
    destruct Hs as (len & _ & _ & _ & _ & _ & _ & Hc & Hlen & Htop & _).
    rewrite ALOOKUP_fmap in Hc, Hlen.
    cbn [MAP the_words word_exp]. unfold get_store. rewrite Hc, Hlen. cbn [the_words].
    assert (Hd : 32 <= dimindex a) by (destruct Hg as [Hg|Hg]; rewrite Hg; lia).
    assert (H1 : w2n (n2w 1 : word a) = 1).
    { rewrite w2n_n2w. apply N.mod_small. unfold dimword.
      apply (N.lt_le_trans _ (2 ^ 32)); [reflexivity|]. apply N.pow_le_mono_r; lia. }
    rewrite H1. unfold word_sh. cbn [negb N.eqb andb].
    destruct (N.leb_spec (dimindex a) 1) as [Hle|_]; [lia|]. cbn [OPTION_MAP option_map the_words].
    cbn [word_op OPTION_MAP option_map FOLDR]. rewrite Htop, WORD_MUL_LSL.
    f_equal. f_equal. change (2 ** 1) with 2. word_ring.
Qed.

End Exp.

(** ** [compile_correct] *)

Ltac lcbn :=
  cbn [loopSem.locals loopSem.globals loopSem.memory loopSem.mdomain loopSem.sh_mdomain
       loopSem.clock loopSem.code loopSem.be loopSem.ffi loopSem.base_addr loopSem.top_addr
       loopSem.set_locals loopSem.set_memory loopSem.set_clock loopSem.set_ffi loopSem.set_var
       loopSem.set_vars loopSem.set_globals loopSem.dec_clock loopSem.call_env] in *.

Ltac wcbn :=
  cbn [locals locals_size fp_regs store stack stack_limit stack_max state_stack_size memory
       mdomain sh_mdomain permute compile compile_oracle code_buffer data_buffer gc_fun handler
       clock termdep code be ffi
       set_locals set_locals_size set_fp_regs set_store_field set_stack set_stack_limit
       set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain set_permute
       set_compile set_compile_oracle set_code_buffer set_data_buffer set_gc_fun set_handler
       set_clock set_termdep set_code set_be set_ffi
       set_var set_vars unset_var set_store dec_clock call_env flush_state] in *.

Ltac csplit := repeat match goal with |- _ /\ _ => split end.

(** Prove [state_rel] of updated states from [state_rel] of the originals. *)
Ltac srel H :=
  let len := fresh "len" in
  let H' := fresh "Hsr" in
  pose proof H as H';
  destruct H' as (len & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
  exists len; lcbn; wcbn; csplit; try assumption; try congruence.

(** The [ffi] fields of related states agree. *)
Ltac sffi H :=
  let Hf := fresh "Hf" in
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (state_rel_intro _ _ H)))))) as Hf;
  lcbn; wcbn; congruence.

(** One step of wordSem's [evaluate] in the goal. *)
Ltac wstep :=
  rewrite evaluate_eqn; cbn [evaluate_body]; rewrite ?wordSem.fix_clock_evaluate.

Section CC.
Context {a : N} {c ffi_t : Type}.

Definition cc_post (res : option (loopSem.result a)) (s1 : loopSem.state a ffi_t)
    (t t1 : state a c ffi_t) (ctxt : num_map N) (retv : word_loc a)
    (res1 : option (result a)) : Prop :=
  match res with
  | NONE => state_rel s1 t1 /\ res1 = NONE /\ lookup 0 (locals t1) = SOME retv /\
            locals_rel ctxt (loopSem.locals s1) (locals t1) /\
            stack t1 = stack t /\ handler t1 = handler t
  | SOME (loopSem.Result v) => state_rel s1 t1 /\ res1 = SOME (Result retv v) /\
            stack t1 = stack t /\ handler t1 = handler t
  | SOME (loopSem.Exception v) =>
      state_rel s1 t1 /\
      (res1 <> SOME Error -> exists u1 u2, res1 = SOME (Exception u1 u2)) /\
      forall r l1 l2,
        jump_exc (set_handler (handler t) (set_stack (stack t) t1)) = SOME (r, (l1, l2)) ->
        res1 = SOME (Exception (Loc l1 l2) v) /\ r = t1
  | SOME (loopSem.Break n) => state_rel s1 t1 /\ res1 = SOME (Break n) /\
            lookup 0 (locals t1) = SOME retv /\
            locals_rel ctxt (loopSem.locals s1) (locals t1) /\
            stack t1 = stack t /\ handler t1 = handler t
  | SOME (loopSem.Continue n) => state_rel s1 t1 /\ res1 = SOME (Continue n) /\
            lookup 0 (locals t1) = SOME retv /\
            locals_rel ctxt (loopSem.locals s1) (locals t1) /\
            stack t1 = stack t /\ handler t1 = handler t
  | SOME loopSem.TimeOut => res1 = SOME TimeOut
  | SOME (loopSem.FinalFFI f) => res1 = SOME (FinalFFI f)
  | _ => False
  end.

Definition cc_P (prog : loopLang.prog a) (s : loopSem.state a ffi_t) : Prop :=
  forall res s1 (t : state a c ffi_t) ctxt retv l,
    loopSem.evaluate (prog, s) = (res, s1) /\ res <> SOME loopSem.Error /\
    state_rel s t /\ locals_rel ctxt (loopSem.locals s) (locals t) /\
    lookup 0 (locals t) = SOME retv /\
    good_dimindex a /\
    ~ isWord retv /\
    domain (loopLang.acc_vars prog LN) SUBSET domain ctxt ->
    exists t1 res1,
      evaluate (FST (comp ctxt prog l), t) = (res1, t1) /\
      ffi t1 = loopSem.ffi s1 /\
      cc_post res s1 t t1 ctxt retv res1.

Lemma lookup0_insert_find_var {B} ctxt (lcl lcl' : num_map B) v w :
  locals_rel ctxt lcl lcl' -> v IN domain ctxt ->
  lookup 0 (insert (find_var ctxt v) w lcl') = lookup 0 lcl'.
Proof.
  intros Hl Hv. rewrite lookup_insert. destruct (decide (0 = find_var ctxt v)) as [E|]; [|reflexivity].
  exfalso. exact (find_var_neq_0 v ctxt lcl lcl' (conj Hv Hl) (eq_sym E)).
Qed.

Lemma in_dom_insert_LN (n : N) (ctxt : num_map N) :
  domain (insert n tt LN) SUBSET domain ctxt -> n IN domain ctxt.
Proof. intros H. apply H. unfold pred_set.IN. rewrite domain_insert. left; reflexivity. Qed.

Lemma cc_Skip s : cc_P loopLang.Skip s.
Proof.
  intros res s1 t ctxt retv l (H & Hne & Hs & Hl & H0 & Hg & Hw & Hd).
  rewrite (proj1 loopSem.evaluate_def) in H. injection H as <- <-.
  exists t, NONE. cbn [comp FST fst]. wstep. split; [reflexivity|].
  split; [sffi Hs|].
  cbn [cc_post]. csplit; try assumption; try reflexivity.
Qed.

Lemma cc_Break s n : cc_P (loopLang.Break n) s.
Proof.
  intros res s1 t ctxt retv l (H & Hne & Hs & Hl & H0 & Hg & Hw & Hd).
  loopProps.unfold_eval_in H. injection H as <- <-.
  exists t, (SOME (Break n)). cbn [comp FST fst]. wstep. split; [reflexivity|].
  split; [sffi Hs|].
  cbn [cc_post]. csplit; try assumption; try reflexivity.
Qed.

Lemma cc_Continue s n : cc_P (loopLang.Continue n) s.
Proof.
  intros res s1 t ctxt retv l (H & Hne & Hs & Hl & H0 & Hg & Hw & Hd).
  loopProps.unfold_eval_in H. injection H as <- <-.
  exists t, (SOME (Continue n)). cbn [comp FST fst]. wstep. split; [reflexivity|].
  split; [sffi Hs|].
  cbn [cc_post]. csplit; try assumption; try reflexivity.
Qed.

Lemma cc_Fail s : cc_P loopLang.Fail s.
Proof.
  intros res s1 t ctxt retv l (H & Hne & _).
  loopProps.unfold_eval_in H. injection H as <- <-. congruence.
Qed.

Lemma cc_Tick s : cc_P loopLang.Tick s.
Proof.
  intros res s1 t ctxt retv l (H & Hne & Hs & Hl & H0 & Hg & Hw & Hd).
  loopProps.unfold_eval_in H. cbn [comp FST fst]. wstep.
  rewrite (state_rel_IMP _ _ Hs).
  destruct (loopSem.clock s =? 0) eqn:E; injection H as <- <-.
  - eexists _, _. split; [reflexivity|]. split; [|reflexivity].
    sffi Hs.
  - eexists _, _. split; [reflexivity|]. split; [sffi Hs|].
    cbn [cc_post]. split; [srel Hs; lia|]. wcbn; lcbn. csplit; try assumption; try reflexivity.
Qed.

Lemma mem_load_32_eq (m : word a -> word_loc a) dm be w :
  loopSem.mem_load_32 m dm be w = mem_load_32 m dm be w.
Proof. reflexivity. Qed.
Lemma mem_store_32_eq (m : word a -> word_loc a) dm be w hw :
  loopSem.mem_store_32 m dm be w hw = mem_store_32 m dm be w hw.
Proof. reflexivity. Qed.
Lemma mem_load_byte_aux_eq (m : word a -> word_loc a) dm be w :
  loopSem.mem_load_byte_aux m dm be w = mem_load_byte_aux m dm be w.
Proof. reflexivity. Qed.
Lemma mem_load_byte_aux_eq' (m : word a -> word_loc a) dm be :
  loopSem.mem_load_byte_aux m dm be = mem_load_byte_aux m dm be.
Proof. reflexivity. Qed.
Lemma mem_store_byte_aux_eq (m : word a -> word_loc a) dm be w b :
  loopSem.mem_store_byte_aux m dm be w b = mem_store_byte_aux m dm be w b.
Proof. reflexivity. Qed.

Lemma addr_word_exp (t : state a c ffi_t) ctxt (l : loopSem.state a ffi_t) ad w :
  locals_rel ctxt (loopSem.locals l) (locals t) ->
  lookup ad (loopSem.locals l) = SOME (Word w) ->
  word_exp t (Op asm.Add [Var (find_var ctxt ad); Const (n2w 0)]) = SOME (Word w).
Proof.
  intros Hl H. cbn [word_exp MAP the_words].
  rewrite (locals_rel_get_var ctxt _ t ad _ (conj Hl H)). cbn [the_words word_op FOLDR OPTION_MAP option_map].
  f_equal; f_equal. rewrite (proj1 WORD_ADD_0), (proj1 WORD_ADD_0). reflexivity.
Qed.

(** Common start of a case: name the hypotheses. *)
Ltac cc_intro := intros ?res ?s1 ?t ?ctxt ?retv ?l (?H & ?Hne & ?Hs & ?Hl & ?H0 & ?Hg & ?Hw & ?Hd).

Lemma cc_Assign s v e : cc_P (loopLang.Assign v e) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.eval s e) as [w|] eqn:E; injection H as <- <-; [|congruence].
  cbn [loopLang.acc_vars] in Hd. apply in_dom_insert_LN in Hd.
  cbn [comp FST fst]. wstep.
  rewrite (comp_exp_preserves_eval s e w t ctxt (conj E (conj Hg (conj Hs Hl)))).
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
  split; [rewrite (lookup0_insert_find_var ctxt _ _ v w Hl Hd); exact H0|].
  split; [apply locals_rel_insert; split; assumption|]. split; reflexivity.
Qed.

Lemma cc_LocValue s v m : cc_P (loopLang.LocValue v m) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (classical_dec (m IN domain (loopSem.code s))) as [Hm|]; injection H as <- <-; [|congruence].
  cbn [loopLang.acc_vars] in Hd. apply in_dom_insert_LN in Hd.
  cbn [comp FST fst]. wstep.
  destruct (classical_dec (m IN domain (code t))) as [_|Hn].
  2:{ exfalso; apply Hn. apply domain_lookup in Hm as [[ps b] Hm].
      destruct (state_rel_intro _ _ Hs) as (_ & _ & _ & _ & _ & _ & _ & Hc).
      apply domain_lookup. eexists. exact (proj1 (Hc _ _ _ Hm)). }
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
  split; [rewrite (lookup0_insert_find_var ctxt _ _ v _ Hl Hd); exact H0|].
  split; [apply locals_rel_insert; split; assumption|]. split; reflexivity.
Qed.

Lemma cc_SetGlobal s dst e : cc_P (loopLang.SetGlobal dst e) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.eval s e) as [w|] eqn:E; injection H as <- <-; [|congruence].
  cbn [comp FST fst]. wstep. cbn [orb].
  rewrite (comp_exp_preserves_eval s e w t ctxt (conj E (conj Hg (conj Hs Hl)))).
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split.
  { destruct Hs as (len & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    exists len. unfold set_store, loopSem.set_globals; wcbn; lcbn. rewrite !ALOOKUP_fmap in *.
    csplit; try assumption.
    intros n v Hn. rewrite !FLOOKUP_UPDATE in *. destruct (decide (dst = n)) as [<-|Hdn].
    - destruct (decide _) as [_|C]; [exact Hn|congruence].
    - destruct (decide _) as [C|_]; [injection C; congruence|exact (H10 _ _ Hn)]. }
  unfold set_store; wcbn; lcbn. csplit; try assumption; reflexivity.
Qed.

Lemma cc_Store s e v : cc_P (loopLang.Store e v) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.eval s e) as [[adr|]|] eqn:E; try (injection H as <- <-; congruence).
  destruct (lookup v (loopSem.locals s)) as [w|] eqn:Ev; [|injection H as <- <-; congruence].
  destruct (loopSem.mem_store adr w s) as [st|] eqn:Em; injection H as <- <-; [|congruence].
  cbn [comp FST fst]. wstep.
  rewrite (comp_exp_preserves_eval s e _ t ctxt (conj E (conj Hg (conj Hs Hl)))),
    (locals_rel_get_var ctxt _ t v w (conj Hl Ev)).
  unfold loopSem.mem_store in Em; unfold mem_store.
  destruct (state_rel_intro _ _ Hs) as (Hm & Hdm & _).
  rewrite Hdm. destruct (classical_dec _); [|discriminate]. injection Em as <-.
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. wcbn; lcbn. csplit; try assumption; reflexivity.
Qed.

Lemma cc_Store32 s ad v : cc_P (loopLang.Store32 ad v) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup ad (loopSem.locals s)) as [[w|]|] eqn:Ea; try (injection H as <- <-; congruence);
  destruct (lookup v (loopSem.locals s)) as [[b|]|] eqn:Ev; try (injection H as <- <-; congruence).
  destruct (loopSem.mem_store_32 _ _ _ _ _) as [m|] eqn:Em; injection H as <- <-; [|congruence].
  cbn [comp FST fst]. wstep. cbn [inst].
  rewrite (addr_word_exp t ctxt s ad w Hl Ea), (locals_rel_get_var ctxt _ t v _ (conj Hl Ev)).
  destruct (state_rel_intro _ _ Hs) as (Hm & Hdm & _ & Hbe & _).
  rewrite Hm, Hdm, Hbe, <- mem_store_32_eq, Em.
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. wcbn; lcbn. csplit; try assumption; reflexivity.
Qed.

Lemma cc_StoreByte s ad v : cc_P (loopLang.StoreByte ad v) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup ad (loopSem.locals s)) as [[w|]|] eqn:Ea; try (injection H as <- <-; congruence);
  destruct (lookup v (loopSem.locals s)) as [[b|]|] eqn:Ev; try (injection H as <- <-; congruence).
  destruct (loopSem.mem_store_byte_aux _ _ _ _ _) as [m|] eqn:Em; injection H as <- <-; [|congruence].
  cbn [comp FST fst]. wstep. cbn [inst].
  rewrite (addr_word_exp t ctxt s ad w Hl Ea), (locals_rel_get_var ctxt _ t v _ (conj Hl Ev)).
  destruct (state_rel_intro _ _ Hs) as (Hm & Hdm & _ & Hbe & _).
  rewrite Hm, Hdm, Hbe, <- mem_store_byte_aux_eq, Em.
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. wcbn; lcbn. csplit; try assumption; reflexivity.
Qed.

Lemma cc_Load32 s ad v : cc_P (loopLang.Load32 ad v) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup ad (loopSem.locals s)) as [[w|]|] eqn:Ea; try (injection H as <- <-; congruence).
  destruct (loopSem.mem_load_32 _ _ _ _) as [b|] eqn:Em; injection H as <- <-; [|congruence].
  cbn [loopLang.acc_vars] in Hd. apply in_dom_insert_LN in Hd.
  cbn [comp FST fst]. wstep. cbn [inst].
  rewrite (addr_word_exp t ctxt s ad w Hl Ea).
  destruct (state_rel_intro _ _ Hs) as (Hm & Hdm & _ & Hbe & _).
  rewrite Hm, Hdm, Hbe, <- mem_load_32_eq, Em.
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
  split; [rewrite (lookup0_insert_find_var ctxt _ _ v _ Hl Hd); exact H0|].
  split; [apply locals_rel_insert; split; assumption|]. split; reflexivity.
Qed.

Lemma cc_LoadByte s ad v : cc_P (loopLang.LoadByte ad v) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup ad (loopSem.locals s)) as [[w|]|] eqn:Ea; try (injection H as <- <-; congruence).
  destruct (loopSem.mem_load_byte_aux _ _ _ _) as [b|] eqn:Em; injection H as <- <-; [|congruence].
  cbn [loopLang.acc_vars] in Hd. apply in_dom_insert_LN in Hd.
  cbn [comp FST fst]. wstep. cbn [inst].
  rewrite (addr_word_exp t ctxt s ad w Hl Ea).
  destruct (state_rel_intro _ _ Hs) as (Hm & Hdm & _ & Hbe & _).
  rewrite Hm, Hdm, Hbe, <- mem_load_byte_aux_eq, Em.
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
  split; [rewrite (lookup0_insert_find_var ctxt _ _ v _ Hl Hd); exact H0|].
  split; [apply locals_rel_insert; split; assumption|]. split; reflexivity.
Qed.

Lemma cc_Return s ns : cc_P (loopLang.Return ns) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.get_vars ns s) as [vs|] eqn:E; injection H as <- <-; [|congruence].
  cbn [comp FST fst]. wstep.
  destruct (locals_rel_get_vars ctxt s t ns vs (conj Hl E)) as [Hgv _].
  unfold get_var. rewrite H0, Hgv. destruct retv as [w|l1 l2]; [exfalso; apply Hw; reflexivity|].
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. wcbn. csplit; reflexivity.
Qed.

Lemma jump_exc_same (t t' : state a c ffi_t) l :
  jump_exc t = SOME (t', l) ->
  jump_exc (set_handler (handler t) (set_stack (stack t) t')) = SOME (t', l).
Proof.
  intros H. destruct t. unfold jump_exc in *. cbn -[LASTN] in *.
  destruct (_ <? _); [|discriminate].
  match type of H with context [match ?x with _ => _ end] =>
    destruct x as [|[m e0 e [[n [l1 l2]]|]] xs] end; try discriminate.
  injection H as <- <-. reflexivity.
Qed.

Lemma set_handler_stack_id (t : state a c ffi_t) :
  set_handler (handler t) (set_stack (stack t) t) = t.
Proof. destruct t; reflexivity. Qed.

Lemma cc_Raise s n : cc_P (loopLang.Raise n) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup n (loopSem.locals s)) as [w|] eqn:E; injection H as <- <-; [|congruence].
  cbn [comp FST fst]. wstep. rewrite (locals_rel_get_var ctxt _ t n w (conj Hl E)).
  destruct (jump_exc t) as [[t' [l1 l2]]|] eqn:Ej.
  - eexists _, _. split; [reflexivity|].
    assert (Hj := Ej). unfold jump_exc in Hj.
    destruct (handler t <? LENGTH (stack t)); [|discriminate].
    destruct (LASTN _ _) as [|[m e0 e [[n' [l1' l2']]|]] xs]; try discriminate.
    injection Hj as <- <- <-.
    split; [sffi Hs|]. cbn [cc_post]. split; [srel Hs|]. split; [eauto|].
    intros r k1 k2 Hr. rewrite (jump_exc_same _ _ _ Ej) in Hr. injection Hr as <- <- <-.
    split; reflexivity.
  - eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
    split; [srel Hs|]. split; [intros C; congruence|].
    intros r k1 k2 Hr. rewrite set_handler_stack_id, Ej in Hr. discriminate.
Qed.

Lemma cc_Mark s p :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.Mark p, s) -> cc_P p' s') ->
  cc_P (loopLang.Mark p) s.
Proof.
  intros IH. cc_intro. loopProps.unfold_eval_in H. cbn [comp loopLang.acc_vars] in *.
  apply (IH p s ltac:(right; split; [reflexivity|cbn [fst snd loopSem.psize]; lia])).
  csplit; assumption.
Qed.

Lemma cc_Seq s p q :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.Seq p q, s) -> cc_P p' s') ->
  cc_P (loopLang.Seq p q) s.
Proof.
  intros IH. cc_intro. loopProps.unfold_eval_in H. cbn [comp loopLang.acc_vars] in *.
  destruct (comp ctxt p l) as [wp lp] eqn:Ep. destruct (comp ctxt q lp) as [wq lq] eqn:Eq.
  cbn [FST fst]. wstep.
  assert (Hdp : domain (loopLang.acc_vars p LN) SUBSET domain ctxt)
    by (intros x Hx; apply Hd; unfold pred_set.IN in *; apply loopProps.acc_vars_acc_iff; left; exact Hx).
  assert (Hdq : domain (loopLang.acc_vars q LN) SUBSET domain ctxt)
    by (intros x Hx; apply Hd; unfold pred_set.IN in *; apply loopProps.acc_vars_acc_iff; right;
        apply loopProps.acc_vars_acc_iff; left; exact Hx).
  destruct (loopSem.evaluate (p, s)) as [r1 u1] eqn:E1.
  assert (Hr1 : r1 <> SOME loopSem.Error) by (intros ->; injection H as <- <-; congruence).
  destruct (IH p s ltac:(right; split; [reflexivity|cbn [fst snd loopSem.psize]; lia])
              r1 u1 t ctxt retv l (conj E1 (conj Hr1 (conj Hs (conj Hl (conj H0 (conj Hg (conj Hw Hdp))))))))
    as (t1 & res1 & Ev1 & Hf1 & Hp1).
  rewrite Ep in Ev1. cbn [FST fst] in Ev1. rewrite Ev1.
  destruct r1 as [r1|].
  - injection H as <- <-. exists t1, res1.
    assert (Hn : res1 <> NONE).
    { destruct r1; cbn [cc_post] in Hp1; try contradiction;
        repeat match goal with Hq : _ /\ _ |- _ => destruct Hq end; try congruence.
      intros ->. match goal with Hq : NONE <> SOME Error -> _ |- _ =>
        destruct (Hq ltac:(discriminate)) as (? & ? & ?); discriminate end. }
    destruct (bool_decide (res1 = NONE)) eqn:Eb.
    + apply bool_decide_spec in Eb; contradiction.
    + split; [reflexivity|]. split; assumption.
  - cbn [cc_post] in Hp1. destruct Hp1 as (Hs1 & -> & H01 & Hl1 & Hst1 & Hh1).
    cbn [bool_decide decide]. destruct (bool_decide (@NONE (result a) = NONE)) eqn:Eb.
    2:{ exfalso. rewrite (proj2 (bool_decide_spec _) eq_refl) in Eb. discriminate. }
    pose proof (loopSem.evaluate_clock _ _ _ _ E1) as Hc1.
    destruct (IH q u1 ltac:(cbn [fst snd]; unfold loopSem.eval_lt; cbn [fst snd loopSem.psize];
                             destruct (N.lt_ge_cases (loopSem.clock u1) (loopSem.clock s)); [left; lia|right; split; lia])
                res s1 t1 ctxt retv lp (conj H (conj Hne (conj Hs1 (conj Hl1 (conj H01 (conj Hg (conj Hw Hdq))))))))
      as (t2 & res2 & Ev2 & Hf2 & Hp2).
    rewrite Eq in Ev2. cbn [FST fst] in Ev2. rewrite Ev2.
    exists t2, res2. split; [reflexivity|]. split; [exact Hf2|].
    destruct res as [[]|]; cbn [cc_post] in *; try contradiction;
      repeat match goal with Hq : _ /\ _ |- _ => destruct Hq end;
      csplit; try assumption; try congruence.
    intros r k1 k2 Hr. rewrite <- Hst1, <- Hh1 in Hr. eauto.
Qed.

Lemma dom_ins_sub k (L : num_set) (D : N -> Prop) :
  domain (insert k tt L) SUBSET D -> k IN D /\ domain L SUBSET D.
Proof.
  intros H. split; [apply H; unfold pred_set.IN; rewrite domain_insert; left; reflexivity|].
  intros x Hx; apply H; unfold pred_set.IN in *; rewrite domain_insert; right; exact Hx.
Qed.

Lemma l0_ins {B} ctxt v w (L : num_map B) :
  (forall n m, lookup n ctxt = SOME m -> m <> 0 /\ EVEN m) -> v IN domain ctxt ->
  lookup 0 (insert (find_var ctxt v) w L) = lookup 0 L.
Proof.
  intros Hc Hv. rewrite lookup_insert. destruct (decide (0 = find_var ctxt v)) as [E|]; [|reflexivity].
  exfalso. exact (find_var_neq_0_ctxt ctxt v (conj Hc Hv) (eq_sym E)).
Qed.

Lemma word_cmp_Word cmp0 (x y : word a) :
  word_cmp cmp0 (Word x) (Word y) = SOME (asm.word_cmp cmp0 x y).
Proof. destruct cmp0; reflexivity. Qed.

Lemma write_bytearray_eq : forall bs (a0 : word a) m dm be,
  loopSem.write_bytearray a0 bs m dm be = write_bytearray a0 bs m dm be.
Proof. induction bs as [|b bs IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma locals_rel_inter {B} ctxt (l1 l2 : num_map B) (x : num_set) :
  locals_rel ctxt l1 l2 -> locals_rel ctxt (inter l1 x) l2.
Proof.
  intros (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros n v Hn. rewrite lookup_inter_alt in Hn. destruct (decide _); [exact (H3 _ _ Hn)|discriminate].
Qed.

Lemma cc_Arith s ar : cc_P (loopLang.Arith ar) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  pose proof Hl as (_ & Hc & _).
  destruct ar as [r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3]; cbn [loopSem.loop_arith] in H;
    cbn [loopLang.acc_vars] in Hd.
  - destruct (lookup r3 (loopSem.locals s)) as [[w3|]|] eqn:E3; try (injection H as <- <-; congruence).
    destruct (lookup r4 (loopSem.locals s)) as [[w4|]|] eqn:E4; try (injection H as <- <-; congruence).
    injection H as <- <-.
    apply dom_ins_sub in Hd as [Hd1 Hd]. apply dom_ins_sub in Hd as [Hd2 _].
    cbn [comp FST fst]. wstep. cbn [inst get_vars].
    rewrite (locals_rel_get_var ctxt _ t r3 _ (conj Hl E3)), (locals_rel_get_var ctxt _ t r4 _ (conj Hl E4)).
    eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
    split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
    split; [rewrite !(l0_ins ctxt) by assumption; exact H0|].
    split; [apply locals_rel_insert; split; [apply locals_rel_insert; split|]; assumption|].
    split; reflexivity.
  - destruct (lookup r3 (loopSem.locals s)) as [[w3|]|] eqn:E3; try (injection H as <- <-; congruence).
    destruct (lookup r4 (loopSem.locals s)) as [[w4|]|] eqn:E4; try (injection H as <- <-; congruence).
    destruct (lookup r5 (loopSem.locals s)) as [[w5|]|] eqn:E5; try (injection H as <- <-; congruence).
    cbv zeta in H. destruct (_ && _) eqn:Eb; injection H as <- <-; [|congruence].
    apply dom_ins_sub in Hd as [Hd1 Hd]. apply dom_ins_sub in Hd as [Hd2 _].
    cbn [comp FST fst]. wstep. cbn [inst get_vars].
    rewrite (locals_rel_get_var ctxt _ t r3 _ (conj Hl E3)), (locals_rel_get_var ctxt _ t r4 _ (conj Hl E4)),
      (locals_rel_get_var ctxt _ t r5 _ (conj Hl E5)). cbv zeta. rewrite Eb.
    eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
    split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
    split; [rewrite !(l0_ins ctxt) by assumption; exact H0|].
    split; [apply locals_rel_insert; split; [apply locals_rel_insert; split|]; assumption|].
    split; reflexivity.
  - destruct (lookup r3 (loopSem.locals s)) as [[w3|]|] eqn:E3; try (injection H as <- <-; congruence).
    destruct (lookup r2 (loopSem.locals s)) as [[w2|]|] eqn:E2; try (injection H as <- <-; congruence).
    destruct (negb _) eqn:Eb; injection H as <- <-; [|congruence].
    apply dom_ins_sub in Hd as [Hd1 _].
    cbn [comp FST fst]. wstep. cbn [inst get_vars].
    rewrite (locals_rel_get_var ctxt _ t r3 _ (conj Hl E3)), (locals_rel_get_var ctxt _ t r2 _ (conj Hl E2)).
    rewrite Eb.
    eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
    split; [srel Hs|]. split; [reflexivity|]. unfold set_var, loopSem.set_var; wcbn; lcbn.
    split; [rewrite !(l0_ins ctxt) by assumption; exact H0|].
    split; [apply locals_rel_insert; split; assumption|].
    split; reflexivity.
Qed.

Lemma cc_FFI s fname p1 l1 p2 l2 live : cc_P (loopLang.FFI fname p1 l1 p2 l2 live) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup l1 (loopSem.locals s)) as [[w1|]|] eqn:E1; try (injection H as <- <-; congruence).
  destruct (lookup p1 (loopSem.locals s)) as [[w2|]|] eqn:E2; try (injection H as <- <-; congruence).
  destruct (lookup l2 (loopSem.locals s)) as [[w3|]|] eqn:E3; try (injection H as <- <-; congruence).
  destruct (lookup p2 (loopSem.locals s)) as [[w4|]|] eqn:E4; try (injection H as <- <-; congruence).
  destruct (loopSem.cut_state live s) as [s'|] eqn:Ec; [|injection H as <- <-; congruence].
  unfold loopSem.cut_state in Ec. destruct (classical_dec _) as [Hsub|]; [|discriminate].
  injection Ec as <-. lcbn.
  cbn [comp FST fst]. wstep.
  rewrite (locals_rel_get_var ctxt _ t l1 _ (conj Hl E1)), (locals_rel_get_var ctxt _ t p1 _ (conj Hl E2)),
    (locals_rel_get_var ctxt _ t l2 _ (conj Hl E3)), (locals_rel_get_var ctxt _ t p2 _ (conj Hl E4)).
  destruct (cut_env_mk_new_cutset ctxt (loopSem.locals s) (locals t) live retv (conj Hl (conj Hsub H0)))
    as (env1 & Henv & Hl1).
  rewrite Henv.
  pose proof (cut_env_mk_new_cutset_IMP _ _ _ _ Henv) as Henv0.
  destruct (state_rel_intro _ _ Hs) as (Hm & Hdm & _ & Hbe & Hff & _).
  rewrite Hm, Hdm, Hbe, Hff. rewrite !mem_load_byte_aux_eq' in H.
  destruct (read_bytearray _ _ _) as [bytes|]; [|injection H as <- <-; congruence].
  destruct (read_bytearray _ _ _) as [bytes2|]; [|injection H as <- <-; congruence].
  destruct (call_FFI _ _ _ _) as [nffi nbytes|outc]; injection H as <- <-.
  - eexists _, _. split; [reflexivity|]. split; [wcbn; lcbn; reflexivity|]. cbn [cc_post].
    split; [srel Hs; symmetry; apply write_bytearray_eq|]. split; [reflexivity|]. wcbn; lcbn.
    split; [rewrite Henv0; exact H0|]. split; [exact Hl1|]. split; reflexivity.
  - eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. reflexivity.
Qed.

Lemma get_var_imm_rel ctxt (s : loopSem.state a ffi_t) (t : state a c ffi_t) ri v :
  locals_rel ctxt (loopSem.locals s) (locals t) -> loopSem.get_var_imm ri s = SOME v ->
  get_var_imm (find_reg_imm ctxt ri) t = SOME v.
Proof.
  intros Hl H. destruct ri as [n|w]; cbn in *; [|exact H].
  exact (locals_rel_get_var ctxt _ t n v (conj Hl H)).
Qed.

Lemma cc_res_not_none (s1 : loopSem.state a ffi_t) (t t1 : state a c ffi_t) ctxt retv (res1 : option (result a)) r :
  cc_post (SOME r) s1 t t1 ctxt retv res1 -> res1 <> NONE.
Proof.
  intros Hp ->. destruct r; cbn [cc_post] in Hp; try contradiction;
    repeat match goal with Hq : _ /\ _ |- _ => destruct Hq end; try congruence.
  match goal with Hq : NONE <> SOME Error -> _ |- _ =>
    destruct (Hq ltac:(discriminate)) as (? & ? & ?); discriminate end.
Qed.

Lemma bool_decide_none_false (r : option (result a)) : r <> NONE -> bool_decide (r = NONE) = false.
Proof. intros Hn. destruct (bool_decide (r = NONE)) eqn:E; [|reflexivity]. apply bool_decide_spec in E; contradiction. Qed.

Lemma bool_decide_none_true : bool_decide (@NONE (result a) = NONE) = true.
Proof. apply bool_decide_spec; reflexivity. Qed.

Lemma cc_If s cmp0 r1 ri c1 c2 lo :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.If cmp0 r1 ri c1 c2 lo, s) -> cc_P p' s') ->
  cc_P (loopLang.If cmp0 r1 ri c1 c2 lo) s.
Proof.
  intros IH. cc_intro. loopProps.unfold_eval_in H.
  destruct (lookup r1 (loopSem.locals s)) as [[x|]|] eqn:Ex; try (injection H as <- <-; congruence).
  destruct (loopSem.get_var_imm ri s) as [[y|]|] eqn:Ey; try (injection H as <- <-; congruence).
  cbv zeta in H. cbn [comp loopLang.acc_vars] in *.
  destruct (comp ctxt c1 l) as [wp l1'] eqn:Ec1. destruct (comp ctxt c2 l1') as [wq l2'] eqn:Ec2.
  cbn [FST fst]. wstep. rewrite (evaluate_eqn (If _ _ _ _ _)). cbn [evaluate_body].
  rewrite (locals_rel_get_var ctxt _ t r1 _ (conj Hl Ex)), (get_var_imm_rel ctxt s t ri _ Hl Ey),
    word_cmp_Word.
  assert (Hd1 : domain (loopLang.acc_vars c1 LN) SUBSET domain ctxt)
    by (intros z Hz; apply Hd; unfold pred_set.IN in *; apply loopProps.acc_vars_acc_iff; left; exact Hz).
  assert (Hd2 : domain (loopLang.acc_vars c2 LN) SUBSET domain ctxt)
    by (intros z Hz; apply Hd; unfold pred_set.IN in *; apply loopProps.acc_vars_acc_iff; right;
        apply loopProps.acc_vars_acc_iff; left; exact Hz).
  assert (G : forall cb wb lb, (cb = c1 \/ cb = c2) -> wb = FST (comp ctxt cb lb) ->
            domain (loopLang.acc_vars cb LN) SUBSET domain ctxt ->
            loopSem.cut_res lo (loopSem.evaluate (cb, s)) = (res, s1) ->
            exists t1 res1,
              (let '(res0, s2) := evaluate (wb, t) in
               if bool_decide (res0 = NONE) then evaluate (Tick, s2) else (res0, s2)) = (res1, t1) /\
              ffi t1 = loopSem.ffi s1 /\ cc_post res s1 t t1 ctxt retv res1).
  { intros cb wb lb Hcb -> Hdb Hcut.
    destruct (loopSem.evaluate (cb, s)) as [r u] eqn:Eb.
    assert (Hr : r <> SOME loopSem.Error).
    { intros ->. cbn in Hcut. injection Hcut as <- <-. congruence. }
    destruct (IH cb s ltac:(right; split; [reflexivity|cbn [fst snd loopSem.psize];
                                           destruct Hcb as [->| ->]; lia])
                r u t ctxt retv lb (conj Eb (conj Hr (conj Hs (conj Hl (conj H0 (conj Hg (conj Hw Hdb))))))))
      as (t1 & res1 & Ev & Hf & Hp).
    rewrite Ev. destruct r as [r|].
    - cbn [loopSem.cut_res IS_SOME] in Hcut. injection Hcut as <- <-.
      rewrite (bool_decide_none_false _ (cc_res_not_none _ t t1 ctxt retv res1 r Hp)).
      exists t1, res1. split; [reflexivity|]. split; assumption.
    - cbn [cc_post] in Hp. destruct Hp as (Hs1 & -> & H01 & Hl1 & Hst & Hh).
      rewrite bool_decide_none_true. wstep.
      cbn [loopSem.cut_res IS_SOME] in Hcut. unfold loopSem.cut_state in Hcut.
      destruct (classical_dec _) as [Hsub|]; [|injection Hcut as <- <-; congruence].
      lcbn. rewrite (state_rel_IMP _ _ Hs1).
      destruct (loopSem.clock u =? 0) eqn:Ec; injection Hcut as <- <-.
      + eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. reflexivity.
      + eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. cbn [cc_post].
        split; [srel Hs1; lia|]. wcbn; lcbn. split; [reflexivity|]. split; [exact H01|].
        split; [apply locals_rel_inter; exact Hl1|]. split; assumption. }
  destruct (asm.word_cmp cmp0 x y).
  - apply (G c1 wp l (or_introl eq_refl)); [rewrite Ec1; reflexivity|exact Hd1|exact H].
  - apply (G c2 wq l1' (or_intror eq_refl)); [rewrite Ec2; reflexivity|exact Hd2|exact H].
Qed.

Lemma lookup_ins_ne {B} k k' (v : B) (L : num_map B) : k <> k' -> lookup k (insert k' v L) = lookup k L.
Proof. intros H. rewrite lookup_insert. destruct (decide (k = k')); [contradiction|reflexivity]. Qed.

Lemma lookup_ins_eq {B} k (v : B) (L : num_map B) : lookup k (insert k v L) = SOME v.
Proof. rewrite lookup_insert. destruct (decide (k = k)); [reflexivity|congruence]. Qed.

Lemma loop_get_vars_cons (s : loopSem.state a ffi_t) x xs v vs :
  loopSem.get_vars (x :: xs) s = SOME (v :: vs) ->
  lookup x (loopSem.locals s) = SOME v /\ loopSem.get_vars xs s = SOME vs.
Proof.
  cbn [loopSem.get_vars]. destruct (lookup x _); [|discriminate].
  destruct (loopSem.get_vars xs s); [|discriminate]. intros H; injection H as <- <-. split; reflexivity.
Qed.

Lemma gv_sv_ne k k' v (t : state a c ffi_t) : k <> k' -> get_var k (set_var k' v t) = get_var k t.
Proof. intros H. unfold get_var, set_var; wcbn. apply lookup_ins_ne, H. Qed.

Lemma gv_sv_eq k v (t : state a c ffi_t) : get_var k (set_var k v t) = SOME v.
Proof. unfold get_var, set_var; wcbn. apply lookup_ins_eq. Qed.

Lemma cc_Primitive s lhss pop rhss : cc_P (loopLang.Primitive lhss pop rhss) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  pose proof Hl as (_ & Hc & _).
  destruct (loopSem.get_vars rhss s) as [ws|] eqn:Egv; [|injection H as <- <-; congruence].
  destruct (locals_rel_get_vars ctxt s t rhss ws (conj Hl Egv)) as [_ Hlen].
  destruct pop. cbn [loopSem.loop_primop] in H.
  destruct (_ && _) eqn:Eb; [|injection H as <- <-; congruence].
  apply andb_prop in Eb as [Elen Ew]. apply N.eqb_eq in Elen.
  destruct ws as [|w1 [|w2 [|w3 [|w4 ws]]]]; cbn [LENGTH] in Elen; try lia.
  cbn [EVERY] in Ew. destruct w1 as [li|]; [|discriminate]. destruct w2 as [ri|]; [|discriminate].
  destruct w3 as [ci|]; [|discriminate].
  change (EL 0 [Word li; Word ri; Word (a := a) ci]) with (Word li) in H.
  change (EL 1 [Word li; Word ri; Word (a := a) ci]) with (Word ri) in H.
  change (EL 2 [Word li; Word ri; Word (a := a) ci]) with (Word ci) in H. cbn [loopSem.theWord] in H.
  destruct (backend_common.word_add_carry li ri ci) as [rs co] eqn:Eac. cbn [LENGTH] in H.
  destruct (LENGTH lhss =? _) eqn:Ell; [|injection H as <- <-; congruence].
  apply N.eqb_eq in Ell.
  destruct lhss as [|y1 [|y2 [|y3 lhss]]]; cbn [LENGTH] in Ell; try lia.
  injection H as <- <-.
  destruct rhss as [|x1 [|x2 [|x3 [|x4 rhss]]]]; cbn [LENGTH] in Hlen; try lia.
  apply loop_get_vars_cons in Egv as [E1 Egv]. apply loop_get_vars_cons in Egv as [E2 Egv].
  apply loop_get_vars_cons in Egv as [E3 _].
  cbn [loopLang.acc_vars list_insert] in Hd.
  apply dom_ins_sub in Hd as [Hd2 Hd]. apply dom_ins_sub in Hd as [Hd1 _].
  assert (Hodd : forall n, find_var ctxt n <> 1 /\ find_var ctxt n <> 3)
    by (intros n; split; apply find_var_neq_odd; split; [exact Hc|discriminate|exact Hc|discriminate]).
  cbn [comp]. cbv zeta.
  change (EL 0 [y1; y2]) with y1. change (EL 1 [y1; y2]) with y2.
  change (EL 0 [x1; x2; x3]) with x1. change (EL 1 [x1; x2; x3]) with x2.
  change (EL 2 [x1; x2; x3]) with x3.
  destruct (decide _) as [_|Hn]; [|exfalso; apply Hn; split; reflexivity].
  cbn [FST fst].
  wstep. wstep. cbn [word_exp]. rewrite (locals_rel_get_var ctxt _ t x3 _ (conj Hl E3)).
  rewrite bool_decide_none_true.
  wstep. wstep. cbn [inst get_vars].
  rewrite (gv_sv_ne _ 1 _ _ (proj1 (Hodd x1))), (gv_sv_ne _ 1 _ _ (proj1 (Hodd x2))), gv_sv_eq.
  rewrite (locals_rel_get_var ctxt _ t x1 _ (conj Hl E1)), (locals_rel_get_var ctxt _ t x2 _ (conj Hl E2)).
  cbv beta iota zeta. rewrite Eac.
  rewrite bool_decide_none_true.
  wstep. wstep. cbn [word_exp]. rewrite gv_sv_eq.
  rewrite bool_decide_none_true.
  wstep. cbn [word_exp].
  rewrite (gv_sv_ne 3 _ _ _ (fun E => proj2 (Hodd y2) (eq_sym E))), gv_sv_ne, gv_sv_eq by lia.
  eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. cbn [cc_post].
  split; [srel Hs|]. split; [reflexivity|]. unfold loopSem.set_vars; lcbn; wcbn.
  cbn [alist_insert].
  split.
  { rewrite !(l0_ins ctxt) by assumption. rewrite !lookup_ins_ne by lia. exact H0. }
  split; [|split; reflexivity].
  apply locals_rel_insert. split; [|exact Hd1].
  apply locals_rel_insert. split; [|exact Hd2].
  apply locals_rel_insert_unmapped. split; [|intros n _; exact (proj1 (Hodd n))].
  apply locals_rel_insert_unmapped. split; [|intros n _; exact (proj2 (Hodd n))].
  apply locals_rel_insert_unmapped. split; [|intros n _; exact (proj1 (Hodd n))].
  exact Hl.
Qed.

Lemma TAKE_1_word_to_bytes_aux : forall n (w : word a) be,
  TAKE 1 (byte.word_to_bytes_aux (SUC n) w be) = [byte.get_byte (n2w 0) w be].
Proof.
  intros n w be. induction n as [|n IH] using N.peano_ind.
  - rewrite (proj2 (byte.word_to_bytes_aux_def 0 w be)), (proj1 (byte.word_to_bytes_aux_def 0 w be)).
    reflexivity.
  - rewrite (proj2 (byte.word_to_bytes_aux_def (SUC n) w be)).
    rewrite !TAKE_firstn in *. rewrite firstn_app.
    assert (Hl : length (byte.word_to_bytes_aux (SUC n) w be) = N.to_nat (SUC n)).
    { pose proof (byte.LENGTH_word_to_bytes_aux (SUC n) w be) as HL.
      rewrite LENGTH_length in HL. lia. }
    rewrite IH, Hl. replace (N.to_nat 1 - N.to_nat (SUC n))%nat with 0%nat by lia. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "TAKE_1_word_to_bytes" *)
Theorem TAKE_1_word_to_bytes : forall (w : word a),
  good_dimindex a -> TAKE 1 (byte.word_to_bytes w false) = [byte.get_byte (n2w 0) w false].
Proof.
  intros w Hg. unfold byte.word_to_bytes.
  replace (dimindex a / 8) with (SUC (dimindex a / 8 - 1)).
  - apply TAKE_1_word_to_bytes_aux.
  - destruct Hg as [Hg|Hg]; rewrite Hg; reflexivity.
Qed.

Ltac shm_ld v s H :=
  destruct (lookup v (loopSem.locals s)) eqn:?; [|injection H as <- <-; congruence].
Ltac shm_st v s t ctxt Hl H :=
  let Ev := fresh "Ev" in
  destruct (lookup v (loopSem.locals s)) as [[?w|]|] eqn:Ev; try (injection H as <- <-; congruence);
  rewrite (locals_rel_get_var ctxt _ t v _ (conj Hl Ev)).

Lemma cc_ShMem s op v e : cc_P (loopLang.ShMem op v e) s.
Proof.
  cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.eval s e) as [[addr|]|] eqn:Ee; try (injection H as <- <-; congruence).
  cbn [comp FST fst]. wstep.
  rewrite (comp_exp_preserves_eval s e _ t ctxt (conj Ee (conj Hg (conj Hs Hl)))).
  cbn [loopLang.acc_vars] in Hd. apply dom_ins_sub in Hd as [Hdv _].
  destruct (state_rel_intro _ _ Hs) as (_ & _ & _ & _ & Hff & _).
  pose proof Hs as (len & _ & _ & Hsh & _).
  destruct op; cbn [is_load loopSem.sh_mem_op share_inst] in H |- *;
    unfold loopSem.sh_mem_load, loopSem.sh_mem_store, sh_mem_set_var, sh_mem_load,
      sh_mem_load_byte, sh_mem_load16, sh_mem_load32, sh_mem_store, sh_mem_store_byte,
      sh_mem_store16, sh_mem_store32 in H |- *;
    cbn [N.eqb Pos.eqb] in H; rewrite Hsh, Hff;
    [ shm_ld v s H | shm_ld v s H | shm_ld v s H | shm_ld v s H
    | shm_st v s t ctxt Hl H | shm_st v s t ctxt Hl H | shm_st v s t ctxt Hl H | shm_st v s t ctxt Hl H ];
    (destruct (classical_dec _); [|injection H as <- <-; congruence]);
    rewrite ?(TAKE_1_word_to_bytes _ Hg) in H;
    destruct (call_FFI _ _ _ _) as [nffi nbytes|outc]; injection H as <- <-;
    (eexists _, _; split; [reflexivity|]; split; [lcbn; wcbn; try reflexivity; sffi Hs|]);
    cbn [cc_post]; try reflexivity;
    (split; [srel Hs|]);
    unfold set_var, loopSem.set_var; wcbn; lcbn; csplit; try reflexivity;
    try (rewrite (l0_ins ctxt) by (try exact Hdv; exact (proj1 (proj2 Hl))); exact H0);
    try exact H0; try exact Hl;
    apply locals_rel_insert; split; assumption.
Qed.

Lemma cc_post_frame res s1 (t t' t1 : state a c ffi_t) ctxt retv res1 :
  stack t' = stack t -> handler t' = handler t ->
  cc_post res s1 t' t1 ctxt retv res1 -> cc_post res s1 t t1 ctxt retv res1.
Proof.
  intros Hst Hh Hp. destruct res as [[]|]; cbn [cc_post] in *; rewrite ?Hst, ?Hh in Hp; exact Hp.
Qed.

Lemma bd_neq {A} `{EqDecision A} (x y : A) : x <> y -> bool_decide (x = y) = false.
Proof. intros Hn. destruct (bool_decide (x = y)) eqn:E; [|reflexivity]. apply bool_decide_spec in E; contradiction. Qed.

Ltac bdf :=
  repeat match goal with
         | |- context [bool_decide (?x = ?y)] =>
             first [ rewrite (bd_neq x y) by discriminate
                   | rewrite (proj2 (bool_decide_spec (x = y)) eq_refl) ]
         end.

Lemma tick_loop_tick (t1 : state a c ffi_t) names body exit_names :
  clock t1 <> 0 ->
  evaluate (Seq Tick (Seq (Loop names body exit_names) Tick), t1) =
  let '(r, s1) := evaluate (Loop names body exit_names, dec_clock t1) in
  if bool_decide (r = NONE) then evaluate (Tick, s1) else (r, s1).
Proof.
  intros Hc. wstep. rewrite (evaluate_eqn Tick). cbn [evaluate_body].
  destruct (N.eqb_spec (clock t1) 0) as [E|_]; [contradiction|].
  rewrite bool_decide_none_true. wstep. reflexivity.
Qed.

Lemma cc_Loop s live_in body live_out :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.Loop live_in body live_out, s) -> cc_P p' s') ->
  cc_P (loopLang.Loop live_in body live_out) s.
Proof.
  intros IH. cc_intro. assert (H' := H). loopProps.unfold_eval_in H.
  cbn [comp loopLang.acc_vars] in *. destruct (comp ctxt body l) as [wbody lb] eqn:Ecb.
  cbn [FST fst].
  unfold loopSem.cut_res in H. cbn [IS_SOME] in H. unfold loopSem.cut_state in H.
  destruct (classical_dec _) as [Hsub|]; [|injection H as <- <-; congruence].
  lcbn. pose proof (state_rel_IMP _ _ Hs) as Hck.
  wstep. rewrite (evaluate_eqn Tick). cbn [evaluate_body]. rewrite Hck.
  destruct (loopSem.clock s =? 0) eqn:Ec0.
  { injection H as <- <-. eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. reflexivity. }
  apply N.eqb_neq in Ec0. rewrite bool_decide_none_true.
  wstep. wstep.
  destruct (cut_env_mk_new_cutset ctxt (loopSem.locals s) (locals t) live_in retv (conj Hl (conj Hsub H0)))
    as (env1 & Henv & Hl1).
  pose proof (cut_env_mk_new_cutset_IMP _ _ _ _ Henv) as Henv0.
  unfold cut_state. wcbn. rewrite Henv.
  rewrite loopSem.fix_clock_evaluate in H.
  set (s0 := loopSem.dec_clock (loopSem.set_locals (inter (loopSem.locals s) live_in) s)) in H.
  set (t0 := set_locals env1 (dec_clock t)).
  assert (Hs0 : state_rel s0 t0) by (unfold s0, t0, loopSem.dec_clock, dec_clock; srel Hs; lia).
  assert (H00 : lookup 0 (locals t0) = SOME retv) by (unfold t0; wcbn; rewrite Henv0; exact H0).
  assert (Hl0 : locals_rel ctxt (loopSem.locals s0) (locals t0)) by (unfold s0, t0; lcbn; wcbn; exact Hl1).
  destruct (loopSem.evaluate (body, s0)) as [rb sb] eqn:Eb.
  assert (Hrb : rb <> SOME loopSem.Error).
  { intros ->. injection H as <- <-. congruence. }
  destruct (IH body s0 ltac:(left; cbn [fst snd]; unfold s0; lcbn; lia)
              rb sb t0 ctxt retv l (conj Eb (conj Hrb (conj Hs0 (conj Hl0 (conj H00 (conj Hg (conj Hw Hd))))))))
    as (tb1 & resb1 & Evb & Hfb & Hpb).
  rewrite Ecb in Evb. cbn [FST fst] in Evb. rewrite wordSem.fix_clock_evaluate, Evb. cbv beta iota zeta.
  pose proof (loopSem.evaluate_clock _ _ _ _ Eb) as Hcb.
  assert (Hst0 : stack t0 = stack t) by reflexivity.
  assert (Hh0 : handler t0 = handler t) by reflexivity.
  (* the recursive iteration *)
  assert (Rec : (rb = NONE \/ rb = SOME (loopSem.Continue 0)) ->
             (resb1 = NONE \/ resb1 = SOME (Continue 0)) ->
             state_rel sb tb1 -> locals_rel ctxt (loopSem.locals sb) (locals tb1) ->
             lookup 0 (locals tb1) = SOME retv -> stack tb1 = stack t -> handler tb1 = handler t ->
             loopSem.evaluate (loopLang.Loop live_in body live_out, sb) = (res, s1) ->
             exists t1 res1,
               (let '(r, s2) := (if cont_loop resb1 then
                                   if clock tb1 =? 0 then (SOME TimeOut, flush_state true tb1)
                                   else evaluate (STOP (Loop (mk_new_cutset ctxt live_in) wbody
                                                         (mk_new_cutset ctxt live_out)), dec_clock tb1)
                                 else if bool_decide (resb1 = SOME (Break 0)) then
                                   match cut_state (mk_new_cutset ctxt live_out, LN) tb1 with
                                   | SOME s3 => (NONE, s3) | NONE => (SOME Error, tb1) end
                                 else (exit_loop resb1, tb1)) in
                if bool_decide (r = NONE) then evaluate (Tick, s2) else (r, s2)) = (res1, t1) /\
               ffi t1 = loopSem.ffi s1 /\ cc_post res s1 t t1 ctxt retv res1).
  { intros Hrb' Hres1 Hs1 Hl1' H01 Hst1 Hh1 Hrec.
    assert (Hcl : cont_loop resb1 = true) by (destruct Hres1 as [-> | ->]; reflexivity).
    rewrite Hcl. rewrite (state_rel_IMP _ _ Hs1).
    destruct (loopSem.clock sb =? 0) eqn:Ecb0.
    - apply N.eqb_eq in Ecb0. rewrite loopSem.evaluate_eqn in Hrec. cbn [loopSem.evaluate_body] in Hrec.
      unfold loopSem.cut_res, loopSem.cut_state in Hrec. cbn [IS_SOME] in Hrec.
      destruct (classical_dec (domain live_in SUBSET domain (loopSem.locals sb)));
        cbn beta iota in Hrec; [|injection Hrec as <- <-; congruence].
      lcbn. rewrite Ecb0 in Hrec. cbn [N.eqb] in Hrec. injection Hrec as <- <-.
      eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. reflexivity.
    - apply N.eqb_neq in Ecb0.
      destruct (IH (loopLang.Loop live_in body live_out) sb
                  ltac:(left; cbn [fst snd]; unfold s0 in Hcb; lcbn; lia)
                  res s1 tb1 ctxt retv l (conj Hrec (conj Hne (conj Hs1 (conj Hl1' (conj H01 (conj Hg (conj Hw Hd))))))))
        as (t1 & res1 & Ev1 & Hf1 & Hp1).
      cbn [comp FST fst] in Ev1. rewrite Ecb in Ev1. cbn [FST fst] in Ev1.
      rewrite tick_loop_tick in Ev1 by (rewrite (state_rel_IMP _ _ Hs1); exact Ecb0).
      unfold STOP. exists t1, res1. split; [exact Ev1|]. split; [exact Hf1|].
      exact (cc_post_frame _ _ _ _ _ _ _ _ Hst1 Hh1 Hp1). }
  destruct rb as [rb|].
  2:{ cbn [cc_post] in Hpb. destruct Hpb as (Hs1 & -> & H01 & Hl1' & Hst1 & Hh1).
      apply Rec; auto; congruence. }
  pose proof (cc_post_frame _ _ _ _ _ _ _ _ Hst0 Hh0 Hpb) as Hpb'.
  destruct rb as [vs|ex|bn|cn| |ff|]; cbn [cc_post] in Hpb; try congruence.
  - (* Result *)
    destruct Hpb as (Hs1 & -> & Hst1 & Hh1). injection H as <- <-.
    cbn [cont_loop]. bdf. cbn [exit_loop]. bdf.
    eexists _, _. split; [reflexivity|]. split; [exact Hfb|]. exact Hpb'.
  - (* Exception *)
    destruct Hpb as (Hs1 & He1 & Hj1). injection H as <- <-.
    destruct (cont_loop resb1) eqn:Ecl.
    { exfalso. destruct resb1 as [[]|]; cbn in Ecl; try discriminate;
        [destruct (He1 ltac:(discriminate)) as (? & ? & ?); discriminate|].
      destruct (He1 ltac:(discriminate)) as (? & ? & ?); discriminate. }
    destruct (bool_decide (resb1 = SOME (Break 0))) eqn:Ebr.
    { exfalso. apply bool_decide_spec in Ebr. subst resb1.
      destruct (He1 ltac:(discriminate)) as (? & ? & ?); discriminate. }
    assert (Hx : exit_loop resb1 = resb1).
    { destruct resb1 as [[]|]; try reflexivity; destruct (He1 ltac:(discriminate)) as (? & ? & ?); discriminate. }
    rewrite Hx. destruct (bool_decide (resb1 = NONE)) eqn:En.
    { exfalso. apply bool_decide_spec in En. subst resb1. destruct (He1 ltac:(discriminate)) as (? & ? & ?); discriminate. }
    eexists _, _. split; [reflexivity|]. split; [exact Hfb|]. exact Hpb'.
  - (* Break *)
    destruct Hpb as (Hs1 & -> & H01 & Hl1' & Hst1 & Hh1). cbn [cont_loop].
    destruct (N.eq_dec bn 0) as [->|Hbn].
    + rewrite (proj2 (bool_decide_spec _) eq_refl).
      unfold loopSem.cut_res, loopSem.cut_state in H. cbn [IS_SOME] in H.
      destruct (classical_dec (domain live_out SUBSET domain (loopSem.locals sb))) as [Hsub2|];
        cbn beta iota in H; [|injection H as <- <-; congruence].
      destruct (cut_env_mk_new_cutset ctxt (loopSem.locals sb) (locals tb1) live_out retv (conj Hl1' (conj Hsub2 H01)))
        as (env2 & Henv2 & Hl2).
      pose proof (cut_env_mk_new_cutset_IMP _ _ _ _ Henv2) as Henv20.
      unfold cut_state. rewrite Henv2. rewrite bool_decide_none_true. wstep.
      wcbn. lcbn. rewrite (state_rel_IMP _ _ Hs1).
      destruct (loopSem.clock sb =? 0); injection H as <- <-.
      * eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. reflexivity.
      * eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. cbn [cc_post].
        split; [srel Hs1; lia|]. wcbn; lcbn. split; [reflexivity|].
        split; [rewrite Henv20; exact H01|]. split; [exact Hl2|]. split; congruence.
    + destruct bn as [|p]; [contradiction|]. cbn beta iota in H.
      bdf. cbn [exit_loop] in *. injection H as <- <-. bdf.
      eexists _, _. split; [reflexivity|]. split; [exact Hfb|]. cbn [cc_post].
      csplit; try assumption; try reflexivity; congruence.
  - (* Continue *)
    destruct Hpb as (Hs1 & -> & H01 & Hl1' & Hst1 & Hh1).
    destruct (N.eq_dec cn 0) as [->|Hcn].
    + apply Rec; auto; congruence.
    + destruct cn as [|p]; [contradiction|]. cbn beta iota in H. cbn [cont_loop N.eqb].
      bdf. cbn [exit_loop] in *. injection H as <- <-. bdf.
      eexists _, _. split; [reflexivity|]. split; [exact Hfb|]. cbn [cc_post].
      csplit; try assumption; try reflexivity; congruence.
  - (* TimeOut *)
    subst resb1. injection H as <- <-. cbn [cont_loop exit_loop]. bdf. cbn [exit_loop]. bdf.
    eexists _, _. split; [reflexivity|]. split; [exact Hfb|]. exact Hpb'.
  - (* FinalFFI *)
    subst resb1. injection H as <- <-. cbn [cont_loop exit_loop]. bdf. cbn [exit_loop]. bdf.
    eexists _, _. split; [reflexivity|]. split; [exact Hfb|]. exact Hpb'.
Qed.

Lemma LENGTH_FRONT_cons {A} (x : A) l : LENGTH (FRONT (x :: l)) = LENGTH l.
Proof.
  revert x; induction l as [|y l IH]; intros x; [reflexivity|].
  cbn [FRONT LENGTH] in *. rewrite IH. reflexivity.
Qed.

Lemma comp_func_ctxt params (body : loopLang.prog a) (argvals : list (word_loc a)) rv name :
  ALL_DISTINCT params -> LENGTH params = LENGTH argvals ->
  exists ctxt1 l1,
    comp_func name params body = FST (comp ctxt1 body l1) /\
    locals_rel ctxt1 (fromAList (ZIP (params, argvals))) (fromList2 (rv :: argvals)) /\
    domain (loopLang.acc_vars body LN) SUBSET domain ctxt1.
Proof.
  intros Hd Hl. unfold comp_func. cbv zeta.
  set (vs := fromNumSet (difference (loopLang.acc_vars body LN) (toNumSet params))).
  exists (make_ctxt 2 (params ++ vs) LN), (name, 2). split; [reflexivity|]. split.
  - apply locals_rel_make_ctxt. split; [exact Hd|]. split; [|exact Hl].
    apply IN_DISJOINT. intros (x & Hx1 & Hx2). unfold vs in Hx2. rewrite set_fromNumSet in Hx2.
    unfold pred_set.IN in Hx2. rewrite domain_difference, domain_toNumSet in Hx2.
    destruct Hx2 as [_ Hx2]. exact (Hx2 Hx1).
  - intros x Hx. unfold pred_set.IN. rewrite domain_make_ctxt, LIST_TO_SET_APPEND.
    unfold pred_set.UNION, pred_set.IN. right.
    destruct (classical_dec (x IN set params)) as [Hp|Hp]; [left; exact Hp|right].
    unfold vs. change (set (fromNumSet (difference (loopLang.acc_vars body LN) (toNumSet params))) x)
      with (x IN set (fromNumSet (difference (loopLang.acc_vars body LN) (toNumSet params)))).
    rewrite set_fromNumSet. unfold pred_set.IN. rewrite domain_difference, domain_toNumSet.
    split; [exact Hx|exact Hp].
Qed.

Lemma call_setup (s : loopSem.state a ffi_t) (t : state a c ffi_t) dest argvals env prog0 rv :
  code_rel (loopSem.code s) (code t) ->
  loopSem.find_code dest argvals (loopSem.code s) = SOME (env, prog0) ->
  exists args1 ss ctxt1 l1,
    find_code dest (rv :: argvals) (code t) (state_stack_size t) =
      SOME (args1, (FST (comp ctxt1 prog0 l1), ss)) /\
    lookup 0 (fromList2 args1) = SOME rv /\
    locals_rel ctxt1 env (fromList2 args1) /\
    domain (loopLang.acc_vars prog0 LN) SUBSET domain ctxt1.
Proof.
  intros Hc Hf. destruct dest as [p|].
  - cbn [loopSem.find_code] in Hf.
    destruct (lookup p (loopSem.code s)) as [[params body]|] eqn:Ep; [|discriminate].
    destruct (LENGTH argvals =? LENGTH params) eqn:El; [|discriminate]. apply N.eqb_eq in El.
    injection Hf as <- <-.
    destruct (Hc _ _ _ Ep) as [Ht Hd].
    destruct (comp_func_ctxt params body argvals rv p Hd (eq_sym El)) as (ctxt1 & l1 & Hcf & Hlr & Hdom).
    exists (rv :: argvals), (lookup p (state_stack_size t)), ctxt1, l1.
    cbn [find_code]. rewrite Ht. cbn [LENGTH]. rewrite El.
    destruct (N.eqb_spec (N.succ (LENGTH params)) (LENGTH params + 1)) as [_|C]; [|lia].
    rewrite Hcf. split; [reflexivity|]. split; [|split; assumption].
    apply (lookup_fromList2_EL (rv :: argvals) 0). cbn [LENGTH]. lia.
  - cbn [loopSem.find_code] in Hf.
    destruct (bool_decide (argvals = [])) eqn:Eb; [discriminate|].
    destruct argvals as [|x0 argvals']; [rewrite (proj2 (bool_decide_spec _) eq_refl) in Eb; discriminate|].
    destruct (LAST (x0 :: argvals')) as [w|loc [|q]] eqn:Elast; try discriminate.
    destruct (lookup loc (loopSem.code s)) as [[params body]|] eqn:Ep; [|discriminate].
    destruct (_ =? _) eqn:El; [|discriminate]. apply N.eqb_eq in El.
    injection Hf as <- <-.
    destruct (Hc _ _ _ Ep) as [Ht Hd].
    assert (Hl' : LENGTH params = LENGTH (FRONT (x0 :: argvals'))).
    { rewrite LENGTH_FRONT_cons. cbn [LENGTH] in El. lia. }
    destruct (comp_func_ctxt params body (FRONT (x0 :: argvals')) rv loc Hd Hl')
      as (ctxt1 & l1 & Hcf & Hlr & Hdom).
    exists (rv :: FRONT (x0 :: argvals')), (lookup loc (state_stack_size t)), ctxt1, l1.
    cbn [find_code]. rewrite (bd_neq (rv :: x0 :: argvals') []) by discriminate.
    change (LAST (rv :: x0 :: argvals')) with (LAST (x0 :: argvals')). rewrite Elast.
    cbn [N.eqb]. rewrite Ht. cbn [LENGTH] in *. rewrite El.
    destruct (N.eqb_spec (N.succ (LENGTH params + 1)) (LENGTH params + 1 + 1)) as [_|C]; [|lia].
    rewrite Hcf. split; [reflexivity|]. split; [|split; assumption].
    apply (lookup_fromList2_EL (rv :: FRONT (x0 :: argvals')) 0). cbn [LENGTH]. lia.
Qed.

Lemma cc_Call_tail s dest argvars handler :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.Call NONE dest argvars handler, s) -> cc_P p' s') ->
  cc_P (loopLang.Call NONE dest argvars handler) s.
Proof.
  intros IH. cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.get_vars argvars s) as [argvals|] eqn:Egv; [|injection H as <- <-; congruence].
  destruct (loopSem.find_code dest argvals (loopSem.code s)) as [[env prog0]|] eqn:Efc;
    [|injection H as <- <-; congruence].
  destruct handler as [hd|]; cbn [IS_SOME] in H; [injection H as <- <-; congruence|].
  destruct (state_rel_intro _ _ Hs) as (_ & _ & Hck & _ & _ & _ & _ & Hcr).
  destruct (call_setup s t dest argvals env prog0 retv Hcr Efc)
    as (args1 & ss & ctxt1 & l1 & Hfc & H01 & Hl1 & Hd1).
  destruct (locals_rel_get_vars ctxt s t argvars argvals (conj Hl Egv)) as [Hgv _].
  cbn [comp FST fst]. wstep. cbn [get_vars]. unfold get_var at 1. rewrite H0, Hgv.
  unfold bad_dest_args. rewrite (bd_neq (0 :: MAP (find_var ctxt) argvars) []) by discriminate.
  rewrite andb_false_r. cbn [add_ret_loc]. rewrite Hfc.
  rewrite (proj2 (bool_decide_spec (@NONE (N * (prog a * (N * N))) = NONE)) eq_refl).
  rewrite Hck. destruct (loopSem.clock s =? 0) eqn:Ec0.
  { injection H as <- <-. eexists _, _. split; [reflexivity|]. split; [sffi Hs|]. reflexivity. }
  apply N.eqb_neq in Ec0.
  set (sc := loopSem.set_locals env (loopSem.dec_clock s)) in H.
  set (tc := call_env args1 ss (dec_clock t)).
  assert (Hsc : state_rel sc tc) by (unfold sc, tc, loopSem.dec_clock, dec_clock; srel Hs; lia).
  destruct (loopSem.evaluate (prog0, sc)) as [r st] eqn:Ev.
  assert (Hr : r <> SOME loopSem.Error) by (intros ->; injection H as <- <-; congruence).
  destruct (IH prog0 sc ltac:(left; cbn [fst snd]; unfold sc; lcbn; lia)
              r st tc ctxt1 retv l1
              (conj Ev (conj Hr (conj Hsc (conj Hl1 (conj H01 (conj Hg (conj Hw Hd1))))))))
    as (t1 & res1 & Ev1 & Hf1 & Hp1).
  rewrite Ev1. pose proof (cc_post_frame _ _ _ _ _ _ _ _ eq_refl eq_refl Hp1) as Hp1'.
  change (stack tc) with (stack t) in Hp1'. change (handler tc) with (handler t) in Hp1'.
  destruct r as [[vs|ex|bn|cn| |ff|]|]; injection H as <- <-; try congruence;
    cbn [cc_post] in Hp1.
  - destruct Hp1 as (_ & -> & _). cbn [bad_fun_return].
    eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. exact Hp1'.
  - destruct Hp1 as (_ & He & _).
    assert (Hb : bad_fun_return res1 = false).
    { destruct res1 as [[]|]; try reflexivity;
        destruct (He ltac:(discriminate)) as (? & ? & ?); discriminate. }
    rewrite Hb. eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. exact Hp1'.
  - subst res1. eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. exact Hp1'.
  - subst res1. eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. exact Hp1'.
Qed.

Lemma state_rel_t (s0 : loopSem.state a ffi_t) (t t' : state a c ffi_t) :
  state_rel s0 t -> memory t' = memory t -> mdomain t' = mdomain t ->
  sh_mdomain t' = sh_mdomain t -> clock t' = clock t -> be t' = be t -> ffi t' = ffi t ->
  store t' = store t -> code t' = code t -> state_rel s0 t'.
Proof.
  intros (len & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) E1 E2 E3 E4 E5 E6 E7 E8.
  exists len. rewrite E1, E2, E3, E4, E5, E6, E7, E8. csplit; assumption.
Qed.

Lemma lookup_alist_insert_notin {B} k xs (ys : list B) L :
  ~ In k xs -> lookup k (alist_insert xs ys L) = lookup k L.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys Hk; [destruct ys; reflexivity|].
  destruct ys as [|y ys]; [reflexivity|]. cbn [alist_insert].
  rewrite lookup_ins_ne by (intros ->; apply Hk; left; reflexivity). apply IH.
  intros H; apply Hk; right; exact H.
Qed.

Lemma jump_exc_frame (t1 : state a c ffi_t) h st fr r k :
  jump_exc (set_handler h (set_stack st t1)) = SOME (r, k) ->
  jump_exc (set_handler h (set_stack (fr :: st) t1)) = SOME (r, k).
Proof.
  unfold jump_exc. wcbn. destruct (N.ltb_spec h (LENGTH st)) as [Hh|]; [|discriminate].
  destruct (N.ltb_spec h (LENGTH (fr :: st))) as [_|C]; [|cbn [LENGTH] in C; lia].
  rewrite LASTN_ADD_CONS by lia.
  destruct (LASTN (h + 1) st) as [|[m e0 e [[n [k1 k2]]|]] xs]; try discriminate.
  intros H; injection H as <- <-. destruct t1; reflexivity.
Qed.

Lemma push_env_NONE_facts (env1 : num_map (word_loc a)) (t : state a c ffi_t) :
  stack (push_env (env1, LN) NONE t) = StackFrame (locals_size t) (toAList env1) [] NONE :: stack t /\
  handler (push_env (env1, LN) NONE t) = handler t.
Proof.
  unfold push_env. cbn [FST SND fst snd]. destruct (env_to_list (a := a) LN (permute t)) as [l' p'] eqn:E.
  apply env_to_list_LN_IMP in E. subst l'. cbv beta iota zeta. wcbn. split; reflexivity.
Qed.

Lemma push_env_SOME_facts (env1 : num_map (word_loc a)) n h l1 l2 (t : state a c ffi_t) :
  stack (push_env (env1, LN) (SOME (n, (h, (l1, l2)))) t) =
    StackFrame (locals_size t) (toAList env1) [] (SOME (handler t, (l1, l2))) :: stack t /\
  handler (push_env (env1, LN) (SOME (n, (h, (l1, l2)))) t) = LENGTH (stack t).
Proof.
  unfold push_env. cbn [FST SND fst snd]. destruct (env_to_list (a := a) LN (permute t)) as [l' p'] eqn:E.
  apply env_to_list_LN_IMP in E. subst l'. cbv beta iota zeta. wcbn. split; reflexivity.
Qed.

Lemma state_rel_push_env (s0 : loopSem.state a ffi_t) (t : state a c ffi_t) x y :
  state_rel s0 t -> state_rel s0 (push_env x y t).
Proof.
  intros Hs. pose proof (consts.push_env_const x y t) as P.
  destruct P as (P1 & P2 & P3 & _ & P5 & _ & _ & _ & _ & _ & P11 & P12 & _ & P14 & _ & P16 & _).
  apply (state_rel_t _ _ _ Hs); assumption.
Qed.

Lemma state_rel_pop_env (s0 : loopSem.state a ffi_t) (t t' : state a c ffi_t) :
  state_rel s0 t -> pop_env t = SOME t' -> state_rel s0 t'.
Proof.
  intros Hs Hp. destruct (consts.pop_env_const _ _ Hp) as (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & _ & _ & _ & _ & _ & _ & P16 & _).
  apply (state_rel_t _ _ _ Hs); assumption.
Qed.

Lemma pop_env_frame (t1 : state a c ffi_t) m e0 hnd st :
  stack t1 = StackFrame m e0 [] hnd :: st ->
  exists t', pop_env t1 = SOME t' /\ locals t' = fromAList e0 /\ stack t' = st /\
    handler t' = (match hnd with SOME (n, _) => n | NONE => handler t1 end) /\
    (forall s0 : loopSem.state a ffi_t, state_rel s0 t1 -> state_rel s0 t') /\ ffi t' = ffi t1.
Proof.
  intros Hst. unfold pop_env. rewrite Hst.
  destruct hnd as [[n x]|]; eexists; (split; [reflexivity|]); wcbn;
    (split; [change (fromAList (@nil (N * word_loc a))) with (@LN (word_loc a)); apply (proj2 (union_LN _))|]); csplit; try reflexivity;
    intros s0 Hs; apply (state_rel_t _ _ _ Hs); reflexivity.
Qed.

Lemma LENGTH_MAP' {A B} (f0 : A -> B) l : LENGTH (MAP f0 l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_map. reflexivity. Qed.

Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros Hn. destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; contradiction. Qed.

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. intros Hp. apply bool_decide_spec, Hp. Qed.

Lemma LASTN_full {A} (fr : A) st : LASTN (LENGTH st + 1) (fr :: st) = fr :: st.
Proof.
  unfold LASTN. rewrite TAKE_firstn, firstn_all2; [apply rev_involutive|].
  rewrite length_rev. cbn [length]. rewrite LENGTH_length. lia.
Qed.

Lemma dom_fromAList_toAList_LN (env1 : num_map (word_loc a)) :
  domain (fromAList (toAList env1)) = domain env1 UNION domain (@LN (word_loc a)).
Proof.
  rewrite consts.domain_fromAList_toAList. apply set_ext; intros x.
  unfold pred_set.UNION, pred_set.IN. cbn. tauto.
Qed.

(** The tail [cut_res live_out] / [Tick] of [If] and of calls with handler. *)
Lemma cc_cut_tick (t t2 t3 : state a c ffi_t) ctxt retv lo (r0 : option (loopSem.result a)) u
    (res2 : option (result a)) res s1 :
  stack t2 = stack t -> handler t2 = handler t ->
  ffi t3 = loopSem.ffi u -> cc_post r0 u t2 t3 ctxt retv res2 ->
  loopSem.cut_res lo (r0, u) = (res, s1) -> res <> SOME loopSem.Error ->
  exists t1 res1,
    (if bool_decide (res2 = NONE) then evaluate (Tick, t3) else (res2, t3)) = (res1, t1) /\
    ffi t1 = loopSem.ffi s1 /\ cc_post res s1 t t1 ctxt retv res1.
Proof.
  intros Hst Hh Hf Hp Hcut Hne. destruct r0 as [r0|].
  - cbn [loopSem.cut_res IS_SOME] in Hcut. injection Hcut as <- <-.
    rewrite (bool_decide_none_false _ (cc_res_not_none _ t2 t3 ctxt retv res2 r0 Hp)).
    exists t3, res2. split; [reflexivity|]. split; [exact Hf|].
    exact (cc_post_frame _ _ _ _ _ _ _ _ Hst Hh Hp).
  - cbn [cc_post] in Hp. destruct Hp as (Hs1 & -> & H01 & Hl1 & Hst1 & Hh1).
    rewrite bool_decide_none_true. wstep.
    cbn [loopSem.cut_res IS_SOME] in Hcut. unfold loopSem.cut_state in Hcut.
    destruct (classical_dec (domain lo SUBSET domain (loopSem.locals u))) as [Hsub|];
      cbn beta iota in Hcut; [|injection Hcut as <- <-; congruence].
    lcbn. rewrite (state_rel_IMP _ _ Hs1).
    destruct (loopSem.clock u =? 0) eqn:Ec; injection Hcut as <- <-.
    + eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. reflexivity.
    + eexists _, _. split; [reflexivity|]. split; [sffi Hs1|]. cbn [cc_post].
      split; [srel Hs1; lia|]. wcbn; lcbn. split; [reflexivity|]. split; [exact H01|].
      split; [apply locals_rel_inter; exact Hl1|]. split; congruence.
Qed.

Lemma bad_dest_args_false (s : loopSem.state a ffi_t) dest argvars argvals ctxt env (prog0 : loopLang.prog a) :
  loopSem.get_vars argvars s = SOME argvals ->
  loopSem.find_code dest argvals (loopSem.code s) = SOME (env, prog0) ->
  bad_dest_args dest (MAP (find_var ctxt) argvars) = false.
Proof.
  intros Hg Hf. unfold bad_dest_args. destruct dest as [p|]; [reflexivity|].
  cbn [loopSem.find_code] in Hf. destruct (bool_decide (argvals = [])) eqn:Eb; [discriminate|].
  destruct argvars as [|x xs]; [cbn in Hg; injection Hg as <-; rewrite bd_true in Eb by reflexivity; discriminate|].
  rewrite (bd_neq (MAP (find_var ctxt) (x :: xs)) []) by discriminate. apply andb_false_r.
Qed.

Lemma locals_rel_toAList {B} ctxt (l1 env : num_map B) :
  locals_rel ctxt l1 env -> locals_rel ctxt l1 (fromAList (toAList env)).
Proof.
  intros (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros n v Hn. destruct (H3 _ _ Hn) as (m & Hm & Hm'). exists m. rewrite lookup_fromAList_toAList. auto.
Qed.

Lemma jump_exc_handler_frame (t1 : state a c ffi_t) m e0 h l1 l2 st :
  jump_exc (set_handler (LENGTH st) (set_stack (StackFrame m e0 [] (SOME (h, (l1, l2))) :: st) t1)) =
  SOME (set_locals_size m (set_stack st (set_locals (union (fromAList []) (fromAList e0))
          (set_handler h (set_handler (LENGTH st)
             (set_stack (StackFrame m e0 [] (SOME (h, (l1, l2))) :: st) t1))))), (l1, l2)).
Proof.
  unfold jump_exc. wcbn. destruct (N.ltb_spec (LENGTH st) (LENGTH (StackFrame m e0 [] (SOME (h, (l1, l2))) :: st))) as [_|C];
    [|cbn [LENGTH] in C; lia].
  rewrite LASTN_full. reflexivity.
Qed.

Lemma locals_call_env x ss (y : state a c ffi_t) : locals (call_env x ss y) = fromList2 x.
Proof. reflexivity. Qed.

Lemma cc_Call_ret s ns live dest argvars handler :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.Call (SOME (ns, live)) dest argvars handler, s) ->
     cc_P p' s') ->
  cc_P (loopLang.Call (SOME (ns, live)) dest argvars handler) s.
Proof.
  intros IH. cc_intro. loopProps.unfold_eval_in H.
  destruct (loopSem.get_vars argvars s) as [argvals|] eqn:Egv; [|injection H as <- <-; congruence].
  destruct (loopSem.find_code dest argvals (loopSem.code s)) as [[env prog0]|] eqn:Efc;
    [|injection H as <- <-; congruence].
  destruct (ALL_DISTINCT ns) eqn:Ead; cbn [negb] in H; [|injection H as <- <-; congruence].
  unfold loopSem.cut_res in H. cbn [IS_SOME] in H. unfold loopSem.cut_state in H.
  destruct (classical_dec (domain live SUBSET domain (loopSem.locals s))) as [Hsub|];
    cbn beta iota in H; [|injection H as <- <-; congruence].
  lcbn.
  destruct (state_rel_intro _ _ Hs) as (_ & _ & Hck & _ & _ & _ & _ & Hcr).
  destruct l as [l0 l1].
  destruct (call_setup s t dest argvals env prog0 (Loc l0 l1) Hcr Efc)
    as (args1 & ss & ctxt1 & lc & Hfc & H01c & Hlc & Hdc).
  destruct (locals_rel_get_vars ctxt s t argvars argvals (conj Hl Egv)) as [Hgv _].
  destruct (cut_env_mk_new_cutset ctxt (loopSem.locals s) (locals t) live retv (conj Hl (conj Hsub H0)))
    as (env1 & Henv & Hl1).
  pose proof (cut_env_mk_new_cutset_IMP _ _ _ _ Henv) as Henv0.
  pose proof (cut_env_LN_IMP _ _ _ Henv) as Hce.
  assert (Hbad := bad_dest_args_false s dest argvars argvals ctxt env prog0 Egv Efc).
  assert (Hvs : set ns SUBSET domain ctxt).
  { intros x Hx. apply Hd. unfold pred_set.IN. cbn [loopLang.acc_vars]. cbv zeta.
    destruct handler as [[n [h [r lo]]]|].
    - apply loopProps.acc_vars_acc_iff; right. apply loopProps.acc_vars_acc_iff; right.
      rewrite domain_insert. right. apply domain_list_insert. left. apply MEM_set, Hx.
    - apply domain_list_insert. left. apply MEM_set, Hx. }
  assert (Hadm : ALL_DISTINCT (MAP (find_var ctxt) ns) = true)
    by (apply (locals_rel_ALL_DISTINCT_MAP ctxt _ _ ns (conj Hl (conj Hvs Ead)))).
  destruct (loopSem.clock s =? 0) eqn:Ec0.
  { injection H as <- <-.
    destruct handler as [[n [h [r lo]]]|]; cbn [comp]; cbv zeta; cbn [FST SND fst snd];
      [destruct (comp ctxt h (l0, l1 + 1)) as [wh lhA]; destruct (comp ctxt r lhA) as [wr lhB];
       cbn [FST fst]; wstep|cbn [FST fst]];
      wstep; rewrite Hgv, Hbad; cbn [add_ret_loc]; rewrite Hfc; cbn [FST fst SND snd];
      rewrite (bd_false _ (domain_mk_new_cutset_not_empty ctxt live)), Hadm; cbn [orb negb];
      rewrite Hce, Hck, Ec0;
      [rewrite (bool_decide_none_false (SOME TimeOut)) by discriminate|];
      (eexists _, _; split; [reflexivity|]; split; [sffi Hs|reflexivity]). }
  apply N.eqb_neq in Ec0.
  rewrite loopSem.fix_clock_evaluate in H.
  set (s' := loopSem.dec_clock (loopSem.set_locals (inter (loopSem.locals s) live) s)) in H.
  set (sc := loopSem.set_locals env s') in H.
  destruct (loopSem.evaluate (prog0, sc)) as [r0 st] eqn:Ev.
  assert (Hr0 : r0 <> SOME loopSem.Error) by (intros ->; injection H as <- <-; congruence).
  assert (Hlt : loopSem.eval_lt (prog0, sc) (loopLang.Call (SOME (ns, live)) dest argvars handler, s))
    by (left; cbn [fst snd]; unfold sc, s'; lcbn; lia).
  assert (Hsd : state_rel sc (dec_clock t)) by (unfold sc, s', loopSem.dec_clock, dec_clock; srel Hs; lia).
  pose proof (loopSem.evaluate_clock _ _ _ _ Ev) as Hcst.
  assert (Hlocs' : loopSem.locals s' = inter (loopSem.locals s) live) by reflexivity.
  destruct handler as [[n [h [r lo]]]|].
  - (* handler *)
    assert (Hdh : domain (loopLang.acc_vars h LN) SUBSET domain ctxt).
    { intros x Hx; apply Hd; unfold pred_set.IN in *; cbn [loopLang.acc_vars]; cbv zeta.
      apply loopProps.acc_vars_acc_iff; left; exact Hx. }
    assert (Hdr : domain (loopLang.acc_vars r LN) SUBSET domain ctxt).
    { intros x Hx; apply Hd; unfold pred_set.IN in *; cbn [loopLang.acc_vars]; cbv zeta.
      apply loopProps.acc_vars_acc_iff; right; apply loopProps.acc_vars_acc_iff; left; exact Hx. }
    assert (Hdn : n IN domain ctxt).
    { apply Hd; unfold pred_set.IN in *; cbn [loopLang.acc_vars]; cbv zeta.
      apply loopProps.acc_vars_acc_iff; right; apply loopProps.acc_vars_acc_iff; right.
      rewrite domain_insert; left; reflexivity. }
    cbn [comp]. cbv zeta. cbn [FST SND fst snd].
    destruct (comp ctxt h (l0, l1 + 1)) as [wh lhA] eqn:Eh.
    destruct (comp ctxt r lhA) as [wr [b0 b1]] eqn:Er. cbn [FST fst].
    wstep. wstep. rewrite Hgv, Hbad. cbn [add_ret_loc]. rewrite Hfc. cbn [FST fst SND snd].
    rewrite (bd_false _ (domain_mk_new_cutset_not_empty ctxt live)), Hadm. cbn [orb negb].
    rewrite Hce, Hck. destruct (N.eqb_spec (loopSem.clock s) 0) as [C|_]; [contradiction|].
    rewrite wordSem.fix_clock_evaluate.
    set (tc := call_env args1 ss (push_env (env1, LN) (SOME (find_var ctxt n, (wh, (b0, b1)))) (dec_clock t))).
    destruct (push_env_SOME_facts env1 (find_var ctxt n) wh b0 b1 (dec_clock t)) as [Hstc Hhc].
    assert (Hsc : state_rel sc tc)
      by (apply (state_rel_t _ (push_env (env1, LN) (SOME (find_var ctxt n, (wh, (b0, b1)))) (dec_clock t)));
          try reflexivity; apply state_rel_push_env; exact Hsd).
    assert (Hlc' : locals_rel ctxt1 (loopSem.locals sc) (locals tc))
      by (unfold tc; rewrite locals_call_env; exact Hlc).
    assert (H01c' : lookup 0 (locals tc) = SOME (Loc l0 l1))
      by (unfold tc; rewrite locals_call_env; exact H01c).
    pose proof (IH prog0 sc Hlt r0 st tc ctxt1 (Loc l0 l1) lc) as HH.
    edestruct HH as (t1 & res1 & Ev1 & Hf1 & Hp1);
      [split; [exact Ev|]; split; [exact Hr0|]; split; [exact Hsc|]; split; [exact Hlc'|];
       split; [exact H01c'|]; split; [exact Hg|]; split; [cbn; discriminate|exact Hdc]|].
    rewrite Ev1.
    assert (Hcsc : loopSem.clock sc < loopSem.clock s) by (unfold sc, s'; lcbn; lia).
    destruct r0 as [[retvs|exn|bn|cn| |ff|]|]; cbn [cc_post] in Hp1; try (injection H as <- <-; congruence).
    + destruct Hp1 as (Hs1 & -> & Hst1 & Hh1).
      destruct (LENGTH retvs =? LENGTH ns) eqn:Elen; cbn [negb] in H; [|injection H as <- <-; congruence].
      rewrite (bd_true (Loc l0 l1 = Loc l0 l1)) by reflexivity. rewrite LENGTH_MAP', Elen. cbn [negb orb].
      change (stack tc) with (stack (push_env (env1, LN) (SOME (find_var ctxt n, (wh, (b0, b1)))) (dec_clock t))) in Hst1.
      rewrite Hstc in Hst1.
      destruct (pop_env_frame t1 _ _ _ _ Hst1) as (t' & Hpop & Hlt' & Hst' & Hh' & Hsr' & Hf').
      rewrite Hpop. cbn [FST SND fst snd]. rewrite Hlt'.
      rewrite (bd_true _ (dom_fromAList_toAList_LN env1)).
      set (sr := loopSem.set_vars ns retvs (loopSem.set_locals (loopSem.locals s') st)) in H.
      set (tr := set_vars (MAP (find_var ctxt) ns) retvs t').
      destruct (loopSem.evaluate (r, sr)) as [r2 u2] eqn:Evr.
      assert (Hr2 : r2 <> SOME loopSem.Error)
        by (intros ->; cbn [loopSem.cut_res IS_SOME] in H; injection H as <- <-; congruence).
      assert (Hsr : state_rel sr tr) by (unfold sr, tr, loopSem.set_vars, set_vars; apply Hsr'; srel Hs1).
      assert (Hlr : locals_rel ctxt (loopSem.locals sr) (locals tr)).
      { unfold sr, tr, loopSem.set_vars, set_vars; lcbn; wcbn. rewrite Hlt'.
        apply locals_rel_alist_insert_toAList. split; [first [exact Hl1|rewrite Hlocs'; exact Hl1]|exact Hvs]. }
      assert (H0r : lookup 0 (locals tr) = SOME retv).
      { unfold tr, set_vars; wcbn. rewrite Hlt'.
        rewrite lookup_alist_insert_notin, lookup_fromAList_toAList, Henv0; [exact H0|].
        intros Hin. apply in_map_iff in Hin as (x & Hx & Hxin).
        apply (find_var_neq_0_ctxt ctxt x); [split; [exact (proj1 (proj2 Hl))|apply Hvs, IN_set, Hxin]|exact Hx]. }
      destruct (IH r sr ltac:(left; cbn [fst snd]; unfold sr, loopSem.set_vars; lcbn; lia)
                  r2 u2 tr ctxt retv lhA (conj Evr (conj Hr2 (conj Hsr (conj Hlr (conj H0r (conj Hg (conj Hw Hdr))))))))
        as (t2 & res2 & Ev2 & Hf2 & Hp2).
      rewrite Er in Ev2. cbn [FST fst] in Ev2. rewrite Ev2. cbn beta iota.
      apply (cc_cut_tick t tr t2 ctxt retv lo r2 u2 res2 res s1).
      * unfold tr, set_vars; wcbn. exact Hst'.
      * unfold tr, set_vars; wcbn. rewrite Hh'. reflexivity.
      * exact Hf2.
      * exact Hp2.
      * exact H.
      * exact Hne.
    + destruct Hp1 as (Hs1 & He1 & Hj1).
      change (stack tc) with (stack (push_env (env1, LN) (SOME (find_var ctxt n, (wh, (b0, b1)))) (dec_clock t))) in Hj1.
      change (handler tc) with (handler (push_env (env1, LN) (SOME (find_var ctxt n, (wh, (b0, b1)))) (dec_clock t))) in Hj1.
      rewrite Hstc, Hhc in Hj1. change (stack (dec_clock t)) with (stack t) in Hj1.
      destruct (Hj1 _ _ _ (jump_exc_handler_frame _ _ _ _ _ _ _)) as [-> Ht1].
      assert (Hlt1 : locals t1 = fromAList (toAList env1))
        by (rewrite <- Ht1; wcbn; change (fromAList (@nil (N * word_loc a))) with (@LN (word_loc a));
            apply (proj2 (union_LN _))).
      assert (Hst1 : stack t1 = stack t) by (rewrite <- Ht1; reflexivity).
      assert (Hh1 : handler t1 = handler t) by (rewrite <- Ht1; reflexivity).
      rewrite (bd_true (Loc b0 b1 = Loc b0 b1)) by reflexivity. cbn [negb].
      rewrite Hlt1, (bd_true _ (dom_fromAList_toAList_LN env1)).
      set (sh := loopSem.set_var n exn (loopSem.set_locals (loopSem.locals s') st)) in H.
      set (th := set_var (find_var ctxt n) exn t1).
      destruct (loopSem.evaluate (h, sh)) as [r2 u2] eqn:Evh.
      assert (Hr2 : r2 <> SOME loopSem.Error)
        by (intros ->; cbn [loopSem.cut_res IS_SOME] in H; injection H as <- <-; congruence).
      assert (Hsh : state_rel sh th) by (unfold sh, th, loopSem.set_var, set_var; srel Hs1).
      assert (Hlh : locals_rel ctxt (loopSem.locals sh) (locals th)).
      { unfold sh, th, loopSem.set_var, set_var; lcbn; wcbn. rewrite Hlt1.
        apply locals_rel_insert. split; [|exact Hdn]. rewrite Hlocs'. apply locals_rel_toAList, Hl1. }
      assert (H0h : lookup 0 (locals th) = SOME retv).
      { unfold th, set_var; wcbn. rewrite Hlt1, (l0_ins ctxt _ _ _ (proj1 (proj2 Hl)) Hdn).
        rewrite lookup_fromAList_toAList, Henv0. exact H0. }
      destruct (IH h sh ltac:(left; cbn [fst snd]; unfold sh, loopSem.set_var; lcbn; lia)
                  r2 u2 th ctxt retv (l0, l1 + 1) (conj Evh (conj Hr2 (conj Hsh (conj Hlh (conj H0h (conj Hg (conj Hw Hdh))))))))
        as (t2 & res2 & Ev2 & Hf2 & Hp2).
      rewrite Eh in Ev2. cbn [FST fst] in Ev2. rewrite Ev2. cbn beta iota.
      apply (cc_cut_tick t th t2 ctxt retv lo r2 u2 res2 res s1).
      * unfold th, set_var; wcbn. exact Hst1.
      * unfold th, set_var; wcbn. exact Hh1.
      * exact Hf2.
      * exact Hp2.
      * exact H.
      * exact Hne.
    + subst res1. injection H as <- <-. bdf.
      eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. reflexivity.
    + subst res1. injection H as <- <-. bdf.
      eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. reflexivity.
  - (* no handler *)
    cbn [comp]. cbv zeta. cbn [FST SND fst snd].
    wstep. rewrite Hgv, Hbad. cbn [add_ret_loc]. rewrite Hfc. cbn [FST fst SND snd].
    rewrite (bd_false _ (domain_mk_new_cutset_not_empty ctxt live)), Hadm. cbn [orb negb].
    rewrite Hce, Hck. destruct (N.eqb_spec (loopSem.clock s) 0) as [C|_]; [contradiction|].
    rewrite wordSem.fix_clock_evaluate.
    set (tc := call_env args1 ss (push_env (env1, LN) NONE (dec_clock t))).
    destruct (push_env_NONE_facts env1 (dec_clock t)) as [Hstc Hhc].
    assert (Hsc : state_rel sc tc)
      by (apply (state_rel_t _ (push_env (env1, LN) NONE (dec_clock t))); try reflexivity;
          apply state_rel_push_env; exact Hsd).
    assert (Hlc' : locals_rel ctxt1 (loopSem.locals sc) (locals tc))
      by (unfold tc; rewrite locals_call_env; exact Hlc).
    assert (H01c' : lookup 0 (locals tc) = SOME (Loc l0 l1))
      by (unfold tc; rewrite locals_call_env; exact H01c).
    pose proof (IH prog0 sc Hlt r0 st tc ctxt1 (Loc l0 l1) lc) as HH.
    edestruct HH as (t1 & res1 & Ev1 & Hf1 & Hp1);
      [split; [exact Ev|]; split; [exact Hr0|]; split; [exact Hsc|]; split; [exact Hlc'|];
       split; [exact H01c'|]; split; [exact Hg|]; split; [cbn; discriminate|exact Hdc]|].
    rewrite Ev1.
    destruct r0 as [[retvs|exn|bn|cn| |ff|]|]; cbn [cc_post] in Hp1; try (injection H as <- <-; congruence).
    + destruct Hp1 as (Hs1 & -> & Hst1 & Hh1).
      destruct (LENGTH retvs =? LENGTH ns) eqn:Elen; cbn [negb] in H; [|injection H as <- <-; congruence].
      injection H as <- <-.
      rewrite (bd_true (Loc l0 l1 = Loc l0 l1)) by reflexivity. rewrite LENGTH_MAP', Elen. cbn [negb orb].
      change (stack tc) with (stack (push_env (env1, LN) NONE (dec_clock t))) in Hst1.
      rewrite Hstc in Hst1.
      destruct (pop_env_frame t1 _ _ _ _ Hst1) as (t' & Hpop & Hlt' & Hst' & Hh' & Hsr' & Hf').
      rewrite Hpop. cbn [FST SND fst snd]. rewrite Hlt'.
      rewrite (bd_true _ (dom_fromAList_toAList_LN env1)). wstep.
      eexists _, _. split; [reflexivity|].
      unfold set_vars, loopSem.set_vars. wcbn; lcbn. split; [congruence|]. cbn [cc_post].
      split; [apply (state_rel_t _ t'); [apply Hsr'; srel Hs1|reflexivity..]|].
      wcbn; lcbn. split; [reflexivity|].
      split.
      { rewrite Hlt', lookup_alist_insert_notin, lookup_fromAList_toAList, Henv0; [exact H0|].
        intros Hin. apply in_map_iff in Hin as (x & Hx & Hxin).
        apply (find_var_neq_0_ctxt ctxt x); [split; [exact (proj1 (proj2 Hl))|apply Hvs, IN_set, Hxin]|exact Hx]. }
      split; [rewrite Hlt'; apply locals_rel_alist_insert_toAList; split; [first [exact Hl1|rewrite Hlocs'; exact Hl1]|exact Hvs]|].
      split; [exact Hst'|]. rewrite Hh'. rewrite Hh1. exact Hhc.
    + destruct Hp1 as (Hs1 & He1 & Hj1). injection H as <- <-.
      assert (Hres1 : res1 = SOME Error \/ exists u1 u2, res1 = SOME (Exception u1 u2)).
      { destruct (classical_dec (res1 = SOME Error)) as [E|E]; [left; exact E|right; exact (He1 E)]. }
      destruct res1 as [[x ys|x y| | | | | |]|]; try (destruct Hres1 as [C|(? & ? & C)]; discriminate C).
      * eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. cbn [cc_post].
        split; [srel Hs1|]. split; [intros; eauto|].
        intros r' k1 k2 Hj. apply Hj1.
        change (stack tc) with (stack (push_env (env1, LN) NONE (dec_clock t))). rewrite Hstc.
        change (handler tc) with (handler (push_env (env1, LN) NONE (dec_clock t))). rewrite Hhc.
        apply jump_exc_frame. exact Hj.
      * eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. cbn [cc_post].
        split; [srel Hs1|]. split; [intros C; contradiction|].
        intros r' k1 k2 Hj. apply Hj1.
        change (stack tc) with (stack (push_env (env1, LN) NONE (dec_clock t))). rewrite Hstc.
        change (handler tc) with (handler (push_env (env1, LN) NONE (dec_clock t))). rewrite Hhc.
        apply jump_exc_frame. exact Hj.
    + subst res1. injection H as <- <-.
      eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. reflexivity.
    + subst res1. injection H as <- <-.
      eexists _, _. split; [reflexivity|]. split; [exact Hf1|]. reflexivity.
Qed.

Lemma cc_Call s ret dest argvars handler :
  (forall p' s', loopSem.eval_lt (p', s') (loopLang.Call ret dest argvars handler, s) -> cc_P p' s') ->
  cc_P (loopLang.Call ret dest argvars handler) s.
Proof.
  intros IH. destruct ret as [[ns live]|]; [apply cc_Call_ret|apply cc_Call_tail]; exact IH.
Qed.

Lemma cc_all : forall x : loopLang.prog a * loopSem.state a ffi_t, cc_P (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction loopSem.eval_lt_wf).
  assert (IH' : forall p' s', loopSem.eval_lt (p', s') (p, s) -> cc_P p' s')
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  cbn [fst snd]. destruct p.
  - apply cc_Skip.
  - apply cc_Assign.
  - apply cc_Primitive.
  - apply cc_Arith.
  - apply cc_Store.
  - apply cc_SetGlobal.
  - apply cc_Load32.
  - apply cc_LoadByte.
  - apply cc_Store32.
  - apply cc_StoreByte.
  - apply cc_Seq; exact IH'.
  - apply cc_If; exact IH'.
  - apply cc_Loop; exact IH'.
  - apply cc_Break.
  - apply cc_Continue.
  - apply cc_Raise.
  - apply cc_Return.
  - apply cc_ShMem.
  - apply cc_Tick.
  - apply cc_Mark; exact IH'.
  - apply cc_Fail.
  - apply cc_LocValue.
  - apply cc_Call; exact IH'.
  - apply cc_FFI.
Qed.

End CC.

Section CompileCorrect.
Context {a : N} {c ffi_t : Type}.

(** HOL states the theorem as the conclusion of [evaluate_ind] instantiated
    with its goal; the statement below is that conclusion. *)
(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall (prog : loopLang.prog a) (s : loopSem.state a ffi_t)
    res s1 (t : state a c ffi_t) ctxt retv l,
  loopSem.evaluate (prog, s) = (res, s1) /\ res <> SOME loopSem.Error /\
  state_rel s t /\ locals_rel ctxt (loopSem.locals s) (locals t) /\
  lookup 0 (locals t) = SOME retv /\
  good_dimindex a /\
  ~ isWord retv /\
  domain (loopLang.acc_vars prog LN) SUBSET domain ctxt ->
  exists t1 res1,
    evaluate (FST (comp ctxt prog l), t) = (res1, t1) /\
    ffi t1 = loopSem.ffi s1 /\
    match res with
    | NONE => state_rel s1 t1 /\ res1 = NONE /\ lookup 0 (locals t1) = SOME retv /\
              locals_rel ctxt (loopSem.locals s1) (locals t1) /\
              stack t1 = stack t /\ handler t1 = handler t
    | SOME (loopSem.Result v) => state_rel s1 t1 /\ res1 = SOME (Result retv v) /\
              stack t1 = stack t /\ handler t1 = handler t
    | SOME (loopSem.Exception v) =>
        state_rel s1 t1 /\
        (res1 <> SOME Error -> exists u1 u2, res1 = SOME (Exception u1 u2)) /\
        forall r l1 l2,
          jump_exc (set_handler (handler t) (set_stack (stack t) t1)) = SOME (r, (l1, l2)) ->
          res1 = SOME (Exception (Loc l1 l2) v) /\ r = t1
    | SOME (loopSem.Break n) => state_rel s1 t1 /\ res1 = SOME (Break n) /\
              lookup 0 (locals t1) = SOME retv /\
              locals_rel ctxt (loopSem.locals s1) (locals t1) /\
              stack t1 = stack t /\ handler t1 = handler t
    | SOME (loopSem.Continue n) => state_rel s1 t1 /\ res1 = SOME (Continue n) /\
              lookup 0 (locals t1) = SOME retv /\
              locals_rel ctxt (loopSem.locals s1) (locals t1) /\
              stack t1 = stack t /\ handler t1 = handler t
    | SOME loopSem.TimeOut => res1 = SOME TimeOut
    | SOME (loopSem.FinalFFI f) => res1 = SOME (FinalFFI f)
    | _ => False
    end.
Proof.
  intros prog s res s1 t ctxt retv l H.
  exact (cc_all (prog, s) res s1 t ctxt retv l H).
Qed.

End CompileCorrect.

(** ** Semantics *)

Section Semantics.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_with_clock" *)
Theorem state_rel_with_clock : forall (s : loopSem.state a ffi_t) (t : state a c ffi_t) k,
  state_rel s t -> state_rel (loopSem.set_clock k s) (set_clock k t).
Proof. intros s t k Hs. srel Hs. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_mk_ctxt_ln" *)
Theorem locals_rel_mk_ctxt_ln : forall {B} n xs (lc : num_map B),
  0 < n /\ EVEN n -> locals_rel (make_ctxt n xs LN) LN lc.
Proof.
  intros B n xs lc [Hn He]. split; [|split].
  - split; [intros; exact Logic.I|]. intros x y [Hx Hy] Hxy.
    apply domain_lookup in Hx as [vx Hx], Hy as [vy Hy].
    unfold find_var in Hxy; rewrite Hx, Hy in Hxy; subst vy.
    exact (make_ctxt_inj xs LN n ltac:(intros ? ? ? [C _]; discriminate C) x y vx (conj Hx Hy)).
  - intros k m Hk. split.
    + destruct (lookup_make_ctxt_range _ _ _ _ _ Hk) as [C|C]; [discriminate C|lia].
    + apply (lookup_make_ctxt_EVEN xs n LN k m). split; [exact He|].
      split; [intros ? ? C; discriminate C|exact Hk].
  - intros k v C; discriminate C.
Qed.

#[local] Instance behaviour_inhabited_w : Inhabited behaviour := ffi.Fail.

Definition word_res_map (res : option (result a)) : crep_to_loopProof.semantics_run_res outcome :=
  match res with
  | SOME TimeOut => crep_to_loopProof.Incomplete
  | SOME (FinalFFI e) => crep_to_loopProof.CompleteResult (FFI_outcome e)
  | SOME (Result ret _) =>
      if bool_decide (ret = Loc 1 0) then crep_to_loopProof.CompleteResult Success
      else crep_to_loopProof.RunError
  | SOME NotEnoughSpace => crep_to_loopProof.CompleteResult Resource_limit_hit
  | SOME (Break _) => crep_to_loopProof.Incomplete
  | SOME (Continue _) => crep_to_loopProof.Incomplete
  | _ => crep_to_loopProof.RunError
  end.

Lemma word_sem_is_wrapper (s : state a c ffi_t) start :
  semantics s start =
  crep_to_loopProof.semantics_wrapper
    ((word_res_map ## (fun s => io_events (ffi s))) ∘
     (fun k => evaluate (@Call a NONE (SOME start) [0] NONE, set_clock k s))).
Proof.
  unfold semantics, crep_to_loopProof.semantics_wrapper. cbv zeta.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P2 with P1
  end.
  2: { apply propositional_extensionality. split.
       - intros [k Hk]. exists k. eexists. unfold PAIR_MAP. cbn [fst].
         destruct (fst (evaluate _)) as [[ret ys| | | | | | |]|]; try contradiction; try reflexivity.
         unfold word_res_map. rewrite bd_false by exact Hk. reflexivity.
       - intros [k [v Hk]]. exists k. pose proof (f_equal fst Hk) as Hk'. clear Hk.
         unfold PAIR_MAP in Hk'. cbv beta in Hk'. cbn [fst] in Hk'.
         destruct (fst (evaluate _)) as [[ret ys| | | | | | |]|]; try discriminate; try exact Logic.I.
         unfold word_res_map in Hk'. destruct (bool_decide (ret = Loc 1 0)) eqn:E; [discriminate|].
         intros ->. rewrite bd_true in E by reflexivity. discriminate. }
  destruct (classical_dec _) as [_|Hnf]; [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q2 with Q1
  end.
  2: { apply functional_extensionality; intros res; apply propositional_extensionality. split.
       - intros (k & t & r & out & H1 & H2 & H3). exists k, out, (io_events (ffi t)).
         unfold PAIR_MAP. rewrite H1. cbn [fst snd].
         split; [|exact H3]. destruct r as [[ret ys| | | | | | |]|]; try contradiction; subst out;
           try reflexivity.
         unfold word_res_map. destruct (bool_decide (ret = Loc 1 0)) eqn:E; [reflexivity|].
         exfalso; apply Hnf. exists k. rewrite H1. cbn [fst]. intros ->.
         rewrite bd_true in E by reflexivity. discriminate.
       - intros (k & r & ev & H1 & H2).
         pose proof (f_equal snd H1) as H1'. pose proof (f_equal fst H1) as H1''. clear H1.
         unfold PAIR_MAP in H1', H1''. cbn [fst snd] in H1', H1''. rename H1'' into H1.
         exists k, (snd (evaluate (@Call a NONE (SOME start) [0] NONE, set_clock k s))),
           (fst (evaluate (@Call a NONE (SOME start) [0] NONE, set_clock k s))), r.
         split; [apply surjective_pairing|]. rewrite <- H1' in H2.
         split; [|exact H2].
         destruct (fst (evaluate _)) as [[ret ys| | | | | | |]|]; try discriminate;
           unfold word_res_map in H1; try (injection H1 as <-; reflexivity).
         destruct (bool_decide _); [injection H1 as <-; reflexivity|discriminate]. }
  reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics : forall (s : loopSem.state a ffi_t) (t : state a c ffi_t) start,
  state_rel s t /\
  isEmpty (loopSem.locals s) /\ good_dimindex a /\
  lookup 0 (locals t) = SOME (Loc 1 0) /\
  (exists prog : loopLang.prog a, lookup start (loopSem.code s) = SOME ([], prog)) /\
  loopSem.semantics s start <> ffi.Fail ->
  semantics t start = loopSem.semantics s start.
Proof.
  intros s t start (Hs & He & Hg & H0 & _ & Hsem).
  rewrite crep_to_loopProof.loop_sem_is_wrapper in Hsem |- *. rewrite word_sem_is_wrapper.
  cbv zeta in Hsem |- *.
  apply crep_to_loopProof.semantics_wrapper_eq; [exact Hsem| | | | |].
  - intros k r ev (Hk & Hr). exists 0. rewrite N.add_0_r.
    unfold PAIR_MAP in Hk |- *. cbv beta in Hk |- *.
    destruct (loopSem.evaluate (loopLang.Call NONE (SOME start) [] NONE, loopSem.set_clock k s))
      as [res s1] eqn:E.
    cbn [fst snd] in Hk.
    assert (Hres : res <> SOME loopSem.Error) by (intros ->; injection Hk as <- _; congruence).
    assert (Hl : locals_rel (@LN N) (loopSem.locals (loopSem.set_clock k s)) (locals (set_clock k t))).
    { lcbn. destruct (loopSem.locals s); try discriminate He.
      split; [split; [intros; exact Logic.I|intros x y [Hx _]; destruct Hx]|].
      split; intros ? ? C; discriminate C. }
    destruct (compile_correct (loopLang.Call NONE (SOME start) [] NONE) (loopSem.set_clock k s) res s1
                (set_clock k t) LN (Loc 1 0) (0, 0))
      as (t1 & res1 & Ev & Hf & Hp).
    { split; [exact E|]. split; [exact Hres|]. split; [apply state_rel_with_clock, Hs|].
      split; [exact Hl|]. split; [exact H0|]. split; [exact Hg|]. split; [cbn; discriminate|].
      intros x Hx; destruct Hx. }
    cbn [comp FST fst MAP] in Ev. rewrite Ev. cbn [fst snd]. rewrite Hf.
    destruct res as [[vs|ex|bn|cn| |ff|]|]; cbn in Hp; try contradiction;
      try (injection Hk as <- _; congruence).
    + destruct Hp as (_ & -> & _). cbn [word_res_map]. rewrite bd_true by reflexivity. exact Hk.
    + subst res1. exact Hk.
    + subst res1. exact Hk.
  - intros k k' r ev Hk Hr.
    unfold PAIR_MAP in Hk |- *. cbv beta in Hk |- *.
    destruct (evaluate (@Call a NONE (SOME start) [0] NONE, set_clock k t)) as [q u] eqn:E.
    cbn [fst snd] in Hk. injection Hk as Hq Hu.
    assert (Hqt : q <> SOME TimeOut) by (intros ->; apply Hr; rewrite <- Hq; reflexivity).
    pose proof (clock.evaluate_add_clock k' _ _ _ _ (conj E Hqt)) as E'.
    cbn [clock set_clock] in E'. replace (set_clock (k + k') (set_clock k t)) with (set_clock (k + k') t)
      in E' by (destruct t; reflexivity).
    rewrite E'. cbn [fst snd ffi set_clock]. rewrite Hq, Hu. reflexivity.
  - intros k k' r ev Hk Hr.
    unfold PAIR_MAP in Hk |- *. cbv beta in Hk |- *.
    destruct (loopSem.evaluate (loopLang.Call NONE (SOME start) [] NONE, loopSem.set_clock k s))
      as [q u] eqn:E.
    cbn [fst snd] in Hk. injection Hk as Hq Hu.
    assert (Hqt : q <> SOME loopSem.TimeOut) by (intros ->; apply Hr; rewrite <- Hq; reflexivity).
    pose proof (loopProps.evaluate_add_clock_eq _ _ _ _ k' (conj E Hqt)) as E'.
    cbn [loopSem.clock loopSem.set_clock] in E'.
    replace (loopSem.set_clock (k + k') (loopSem.set_clock k s)) with (loopSem.set_clock (k + k') s)
      in E' by (destruct s; reflexivity).
    rewrite E'. cbn [fst snd loopSem.ffi loopSem.set_clock]. rewrite Hq, Hu. reflexivity.
  - intros k k' ev Hk.
    exists (fst (((fun res => match res with
                              | SOME loopSem.TimeOut => crep_to_loopProof.Incomplete
                              | SOME (loopSem.FinalFFI e) => crep_to_loopProof.CompleteResult (FFI_outcome e)
                              | SOME (loopSem.Result _) => crep_to_loopProof.CompleteResult Success
                              | _ => crep_to_loopProof.RunError
                              end) ## (fun s => io_events (loopSem.ffi s)))
                  (loopSem.evaluate (loopLang.Call NONE (SOME start) [] NONE, loopSem.set_clock k s)))).
    eexists. split; [apply surjective_pairing|].
    unfold PAIR_MAP in Hk |- *. cbv beta in Hk |- *. cbn [snd] in Hk |- *.
    injection Hk as _ <-.
    pose proof (loopProps.evaluate_add_clock_io_events_mono (loopLang.Call NONE (SOME start) [] NONE)
                  (loopSem.set_clock k s) k') as P.
    cbn [loopSem.clock loopSem.set_clock] in P.
    replace (loopSem.set_clock (k + k') (loopSem.set_clock k s)) with (loopSem.set_clock (k + k') s)
      in P by (destruct s; reflexivity).
    exact P.
  - intros k k' ev Hk.
    exists (fst ((word_res_map ## (fun s => io_events (ffi s)))
                  (evaluate (@Call a NONE (SOME start) [0] NONE, set_clock k t)))).
    eexists. split; [apply surjective_pairing|].
    unfold PAIR_MAP in Hk |- *. cbv beta in Hk |- *. cbn [snd] in Hk |- *.
    injection Hk as _ <-.
    pose proof (clock.evaluate_add_clock_io_events_mono (@Call a NONE (SOME start) [0] NONE)
                  (set_clock k t) k') as P.
    cbn [clock set_clock] in P.
    replace (set_clock (k + k') (set_clock k t)) with (set_clock (k + k') t)
      in P by (destruct t; reflexivity).
    exact P.
Qed.

End Semantics.

(** ** Whole programs *)

Section Programs.
Context {a : N}.

Lemma MAP_FST_compile_prog (prog : list (N * (list N * loopLang.prog a))) :
  MAP FST (compile_prog prog) = MAP FST prog.
Proof.
  unfold compile_prog. rewrite map_map. apply map_ext. intros [n [ps b]]. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "first_compile_prog_all_distinct" *)
Theorem first_compile_prog_all_distinct : forall (prog : list (N * (list N * loopLang.prog a))),
  ALL_DISTINCT (MAP FST prog) -> ALL_DISTINCT (MAP FST (compile_prog prog)).
Proof. intros prog H. rewrite MAP_FST_compile_prog. exact H. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "first_compile_all_distinct" *)
Theorem first_compile_all_distinct : forall (prog : list (N * (list N * loopLang.prog a))),
  ALL_DISTINCT (MAP FST prog) -> ALL_DISTINCT (MAP FST (compile prog)).
Proof. intros prog H. unfold compile. apply first_compile_prog_all_distinct, H. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "lookup_prog_some_lookup_compile_prog" *)
Theorem lookup_prog_some_lookup_compile_prog : forall (prog : list (N * (list N * loopLang.prog a)))
    name params body,
  lookup name (fromAList prog) = SOME (params, body) ->
  lookup name (fromAList (compile_prog prog)) =
  SOME (LENGTH params + 1, comp_func name params body).
Proof.
  intros prog name params body. rewrite !lookup_fromAList.
  induction prog as [|[n [ps b]] prog IH]; cbn [ALOOKUP]; [discriminate|].
  unfold compile_prog in *. cbn [List.map ALOOKUP].
  destruct (decide (n = name)) as [->|]; [intros H; injection H as <- <-; reflexivity|exact IH].
Qed.

End Programs.

(** ** Labels and handlers *)

Section Labels.
Context {a : N}.

Lemma LENGTH_app' {A} (x y : list A) : LENGTH (x ++ y) = LENGTH x + LENGTH y.
Proof. induction x as [|h x IH]; cbn [LENGTH app]; [lia|rewrite IH; lia]. Qed.

Definition labs_inv (l l' : N * N) (p' : prog a) : Prop :=
  FST l' = FST l /\ SND l <= SND l' /\ good_handlers (FST l) p' = true /\
  LENGTH (extract_labels p') = SND l' - SND l /\
  Forall (fun '(q, r) => q = FST l /\ SND l <= r /\ r < SND l') (extract_labels p') /\
  NoDup (extract_labels p').

Lemma labs_inv_app l l1 l2 (p q : prog a) :
  labs_inv l l1 p -> labs_inv l1 l2 q ->
  FST l2 = FST l /\ SND l <= SND l2 /\
  good_handlers (FST l) p && good_handlers (FST l) q = true /\
  LENGTH (extract_labels p ++ extract_labels q) = SND l2 - SND l /\
  Forall (fun '(q0, r) => q0 = FST l /\ SND l <= r /\ r < SND l2) (extract_labels p ++ extract_labels q) /\
  NoDup (extract_labels p ++ extract_labels q).
Proof.
  intros (A1 & B1 & C1 & D1 & E1 & F1) (A2 & B2 & C2 & D2 & E2 & F2).
  split; [congruence|]. split; [lia|]. split; [rewrite C1, <- A1, C2; reflexivity|].
  split; [rewrite LENGTH_app'; lia|].
  split.
  - apply Forall_app. split.
    + eapply Forall_impl; [|exact E1]. intros [q0 r] (? & ? & ?). split; [assumption|lia].
    + eapply Forall_impl; [|exact E2]. intros [q0 r] (? & ? & ?). split; [congruence|lia].
  - apply NoDup_app; [exact F1|exact F2|].
    intros [q0 r] H1 H2. rewrite Forall_forall in E1, E2.
    destruct (E1 _ H1) as (_ & _ & X1). destruct (E2 _ H2) as (_ & X2 & _). lia.
Qed.

Lemma comp_labs : forall ctxt (p : loopLang.prog a) l p' l',
  comp ctxt p l = (p', l') -> labs_inv l l' p'.
Proof.
  intros ctxt p. induction p using loopProps.prog_nested_ind; intros l0 p' l' Hcp; cbn [comp] in Hcp;
    try (injection Hcp as <- <-; unfold labs_inv; cbn [extract_labels good_handlers LENGTH];
         split; [reflexivity|]; split; [lia|]; split; [reflexivity|];
         split; [lia|]; split; [constructor|constructor]).
  - (* Primitive *)
    destruct pop; destruct (decide _); injection Hcp as <- <-; unfold labs_inv;
      cbn [extract_labels good_handlers LENGTH app andb];
      (split; [reflexivity|]); (split; [lia|]); (split; [reflexivity|]);
      (split; [lia|]); (split; constructor).
  - (* Arith *)
    destruct ar; injection Hcp as <- <-; unfold labs_inv; cbn [extract_labels good_handlers LENGTH];
      (split; [reflexivity|]); (split; [lia|]); (split; [reflexivity|]);
      (split; [lia|]); (split; constructor).
  - (* Seq *)
    destruct (comp ctxt p1 l0) as [wp l1] eqn:E1. destruct (comp ctxt p2 l1) as [wq l2] eqn:E2.
    injection Hcp as <- <-. unfold labs_inv. cbn [extract_labels good_handlers].
    exact (labs_inv_app _ _ _ _ _ (IHp1 _ _ _ E1) (IHp2 _ _ _ E2)).
  - (* If *)
    destruct (comp ctxt p1 l0) as [wp l1] eqn:E1. destruct (comp ctxt p2 l1) as [wq l2] eqn:E2.
    injection Hcp as <- <-. unfold labs_inv. cbn [extract_labels good_handlers app].
    rewrite app_nil_r, andb_true_r.
    exact (labs_inv_app _ _ _ _ _ (IHp1 _ _ _ E1) (IHp2 _ _ _ E2)).
  - (* Loop *)
    destruct (comp ctxt p l0) as [wb lb1] eqn:E1. injection Hcp as <- <-.
    destruct (IHp _ _ _ E1) as (A & B & C & D & E & F).
    unfold labs_inv. cbn [extract_labels good_handlers app]. rewrite app_nil_r.
    split; [exact A|]. split; [exact B|]. split; [rewrite C; reflexivity|]. split; [exact D|]. split; assumption.
  - (* Mark *)
    exact (IHp _ _ _ Hcp).
  - (* Call *)
    destruct ret as [[vs live]|].
    2:{ injection Hcp as <- <-. unfold labs_inv; cbn [extract_labels good_handlers LENGTH].
        split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [lia|]; split; constructor. }
    cbv zeta in Hcp. destruct l0 as [x0 y0]. cbn [FST SND fst snd] in *.
    destruct h as [[n [p1 [p2 lo]]]|].
    + destruct H as [IH1 IH2].
      destruct (comp ctxt p1 (x0, y0 + 1)) as [w1 la] eqn:E1.
      destruct (comp ctxt p2 la) as [w2 lb] eqn:E2. injection Hcp as <- <-.
      destruct (IH1 _ _ _ E1) as (A1 & B1 & C1 & D1 & EE1 & F1).
      destruct (IH2 _ _ _ E2) as (A2 & B2 & C2 & D2 & EE2 & F2).
      destruct la as [xa ya], lb as [xb yb]. cbn [FST SND fst snd] in *. subst xa xb.
      unfold labs_inv. cbn [extract_labels good_handlers FST SND fst snd app].
      split; [reflexivity|]. split; [lia|].
      split; [rewrite C2, C1, N.eqb_refl; reflexivity|].
      split; [rewrite app_nil_r; cbn [LENGTH]; rewrite LENGTH_app'; lia|].
      rewrite app_nil_r. split.
      * constructor; [split; [reflexivity|lia]|]. constructor; [split; [reflexivity|lia]|].
        apply Forall_app. split.
        -- eapply Forall_impl; [|exact EE2]. intros [q r] (? & ? & ?). split; [assumption|lia].
        -- eapply Forall_impl; [|exact EE1]. intros [q r] (? & ? & ?). split; [assumption|lia].
      * rewrite Forall_forall in EE1, EE2.
        constructor.
        { intros Hin. destruct Hin as [Hq|Hin]; [injection Hq; lia|].
          apply in_app_iff in Hin as [Hin|Hin];
            [destruct (EE2 _ Hin) as (_ & ? & _)|destruct (EE1 _ Hin) as (_ & ? & _)]; lia. }
        constructor.
        { intros Hin. apply in_app_iff in Hin as [Hin|Hin];
            [destruct (EE2 _ Hin) as (_ & _ & ?)|destruct (EE1 _ Hin) as (_ & _ & ?)]; lia. }
        apply NoDup_app; [exact F2|exact F1|].
        intros [q r] H1 H2. destruct (EE2 _ H1) as (_ & ? & _). destruct (EE1 _ H2) as (_ & _ & ?). lia.
    + injection Hcp as <- <-. unfold labs_inv. cbn [extract_labels good_handlers FST SND fst snd app LENGTH].
      split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
      split; [constructor; [split; [reflexivity|lia]|constructor]|].
      constructor; [intros []|constructor].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "comp_l_invariant" *)
Theorem comp_l_invariant : forall ctxt (prog : loopLang.prog a) l prog' l',
  comp ctxt prog l = (prog', l') -> FST l' = FST l.
Proof. intros ctxt prog l prog' l' H. exact (proj1 (comp_labs _ _ _ _ _ H)). Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "good_handlers_comp" *)
Theorem good_handlers_comp : forall ctxt (prog : loopLang.prog a) l,
  good_handlers (FST l) (FST (comp ctxt prog l)).
Proof.
  intros ctxt prog l. destruct (comp ctxt prog l) as [p' l'] eqn:E.
  exact (proj1 (proj2 (proj2 (comp_labs _ _ _ _ _ E)))).
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_good_handlers" *)
Theorem loop_to_word_good_handlers : forall (prog : list (N * (list N * loopLang.prog a))) prog',
  compile_prog prog = prog' ->
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) prog'.
Proof.
  intros prog prog' <-. unfold compile_prog. induction prog as [|[n [ps b]] prog IH]; [reflexivity|].
  cbn [List.map EVERY]. unfold is_true in *. apply andb_true_intro. split; [|exact IH].
  unfold comp_func. cbv zeta. apply (good_handlers_comp _ b (n, 2)).
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_SND_LE" *)
Theorem loop_to_word_comp_SND_LE : forall ctxt (prog : loopLang.prog a) l p r,
  comp ctxt prog l = (p, r) -> SND l <= SND r.
Proof. intros ctxt prog l p r H. exact (proj1 (proj2 (comp_labs _ _ _ _ _ H))). Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_extract_labels_len" *)
Theorem loop_to_word_comp_extract_labels_len : forall ctxt (prog : loopLang.prog a) l p r,
  comp ctxt prog l = (p, r) -> LENGTH (extract_labels p) = SND r - SND l.
Proof. intros ctxt prog l p r H. exact (proj1 (proj2 (proj2 (proj2 (comp_labs _ _ _ _ _ H))))). Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_extract_labels" *)
Theorem loop_to_word_comp_extract_labels : forall ctxt (prog : loopLang.prog a) l p l',
  comp ctxt prog l = (p, l') ->
  EVERY (fun '(q, r) => (q =? FST l) && (SND l <=? r) && (r <? SND l')) (extract_labels p).
Proof.
  intros ctxt prog l p l' H. destruct (comp_labs _ _ _ _ _ H) as (_ & _ & _ & _ & E & _).
  unfold is_true. apply EVERY_Forall. eapply Forall_impl; [|exact E].
  intros [q r] (-> & H1 & H2). rewrite N.eqb_refl. apply N.leb_le in H1. apply N.ltb_lt in H2.
  rewrite H1, H2. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_ALL_DISTINCT" *)
Theorem loop_to_word_comp_ALL_DISTINCT : forall ctxt (prog : loopLang.prog a) l p r,
  comp ctxt prog l = (p, r) -> ALL_DISTINCT (extract_labels p).
Proof.
  intros ctxt prog l p r H. destruct (comp_labs _ _ _ _ _ H) as (_ & _ & _ & _ & _ & F).
  apply ALL_DISTINCT_NoDup_list, F.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_func_lab_pres" *)
Theorem loop_to_word_comp_func_lab_pres : forall n' params (body : loopLang.prog a) p,
  comp_func n' params body = p ->
  (forall n, n < LENGTH (extract_labels p) ->
     (fun '(l1, l2) => l1 = n' /\ l2 <> 0 /\ l2 <> 1) (EL n (extract_labels p))) /\
  ALL_DISTINCT (extract_labels p).
Proof.
  intros n' params body p <-. unfold comp_func. cbv zeta.
  match goal with |- context [comp ?ct body (n', 2)] => destruct (comp ct body (n', 2)) as [p' l'] eqn:E end.
  cbn [FST fst]. destruct (comp_labs _ _ _ _ _ E) as (_ & _ & _ & _ & EE & F). split.
  - intros n Hn. rewrite Forall_forall in EE. rewrite EL_nth by exact Hn.
    assert (Hin : In (nth (N.to_nat n) (extract_labels p') ARB) (extract_labels p'))
      by (apply nth_In; rewrite LENGTH_length in Hn; lia).
    destruct (nth _ _ _) as [q r]. destruct (EE _ Hin) as (Hq & Hr & _). cbn [FST SND fst snd] in *.
    split; [exact Hq|]. split; lia.
  - apply ALL_DISTINCT_NoDup_list, F.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_prog_lab_pres" *)
Theorem loop_to_word_compile_prog_lab_pres : forall (prog : list (N * (list N * loopLang.prog a))) prog',
  compile_prog prog = prog' ->
  EVERY (fun '(n, (m, p)) =>
           let labs := extract_labels p in
           EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) labs &&
           ALL_DISTINCT labs) prog'.
Proof.
  intros prog prog' <-. unfold compile_prog. induction prog as [|[n [ps b]] prog IH]; [reflexivity|].
  cbn [List.map EVERY]. unfold is_true in *. apply andb_true_intro. split; [|exact IH].
  cbv zeta. unfold comp_func. cbv zeta.
  match goal with |- context [comp ?ct b (n, 2)] => destruct (comp ct b (n, 2)) as [p' l'] eqn:E end.
  cbn [FST fst]. destruct (comp_labs _ _ _ _ _ E) as (_ & _ & _ & _ & EE & F).
  apply andb_true_intro. split; [|apply ALL_DISTINCT_NoDup_list, F].
  apply EVERY_Forall. eapply Forall_impl; [|exact EE]. intros [q r] (-> & H1 & H2). cbn [FST SND fst snd] in *.
  rewrite N.eqb_refl. destruct (N.eqb_spec r 0); [lia|]. destruct (N.eqb_spec r 1); [lia|]. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_prog_FST_eq" *)
Theorem loop_to_word_compile_prog_FST_eq : forall (prog : list (N * (list N * loopLang.prog a))) prog',
  compile_prog prog = prog' -> MAP FST prog' = MAP FST prog.
Proof. intros prog prog' <-. apply MAP_FST_compile_prog. Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_prog_lab_min" *)
Theorem loop_to_word_compile_prog_lab_min : forall (prog : list (N * (list N * loopLang.prog a))) prog' x,
  compile_prog prog = prog' /\ EVERY (fun p => x <=? FST p) prog ->
  EVERY (fun p => x <=? FST p) prog'.
Proof.
  intros prog prog' x [<- H]. unfold compile_prog. induction prog as [|[n [ps b]] prog IH]; [reflexivity|].
  cbn [List.map EVERY FST fst] in *. unfold is_true in *. apply andb_prop in H as [H1 H2].
  rewrite H1, (IH H2). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_lab_min" *)
Theorem loop_to_word_compile_lab_min : forall (prog : list (N * (list N * loopLang.prog a))) prog' x,
  compile prog = prog' /\ EVERY (fun p => x <=? FST p) prog ->
  EVERY (fun p => x <=? FST p) prog'.
Proof. intros prog prog' x [<- H]. apply (loop_to_word_compile_prog_lab_min prog _ x (conj eq_refl H)). Qed.

End Labels.

(** ** Subprograms that are not created *)

Section NotCreated.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_not_created" *)
Theorem loop_to_word_comp_not_created : forall (P : prog a -> Prop),
  (forall x, match x with
             | ShareInst _ _ _ => True | Call _ _ _ _ => True | LocValue _ _ => True
             | _ => False end -> P x) ->
  forall ctxt (prog : loopLang.prog a) l wprog l2,
    comp ctxt prog l = (wprog, l2) -> not_created_subprogs P wprog.
Proof.
  intros P HP ctxt prog. induction prog using loopProps.prog_nested_ind; intros l0 wprog lr Hcp;
    cbn [comp] in Hcp;
    try (injection Hcp as <- <-; cbn [not_created_subprogs]; try exact Logic.I;
         apply HP; exact Logic.I).
  - destruct pop; destruct (decide _); injection Hcp as <- <-; cbn [not_created_subprogs];
      repeat split.
  - destruct ar; injection Hcp as <- <-; exact Logic.I.
  - destruct (comp ctxt prog1 l0) as [wp l1] eqn:E1. destruct (comp ctxt prog2 l1) as [wq l3] eqn:E2.
    injection Hcp as <- <-. cbn [not_created_subprogs]. split; [exact (IHprog1 _ _ _ E1)|exact (IHprog2 _ _ _ E2)].
  - destruct (comp ctxt prog1 l0) as [wp l1] eqn:E1. destruct (comp ctxt prog2 l1) as [wq l3] eqn:E2.
    injection Hcp as <- <-. cbn [not_created_subprogs].
    split; [split; [exact (IHprog1 _ _ _ E1)|exact (IHprog2 _ _ _ E2)]|exact Logic.I].
  - destruct (comp ctxt prog l0) as [wb lb] eqn:E1. injection Hcp as <- <-. cbn [not_created_subprogs].
    split; [exact Logic.I|]. split; [exact (IHprog _ _ _ E1)|exact Logic.I].
  - exact (IHprog _ _ _ Hcp).
  - destruct ret as [[vs live]|].
    2:{ injection Hcp as <- <-. cbn [not_created_subprogs]. split; [apply HP; exact Logic.I|].
        split; exact Logic.I. }
    cbv zeta in Hcp. destruct h as [[n [p1 [p2 lo]]]|].
    + destruct H as [IH1 IH2].
      destruct (comp ctxt p1 _) as [w1 la] eqn:E1. destruct (comp ctxt p2 la) as [w2 lb] eqn:E2.
      destruct lb as [b0 b1]. injection Hcp as <- <-. cbn [not_created_subprogs].
      repeat split; first [apply HP; exact Logic.I | exact (IH1 _ _ _ E1) | exact (IH2 _ _ _ E2)].
    + injection Hcp as <- <-. cbn [not_created_subprogs].
      split; [apply HP; exact Logic.I|]. split; exact Logic.I.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_func_not_created" *)
Theorem loop_to_word_comp_func_not_created : forall (P : prog a -> Prop),
  (forall x, match x with
             | ShareInst _ _ _ => True | Call _ _ _ _ => True | LocValue _ _ => True
             | _ => False end -> P x) ->
  forall (body : loopLang.prog a) name params, not_created_subprogs P (comp_func name params body).
Proof.
  intros P HP body name params. unfold comp_func. cbv zeta.
  match goal with |- context [comp ?ct body ?l] => destruct (comp ct body l) as [p' l'] eqn:E end.
  exact (loop_to_word_comp_not_created P HP _ _ _ _ _ E).
Qed.

End NotCreated.
