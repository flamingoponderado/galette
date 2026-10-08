(** * Pancake [crep_to_loopProof]: correctness of [crep_to_loop] (first part)

    Port of [cakeml/pancake/proofs/crep_to_loopProofScript.sml].

    Naming: [loopSem] is imported, so unqualified [state], [locals],
    [evaluate], [eval], ... are loopSem's; crepSem's are written
    [crepSem.X].  As in [crep_to_loop.v], unqualified program and
    expression constructors are loopLang's and crepLang's are written
    [crepLang.X].  HOL's [t with clock := c] is [set_clock c t].

    [ncompile_correct] (HOL: [recInduct evaluate_ind] with one [Resume] per
    statement) is well-founded induction on [crepSem.eval_lt]; each statement
    is handled by a Galette-only lemma [nc_<Stmt>] about the predicate
    [nc_P] (the theorem's conclusion with [rels], [nc_res] and [nc_post]
    naming its parts).  Likewise [rels], [pe_exp], [keep_eval], [mf_list],
    [cp_list] and the other untagged lemmas are Galette-only helpers; the
    HOL [local] lemmas [opt_mmap_rhss_locals_rel], [opt_mmap_lhss_locals_rel]
    and [not_mem_nlhss_lemma] are covered by [rhss_rel] and [lhss_rel].

    Not ported (index-based list lemmas off the path to
    [state_rel_imp_semantics], or HOL [local] lemmas whose role is played
    by Galette-only helpers): [ALOOKUP_EQ_EL], [alookup_el_pair_eq_el],
    [initial_prog_make_funcs_el], [evaluate_less_clock_cases],
    [evaluate_twice_cases], [evaluate_io_mono_rephrases],
    [PAIR_MAP_EQ_UNCURRY], [member_cutset_survives_comp_exp(s)_flip],
    [evaluate_none_nested_seq_append_eq], [find_code_collapse_cases],
    [OPT_MMAP_APPEND], [case_le], [crep_eval_upd_clock],
    [loop_eval_upd_clock], [UNCURRY_eq_case], [locals_rel_lookup_same],
    [locals_rel_inter_helper].  [mem_lookup_fromalist_some] needs
    [EqDecision] on the value type for HOL's [MEM]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte bitstring.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
Import wordLang(word_loc(..)).
From Galette.cakeml.pancake Require Import pan_common crepLang loopLang crep_to_loop.
From Galette.cakeml.pancake.semantics Require panSem crepSem crepProps.
From Galette.cakeml.pancake.semantics Require Import pan_commonProps loopSem loopProps.
From Galette.cakeml.pancake.proofs Require loop_liveProof crep_arithProof.
Open Scope N_scope.

(** ** Nested sequences (aliases of [loopProps] facts) *)

Section NestedSeq.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_nested_seq_append_first" *)
Theorem evaluate_nested_seq_append_first : forall (p q : list (loopLang.prog a))
    (s : state a ffi_t) st t,
  evaluate (nested_seq (p ++ q), s) = (NONE, t) /\
  evaluate (nested_seq p, s) = (NONE, st) ->
  evaluate (nested_seq q, st) = (NONE, t).
Proof. exact (proj1 evaluate_nested_seq_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_none_nested_seq_append" *)
Theorem evaluate_none_nested_seq_append : forall (p : list (loopLang.prog a))
    (s : state a ffi_t) st q,
  evaluate (nested_seq p, s) = (NONE, st) ->
  evaluate (nested_seq (p ++ q), s) = evaluate (nested_seq q, st).
Proof. exact (proj1 (proj2 evaluate_nested_seq_cases)). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_not_none_nested_seq_append" *)
Theorem evaluate_not_none_nested_seq_append : forall (p : list (loopLang.prog a))
    (s : state a ffi_t) res st q,
  evaluate (nested_seq p, s) = (res, st) /\ res <> NONE ->
  evaluate (nested_seq (p ++ q), s) = evaluate (nested_seq p, s).
Proof. exact (proj2 (proj2 evaluate_nested_seq_cases)). Qed.

End NestedSeq.

(** ** State relation *)

Section Rel.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_def" *)
Definition state_rel (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t) : Prop :=
  crepSem.memaddrs s = mdomain t /\
  crepSem.sh_memaddrs s = sh_mdomain t /\
  crepSem.clock s = clock t /\
  crepSem.be s = be t /\
  crepSem.ffi s = ffi t /\
  crepSem.base_addr s = base_addr t /\
  crepSem.top_addr s = top_addr t.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "wlab_wloc_def" *)
Definition wlab_wloc (w : panSem.word_lab a) : word_loc a :=
  match w with panSem.Word w => Word w end.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_rel_def" *)
Definition mem_rel (smem : word a -> panSem.word_lab a) (tmem : word a -> word_loc a)
    (dom : word a -> Prop) : Prop :=
  forall ad, ad IN dom -> wlab_wloc (smem ad) = tmem ad.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_def" *)
Definition globals_rel (sglobals : fmap (word 5) (panSem.word_lab a))
    (tglobals : fmap (word 5) (word_loc a)) : Prop :=
  forall ad v, FLOOKUP sglobals ad = SOME v -> FLOOKUP tglobals ad = SOME (wlab_wloc v).

End Rel.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_funcs_def" *)
Definition distinct_funcs {K B} (fm : fmap K (N * B)) : Prop :=
  forall x y n m rm rm', FLOOKUP fm x = SOME (n, rm) /\ FLOOKUP fm y = SOME (m, rm') /\ n = m ->
  x = y.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ctxt_fc_def" *)
Definition ctxt_fc (c : architecture) (cvs : fmap crepLang.funname (N * N)) (ns : list N)
    (args : list N) : context :=
  {| vars := FEMPTY |++ ZIP (ns, args);
     funcs := cvs;
     vmax := MAX_LIST args;
     target := c |}.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel_def" *)
Definition code_rel {a : N} (ctxt : context)
    (s_code : fmap crepLang.funname (list N * crepLang.prog a))
    (t_code : spt (list N * loopLang.prog a)) : Prop :=
  distinct_funcs (funcs ctxt) /\
  forall f ns prog,
    FLOOKUP s_code f = SOME (ns, prog) ->
    exists loc len, FLOOKUP (funcs ctxt) f = SOME (loc, len) /\
      LENGTH ns = len /\
      let args := GENLIST I len in
      let nctxt := ctxt_fc (target ctxt) (funcs ctxt) ns args in
      lookup loc t_code = SOME (args, ocompile nctxt (list_to_num_set args) prog).

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ctxt_max_def" *)
Definition ctxt_max {K} (n : N) (fm : fmap K N) : Prop :=
  forall v m, FLOOKUP fm v = SOME m -> m <= n.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_vars_def" *)
Definition distinct_vars {K V} (fm : fmap K V) : Prop :=
  forall x y n m, FLOOKUP fm x = SOME n /\ FLOOKUP fm y = SOME m /\ n = m -> x = y.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_def" *)
Definition locals_rel {a : N} (ctxt : context) (l : num_set)
    (s_locals : fmap N (panSem.word_lab a)) (t_locals : spt (word_loc a)) : Prop :=
  distinct_vars (vars ctxt) /\ ctxt_max (vmax ctxt) (vars ctxt) /\
  domain l SUBSET domain t_locals /\
  forall vname v,
    FLOOKUP s_locals vname = SOME v ->
    exists n, FLOOKUP (vars ctxt) vname = SOME n /\ n IN domain l /\
      lookup n t_locals = SOME (wlab_wloc v).

Section Intro.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_intro" *)
Theorem state_rel_intro : forall (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t),
  state_rel s t <->
  crepSem.memaddrs s = mdomain t /\
  crepSem.sh_memaddrs s = sh_mdomain t /\
  crepSem.clock s = clock t /\
  crepSem.be s = be t /\
  crepSem.ffi s = ffi t /\
  crepSem.base_addr s = base_addr t /\
  crepSem.top_addr s = top_addr t.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_intro" *)
Theorem locals_rel_intro : forall ctxt l (s_locals : fmap N (panSem.word_lab a)) t_locals,
  locals_rel ctxt l s_locals t_locals ->
  distinct_vars (vars ctxt) /\ ctxt_max (vmax ctxt) (vars ctxt) /\
  domain l SUBSET domain t_locals /\
  forall vname v,
    FLOOKUP s_locals vname = SOME v ->
    exists n, FLOOKUP (vars ctxt) vname = SOME n /\ n IN domain l /\
      lookup n t_locals = SOME (wlab_wloc v).
Proof. intros; assumption. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel_intro" *)
Theorem code_rel_intro : forall ctxt (s_code : fmap crepLang.funname (list N * crepLang.prog a))
    (t_code : spt (list N * loopLang.prog a)),
  code_rel ctxt s_code t_code ->
  distinct_funcs (funcs ctxt) /\
  forall f ns prog,
    FLOOKUP s_code f = SOME (ns, prog) ->
    exists loc len, FLOOKUP (funcs ctxt) f = SOME (loc, len) /\
      LENGTH ns = len /\
      let args := GENLIST I len in
      let nctxt := ctxt_fc (target ctxt) (funcs ctxt) ns args in
      lookup loc t_code = SOME (args, ocompile nctxt (list_to_num_set args) prog).
Proof. intros; assumption. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_rel_intro" *)
Theorem mem_rel_intro : forall (smem : word a -> panSem.word_lab a) tmem dm,
  mem_rel smem tmem dm -> forall ad, ad IN dm -> wlab_wloc (smem ad) = tmem ad.
Proof. intros; auto. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "globals_rel_intro" *)
Theorem globals_rel_intro : forall (sglobals : fmap (word 5) (panSem.word_lab a)) tglobals,
  globals_rel sglobals tglobals ->
  forall ad v, FLOOKUP sglobals ad = SOME v -> FLOOKUP tglobals ad = SOME (wlab_wloc v).
Proof. intros; auto. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_clock_add_zero" *)
Theorem state_rel_clock_add_zero : forall (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t),
  state_rel s t -> exists ck, state_rel s (set_clock (ck + clock t) t).
Proof. intros s t H; exists 0; exact H. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_insert_gt_vmax" *)
Theorem locals_rel_insert_gt_vmax : forall ct cset (lcl : fmap N (panSem.word_lab a)) lcl' n w,
  locals_rel ct cset lcl lcl' /\ vmax ct < n ->
  locals_rel ct cset lcl (insert n w lcl').
Proof.
  intros ct cset lcl lcl' n w ((Hd & Hm & Hs & Hl) & Hn).
  split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk; unfold pred_set.IN in *; rewrite domain_insert; right; exact (Hs k Hk).
  - intros v x Hx. destruct (Hl v x Hx) as (m & Hv & Hmd & Hlk).
    exists m; split; [exact Hv|]; split; [exact Hmd|].
    rewrite lookup_insert. destruct (decide (m = n)) as [->|]; [|exact Hlk].
    specialize (Hm _ _ Hv). lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "locals_rel_cutset_prop" *)
Theorem locals_rel_cutset_prop : forall ct cset (lcl : fmap N (panSem.word_lab a)) lcl' cset' lcl'',
  locals_rel ct cset lcl lcl' /\
  locals_rel ct cset' lcl lcl'' /\
  subspt cset cset' ->
  locals_rel ct cset lcl lcl''.
Proof.
  intros ct cset lcl lcl' cset' lcl'' ((Hd & Hm & Hs & Hl) & (Hd' & Hm' & Hs' & Hl') & Hsub).
  rewrite subspt_def in Hsub.
  split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk. apply Hs'. apply Hsub. exact Hk.
  - intros v x Hx. destruct (Hl v x Hx) as (m & Hv & Hmd & _).
    destruct (Hl' v x Hx) as (m' & Hv' & _ & Hlk).
    rewrite Hv in Hv'. injection Hv' as <-.
    exists m; split; [exact Hv|]; split; [exact Hmd|exact Hlk].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "write_bytearray_mem_rel" *)
Theorem write_bytearray_mem_rel : forall nb (sm : word a -> panSem.word_lab a) tm (w : word a) dm be,
  mem_rel sm tm dm ->
  mem_rel (panSem.write_bytearray w nb sm dm be) (write_bytearray w nb tm dm be) dm.
Proof.
  induction nb as [|b nb IH]; intros sm tm w dm be H; [exact H|].
  cbn [panSem.write_bytearray write_bytearray].
  specialize (IH sm tm (w + n2w 1)%w dm be H).
  set (sm1 := panSem.write_bytearray (w + n2w 1)%w nb sm dm be) in *.
  set (tm1 := write_bytearray (w + n2w 1)%w nb tm dm be) in *.
  unfold panSem.mem_store_byte, mem_store_byte_aux.
  destruct (sm1 (byte_align w)) as [v] eqn:Es.
  destruct (classical_dec (byte_align w IN dm)) as [Hin|Hin].
  - rewrite <- (IH _ Hin), Es. cbn [wlab_wloc].
    intros ad Had. unfold UPDATE.
    destruct (decide (byte_align w = ad)) as [<-|Hne]; [reflexivity|].
    apply IH; exact Had.
  - destruct (tm1 (byte_align w)) as [v'|]; exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_comb_seq" *)
Theorem evaluate_comb_seq : forall (p : loopLang.prog a) (s : state a ffi_t) t q r,
  evaluate (p, s) = (NONE, t) /\ evaluate (q, t) = (NONE, r) ->
  evaluate (Seq p q, s) = (NONE, r).
Proof.
  intros p s t q r [H1 H2]. unfold_eval. rewrite H1. exact H2.
Qed.

End Intro.

(** ** Syntactic lemmas *)

Section Syntax.
Context {a : N}.

Lemma GENLIST_add_SUC (k : N) n :
  GENLIST (N.add k) (SUC n) = k :: GENLIST (N.add (k + 1)) n.
Proof.
  rewrite GENLIST_CONS_aux. rewrite N.add_0_r. f_equal.
  f_equal. apply functional_extensionality; intros i; lia.
Qed.

Lemma cut_sets_MAPi_from : forall (les : list (loopLang.exp a)) cs i offset,
  cut_sets cs (nested_seq (crep_to_loop.MAPi_from i (fun n => Assign (n + offset)) les)) =
  list_insert (GENLIST (N.add (i + offset)) (LENGTH les)) cs.
Proof.
  induction les as [|e les IH]; intros cs i offset; [reflexivity|].
  cbn [crep_to_loop.MAPi_from nested_seq cut_sets LENGTH].
  rewrite IH, GENLIST_add_SUC. cbn [list_insert].
  replace (i + 1 + offset) with (i + offset + 1) by lia. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "cut_sets_MAPi_Assign" *)
Theorem cut_sets_MAPi_Assign : forall (les : list (loopLang.exp a)) cs offset,
  cut_sets cs (nested_seq (crep_to_loop.MAPi (fun n => Assign (n + offset)) les)) =
  list_insert (GENLIST (N.add offset) (LENGTH les)) cs.
Proof. intros les cs offset; apply (cut_sets_MAPi_from les cs 0 offset). Qed.

Lemma assigned_vars_MAPi_from : forall (les : list (loopLang.exp a)) i offset,
  assigned_vars (nested_seq (crep_to_loop.MAPi_from i (fun n => Assign (n + offset)) les)) =
  GENLIST (N.add (i + offset)) (LENGTH les).
Proof.
  induction les as [|e les IH]; intros i offset; [reflexivity|].
  cbn [crep_to_loop.MAPi_from nested_seq assigned_vars LENGTH].
  rewrite IH, GENLIST_add_SUC.
  replace (i + 1 + offset) with (i + offset + 1) by lia. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "assigned_vars_MAPi_Assign" *)
Theorem assigned_vars_MAPi_Assign : forall (les : list (loopLang.exp a)) offset,
  assigned_vars (nested_seq (crep_to_loop.MAPi (fun n => Assign (n + offset)) les)) =
  GENLIST (N.add offset) (LENGTH les).
Proof. intros les offset; apply (assigned_vars_MAPi_from les 0 offset). Qed.

Lemma survives_MAPi_from : forall n (les : list (loopLang.exp a)) i offset,
  survives n (nested_seq (crep_to_loop.MAPi_from i (fun n => Assign (n + offset)) les)).
Proof.
  intros n; induction les as [|e les IH]; intros i offset; cbn; [exact Logic.I|].
  split; [exact Logic.I|apply IH].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "survives_MAPi_Assign" *)
Theorem survives_MAPi_Assign : forall n (les : list (loopLang.exp a)) offset,
  survives n (nested_seq (crep_to_loop.MAPi (fun n => Assign (n + offset)) les)) = True.
Proof.
  intros n les offset; apply propositional_extensionality; split; [intros; exact Logic.I|].
  intros _; apply survives_MAPi_from.
Qed.

End Syntax.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "insert_insert_eq" *)
Theorem insert_insert_eq : forall {A} a (b : A) c, insert a b (insert a b c) = insert a b c.
Proof. intros; apply insert_shadow. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "list_insert_SNOC" *)
Theorem list_insert_SNOC : forall y l x,
  list_insert (SNOC x y) l = insert x tt (list_insert y l).
Proof.
  induction y as [|h y IH]; intros l x; [reflexivity|].
  cbn [SNOC list_insert]. apply IH.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "list_insert_insert" *)
Theorem list_insert_insert : forall x xs l,
  insert x tt (list_insert xs l) = list_insert xs (insert x tt l).
Proof.
  intros x xs; induction xs as [|y xs IH]; intros l; [reflexivity|].
  cbn [list_insert]. rewrite IH. f_equal.
  destruct (decide (x = y)) as [->|Hne]; [reflexivity|].
  apply insert_swap; exact Hne.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "list_insert_append" *)
Theorem list_insert_append : forall xs ys l,
  list_insert (xs ++ ys) l = list_insert xs (list_insert ys l).
Proof.
  induction xs as [|x xs IH]; intros ys l; [reflexivity|].
  cbn [list_insert app]. rewrite IH, list_insert_insert. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exps_alt" *)
Theorem compile_exps_alt : forall {a} ctxt tmp l (e : crepLang.exp a) es,
  compile_exps ctxt tmp l (@nil (crepLang.exp a)) = ([], ([], (tmp, l))) /\
  compile_exps ctxt tmp l (e :: es) =
  let '(p, (le, (tmp', l'))) := compile_exp ctxt tmp l e in
  let '(p1, (les, (tmp'', l''))) := compile_exps ctxt tmp' l' es in
  (p ++ p1, (le :: les, (tmp'', l''))).
Proof. intros; split; reflexivity. Qed.

Section OutRel.
Context {a : N}.

Lemma comp_syntax_ok_MAPi_from : forall (les : list (loopLang.exp a)) cs i offset,
  comp_syntax_ok cs (nested_seq (crep_to_loop.MAPi_from i (fun n => Assign (n + offset)) les)).
Proof.
  induction les as [|e les IH]; intros cs i offset; cbn; [exact Logic.I|].
  split; [exact Logic.I|apply IH].
Qed.

Lemma MAPi_from_add_comm (tmp i : N) (les : list (loopLang.exp a)) :
  crep_to_loop.MAPi_from i (fun n => Assign (tmp + n)) les =
  crep_to_loop.MAPi_from i (fun n => Assign (n + tmp)) les.
Proof.
  f_equal. apply functional_extensionality; intros n. rewrite N.add_comm; reflexivity.
Qed.

Lemma MAPi_add_comm (tmp : N) (les : list (loopLang.exp a)) :
  crep_to_loop.MAPi (fun n => Assign (tmp + n)) les =
  crep_to_loop.MAPi (fun n => Assign (n + tmp)) les.
Proof.
  f_equal. apply functional_extensionality; intros n. rewrite N.add_comm; reflexivity.
Qed.

Definition out_rel_exp (e : crepLang.exp a) : Prop :=
  forall ct tmp l p le ntmp nl,
    compile_exp ct tmp l e = (p, (le, (ntmp, nl))) ->
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p).

Definition out_rel_exps (e : list (crepLang.exp a)) : Prop :=
  forall ct tmp l p le ntmp nl,
    compile_exps ct tmp l e = (p, (le, (ntmp, nl))) ->
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p) /\
    LENGTH le = LENGTH e.

Lemma out_rel_exps_of : forall es, Forall out_rel_exp es -> out_rel_exps es.
Proof.
  intros es HF; induction HF as [|e es He Hes IH]; intros ct tmp l p le ntmp nl Hc.
  - injection Hc as <- <- <- <-. cbn. repeat split; try exact Logic.I; try lia; try reflexivity.
  - cbn [compile_exps] in Hc.
    destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps ct tmp1 l1 es) as [p2 [les2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-.
    destruct (He _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & ->).
    destruct (IH _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & -> & Len).
    split; [apply comp_syn_ok_nested_seq; split; assumption|].
    split; [lia|]. split; [rewrite cut_sets_nested_seq; reflexivity|].
    cbn [LENGTH]. rewrite Len. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_out_rel_cases" *)
Theorem compile_exp_out_rel_cases :
  (forall ct tmp l (e : crepLang.exp a) p le ntmp nl,
    compile_exp ct tmp l e = (p, (le, (ntmp, nl))) ->
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p)) /\
  (forall ct tmp l (e : list (crepLang.exp a)) p le ntmp nl,
    compile_exps ct tmp l e = (p, (le, (ntmp, nl))) ->
    comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p) /\
    LENGTH le = LENGTH e).
Proof.
  assert (G : forall e, out_rel_exp e).
  { intros e; induction e as [w|v|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2
                             |sh e1 e2 IH1 IH2| |] using crepProps.cexp_nested_ind;
      intros ct tmp l p le ntmp nl Hc; cbn [compile_exp] in Hc;
      try rewrite compile_exps_nested in Hc.
    all: try solve [injection Hc; intros; subst; cbn; repeat split; try exact Logic.I; try lia; try reflexivity].
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. exact (IH _ _ _ _ _ _ _ C1).
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      destruct (IH _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & ->).
      split; [apply comp_syn_ok_nested_seq; split; [exact Ok1|cbn; tauto]|].
      split; [lia|]. rewrite cut_sets_nested_seq. cbn. rewrite insert_shadow. reflexivity.
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      destruct (IH _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & ->).
      split; [apply comp_syn_ok_nested_seq; split; [exact Ok1|cbn; tauto]|].
      split; [lia|]. rewrite cut_sets_nested_seq. cbn. rewrite insert_shadow. reflexivity.
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      destruct (out_rel_exps_of es IH _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & -> & _).
      tauto.
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      destruct (out_rel_exps_of es IH _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & -> & _).
      destruct op. cbn [compile_crepop] in Hc.
      rewrite MAPi_add_comm in Hc.
      set (n := LENGTH les1) in *.
      destruct (decide (target ct = ARMv7)); injection Hc as <- <- <- <-.
      + split.
        { apply comp_syn_ok_nested_seq; split; [exact Ok1|].
          apply comp_syn_ok_nested_seq; split; [apply comp_syntax_ok_MAPi_from|cbn; tauto]. }
        split; [lia|].
        rewrite !cut_sets_nested_seq. unfold crep_to_loop.MAPi. rewrite cut_sets_MAPi_from.
        cbn [nested_seq cut_sets]. rewrite N.add_0_l.
        replace (tmp1 + n + 1 - tmp1) with (SUC n) by lia.
        rewrite (proj2 (GENLIST_thm _ n)), list_insert_SNOC.
        rewrite insert_swap by lia. reflexivity.
      + split.
        { apply comp_syn_ok_nested_seq; split; [exact Ok1|].
          apply comp_syn_ok_nested_seq; split; [apply comp_syntax_ok_MAPi_from|cbn; tauto]. }
        split; [lia|].
        rewrite !cut_sets_nested_seq. unfold crep_to_loop.MAPi. rewrite cut_sets_MAPi_from.
        cbn [nested_seq cut_sets]. rewrite N.add_0_l, insert_shadow.
        replace (tmp1 + n - tmp1) with n by lia. reflexivity.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (IH1 _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & ->).
      destruct (IH2 _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & ->).
      unfold prog_if. rewrite app_assoc.
      split.
      { apply comp_syn_ok_nested_seq; split;
          [apply comp_syn_ok_nested_seq; split; assumption|].
        cbn. split; [exact Logic.I|]. split; [exact Logic.I|]. split; [|exact Logic.I].
        split; [exact Logic.I|]. split; [exact Logic.I|]. exists []. rewrite cut_sets_nested_seq. reflexivity. }
      split; [lia|].
      rewrite cut_sets_nested_seq. reflexivity.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (IH1 _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & ->).
      destruct (IH2 _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & ->).
      split; [apply comp_syn_ok_nested_seq; split; assumption|].
      split; [lia|]. rewrite cut_sets_nested_seq. reflexivity. }
  split; [intros ct tmp l e; exact (G e ct tmp l)|].
  intros ct tmp l es. apply out_rel_exps_of. apply Forall_forall. intros e _; apply G.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_out_rel" *)
Theorem compile_exp_out_rel : forall ct tmp l (e : crepLang.exp a) p le ntmp nl,
  compile_exp ct tmp l e = (p, (le, (ntmp, nl))) ->
  comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p).
Proof. exact (proj1 compile_exp_out_rel_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exps_out_rel" *)
Theorem compile_exps_out_rel : forall ct tmp l (e : list (crepLang.exp a)) p le ntmp nl,
  compile_exps ct tmp l e = (p, (le, (ntmp, nl))) ->
  comp_syntax_ok l (nested_seq p) /\ tmp <= ntmp /\ nl = cut_sets l (nested_seq p) /\
  LENGTH le = LENGTH e.
Proof. exact (proj2 compile_exp_out_rel_cases). Qed.

End OutRel.

Section TmpBound.
Context {a : N}.

Definition tmp_bound_exp (e : crepLang.exp a) : Prop :=
  forall ct tmp l p le ntmp nl n,
    compile_exp ct tmp l e = (p, (le, (ntmp, nl))) -> In n (assigned_vars (nested_seq p)) ->
    tmp <= n /\ n < ntmp.

Definition tmp_bound_exps (e : list (crepLang.exp a)) : Prop :=
  forall ct tmp l p le ntmp nl n,
    compile_exps ct tmp l e = (p, (le, (ntmp, nl))) -> In n (assigned_vars (nested_seq p)) ->
    tmp <= n /\ n < ntmp.

Lemma tmp_bound_exps_of : forall es, Forall tmp_bound_exp es -> tmp_bound_exps es.
Proof.
  intros es HF; induction HF as [|e es He Hes IH]; intros ct tmp l p le ntmp nl n Hc Hn.
  - injection Hc as <- <- <- <-. contradiction.
  - cbn [compile_exps] in Hc.
    destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps ct tmp1 l1 es) as [p2 [les2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C2) as (_ & Le2 & _).
    rewrite assigned_vars_nested_seq_split, in_app_iff in Hn.
    destruct Hn as [Hn|Hn]; [apply (He _ _ _ _ _ _ _ _ C1) in Hn|apply (IH _ _ _ _ _ _ _ _ C2) in Hn];
      lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_assigned_vars_tmp_bound_cases" *)
Theorem comp_exp_assigned_vars_tmp_bound_cases :
  (forall ct tmp l (e : crepLang.exp a) p le ntmp nl n,
    compile_exp ct tmp l e = (p, (le, (ntmp, nl))) /\ MEM n (assigned_vars (nested_seq p)) ->
    tmp <= n /\ n < ntmp) /\
  (forall ct tmp l (e : list (crepLang.exp a)) p le ntmp nl n,
    compile_exps ct tmp l e = (p, (le, (ntmp, nl))) /\ MEM n (assigned_vars (nested_seq p)) ->
    tmp <= n /\ n < ntmp).
Proof.
  assert (G : forall e, tmp_bound_exp e).
  { intros e; induction e as [w|v|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2
                             |sh e1 e2 IH1 IH2| |] using crepProps.cexp_nested_ind;
      intros ct tmp l p le ntmp nl n Hc Hn; cbn [compile_exp] in Hc;
      try rewrite compile_exps_nested in Hc.
    all: try solve [injection Hc; intros; subst; contradiction].
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. exact (IH _ _ _ _ _ _ _ _ C1 Hn).
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
      rewrite assigned_vars_nested_seq_split, in_app_iff in Hn.
      destruct Hn as [Hn|Hn]; [apply (IH _ _ _ _ _ _ _ _ C1) in Hn; lia|].
      cbn in Hn. intuition lia.
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
      rewrite assigned_vars_nested_seq_split, in_app_iff in Hn.
      destruct Hn as [Hn|Hn]; [apply (IH _ _ _ _ _ _ _ _ C1) in Hn; lia|].
      cbn in Hn. intuition lia.
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      exact (tmp_bound_exps_of es IH _ _ _ _ _ _ _ _ C1 Hn).
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
      destruct op. cbn [compile_crepop] in Hc.
      rewrite MAPi_add_comm in Hc.
      destruct (decide (target ct = ARMv7)); injection Hc as <- <- <- <-;
        rewrite !assigned_vars_nested_seq_split, !in_app_iff in Hn;
        unfold crep_to_loop.MAPi in Hn; rewrite assigned_vars_MAPi_from, In_GENLIST_iff in Hn;
        (destruct Hn as [Hn|[[i [Hi ->]]|Hn]];
         [apply (tmp_bound_exps_of es IH _ _ _ _ _ _ _ _ C1) in Hn; lia|lia|cbn in Hn; intuition lia]).
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (_ & Le2 & _).
      unfold prog_if in Hn.
      rewrite !assigned_vars_nested_seq_split, !in_app_iff in Hn.
      destruct Hn as [Hn|[Hn|Hn]];
        [apply (IH1 _ _ _ _ _ _ _ _ C1) in Hn; lia|apply (IH2 _ _ _ _ _ _ _ _ C2) in Hn; lia|].
      cbn in Hn. intuition lia.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (_ & Le2 & _).
      rewrite !assigned_vars_nested_seq_split, !in_app_iff in Hn.
      destruct Hn as [Hn|Hn];
        [apply (IH1 _ _ _ _ _ _ _ _ C1) in Hn; lia|apply (IH2 _ _ _ _ _ _ _ _ C2) in Hn; lia]. }
  split.
  - intros ct tmp l e p le ntmp nl n [Hc Hn]. apply MEM_In in Hn. exact (G e _ _ _ _ _ _ _ _ Hc Hn).
  - intros ct tmp l es p le ntmp nl n [Hc Hn]. apply MEM_In in Hn.
    refine (tmp_bound_exps_of es _ _ _ _ _ _ _ _ _ Hc Hn).
    apply Forall_forall. intros e _; apply G.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_assigned_vars_tmp_bound" *)
Theorem comp_exp_assigned_vars_tmp_bound : forall ct tmp l (e : crepLang.exp a) p le ntmp nl n,
  compile_exp ct tmp l e = (p, (le, (ntmp, nl))) /\ MEM n (assigned_vars (nested_seq p)) ->
  tmp <= n /\ n < ntmp.
Proof. exact (proj1 comp_exp_assigned_vars_tmp_bound_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exps_assigned_vars_tmp_bound" *)
Theorem comp_exps_assigned_vars_tmp_bound : forall ct tmp l (e : list (crepLang.exp a)) p le ntmp nl n,
  compile_exps ct tmp l e = (p, (le, (ntmp, nl))) /\ MEM n (assigned_vars (nested_seq p)) ->
  tmp <= n /\ n < ntmp.
Proof. exact (proj2 comp_exp_assigned_vars_tmp_bound_cases). Qed.

End TmpBound.

Section LeTmp.
Context {a : N}.

Definition le_tmp_exp (e : crepLang.exp a) : Prop :=
  forall ct tmp l p le tmp' l' n,
    ctxt_max (vmax ct) (vars ct) ->
    compile_exp ct tmp l e = (p, (le, (tmp', l'))) -> vmax ct < tmp ->
    (forall n, In n (var_cexp e) -> exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) ->
    In n (locals_touched le) -> n < tmp' /\ n IN domain l'.

Definition le_tmp_exps (es : list (crepLang.exp a)) : Prop :=
  forall ct tmp l p les tmp' l' n,
    ctxt_max (vmax ct) (vars ct) ->
    compile_exps ct tmp l es = (p, (les, (tmp', l'))) -> vmax ct < tmp ->
    (forall n, In n (FLAT (MAP var_cexp es)) ->
       exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) ->
    In n (FLAT (MAP locals_touched les)) -> n < tmp' /\ n IN domain l'.

Lemma var_hyp_mono (ct : context) (l l1 : num_set) (vs : list N) :
  (forall k, k IN domain l -> k IN domain l1) ->
  (forall n, In n vs -> exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) ->
  (forall n, In n vs -> exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l1).
Proof.
  intros Hs H n Hn. destruct (H n Hn) as (m & Hm & Hd). exists m; split; [exact Hm|apply Hs; exact Hd].
Qed.

Lemma le_tmp_exps_of : forall es, Forall le_tmp_exp es -> le_tmp_exps es.
Proof.
  intros es HF; induction HF as [|e es He Hes IH]; intros ct tmp l p les tmp' l' n Hm Hc Hv Hvar Hn.
  - injection Hc as <- <- <- <-. contradiction.
  - cbn [compile_exps] in Hc.
    destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps ct tmp1 l1 es) as [p2 [les2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
    destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & El2 & _).
    cbn [MAP FLAT] in Hvar, Hn. rewrite in_app_iff in Hn.
    destruct Hn as [Hn|Hn].
    + destruct (He _ _ _ _ _ _ _ _ Hm C1 Hv
                  (fun n Hn => Hvar n (proj2 (in_app_iff _ _ _) (or_introl Hn))) Hn) as [Hlt Hd].
      split; [lia|]. rewrite El2. apply comp_syn_cut_sets_mem_domain; split; assumption.
    + apply (IH _ _ _ _ _ _ _ _ Hm C2); [lia| |exact Hn].
      apply (var_hyp_mono ct l); [|intros k Hk; apply Hvar; apply in_app_iff; right; exact Hk].
      intros k Hk. rewrite El1. apply comp_syn_cut_sets_mem_domain; split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_le_tmp_domain_cases" *)
Theorem compile_exp_le_tmp_domain_cases :
  (forall ct tmp l (e : crepLang.exp a) p le tmp' l' n,
    ctxt_max (vmax ct) (vars ct) /\
    compile_exp ct tmp l e = (p, (le, (tmp', l'))) /\ vmax ct < tmp /\
    (forall n, MEM n (var_cexp e) -> exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) /\
    MEM n (locals_touched le) -> n < tmp' /\ n IN domain l') /\
  (forall ct tmp l (es : list (crepLang.exp a)) p les tmp' l' n,
    ctxt_max (vmax ct) (vars ct) /\
    compile_exps ct tmp l es = (p, (les, (tmp', l'))) /\ vmax ct < tmp /\
    (forall n, MEM n (FLAT (MAP var_cexp es)) ->
       exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) /\
    MEM n (FLAT (MAP locals_touched les)) -> n < tmp' /\ n IN domain l').
Proof.
  assert (G : forall e, le_tmp_exp e).
  { intros e; induction e as [w|v|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2
                             |sh e1 e2 IH1 IH2| |] using crepProps.cexp_nested_ind;
      intros ct tmp l p le tmp' l' n Hm Hc Hv Hvar Hn; cbn [compile_exp] in Hc;
      try rewrite compile_exps_nested in Hc.
    all: try solve [injection Hc; intros; subst; contradiction].
    - injection Hc as <- <- <- <-. cbn [locals_touched In var_cexp] in Hn, Hvar.
      destruct Hn as [<-|[]]. destruct (Hvar v (or_introl eq_refl)) as (m & Hfm & Hd).
      unfold find_var. rewrite Hfm. split; [specialize (Hm _ _ Hfm); lia|exact Hd].
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. exact (IH _ _ _ _ _ _ _ _ Hm C1 Hv Hvar Hn).
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. cbn in Hn. destruct Hn as [<-|[]].
      split; [lia|]. unfold pred_set.IN; rewrite domain_insert; left; reflexivity.
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. cbn in Hn. destruct Hn as [<-|[]].
      split; [lia|]. unfold pred_set.IN; rewrite domain_insert; left; reflexivity.
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-.
      exact (le_tmp_exps_of es IH _ _ _ _ _ _ _ _ Hm C1 Hv Hvar Hn).
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      destruct op. cbn [compile_crepop] in Hc.
      destruct (decide (target ct = ARMv7)); injection Hc as <- <- <- <-;
        cbn in Hn; destruct Hn as [<-|[]]; (split; [lia|]);
        unfold pred_set.IN; rewrite domain_insert; left; reflexivity.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-. cbn in Hn. destruct Hn as [<-|[]].
      split; [lia|]. unfold pred_set.IN; cbn [list_insert]; rewrite !domain_insert; right; left; reflexivity.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & El2).
      cbn [locals_touched var_cexp] in Hn, Hvar. rewrite in_app_iff in Hn.
      destruct Hn as [Hn|Hn].
      + destruct (IH1 _ _ _ _ _ _ _ _ Hm C1 Hv
                    (fun n Hn => Hvar n (proj2 (in_app_iff _ _ _) (or_introl Hn))) Hn) as [Hlt Hd].
        split; [lia|]. rewrite El2. apply comp_syn_cut_sets_mem_domain; split; assumption.
      + apply (IH2 _ _ _ _ _ _ _ _ Hm C2); [lia| |exact Hn].
        apply (var_hyp_mono ct l); [|intros k Hk; apply Hvar; apply in_app_iff; right; exact Hk].
        intros k Hk. rewrite El1. apply comp_syn_cut_sets_mem_domain; split; assumption. }
  split.
  - intros ct tmp l e p le tmp' l' n (Hm & Hc & Hv & Hvar & Hn). apply MEM_In in Hn.
    apply (G e _ _ _ _ _ _ _ _ Hm Hc Hv); [|exact Hn].
    intros k Hk; apply Hvar, MEM_In, Hk.
  - intros ct tmp l es p les tmp' l' n (Hm & Hc & Hv & Hvar & Hn). apply MEM_In in Hn.
    refine (le_tmp_exps_of es _ _ _ _ _ _ _ _ _ Hm Hc Hv _ Hn).
    + apply Forall_forall. intros e _; apply G.
    + intros k Hk; apply Hvar, MEM_In, Hk.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_le_tmp_domain" *)
Theorem compile_exp_le_tmp_domain : forall ct tmp l (e : crepLang.exp a) p le tmp' l' n,
  ctxt_max (vmax ct) (vars ct) /\
  compile_exp ct tmp l e = (p, (le, (tmp', l'))) /\ vmax ct < tmp /\
  (forall n, MEM n (var_cexp e) -> exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) /\
  MEM n (locals_touched le) -> n < tmp' /\ n IN domain l'.
Proof. exact (proj1 compile_exp_le_tmp_domain_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exps_le_tmp_domain" *)
Theorem compile_exps_le_tmp_domain : forall ct tmp l (es : list (crepLang.exp a)) p les tmp' l' n,
  ctxt_max (vmax ct) (vars ct) /\
  compile_exps ct tmp l es = (p, (les, (tmp', l'))) /\ vmax ct < tmp /\
  (forall n, MEM n (FLAT (MAP var_cexp es)) ->
     exists m, FLOOKUP (vars ct) n = SOME m /\ m IN domain l) /\
  MEM n (FLAT (MAP locals_touched les)) -> n < tmp' /\ n IN domain l'.
Proof. exact (proj2 compile_exp_le_tmp_domain_cases). Qed.

End LeTmp.

(** ** Expression compilation preserves evaluation *)

Section PreservesEval.
Context {a : N} {ffi_t : Type}.
Implicit Types (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t).

(** The relations of [comp_exp_preserves_eval]'s hypotheses. *)
Definition rels s t ctxt (l : num_set) : Prop :=
  state_rel s t /\ mem_rel (crepSem.memory s) (memory t) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals t) /\ code_rel ctxt (crepSem.code s) (code t) /\
  locals_rel ctxt l (crepSem.locals s) (locals t).

Lemma rels_set_locals s t ctxt l l' L :
  rels s t ctxt l -> locals_rel ctxt l' (crepSem.locals s) L -> rels s (set_locals L t) ctxt l'.
Proof.
  intros (H1 & H2 & H3 & H4 & _) H5.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|exact H5].
Qed.

Lemma rels_upd s t t' ctxt l l' :
  rels s t ctxt l -> clock t' = clock t -> t' = set_clock (clock t') (set_locals (locals t') t) ->
  locals_rel ctxt l' (crepSem.locals s) (locals t') -> rels s t' ctxt l'.
Proof.
  intros Hr Hc -> Hl. rewrite Hc. replace (set_clock (clock t) (set_locals (locals t') t))
    with (set_locals (locals t') t) by (destruct t; reflexivity).
  exact (rels_set_locals s t ctxt l l' _ Hr Hl).
Qed.

Lemma rels_clock s t ctxt l : rels s t ctxt l -> crepSem.clock s = clock t.
Proof. intros (H & _); apply H. Qed.

Lemma set_clock_add0 t : set_clock (clock t + 0) t = t.
Proof. rewrite N.add_0_r. destruct t; reflexivity. Qed.

Lemma ev_nested_app (p q : list (loopLang.prog a)) t st :
  evaluate (nested_seq p, t) = (NONE, st) ->
  evaluate (nested_seq (p ++ q), t) = evaluate (nested_seq q, st).
Proof. apply (proj1 (proj2 evaluate_nested_seq_cases)). Qed.

Lemma ev_Seq (p q : loopLang.prog a) t :
  evaluate (Seq p q, t) =
  let '(res, s1) := evaluate (p, t) in match res with NONE => evaluate (q, s1) | _ => (res, s1) end.
Proof. unfold_eval. reflexivity. Qed.

Lemma ev_Skip t : evaluate (@Skip a, t) = (NONE, t).
Proof. unfold_eval. reflexivity. Qed.

Lemma ev_Assign n e t w : eval t e = SOME w -> evaluate (@Assign a n e, t) = (NONE, set_var n w t).
Proof. intros H. unfold_eval. rewrite H. reflexivity. Qed.

Lemma locals_rel_insert_tmp ctxt l (sl : fmap N (panSem.word_lab a)) tl n w :
  locals_rel ctxt l sl tl -> vmax ctxt < n -> locals_rel ctxt (insert n tt l) sl (insert n w tl).
Proof.
  intros (Hd & Hm & Hs & Hl) Hn. split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk; unfold pred_set.IN in *; rewrite domain_insert in Hk; rewrite domain_insert.
    destruct Hk as [->|Hk]; [left; reflexivity|right; exact (Hs k Hk)].
  - intros v x Hx. destruct (Hl v x Hx) as (m & Hv & Hmd & Hlk).
    exists m; split; [exact Hv|]; split.
    + unfold pred_set.IN in *; rewrite domain_insert; right; exact Hmd.
    + rewrite lookup_insert. destruct (decide (m = n)) as [->|]; [|exact Hlk].
      specialize (Hm _ _ Hv). lia.
Qed.

Lemma var_hyp_of_eval s t ctxt l (e : crepLang.exp a) v :
  rels s t ctxt l -> crepSem.eval s e = SOME v ->
  forall n, In n (var_cexp e) -> exists m, FLOOKUP (vars ctxt) n = SOME m /\ m IN domain l.
Proof.
  intros (_ & _ & _ & _ & (_ & _ & _ & Hl)) He n Hn.
  destruct (crepProps.eval_some_var_cexp_local_lookup s e v n (conj He (proj2 (MEM_In _ _) Hn)))
    as [w Hw].
  destruct (Hl n w Hw) as (m & Hm & Hd & _). exists m; split; assumption.
Qed.

Lemma var_hyp_of_evals s t ctxt l (es : list (crepLang.exp a)) vs :
  rels s t ctxt l -> OPT_MMAP (crepSem.eval s) es = SOME vs ->
  forall n, In n (FLAT (MAP var_cexp es)) -> exists m, FLOOKUP (vars ctxt) n = SOME m /\ m IN domain l.
Proof.
  intros Hr; revert vs; induction es as [|e es IH]; intros vs H n Hn; [contradiction|].
  cbn [OPT_MMAP OPTION_BIND] in H.
  destruct (crepSem.eval s e) as [v|] eqn:E; [|discriminate]. cbn [OPTION_BIND] in H.
  destruct (OPT_MMAP (crepSem.eval s) es) as [vs'|] eqn:E2; [|discriminate].
  cbn [MAP FLAT] in Hn. apply in_app_iff in Hn as [Hn|Hn].
  - exact (var_hyp_of_eval s t ctxt l e v Hr E n Hn).
  - exact (IH vs' eq_refl n Hn).
Qed.

(** Evaluation of the result of a compiled expression survives the code of
    later compiled expressions. *)
Lemma keep_eval ctxt tmp l (e : crepLang.exp a) p1 le1 tmp1 l1 (q : list (loopLang.prog a))
    s t ck st1 ck' r v w :
  compile_exp ctxt tmp l e = (p1, (le1, (tmp1, l1))) ->
  comp_syntax_ok l1 (nested_seq q) ->
  (forall n, In n (assigned_vars (nested_seq q)) -> tmp1 <= n) ->
  crepSem.eval s e = SOME v -> rels s t ctxt l -> vmax ctxt < tmp ->
  evaluate (nested_seq p1, set_clock (clock t + ck) t) = (NONE, st1) ->
  evaluate (nested_seq q, set_clock (clock st1 + ck') st1) = (NONE, r) ->
  eval st1 le1 = SOME w -> eval r le1 = SOME w.
Proof.
  intros Hc Okq Hq He Hr Hv E1 E2 Hw.
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ Hc) as (Ok1 & Le1 & El1).
  rewrite N.add_comm in E1, E2.
  assert (Hmax : ctxt_max (vmax ctxt) (vars ctxt)) by apply Hr.
  assert (Hvar : forall k, MEM k (var_cexp e) ->
                   exists m, FLOOKUP (vars ctxt) k = SOME m /\ m IN domain l).
  { intros k Hk. apply (var_hyp_of_eval s t ctxt l e v Hr He). apply MEM_In, Hk. }
  apply (nested_seq_pure_evaluation p1 q t r st1 l tmp1 le1 w ck ck').
  refine (conj E1 (conj E2 (conj Ok1 (conj _ (conj _ (conj _ (conj _ Hw))))))).
  - rewrite <- El1; exact Okq.
  - intros k Hk. exact (proj2 (comp_exp_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ k (conj Hc Hk))).
  - intros k Hk. apply Hq, MEM_In, Hk.
  - intros k Hk. rewrite <- El1.
    exact (compile_exp_le_tmp_domain ctxt tmp l e p1 le1 tmp1 l1 k
             (conj Hmax (conj Hc (conj Hv (conj Hvar Hk))))).
Qed.

Lemma ev_combine (p1 p2 : list (loopLang.prog a)) t ck1 st1 ck2 r :
  evaluate (nested_seq p1, set_clock (clock t + ck1) t) = (NONE, st1) ->
  evaluate (nested_seq p2, set_clock (clock st1 + ck2) st1) = (NONE, r) ->
  evaluate (nested_seq (p1 ++ p2), set_clock (clock t + (ck1 + ck2)) t) = (NONE, r).
Proof.
  intros E1 E2.
  assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
  pose proof (evaluate_add_clock_eq _ _ _ _ ck2 (conj E1 Hnt)) as E1'.
  rewrite set_clock_set_clock in E1'. cbn [clock set_clock] in E1'.
  rewrite N.add_assoc. rewrite (ev_nested_app _ _ _ _ E1'). exact E2.
Qed.

Lemma mem_load_32_rel sm tm dm (be0 : bool) (w : word a) x :
  mem_rel sm tm dm -> panSem.mem_load_32 sm dm be0 w = SOME x -> mem_load_32 tm dm be0 w = SOME x.
Proof.
  unfold panSem.mem_load_32, mem_load_32. intros Hm H.
  destruct (aligned 2 w); [|discriminate].
  destruct (sm (byte_align w)) as [v] eqn:E.
  destruct (classical_dec (byte_align w IN dm)) as [Hin|]; [|discriminate].
  rewrite <- (Hm _ Hin), E. exact H.
Qed.

Lemma mem_load_byte_rel sm tm dm (be0 : bool) (w : word a) x :
  mem_rel sm tm dm -> panSem.mem_load_byte sm dm be0 w = SOME x ->
  mem_load_byte_aux tm dm be0 w = SOME x.
Proof.
  unfold panSem.mem_load_byte, mem_load_byte_aux. intros Hm H.
  destruct (sm (byte_align w)) as [v] eqn:E.
  destruct (classical_dec (byte_align w IN dm)) as [Hin|]; [|discriminate].
  rewrite <- (Hm _ Hin), E. exact H.
Qed.

Lemma ev_Load32_tail t n le (w : word a) x :
  eval t le = SOME (Word w) -> mem_load_32 (memory t) (mdomain t) (be t) w = SOME x ->
  evaluate (nested_seq [Assign n le; Load32 n n], t) =
  (NONE, set_var n (Word (w2w x)) (set_var n (Word w) t)).
Proof.
  intros He Hm. cbn [nested_seq]. rewrite ev_Seq, (ev_Assign _ _ _ _ He). cbv beta iota.
  rewrite ev_Seq. unfold_eval. cbn [set_var set_locals locals memory mdomain be].
  rewrite lookup_insert. destruct (decide (n = n)) as [_|]; [|congruence].
  cbn beta iota. rewrite Hm. cbv beta iota. rewrite ev_Skip. reflexivity.
Qed.

Lemma ev_LoadByte_tail t n le (w : word a) x :
  eval t le = SOME (Word w) -> mem_load_byte_aux (memory t) (mdomain t) (be t) w = SOME x ->
  evaluate (nested_seq [Assign n le; LoadByte n n], t) =
  (NONE, set_var n (Word (w2w x)) (set_var n (Word w) t)).
Proof.
  intros He Hm. cbn [nested_seq]. rewrite ev_Seq, (ev_Assign _ _ _ _ He). cbv beta iota.
  rewrite ev_Seq. unfold_eval. cbn [set_var set_locals locals memory mdomain be].
  rewrite lookup_insert. destruct (decide (n = n)) as [_|]; [|congruence].
  cbn beta iota. rewrite Hm. cbv beta iota. rewrite ev_Skip. reflexivity.
Qed.

Lemma rels_set_var2 s t ctxt l n (x y : word_loc a) :
  rels s t ctxt l -> vmax ctxt < n ->
  rels s (set_var n y (set_var n x t)) ctxt (insert n tt l).
Proof.
  intros Hr Hn. change (set_var n y (set_var n x t)) with (set_locals (insert n y (insert n x (locals t))) t).
  rewrite insert_shadow. apply (rels_set_locals s t ctxt l); [exact Hr|].
  apply locals_rel_insert_tmp; [apply Hr|exact Hn].
Qed.

Lemma ev_cmp_tail t c n m le1 le2 (w1 w2 : word a) (cs : num_set) :
  eval t le1 = SOME (Word w1) -> eval (set_var n (Word w1) t) le2 = SOME (Word w2) -> n <> m ->
  (forall k, domain cs k -> domain (locals t) k) -> clock t <> 0 ->
  exists st, evaluate (nested_seq [Assign n le1; Assign m le2;
                 If c n (Reg m) (Assign n (Const (n2w 1))) (Assign n (Const (n2w 0)))
                    (list_insert [n; m] cs)], t) = (NONE, st) /\
    clock st = clock t - 1 /\ st = set_clock (clock st) (set_locals (locals st) t) /\
    locals st = inter (insert n (Word (v2w [word_cmp c w1 w2]))
                         (insert m (Word w2) (insert n (Word w1) (locals t))))
                      (list_insert [n; m] cs).
Proof.
  intros H1 H2 Hnm Hcs Hck.
  cbn [nested_seq]. rewrite ev_Seq, (ev_Assign _ _ _ _ H1). cbv beta iota.
  rewrite ev_Seq, (ev_Assign _ _ _ _ H2). cbv beta iota.
  rewrite ev_Seq. unfold_eval. cbn [set_var set_locals locals get_var_imm].
  rewrite (lookup_insert m), (lookup_insert n).
  destruct (decide (n = m)) as [|_]; [contradiction|].
  destruct (decide (n = n)) as [_|]; [|congruence].
  rewrite (lookup_insert m). destruct (decide (m = m)) as [_|]; [|congruence].
  cbn zeta. rewrite v2w_sing.
  destruct (word_cmp c w1 w2);
    (rewrite (ev_Assign _ _ _ (Word _)) by reflexivity; cbn [cut_res IS_SOME]; unfold cut_state;
     destruct (classical_dec _) as [_|Hn];
     [|exfalso; apply Hn; intros k Hk; unfold pred_set.IN in *; cbn [set_var set_locals locals];
       cbn [list_insert] in Hk; rewrite !domain_insert in Hk; rewrite !domain_insert;
       destruct Hk as [->|[->|Hk]]; [right; left; reflexivity|left; reflexivity|];
       right; right; right; apply Hcs; exact Hk];
     cbn [set_var set_locals clock]; destruct (N.eqb_spec (clock t) 0) as [|_]; [contradiction|];
     cbv beta iota; rewrite ev_Skip;
     eexists; split; [reflexivity|]; split; [reflexivity|]; split; reflexivity).
Qed.

Lemma ev_mul_tail t le1 le2 (w1 w2 : word a) x r1 r2 :
  eval t le1 = SOME (Word w1) -> eval (set_var x (Word w1) t) le2 = SOME (Word w2) ->
  x <> x + 1 ->
  evaluate (nested_seq (crep_to_loop.MAPi (fun n => Assign (x + n)) [le1; le2] ++
                        [Arith (LLongMul r1 r2 x (x + 1))]), t) =
  (NONE, set_var r2 (Word (n2w (w2n w1 * w2n w2)))
           (set_var r1 (Word (n2w (w2n w1 * w2n w2 DIV dimword a)))
              (set_var (x + 1) (Word w2) (set_var x (Word w1) t)))).
Proof.
  intros H1 H2 Hx. cbn [crep_to_loop.MAPi crep_to_loop.MAPi_from app nested_seq].
  rewrite N.add_0_r, N.add_0_l.
  rewrite ev_Seq, (ev_Assign _ _ _ _ H1). cbv beta iota.
  rewrite ev_Seq, (ev_Assign _ _ _ _ H2). cbv beta iota.
  rewrite ev_Seq. unfold_eval. cbn [loop_arith set_var set_locals locals].
  rewrite (lookup_insert (x + 1) _ _ x), (lookup_insert x _ _ x).
  destruct (decide (x = x + 1)) as [|_]; [lia|]. destruct (decide (x = x)) as [_|]; [|congruence].
  rewrite (lookup_insert (x + 1) _ _ (x + 1)). destruct (decide (x + 1 = x + 1)) as [_|]; [|congruence].
  cbv beta iota zeta. rewrite ev_Skip. reflexivity.
Qed.

Lemma locals_rel_mono ctxt (l1 X : num_set) (sl : fmap N (panSem.word_lab a)) L L' :
  locals_rel ctxt l1 sl L ->
  (forall k, domain X k -> domain L' k) ->
  (forall k, k <= vmax ctxt -> lookup k L' = lookup k L) ->
  (forall k, domain l1 k -> domain X k) ->
  locals_rel ctxt X sl L'.
Proof.
  intros (Hd & Hm & Hs & Hl) HX HL Hl1. split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk. exact (HX k Hk).
  - intros vn x Hx. destruct (Hl vn x Hx) as (k & Hk & Hkd & Hlk).
    exists k. split; [exact Hk|]. split; [exact (Hl1 k Hkd)|].
    rewrite HL; [exact Hlk|exact (Hm _ _ Hk)].
Qed.

Definition pe_exp (e : crepLang.exp a) : Prop :=
  forall s v t ctxt tmp l p le ntmp nl,
    crepSem.eval s e = SOME v -> rels s t ctxt l ->
    compile_exp ctxt tmp l e = (p, (le, (ntmp, nl))) -> vmax ctxt < tmp ->
    exists ck st, evaluate (nested_seq p, set_clock (clock t + ck) t) = (NONE, st) /\
      eval st le = SOME (wlab_wloc v) /\ rels s st ctxt nl.

Definition pe_exps (es : list (crepLang.exp a)) : Prop :=
  forall s vs t ctxt tmp l p les ntmp nl,
    OPT_MMAP (crepSem.eval s) es = SOME vs -> rels s t ctxt l ->
    compile_exps ctxt tmp l es = (p, (les, (ntmp, nl))) -> vmax ctxt < tmp ->
    exists ck st, evaluate (nested_seq p, set_clock (clock t + ck) t) = (NONE, st) /\
      OPT_MMAP (eval st) les = SOME (MAP wlab_wloc vs) /\ rels s st ctxt nl.

Lemma pe_exps_of : forall es, Forall pe_exp es -> pe_exps es.
Proof.
  intros es HF; induction HF as [|e es He Hes IH];
    intros s vs t ctxt tmp l p les ntmp nl Hev Hr Hc Hv.
  - injection Hev as <-. injection Hc as <- <- <- <-.
    exists 0, t. rewrite set_clock_add0. split; [cbn [nested_seq]; apply ev_Skip|].
    split; [reflexivity|exact Hr].
  - cbn [OPT_MMAP OPTION_BIND] in Hev.
    destruct (crepSem.eval s e) as [v|] eqn:Ee; [|discriminate]. cbn [OPTION_BIND] in Hev.
    destruct (OPT_MMAP (crepSem.eval s) es) as [vs'|] eqn:Ees; [|discriminate].
    injection Hev as <-.
    cbn [compile_exps] in Hc.
    destruct (compile_exp ctxt tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps ctxt tmp1 l1 es) as [p2 [les2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
    destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & El2 & _).
    destruct (He s v t ctxt tmp l p1 le1 tmp1 l1 Ee Hr C1 Hv) as (ck1 & st1 & E1 & Hle1 & Hr1).
    destruct (IH s vs' st1 ctxt tmp1 l1 p2 les2 tmp2 l2 Ees Hr1 C2 ltac:(lia))
      as (ck2 & st2 & E2 & Hles & Hr2).
    exists (ck1 + ck2), st2. split; [exact (ev_combine _ _ _ _ _ _ _ E1 E2)|].
    split; [|exact Hr2].
    cbn [OPT_MMAP OPTION_BIND MAP].
    rewrite (keep_eval ctxt tmp l e p1 le1 tmp1 l1 p2 s t ck1 st1 ck2 st2 v (wlab_wloc v)
               C1 Ok2
               ltac:(intros k Hk; exact (proj1 (comp_exps_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ k
                                                  (conj C2 (proj2 (MEM_In _ _) Hk)))))
               Ee Hr Hv E1 E2 Hle1).
    cbn [OPTION_BIND]. rewrite Hles. reflexivity.
Qed.

Lemma the_words_wlab (ws : list (panSem.word_lab a)) :
  the_words (MAP SOME (MAP wlab_wloc ws)) = SOME (MAP (fun w => match w with panSem.Word n => n end) ws).
Proof. induction ws as [|[w] ws IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma EVERY_word_lab (ws : list (panSem.word_lab a)) :
  EVERY (fun w => match w with panSem.Word _ => true end) ws = true.
Proof. induction ws as [|[w] ws IH]; [reflexivity|exact IH]. Qed.

Lemma pe_all : forall e, pe_exp e.
Proof.
  intros e; induction e as [w|vn|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2
                           |sh e1 e2 IH1 IH2| |] using crepProps.cexp_nested_ind;
    intros s v t ctxt tmp l p le ntmp nl He Hr Hc Hv; cbn [compile_exp] in Hc;
    try rewrite compile_exps_nested in Hc.
  - (* Const *)
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He. injection He as <-.
    exists 0, t. rewrite set_clock_add0. split; [apply ev_Skip|]. split; [reflexivity|exact Hr].
  - (* Var *)
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    exists 0, t. rewrite set_clock_add0. split; [apply ev_Skip|]. split; [|exact Hr].
    destruct Hr as (_ & _ & _ & _ & (_ & _ & _ & Hl)).
    destruct (Hl vn v He) as (n & Hn & _ & Hlk).
    cbn [eval]. unfold find_var. rewrite Hn. exact Hlk.
  - (* Load *)
    destruct (compile_exp ctxt tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    destruct (crepSem.eval s e) as [[w]|] eqn:Ee; [|discriminate].
    destruct (IH s _ t ctxt tmp l p1 le1 tmp1 l1 Ee Hr C1 Hv) as (ck & st & E1 & Hle & Hr1).
    exists ck, st. split; [exact E1|]. split; [|exact Hr1].
    cbn [eval]. rewrite Hle. cbn [wlab_wloc].
    unfold crepSem.mem_load, mem_load in *.
    destruct Hr1 as ((Hd & _) & Hm & _).
    destruct (classical_dec (w IN crepSem.memaddrs s)) as [Hin|]; [|discriminate].
    injection He as <-. rewrite <- Hd.
    destruct (classical_dec (w IN crepSem.memaddrs s)) as [_|]; [|contradiction].
    rewrite (Hm w Hin). reflexivity.
  - (* Load32 *)
    destruct (compile_exp ctxt tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    destruct (crepSem.eval s e) as [[w]|] eqn:Ee; [|discriminate].
    destruct (panSem.mem_load_32 _ _ _ w) as [x|] eqn:Em; [|discriminate]. injection He as <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
    destruct (IH s _ t ctxt tmp l p1 le1 tmp1 l1 Ee Hr C1 Hv) as (ck & st & E1 & Hle & Hr1).
    assert (Hm32 : mem_load_32 (memory st) (mdomain st) (be st) w = SOME x).
    { destruct Hr1 as ((Hd & _ & _ & Hbe & _) & Hm & _). rewrite <- Hd, <- Hbe.
      exact (mem_load_32_rel _ _ _ _ _ _ Hm Em). }
    exists ck, (set_var tmp1 (Word (w2w x)) (set_var tmp1 (Word w) st)).
    split; [rewrite (ev_nested_app _ _ _ _ E1); exact (ev_Load32_tail _ _ _ _ _ Hle Hm32)|].
    split.
    + cbn [eval set_var set_locals locals]. rewrite lookup_insert.
      destruct (decide (tmp1 = tmp1)); [reflexivity|congruence].
    + apply rels_set_var2; [exact Hr1|lia].
  - (* LoadByte *)
    destruct (compile_exp ctxt tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    destruct (crepSem.eval s e) as [[w]|] eqn:Ee; [|discriminate].
    destruct (panSem.mem_load_byte _ _ _ w) as [x|] eqn:Em; [|discriminate]. injection He as <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
    destruct (IH s _ t ctxt tmp l p1 le1 tmp1 l1 Ee Hr C1 Hv) as (ck & st & E1 & Hle & Hr1).
    assert (Hm8 : mem_load_byte_aux (memory st) (mdomain st) (be st) w = SOME x).
    { destruct Hr1 as ((Hd & _ & _ & Hbe & _) & Hm & _). rewrite <- Hd, <- Hbe.
      exact (mem_load_byte_rel _ _ _ _ _ _ Hm Em). }
    exists ck, (set_var tmp1 (Word (w2w x)) (set_var tmp1 (Word w) st)).
    split; [rewrite (ev_nested_app _ _ _ _ E1); exact (ev_LoadByte_tail _ _ _ _ _ Hle Hm8)|].
    split.
    + cbn [eval set_var set_locals locals]. rewrite lookup_insert.
      destruct (decide (tmp1 = tmp1)); [reflexivity|congruence].
    + apply rels_set_var2; [exact Hr1|lia].
  - (* LoadGlob *)
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    exists 0, t. rewrite set_clock_add0. split; [apply ev_Skip|]. split; [|exact Hr].
    destruct Hr as (_ & _ & Hg & _). exact (Hg g v He).
  - (* Op *)
    destruct (compile_exps ctxt tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    destruct (OPT_MMAP (crepSem.eval s) es) as [ws|] eqn:Ees; [|discriminate].
    rewrite EVERY_word_lab in He.
    destruct (pe_exps_of es IH s ws t ctxt tmp l p1 les1 tmp1 l1 Ees Hr C1 Hv)
      as (ck & st & E1 & Hles & Hr1).
    exists ck, st. split; [exact E1|]. split; [|exact Hr1].
    cbn [eval]. apply opt_mmap_eq_some in Hles. rewrite Hles, the_words_wlab.
    destruct (wordLang.word_op op _) as [x|]; [|discriminate]. injection He as <-. reflexivity.
  - (* Crepop *)
    destruct (compile_exps ctxt tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
    cbn [crepSem.eval] in He.
    destruct (OPT_MMAP (crepSem.eval s) es) as [ws|] eqn:Ees; [|discriminate].
    rewrite EVERY_word_lab in He.
    destruct op.
    destruct ws as [|[w1] [|[w2] [|]]]; cbn in He; try discriminate.
    injection He as <-.
    destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1 & Len1).
    pose proof (opt_mmap_length_eq _ _ _ Ees) as Lenes.
    destruct (pe_exps_of es IH s _ t ctxt tmp l p1 les1 tmp1 l1 Ees Hr C1 Hv)
      as (ck & st1 & E1 & Hles & Hr1).
    destruct les1 as [|le1 [|le2 [|]]]; cbn in Len1, Lenes; try lia.
    cbn [OPT_MMAP OPTION_BIND MAP wlab_wloc] in Hles.
    destruct (eval st1 le1) as [x1|] eqn:Hl1; [|discriminate]. cbn [OPTION_BIND] in Hles.
    destruct (eval st1 le2) as [x2|] eqn:Hl2; [|discriminate]. cbn [OPTION_BIND] in Hles.
    injection Hles as -> ->.
    assert (Hmax : ctxt_max (vmax ctxt) (vars ctxt)) by apply Hr.
    assert (Htouch : forall k, In k (locals_touched le2) -> k < tmp1).
    { intros k Hk.
      refine (proj1 (compile_exps_le_tmp_domain ctxt tmp l es p1 [le1; le2] tmp1 l1 k
                (conj Hmax (conj C1 (conj Hv (conj _ _)))))).
      - intros k' Hk'. apply (var_hyp_of_evals s t ctxt l es _ Hr Ees). apply MEM_In, Hk'.
      - apply MEM_In. cbn [MAP FLAT]. apply in_app_iff; right; apply in_app_iff; left; exact Hk. }
    assert (Hl2' : eval (set_var tmp1 (Word w1) st1) le2 = SOME (Word w2)).
    { rewrite <- Hl2. symmetry. apply locals_touched_eq_eval_eq.
      repeat split; try reflexivity. intros k Hk. apply MEM_In, Htouch in Hk.
      cbn [set_var set_locals locals]. rewrite lookup_insert.
      destruct (decide (k = tmp1)); [lia|reflexivity]. }
    cbn [compile_crepop LENGTH] in Hc. change (N.succ (N.succ 0)) with 2 in Hc.
    assert (Hdom1 : forall k, domain l1 k -> domain (locals st1) k).
    { intros k Hk. destruct Hr1 as (_ & _ & _ & _ & (_ & _ & Hs & _)). exact (Hs k Hk). }
    destruct (decide (target ctxt = ARMv7)); injection Hc as <- <- <- <-;
      (eexists ck, _; split;
       [rewrite (ev_nested_app _ _ _ _ E1); apply ev_mul_tail; [exact Hl1|exact Hl2'|lia]|]);
      (split;
       [cbn [eval set_var set_locals locals]; rewrite lookup_insert;
        (destruct (decide _) as [_|]; [|congruence]); reflexivity|]);
      (apply (rels_set_locals s st1 ctxt l1); [exact Hr1|]);
      (apply (locals_rel_mono ctxt l1 _ _ (locals st1)); [apply Hr1| | |]).
    + intros k Hk. rewrite domain_insert in Hk. cbn [set_var set_locals locals]. rewrite !domain_insert.
      destruct Hk as [->|Hk]; [left; reflexivity|].
      rewrite domain_list_insert in Hk. unfold is_true in Hk. rewrite MEM_In, In_GENLIST_iff in Hk.
      destruct Hk as [[i [Hi ->]]|Hk]; [|right; right; right; right; exact (Hdom1 k Hk)].
      replace (tmp1 + 2 + 1 - tmp1) with 3 in Hi by lia.
      assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia; lia.
    + intros k Hk. assert (k < tmp1) by lia. cbn [set_var set_locals locals]. rewrite !lookup_insert.
      repeat (destruct (decide _); [lia|]). reflexivity.
    + intros k Hk. rewrite domain_insert, domain_list_insert. right; right; exact Hk.
    + intros k Hk. rewrite domain_insert in Hk. cbn [set_var set_locals locals]. rewrite !domain_insert.
      destruct Hk as [->|Hk]; [left; reflexivity|].
      rewrite domain_list_insert in Hk. unfold is_true in Hk. rewrite MEM_In, In_GENLIST_iff in Hk.
      destruct Hk as [[i [Hi ->]]|Hk]; [|right; right; right; right; exact (Hdom1 k Hk)].
      replace (tmp1 + 2 - tmp1) with 2 in Hi by lia.
      assert (Hi2 : i = 0 \/ i = 1) by lia; lia.
    + intros k Hk. assert (k < tmp1) by lia. cbn [set_var set_locals locals]. rewrite !lookup_insert.
      repeat (destruct (decide _); [lia|]). reflexivity.
    + intros k Hk. rewrite domain_insert, domain_list_insert. right; right; exact Hk.
  - (* Cmp *)
    destruct (compile_exp ctxt tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    destruct (crepSem.eval s e1) as [[w1]|] eqn:Ee1; [|discriminate].
    destruct (crepSem.eval s e2) as [[w2]|] eqn:Ee2; [|discriminate].
    injection He as <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & El2).
    destruct (IH1 s _ t ctxt tmp l p1 le1 tmp1 l1 Ee1 Hr C1 Hv) as (ck1 & st1 & E1 & Hle1 & Hr1).
    destruct (IH2 s _ st1 ctxt tmp1 l1 p2 le2 tmp2 l2 Ee2 Hr1 C2 ltac:(lia))
      as (ck2 & st2 & E2 & Hle2 & Hr2).
    pose proof (keep_eval ctxt tmp l e1 p1 le1 tmp1 l1 p2 s t ck1 st1 ck2 st2 _ _ C1 Ok2
                  ltac:(intros k Hk; exact (proj1 (comp_exp_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ k
                                                     (conj C2 (proj2 (MEM_In _ _) Hk)))))
                  Ee1 Hr Hv E1 E2 Hle1) as Hle1'.
    cbn [wlab_wloc] in Hle1', Hle2.
    assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
    pose proof (evaluate_add_clock_eq _ _ _ _ 1 (conj E2 Hnt)) as E2'.
    rewrite set_clock_set_clock in E2'. cbn [clock set_clock] in E2'.
    rewrite <- N.add_assoc in E2'.
    pose proof (ev_combine _ _ _ _ _ _ _ E1 E2') as E12.
    assert (Hmax : ctxt_max (vmax ctxt) (vars ctxt)) by apply Hr1.
    assert (Htouch : forall k, In k (locals_touched le2) -> k < tmp2).
    { intros k Hk. assert (Hv1 : vmax ctxt < tmp1) by lia.
      refine (proj1 (compile_exp_le_tmp_domain ctxt tmp1 l1 e2 p2 le2 tmp2 l2 k
                (conj Hmax (conj C2 (conj Hv1 (conj _ (proj2 (MEM_In _ _) Hk))))))).
      intros k' Hk'. apply (var_hyp_of_eval s st1 ctxt l1 e2 _ Hr1 Ee2). apply MEM_In, Hk'. }
    set (st2' := set_clock (clock st2 + 1) st2) in *.
    assert (Hl1 : eval st2' le1 = SOME (Word w1)) by (unfold st2'; rewrite eval_set_clock; exact Hle1').
    assert (Hl2 : eval (set_var (tmp2 + 1) (Word w1) st2') le2 = SOME (Word w2)).
    { rewrite <- Hle2. symmetry. apply locals_touched_eq_eval_eq.
      repeat split; try reflexivity. intros k Hk. apply MEM_In, Htouch in Hk.
      cbn [st2' set_var set_locals set_clock locals]. rewrite lookup_insert.
      destruct (decide (k = tmp2 + 1)); [lia|reflexivity]. }
    assert (Hcs : forall k, domain l2 k -> domain (locals st2') k).
    { intros k Hk. destruct Hr2 as (_ & _ & _ & _ & (_ & _ & Hs & _)). apply Hs. exact Hk. }
    destruct (ev_cmp_tail st2' c (tmp2 + 1) (tmp2 + 2) le1 le2 w1 w2 l2 Hl1 Hl2 ltac:(lia) Hcs
                ltac:(unfold st2'; cbn [clock set_clock]; lia)) as (st & Et & Hck & Hst & Hlo).
    exists (ck1 + (ck2 + 1)), st. split.
    { unfold prog_if. rewrite app_assoc, (ev_nested_app _ _ _ _ E12). exact Et. }
    split.
    + cbn [eval]. rewrite Hlo, lookup_inter_alt.
      destruct (decide _) as [_|Hn].
      * rewrite lookup_insert. destruct (decide _); [reflexivity|congruence].
      * exfalso; apply Hn. cbn [list_insert]. rewrite !domain_insert. right; left; reflexivity.
    + apply (rels_upd s st2 st ctxt l2).
      * exact Hr2.
      * rewrite Hck. unfold st2'. cbn [clock set_clock]. lia.
      * rewrite Hst at 1. unfold st2'. reflexivity.
      * destruct Hr2 as (_ & _ & _ & _ & (Hd & Hm & Hs & Hl)).
        split; [exact Hd|]. split; [exact Hm|]. split.
        -- intros k Hk. unfold pred_set.IN in *. rewrite Hlo, domain_inter. split; [|exact Hk].
           cbn [list_insert] in Hk. rewrite !domain_insert in Hk. rewrite !domain_insert.
           destruct Hk as [->|[->|Hk]]; [right; left; reflexivity|left; reflexivity|].
           right; right; right. exact (Hs k Hk).
        -- intros vn x Hx. destruct (Hl vn x Hx) as (k & Hk & Hkd & Hlk).
           exists k. split; [exact Hk|]. specialize (Hm _ _ Hk).
           split.
           ++ unfold pred_set.IN in *. cbn [list_insert]. rewrite !domain_insert. right; right; exact Hkd.
           ++ rewrite Hlo, lookup_inter_alt. destruct (decide _) as [_|Hn].
              ** rewrite !lookup_insert.
                 repeat (destruct (decide _); [lia|]). exact Hlk.
              ** exfalso; apply Hn. cbn [list_insert]. rewrite !domain_insert. right; right; exact Hkd.
  - (* Shift *)
    destruct (compile_exp ctxt tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He.
    destruct (crepSem.eval s e1) as [[w1]|] eqn:Ee1; [|discriminate].
    destruct (crepSem.eval s e2) as [[w2]|] eqn:Ee2; [|discriminate].
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & El2).
    destruct (IH1 s _ t ctxt tmp l p1 le1 tmp1 l1 Ee1 Hr C1 Hv) as (ck1 & st1 & E1 & Hle1 & Hr1).
    destruct (IH2 s _ st1 ctxt tmp1 l1 p2 le2 tmp2 l2 Ee2 Hr1 C2 ltac:(lia))
      as (ck2 & st2 & E2 & Hle2 & Hr2).
    pose proof (keep_eval ctxt tmp l e1 p1 le1 tmp1 l1 p2 s t ck1 st1 ck2 st2 _ _ C1 Ok2
                  ltac:(intros k Hk; exact (proj1 (comp_exp_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ k
                                                     (conj C2 (proj2 (MEM_In _ _) Hk)))))
                  Ee1 Hr Hv E1 E2 Hle1) as Hle1'.
    exists (ck1 + ck2), st2. split; [exact (ev_combine _ _ _ _ _ _ _ E1 E2)|].
    split; [|exact Hr2].
    cbn [eval]. rewrite Hle1', Hle2. cbn [wlab_wloc].
    destruct (wordLang.word_sh sh w1 (w2n w2)) as [x|]; [|discriminate].
    injection He as <-. reflexivity.
  - (* BaseAddr *)
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He. injection He as <-.
    exists 0, t. rewrite set_clock_add0. split; [apply ev_Skip|]. split; [|exact Hr].
    cbn [eval]. destruct Hr as ((_ & _ & _ & _ & _ & Hb & _) & _). rewrite Hb. reflexivity.
  - (* TopAddr *)
    injection Hc as <- <- <- <-. cbn [crepSem.eval] in He. injection He as <-.
    exists 0, t. rewrite set_clock_add0. split; [apply ev_Skip|]. split; [|exact Hr].
    cbn [eval]. destruct Hr as ((_ & _ & _ & _ & _ & _ & Hb) & _). rewrite Hb. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval" *)
Theorem comp_exp_preserves_eval : forall s (e : crepLang.exp a) v t ctxt tmp l p le ntmp nl,
  crepSem.eval s e = SOME v /\
  state_rel s t /\ mem_rel (crepSem.memory s) (memory t) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals t) /\
  code_rel ctxt (crepSem.code s) (code t) /\
  locals_rel ctxt l (crepSem.locals s) (locals t) /\
  compile_exp ctxt tmp l e = (p, (le, (ntmp, nl))) /\
  vmax ctxt < tmp ->
  exists ck st, evaluate (nested_seq p, set_clock (clock t + ck) t) = (NONE, st) /\
    eval st le = SOME (wlab_wloc v) /\
    state_rel s st /\ mem_rel (crepSem.memory s) (memory st) (crepSem.memaddrs s) /\
    globals_rel (crepSem.globals s) (globals st) /\
    code_rel ctxt (crepSem.code s) (code st) /\
    locals_rel ctxt nl (crepSem.locals s) (locals st).
Proof.
  intros s e v t ctxt tmp l p le ntmp nl (He & H1 & H2 & H3 & H4 & H5 & Hc & Hv).
  destruct (pe_all e s v t ctxt tmp l p le ntmp nl He (conj H1 (conj H2 (conj H3 (conj H4 H5))))
              Hc Hv) as (ck & st & E & Hle & Hr).
  exists ck, st. split; [exact E|]. split; [exact Hle|]. exact Hr.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exps_preserves_eval" *)
Theorem comp_exps_preserves_eval : forall (es : list (crepLang.exp a)) s vs t ctxt tmp l p les ntmp nl,
  OPT_MMAP (crepSem.eval s) es = SOME vs /\
  state_rel s t /\ mem_rel (crepSem.memory s) (memory t) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals t) /\
  code_rel ctxt (crepSem.code s) (code t) /\
  locals_rel ctxt l (crepSem.locals s) (locals t) /\
  compile_exps ctxt tmp l es = (p, (les, (ntmp, nl))) /\
  vmax ctxt < tmp ->
  exists ck st, evaluate (nested_seq p, set_clock (clock t + ck) t) = (NONE, st) /\
    OPT_MMAP (eval st) les = SOME (MAP wlab_wloc vs) /\
    state_rel s st /\ mem_rel (crepSem.memory s) (memory st) (crepSem.memaddrs s) /\
    globals_rel (crepSem.globals s) (globals st) /\
    code_rel ctxt (crepSem.code s) (code st) /\
    locals_rel ctxt nl (crepSem.locals s) (locals st).
Proof.
  intros es s vs t ctxt tmp l p les ntmp nl (He & H1 & H2 & H3 & H4 & H5 & Hc & Hv).
  assert (HF : Forall pe_exp es) by (apply Forall_forall; intros e _; apply pe_all).
  destruct (pe_exps_of es HF s vs t ctxt tmp l p les ntmp nl He
              (conj H1 (conj H2 (conj H3 (conj H4 H5)))) Hc Hv) as (ck & st & E & Hle & Hr).
  exists ck, st. split; [exact E|]. split; [exact Hle|]. exact Hr.
Qed.

End PreservesEval.

(** ** Survival of cut-set members and assigned variables *)

Section Survives.
Context {a : N}.

Definition surv_exp (e : crepLang.exp a) : Prop :=
  forall ct tmp l p le ntmp nl n,
    n IN domain l -> compile_exp ct tmp l e = (p, (le, (ntmp, nl))) -> survives n (nested_seq p).

Definition surv_exps (es : list (crepLang.exp a)) : Prop :=
  forall ct tmp l p les ntmp nl n,
    n IN domain l -> compile_exps ct tmp l es = (p, (les, (ntmp, nl))) -> survives n (nested_seq p).

Lemma surv_exps_of : forall es, Forall surv_exp es -> surv_exps es.
Proof.
  intros es HF; induction HF as [|e es He Hes IH]; intros ct tmp l p les ntmp nl n Hn Hc.
  - injection Hc as <- <- <- <-. exact Logic.I.
  - cbn [compile_exps] in Hc.
    destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps ct tmp1 l1 es) as [p2 [les2 [tmp2 l2]]] eqn:C2.
    injection Hc as <- <- <- <-.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & _ & El1).
    assert (Hn1 : n IN domain l1)
      by (rewrite El1; apply comp_syn_cut_sets_mem_domain; split; assumption).
    apply survives_nested_seq_intro. split; [exact (He _ _ _ _ _ _ _ _ Hn C1)|].
    exact (IH _ _ _ _ _ _ _ _ Hn1 C2).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exp_cases" *)
Theorem member_cutset_survives_comp_exp_cases :
  (forall ct tmp l (e : crepLang.exp a) p le ntmp nl n,
    n IN domain l /\ compile_exp ct tmp l e = (p, (le, (ntmp, nl))) ->
    survives n (nested_seq p)) /\
  (forall ct tmp l (e : list (crepLang.exp a)) p le ntmp nl n,
    n IN domain l /\ compile_exps ct tmp l e = (p, (le, (ntmp, nl))) ->
    survives n (nested_seq p)).
Proof.
  assert (G : forall e, surv_exp e).
  { intros e; induction e as [w|v|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2
                             |sh e1 e2 IH1 IH2| |] using crepProps.cexp_nested_ind;
      intros ct tmp l p le ntmp nl n Hn Hc; cbn [compile_exp] in Hc;
      try rewrite compile_exps_nested in Hc.
    all: try solve [injection Hc; intros; subst; exact Logic.I].
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. exact (IH _ _ _ _ _ _ _ _ Hn C1).
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. apply survives_nested_seq_intro.
      split; [exact (IH _ _ _ _ _ _ _ _ Hn C1)|cbn; tauto].
    - destruct (compile_exp ct tmp l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. apply survives_nested_seq_intro.
      split; [exact (IH _ _ _ _ _ _ _ _ Hn C1)|cbn; tauto].
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      injection Hc as <- <- <- <-. exact (surv_exps_of es IH _ _ _ _ _ _ _ _ Hn C1).
    - destruct (compile_exps ct tmp l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
      destruct op. cbn [compile_crepop] in Hc.
      destruct (decide (target ct = ARMv7)); injection Hc as <- <- <- <-;
        (apply survives_nested_seq_intro; split; [exact (surv_exps_of es IH _ _ _ _ _ _ _ _ Hn C1)|]);
        (apply survives_nested_seq_intro; split; [|cbn; tauto]);
        unfold crep_to_loop.MAPi; rewrite MAPi_from_add_comm; apply survives_MAPi_from.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & _ & El1).
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & _ & El2).
      assert (Hn1 : n IN domain l1)
        by (rewrite El1; apply comp_syn_cut_sets_mem_domain; split; assumption).
      assert (Hn2 : n IN domain l2)
        by (rewrite El2; apply comp_syn_cut_sets_mem_domain; split; assumption).
      unfold prog_if. apply survives_nested_seq_intro; split; [exact (IH1 _ _ _ _ _ _ _ _ Hn C1)|].
      apply survives_nested_seq_intro; split; [exact (IH2 _ _ _ _ _ _ _ _ Hn1 C2)|].
      cbn. split; [exact Logic.I|]. split; [exact Logic.I|]. split; [|exact Logic.I].
      split; [exact Logic.I|]. split; [exact Logic.I|].
      unfold pred_set.IN in *. rewrite !domain_insert. right; right; exact Hn2.
    - destruct (compile_exp ct tmp l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
      destruct (compile_exp ct tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
      injection Hc as <- <- <- <-.
      destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & _ & El1).
      assert (Hn1 : n IN domain l1)
        by (rewrite El1; apply comp_syn_cut_sets_mem_domain; split; assumption).
      apply survives_nested_seq_intro; split;
        [exact (IH1 _ _ _ _ _ _ _ _ Hn C1)|exact (IH2 _ _ _ _ _ _ _ _ Hn1 C2)]. }
  split.
  - intros ct tmp l e p le ntmp nl n [Hn Hc]. exact (G e _ _ _ _ _ _ _ _ Hn Hc).
  - intros ct tmp l es p le ntmp nl n [Hn Hc].
    refine (surv_exps_of es _ _ _ _ _ _ _ _ _ Hn Hc).
    apply Forall_forall; intros e _; apply G.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exp" *)
Theorem member_cutset_survives_comp_exp : forall ct tmp l (e : crepLang.exp a) p le ntmp nl n,
  n IN domain l /\ compile_exp ct tmp l e = (p, (le, (ntmp, nl))) ->
  survives n (nested_seq p).
Proof. exact (proj1 member_cutset_survives_comp_exp_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exps" *)
Theorem member_cutset_survives_comp_exps : forall ct tmp l (e : list (crepLang.exp a)) p le ntmp nl n,
  n IN domain l /\ compile_exps ct tmp l e = (p, (le, (ntmp, nl))) ->
  survives n (nested_seq p).
Proof. exact (proj2 member_cutset_survives_comp_exp_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_assigned_mem_gt_comp_exp_cases" *)
Theorem not_mem_assigned_mem_gt_comp_exp_cases :
  (forall ctxt tmp l (e : crepLang.exp a) p le ntmp nl n,
    compile_exp ctxt tmp l e = (p, (le, (ntmp, nl))) /\
    ctxt_max (vmax ctxt) (vars ctxt) /\
    (forall v m, FLOOKUP (vars ctxt) v = SOME m -> n <> m) /\ n < tmp ->
    ~ MEM n (assigned_vars (nested_seq p))) /\
  (forall ctxt tmp l (e : list (crepLang.exp a)) p le ntmp nl n,
    compile_exps ctxt tmp l e = (p, (le, (ntmp, nl))) /\
    ctxt_max (vmax ctxt) (vars ctxt) /\
    (forall v m, FLOOKUP (vars ctxt) v = SOME m -> n <> m) /\ n < tmp ->
    ~ MEM n (assigned_vars (nested_seq p))).
Proof.
  split.
  - intros ctxt tmp l e p le ntmp nl n (Hc & _ & _ & Hn) Hm.
    pose proof (comp_exp_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ _ (conj Hc Hm)). lia.
  - intros ctxt tmp l e p le ntmp nl n (Hc & _ & _ & Hn) Hm.
    pose proof (comp_exps_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ _ (conj Hc Hm)). lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_assigned_mem_gt_comp_exp" *)
Theorem not_mem_assigned_mem_gt_comp_exp : forall ctxt tmp l (e : crepLang.exp a) p le ntmp nl n,
  compile_exp ctxt tmp l e = (p, (le, (ntmp, nl))) /\
  ctxt_max (vmax ctxt) (vars ctxt) /\
  (forall v m, FLOOKUP (vars ctxt) v = SOME m -> n <> m) /\ n < tmp ->
  ~ MEM n (assigned_vars (nested_seq p)).
Proof. exact (proj1 not_mem_assigned_mem_gt_comp_exp_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_assigned_mem_gt_comp_exps" *)
Theorem not_mem_assigned_mem_gt_comp_exps : forall ctxt tmp l (e : list (crepLang.exp a)) p le ntmp nl n,
  compile_exps ctxt tmp l e = (p, (le, (ntmp, nl))) /\
  ctxt_max (vmax ctxt) (vars ctxt) /\
  (forall v m, FLOOKUP (vars ctxt) v = SOME m -> n <> m) /\ n < tmp ->
  ~ MEM n (assigned_vars (nested_seq p)).
Proof. exact (proj2 not_mem_assigned_mem_gt_comp_exp_cases). Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "assigned_vars_nested_seq_assign" *)
Theorem assigned_vars_nested_seq_assign : forall vs (es : list (loopLang.exp a)),
  LENGTH vs = LENGTH es -> assigned_vars (nested_seq (MAP2 Assign vs es)) = vs.
Proof. exact assigned_vars_nested_assign. Qed.

Lemma LENGTH_GENLIST_c {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, !LENGTH_length, length_app; cbn [length].
  rewrite LENGTH_length in IH; lia.
Qed.

Ltac sv_split :=
  repeat match goal with
         | |- survives _ (nested_seq (_ ++ _)) => apply survives_nested_seq_intro; split
         end.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_prog" *)
Theorem member_cutset_survives_comp_prog : forall ctxt l (p : crepLang.prog a) n,
  n IN domain l -> survives n (compile ctxt l p).
Proof.
  intros ctxt l p; revert ctxt l.
  induction p as [|v e p IH|v e|lhs op rhs|e1 e2|e1 e2|e1 e2|g e|p q IHp IHq|e p q IHp IHq
                 |e p IH|k|k|o f es IH|f p1 l1 p2 l2|w|es|op v e|] using crepProps.cprog_nested_ind;
    intros ctxt l n Hn; cbn [compile].
  all: try exact Logic.I.
  - (* Dec *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    cbn [survives]. split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))|].
    split; [exact Logic.I|]. apply IH.
    unfold pred_set.IN in *. rewrite domain_insert. right; exact Hn.
  - (* Assign *)
    destruct (FLOOKUP (vars ctxt) v) as [m|]; [|exact Logic.I].
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))|cbn; tauto].
  - (* Primitive *)
    destruct (OPT_MMAP (FLOOKUP (vars ctxt)) lhs), (OPT_MMAP (FLOOKUP (vars ctxt)) rhs); exact Logic.I.
  - (* Store *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & _ & El1).
    assert (Hn1 : n IN domain l1)
      by (rewrite El1; apply comp_syn_cut_sets_mem_domain; split; assumption).
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))
              |exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn1 C2))|cbn; tauto].
  - (* Store32 *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & _ & El1).
    assert (Hn1 : n IN domain l1)
      by (rewrite El1; apply comp_syn_cut_sets_mem_domain; split; assumption).
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))
              |exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn1 C2))|cbn; tauto].
  - (* StoreByte *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & _ & El1).
    assert (Hn1 : n IN domain l1)
      by (rewrite El1; apply comp_syn_cut_sets_mem_domain; split; assumption).
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))
              |exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn1 C2))|cbn; tauto].
  - (* StoreGlob *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))|cbn; tauto].
  - (* Seq *)
    cbn [survives]. split; [apply IHp; exact Hn|apply IHq; exact Hn].
  - (* If *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))|].
    cbn [nested_seq survives]. split; [exact Logic.I|]. split; [|exact Logic.I].
    split; [apply IHp; exact Hn|]. split; [apply IHq; exact Hn|exact Hn].
  - (* While *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    cbn [survives]. split; [exact Hn|]. split; [exact Hn|].
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))|].
    cbn [nested_seq survives]. split; [exact Logic.I|]. split; [|exact Logic.I].
    split; [split; [apply IH; exact Hn|exact Logic.I]|]. split; [exact Logic.I|exact Hn].
  - (* Call *)
    destruct (compile_exps ctxt (vmax ctxt + 1) l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
    destruct o as [[rts [[eid ep]|]]|]; cbv beta iota zeta; sv_split;
      try exact (member_cutset_survives_comp_exps _ _ _ _ _ _ _ _ _ (conj Hn C1));
      try (apply nested_assigns_survives; unfold gen_temps; apply LENGTH_GENLIST_c);
      cbn [nested_seq survives].
    + split; [|exact Logic.I]. split; [exact Hn|]. split; [exact Hn|].
      split; [|exact Logic.I]. split; [exact Logic.I|]. split; [|exact Hn].
      split; [exact Logic.I|]. apply (IH rts eid ep eq_refl); exact Hn.
    + split; [|exact Logic.I]. split; [exact Hn|]. split; [exact Hn|].
      split; exact Logic.I.
    + split; exact Logic.I.
  - (* ExtCall *)
    destruct (FLOOKUP (vars ctxt) p1), (FLOOKUP (vars ctxt) l1), (FLOOKUP (vars ctxt) p2),
      (FLOOKUP (vars ctxt) l2); try exact Logic.I. exact Hn.
  - (* Raise *)
    cbn. split; exact Logic.I.
  - (* Return *)
    destruct (compile_exps ctxt (vmax ctxt + 1) l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
    sv_split.
    + exact (member_cutset_survives_comp_exps _ _ _ _ _ _ _ _ _ (conj Hn C1)).
    + apply nested_assigns_survives. unfold gen_temps. apply LENGTH_GENLIST_c.
    + cbn; tauto.
  - (* ShMem *)
    destruct (FLOOKUP (vars ctxt) v) as [m|]; [|exact Logic.I].
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    sv_split; [exact (member_cutset_survives_comp_exp _ _ _ _ _ _ _ _ _ (conj Hn C1))|cbn; tauto].
Qed.

Lemma OPT_MMAP_In_res {A B} (f : A -> option B) l ys y :
  OPT_MMAP f l = SOME ys -> In y ys -> exists x, In x l /\ f x = SOME y.
Proof.
  revert ys; induction l as [|x l IHl]; intros ys H Hy; cbn in H.
  - injection H as <-. contradiction.
  - destruct (f x) as [z|] eqn:Ef; [|discriminate]. cbn in H.
    destruct (OPT_MMAP f l) as [zs|] eqn:E2; [|discriminate]. injection H as <-.
    destruct Hy as [<-|Hy]; [exists x; split; [left; reflexivity|exact Ef]|].
    destruct (IHl zs eq_refl Hy) as (x' & Hx' & Hf). exists x'; split; [right; exact Hx'|exact Hf].
Qed.

Ltac av_split H :=
  repeat (progress (cbn [nested_seq assigned_vars app In] in H;
                    repeat first [ rewrite assigned_vars_nested_seq_split in H
                                 | rewrite in_app_iff in H ])).

Lemma not_assigned_exp ctxt tmp l (e : crepLang.exp a) p le ntmp nl n :
  compile_exp ctxt tmp l e = (p, (le, (ntmp, nl))) -> n < tmp ->
  ~ In n (assigned_vars (nested_seq p)).
Proof.
  intros Hc Hn Hi. apply MEM_In in Hi.
  pose proof (comp_exp_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ _ (conj Hc Hi)). lia.
Qed.

Lemma not_assigned_exps ctxt tmp l (e : list (crepLang.exp a)) p le ntmp nl n :
  compile_exps ctxt tmp l e = (p, (le, (ntmp, nl))) -> n < tmp ->
  ~ In n (assigned_vars (nested_seq p)).
Proof.
  intros Hc Hn Hi. apply MEM_In in Hi.
  pose proof (comp_exps_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ _ (conj Hc Hi)). lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_context_assigned_mem_gt" *)
Theorem not_mem_context_assigned_mem_gt : forall ctxt l (p : crepLang.prog a) n,
  ctxt_max (vmax ctxt) (vars ctxt) /\
  (forall v m, FLOOKUP (vars ctxt) v = SOME m -> n <> m) /\
  n <= vmax ctxt ->
  ~ MEM n (assigned_vars (compile ctxt l p)).
Proof.
  intros ctxt l p; revert ctxt l.
  induction p as [|v e p IH|v e|lhs op rhs|e1 e2|e1 e2|e1 e2|g e|p q IHp IHq|e p q IHp IHq
                 |e p IH|k|k|o f es IH|f p1 l1 p2 l2|w|es|op v e|] using crepProps.cprog_nested_ind;
    intros ctxt l n (Hm & Hv & Hn) Hi; apply MEM_In in Hi; cbn [compile] in Hi.
  all: try (cbn [assigned_vars In] in Hi; exact Hi).
  - (* Dec *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    av_split Hi. destruct Hi as [Hi|[Hi|Hi]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + lia.
    + refine (IH _ _ n _ (proj2 (MEM_In _ _) Hi)). cbn [vars vmax].
      split; [|split].
      * intros v' m' Hf. rewrite FLOOKUP_UPDATE in Hf. destruct (decide _).
        -- injection Hf as <-. lia.
        -- specialize (Hm _ _ Hf). lia.
      * intros v' m' Hf. rewrite FLOOKUP_UPDATE in Hf. destruct (decide _).
        -- injection Hf as <-. lia.
        -- exact (Hv _ _ Hf).
      * lia.
  - (* Assign *)
    destruct (FLOOKUP (vars ctxt) v) as [m|] eqn:Ev; [|cbn in Hi; exact Hi].
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    av_split Hi. destruct Hi as [Hi|[Hi|[]]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + exact (Hv _ _ Ev (eq_sym Hi)).
  - (* Primitive *)
    destruct (OPT_MMAP (FLOOKUP (vars ctxt)) lhs) as [nl|] eqn:E1;
      [|cbn in Hi; exact Hi].
    destruct (OPT_MMAP (FLOOKUP (vars ctxt)) rhs) as [nr|]; cbn [assigned_vars] in Hi; [|exact Hi].
    destruct (OPT_MMAP_In_res _ _ _ _ E1 Hi) as (x & _ & Hx). exact (Hv _ _ Hx eq_refl).
  - (* Store *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (_ & Le2 & _).
    av_split Hi. destruct Hi as [Hi|[Hi|Hi]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C2 ltac:(lia) Hi).
    + intuition lia.
  - (* Store32 *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (_ & Le2 & _).
    av_split Hi. destruct Hi as [Hi|[Hi|Hi]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C2 ltac:(lia) Hi).
    + intuition lia.
  - (* StoreByte *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e1) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp ctxt tmp1 l1 e2) as [p2 [le2 [tmp2 l2]]] eqn:C2.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (_ & Le2 & _).
    av_split Hi. destruct Hi as [Hi|[Hi|Hi]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C2 ltac:(lia) Hi).
    + intuition lia.
  - (* StoreGlob *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    av_split Hi. destruct Hi as [Hi|[]].
    exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
  - (* Seq *)
    av_split Hi. destruct Hi as [Hi|Hi];
      [exact (IHp _ _ n (conj Hm (conj Hv Hn)) (proj2 (MEM_In _ _) Hi))
      |exact (IHq _ _ n (conj Hm (conj Hv Hn)) (proj2 (MEM_In _ _) Hi))].
  - (* If *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    av_split Hi. destruct Hi as [Hi|[Hi|[[Hi|Hi]|[]]]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + lia.
    + exact (IHp _ _ n (conj Hm (conj Hv Hn)) (proj2 (MEM_In _ _) Hi)).
    + exact (IHq _ _ n (conj Hm (conj Hv Hn)) (proj2 (MEM_In _ _) Hi)).
  - (* While *)
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _).
    av_split Hi. destruct Hi as [Hi|[Hi|[[[Hi|[]]|[]]|[]]]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + lia.
    + exact (IH _ _ n (conj Hm (conj Hv Hn)) (proj2 (MEM_In _ _) Hi)).
  - (* Call *)
    destruct (compile_exps ctxt (vmax ctxt + 1) l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _ & _).
    assert (Hlen : LENGTH (gen_temps tmp1 (LENGTH les1)) = LENGTH les1)
      by (unfold gen_temps; apply LENGTH_GENLIST_c).
    assert (Hrt : forall rts, ~ In n (rt_vars (vars ctxt) rts (vmax ctxt + 1))).
    { intros rts Hr. unfold rt_vars in Hr.
      destruct (OPT_MMAP (FLOOKUP (vars ctxt)) rts) as [ms|] eqn:Eo.
      - destruct (OPT_MMAP_In_res _ _ _ _ Eo Hr) as (x & _ & Hx). exact (Hv _ _ Hx eq_refl).
      - destruct Hr as [Hr|[]]. lia. }
    destruct o as [[rts [[eid ep]|]]|]; cbv beta iota zeta in Hi; av_split Hi;
      rewrite (assigned_vars_nested_assign _ _ Hlen) in Hi;
      (destruct Hi as [Hi|[Hi|Hi]];
       [exact (not_assigned_exps _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi)
       |unfold gen_temps in Hi; apply In_GENLIST_iff in Hi as (i & _ & ->); lia|]).
    + destruct Hi as [[Hi|[Hi|[Hi|[]]]]|[]]; [exact (Hrt rts Hi)|lia|].
      exact (IH rts eid ep eq_refl _ _ n (conj Hm (conj Hv Hn)) (proj2 (MEM_In _ _) Hi)).
    + destruct Hi as [[Hi|[Hi|[]]]|[]]; [exact (Hrt rts Hi)|lia].
    + contradiction.
  - (* ExtCall *)
    destruct (FLOOKUP (vars ctxt) p1), (FLOOKUP (vars ctxt) l1), (FLOOKUP (vars ctxt) p2),
      (FLOOKUP (vars ctxt) l2); cbn in Hi; exact Hi.
  - (* Raise *)
    cbn in Hi. destruct Hi as [Hi|[]]. lia.
  - (* Return *)
    destruct (compile_exps ctxt (vmax ctxt + 1) l es) as [p1 [les1 [tmp1 l1]]] eqn:C1.
    destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C1) as (_ & Le1 & _ & _).
    assert (Hlen : LENGTH (gen_temps tmp1 (LENGTH les1)) = LENGTH les1)
      by (unfold gen_temps; apply LENGTH_GENLIST_c).
    av_split Hi. rewrite (assigned_vars_nested_assign _ _ Hlen) in Hi.
    destruct Hi as [Hi|[Hi|[]]].
    + exact (not_assigned_exps _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + unfold gen_temps in Hi; apply In_GENLIST_iff in Hi as (i & _ & ->); lia.
  - (* ShMem *)
    destruct (FLOOKUP (vars ctxt) v) as [m|] eqn:Ev; [|cbn in Hi; exact Hi].
    destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p1 [le1 [tmp1 l1]]] eqn:C1.
    av_split Hi. destruct Hi as [Hi|[Hi|[]]].
    + exact (not_assigned_exp _ _ _ _ _ _ _ _ n C1 ltac:(lia) Hi).
    + exact (Hv _ _ Ev (eq_sym Hi)).
Qed.

End Survives.

Ltac crep_cbn :=
  cbn [crepSem.locals crepSem.globals crepSem.code crepSem.memory crepSem.memaddrs
       crepSem.sh_memaddrs crepSem.clock crepSem.be crepSem.ffi crepSem.base_addr
       crepSem.top_addr crepSem.set_locals crepSem.set_memory crepSem.set_clock crepSem.set_ffi
       crepSem.set_code crepSem.set_globals crepSem.dec_clock crepSem.empty_locals
       crepSem.set_var] in *.

Ltac loop_cbn :=
  cbn [locals globals memory mdomain sh_mdomain clock code be ffi base_addr top_addr
       set_locals set_memory set_clock set_ffi set_var set_vars set_globals dec_clock
       call_env] in *.

(** Close a [state_rel] goal from a [state_rel] hypothesis. *)
Ltac srel S1 :=
  let A1 := fresh in let A2 := fresh in let A3 := fresh in let A4 := fresh in
  let A5 := fresh in let A6 := fresh in let A7 := fresh in
  destruct S1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7); unfold state_rel; crep_cbn; loop_cbn;
  repeat split; first [congruence | lia].

(** ** [ncompile_correct] *)

Section NCompile.
Context {a : N} {ffi_t : Type}.
Implicit Types (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t).

(** The result correspondence and the locals obligation of
    [ncompile_correct]'s conclusion. *)
Definition nc_res (res : option (crepSem.result a)) : option (loopSem.result a) :=
  match res with
  | NONE => NONE
  | SOME (crepSem.Break n) => SOME (Break n)
  | SOME (crepSem.Continue n) => SOME (Continue n)
  | SOME (crepSem.Return vs) => SOME (Result (MAP wlab_wloc vs))
  | SOME (crepSem.Exception eid) => SOME (Exception (Word eid))
  | SOME crepSem.TimeOut => SOME TimeOut
  | SOME (crepSem.FinalFFI f) => SOME (FinalFFI f)
  | SOME crepSem.Error => SOME Error
  end.

Definition nc_post ctxt l (res : option (crepSem.result a)) s1 t1 : Prop :=
  match res with
  | NONE => locals_rel ctxt l (crepSem.locals s1) (locals t1)
  | SOME (crepSem.Break n) => locals_rel ctxt l (crepSem.locals s1) (locals t1)
  | SOME (crepSem.Continue n) => locals_rel ctxt l (crepSem.locals s1) (locals t1)
  | SOME (crepSem.Return vs) => True
  | SOME crepSem.Error => False
  | _ => True
  end.

Definition nc_P (v : crepLang.prog a) s : Prop :=
  forall res s1 t ctxt l,
    crepSem.evaluate (v, s) = (res, s1) -> res <> SOME crepSem.Error -> rels s t ctxt l ->
    exists ck res1 t1,
      evaluate (compile ctxt l v, set_clock (clock t + ck) t) = (res1, t1) /\
      state_rel s1 t1 /\ mem_rel (crepSem.memory s1) (memory t1) (crepSem.memaddrs s1) /\
      globals_rel (crepSem.globals s1) (globals t1) /\
      code_rel ctxt (crepSem.code s1) (code t1) /\
      res1 = nc_res res /\ nc_post ctxt l res s1 t1.

Lemma crep_unfold (p : crepLang.prog a) s :
  crepSem.evaluate (p, s) =
  crepSem.evaluate_body (fun p' s' => crepSem.evaluate (p', s'))
                        (fun p' s' => crepSem.evaluate (p', s')) p s.
Proof. apply crepProps.evaluate_unfold. Qed.

Ltac crep_step H := rewrite crep_unfold in H; cbn [crepSem.evaluate_body] in H;
  unfold crepSem.fcl in H; rewrite ?crepSem.fix_clock_evaluate in H; cbn beta in H.

(** Finish with the target state, [ck] given. *)
Lemma nc_finish ck res1 t1 s1 ctxt l res t v :
  evaluate (compile ctxt l v, set_clock (clock t + ck) t) = (res1, t1) ->
  state_rel s1 t1 -> mem_rel (crepSem.memory s1) (memory t1) (crepSem.memaddrs s1) ->
  globals_rel (crepSem.globals s1) (globals t1) -> code_rel ctxt (crepSem.code s1) (code t1) ->
  res1 = nc_res res ->
  (forall n, res <> SOME (crepSem.Break n)) -> (forall n, res <> SOME (crepSem.Continue n)) ->
  res <> SOME crepSem.Error -> res <> NONE ->
  exists ck res1 t1,
    evaluate (compile ctxt l v, set_clock (clock t + ck) t) = (res1, t1) /\
    state_rel s1 t1 /\ mem_rel (crepSem.memory s1) (memory t1) (crepSem.memaddrs s1) /\
    globals_rel (crepSem.globals s1) (globals t1) /\
    code_rel ctxt (crepSem.code s1) (code t1) /\
    res1 = nc_res res /\ nc_post ctxt l res s1 t1.
Proof.
  intros E H1 H2 H3 H4 Hres Hb Hc He Hn.
  exists ck, res1, t1. do 5 (split; [assumption|]). split; [exact Hres|].
  destruct res as [[]|]; cbn; try exact Logic.I; try congruence;
    try (exfalso; eapply Hb; reflexivity); try (exfalso; eapply Hc; reflexivity).
Qed.

Lemma nc_finish_rel ck res1 t1 s1 ctxt l res t v :
  evaluate (compile ctxt l v, set_clock (clock t + ck) t) = (res1, t1) ->
  rels s1 t1 ctxt l -> res1 = nc_res res -> res <> SOME crepSem.Error ->
  exists ck res1 t1,
    evaluate (compile ctxt l v, set_clock (clock t + ck) t) = (res1, t1) /\
    state_rel s1 t1 /\ mem_rel (crepSem.memory s1) (memory t1) (crepSem.memaddrs s1) /\
    globals_rel (crepSem.globals s1) (globals t1) /\
    code_rel ctxt (crepSem.code s1) (code t1) /\
    res1 = nc_res res /\ nc_post ctxt l res s1 t1.
Proof.
  intros E (H1 & H2 & H3 & H4 & H5) Hres He.
  exists ck, res1, t1. do 5 (split; [assumption|]). split; [exact Hres|].
  destruct res as [[]|]; cbn; try exact Logic.I; try congruence; exact H5.
Qed.

Lemma nc_Skip s : nc_P crepLang.Skip s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H. injection H as <- <-.
  apply (nc_finish_rel 0 NONE t); [rewrite set_clock_add0; apply ev_Skip|exact Hr|reflexivity|exact Hne].
Qed.

Lemma nc_Break s n : nc_P (crepLang.Break n) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H. injection H as <- <-.
  apply (nc_finish_rel 0 (SOME (Break n)) t); [|exact Hr|reflexivity|exact Hne].
  rewrite set_clock_add0. cbn [compile]. unfold_eval. reflexivity.
Qed.

Lemma nc_Continue s n : nc_P (crepLang.Continue n) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H. injection H as <- <-.
  apply (nc_finish_rel 0 (SOME (Continue n)) t); [|exact Hr|reflexivity|exact Hne].
  rewrite set_clock_add0. cbn [compile]. unfold_eval. reflexivity.
Qed.

Lemma rels_dec_clock s t ctxt l :
  rels s t ctxt l -> rels (crepSem.dec_clock s) (dec_clock t) ctxt l.
Proof.
  intros ((H1 & H2 & H3 & H4 & H5 & H6 & H7) & R2 & R3 & R4 & R5).
  split; [|exact (conj R2 (conj R3 (conj R4 R5)))].
  repeat split; try assumption. cbn [crepSem.dec_clock dec_clock crepSem.set_clock set_clock
                                    crepSem.clock clock]. rewrite H3. reflexivity.
Qed.

Lemma nc_Tick s : nc_P crepLang.Tick s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  assert (Hc : crepSem.clock s = clock t) by apply (rels_clock _ _ _ _ Hr).
  destruct (crepSem.clock s =? 0) eqn:Ec; injection H as <- <-.
  - apply (nc_finish 0 (SOME TimeOut) (set_locals LN t)).
    + rewrite set_clock_add0. cbn [compile]. unfold_eval. rewrite <- Hc, Ec. reflexivity.
    + apply Hr.
    + apply Hr.
    + apply Hr.
    + apply Hr.
    + reflexivity.
    + intros n Hn; discriminate.
    + intros n Hn; discriminate.
    + discriminate.
    + discriminate.
  - apply (nc_finish_rel 0 NONE (dec_clock t)).
    + rewrite set_clock_add0. cbn [compile]. unfold_eval. rewrite <- Hc, Ec. reflexivity.
    + apply rels_dec_clock; exact Hr.
    + reflexivity.
    + discriminate.
Qed.

Lemma nc_Raise s eid : nc_P (crepLang.Raise eid) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H. injection H as <- <-.
  exists 0, (SOME (Exception (Word eid))),
    (call_env [] (set_var (vmax ctxt + 1) (Word eid) t)).
  rewrite set_clock_add0. split.
  { cbn [compile]. rewrite ev_Seq, (ev_Assign _ _ _ (Word eid)) by reflexivity. cbv beta iota.
    unfold_eval. cbn [set_var set_locals locals]. rewrite lookup_insert.
    destruct (decide (vmax ctxt + 1 = vmax ctxt + 1)); [reflexivity|congruence]. }
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [reflexivity|exact Logic.I].
Qed.

Lemma nc_Seq c1 c2 s :
  (forall p' s', crepSem.eval_lt (p', s') (crepLang.Seq c1 c2, s) -> nc_P p' s') ->
  nc_P (crepLang.Seq c1 c2) s.
Proof.
  intros IH res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.evaluate (c1, s)) as [r1 s'] eqn:E1.
  assert (Hr1 : r1 <> SOME crepSem.Error)
    by (intros ->; injection H as <- _; exact (Hne eq_refl)).
  destruct (IH c1 s ltac:(crepProps.lt_tac) r1 s' t ctxt l E1 Hr1 Hr)
    as (ck1 & q1 & t1 & T1 & R1 & R2 & R3 & R4 & Eq1 & P1).
  destruct r1 as [r1|].
  - injection H as <- <-. exists ck1, q1, t1. split.
    + cbn [compile]. unfold_eval. rewrite T1. subst q1. destruct r1; reflexivity.
    + repeat (split; [assumption|]). exact P1.
  - cbn [nc_res nc_post] in Eq1, P1. subst q1.
    destruct (IH c2 s' ltac:(crepProps.lt_tac) res s1 t1 ctxt l H Hne
                (conj R1 (conj R2 (conj R3 (conj R4 P1)))))
      as (ck2 & q2 & t2 & T2 & S1 & S2 & S3 & S4 & Eq2 & P2).
    exists (ck1 + ck2), q2, t2. split.
    + assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock_eq _ _ _ _ ck2 (conj T1 Hnt)) as T1'.
      rewrite set_clock_set_clock in T1'. cbn [clock set_clock] in T1'.
      rewrite <- N.add_assoc in T1'.
      cbn [compile]. unfold_eval. rewrite T1'. exact T2.
    + repeat (split; [assumption|]). exact P2.
Qed.

Lemma nc_Return s es : nc_P (crepLang.Return es) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (OPT_MMAP (crepSem.eval s) es) as [ws|] eqn:Ees; [|injection H as <- _; congruence].
  injection H as <- <-.
  cbn [compile].
  destruct (compile_exps ctxt (vmax ctxt + 1) l es) as [p [les [ntmp nl]]] eqn:C.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exps_preserves_eval es s ws t ctxt (vmax ctxt + 1) l p les ntmp nl
              (conj Ees (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck & st & E & Hles & S1 & S2 & S3 & S4 & S5).
  destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C) as (_ & Le & _ & Len).
  set (ntmps := gen_temps ntmp (LENGTH les)).
  assert (Hlen : LENGTH ntmps = LENGTH les) by (unfold ntmps, gen_temps; apply LENGTH_GENLIST_c).
  assert (Hdist : ALL_DISTINCT ntmps).
  { unfold ntmps, gen_temps. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & Hm). lia. }
  assert (Hlenws : LENGTH les = LENGTH (MAP wlab_wloc ws)).
  { rewrite (opt_mmap_length_eq _ _ _ Hles). reflexivity. }
  assert (Hdl : distinct_lists ntmps (FLAT (MAP locals_touched les))).
  { apply distinct_lists_iff. intros x Hx Hx'.
    unfold ntmps, gen_temps in Hx. apply In_GENLIST_iff in Hx as (i & _ & ->).
    pose proof (proj1 (proj2 R5)) as Hmax.
    refine (_ (compile_exps_le_tmp_domain ctxt (vmax ctxt + 1) l es p les ntmp nl (ntmp + i)
                 (conj Hmax (conj C (conj Hv (conj _ (proj2 (MEM_In _ _) Hx'))))))).
    - intros [Hlt _]. lia.
    - intros k Hk. apply (var_hyp_of_evals s t ctxt l es ws); [|exact Ees|apply MEM_In, Hk].
      exact (conj R1 (conj R2 (conj R3 (conj R4 R5)))). }
  apply opt_mmap_eq_some in Hles.
  pose proof (loop_eval_nested_assign_distinct_eq les ntmps st (MAP wlab_wloc ws)
                (conj Hles (conj Hdl (conj Hdist Hlen)))) as EA.
  exists ck, (SOME (Result (MAP wlab_wloc ws))),
    (call_env [] (set_locals (alist_insert ntmps (MAP wlab_wloc ws) (locals st)) st)).
  split.
  - rewrite (ev_nested_app _ _ _ _ E), (ev_nested_app _ _ _ _ EA).
    cbn [nested_seq]. rewrite ev_Seq. unfold_eval.
    rewrite get_vars_local_update_some_eq by (split; [exact Hdist|rewrite Hlen; exact Hlenws]).
    cbv beta iota. reflexivity.
  - split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
    split; [reflexivity|exact Logic.I].
Qed.

Lemma mem_store_32_rel sm tm dm (be0 : bool) (adr : word a) hw sm' :
  mem_rel sm tm dm -> panSem.mem_store_32 sm dm be0 adr hw = SOME sm' ->
  exists tm', mem_store_32 tm dm be0 adr hw = SOME tm' /\ mem_rel sm' tm' dm.
Proof.
  unfold panSem.mem_store_32, mem_store_32. intros Hm H.
  destruct (aligned 2 adr); [|discriminate].
  destruct (sm (byte_align adr)) as [v] eqn:E.
  destruct (classical_dec (byte_align adr IN dm)) as [Hin|]; [|discriminate].
  injection H as <-. rewrite <- (Hm _ Hin), E. cbn [wlab_wloc].
  eexists; split; [reflexivity|].
  intros ad Had. unfold UPDATE. destruct (decide _); [reflexivity|apply Hm; exact Had].
Qed.

Lemma mem_store_byte_rel sm tm dm (be0 : bool) (adr : word a) b sm' :
  mem_rel sm tm dm -> panSem.mem_store_byte sm dm be0 adr b = SOME sm' ->
  exists tm', mem_store_byte_aux tm dm be0 adr b = SOME tm' /\ mem_rel sm' tm' dm.
Proof.
  unfold panSem.mem_store_byte, mem_store_byte_aux. intros Hm H.
  destruct (sm (byte_align adr)) as [v] eqn:E.
  destruct (classical_dec (byte_align adr IN dm)) as [Hin|]; [|discriminate].
  injection H as <-. rewrite <- (Hm _ Hin), E. cbn [wlab_wloc].
  eexists; split; [reflexivity|].
  intros ad Had. unfold UPDATE. destruct (decide _); [reflexivity|apply Hm; exact Had].
Qed.

Lemma locals_rel_update ctxt l (sl : fmap N (panSem.word_lab a)) tl v n w :
  locals_rel ctxt l sl tl -> FLOOKUP (vars ctxt) v = SOME n -> n IN domain l ->
  locals_rel ctxt l (sl |+ (v, w)) (insert n (wlab_wloc w) tl).
Proof.
  intros (Hd & Hm & Hs & Hl) Hn Hnd. split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk; unfold pred_set.IN in *; rewrite domain_insert; right; exact (Hs k Hk).
  - intros vn x Hx. rewrite FLOOKUP_UPDATE in Hx. destruct (decide (v = vn)) as [<-|Hne].
    + injection Hx as <-. exists n. split; [exact Hn|]. split; [exact Hnd|].
      rewrite lookup_insert. destruct (decide (n = n)); [reflexivity|congruence].
    + destruct (Hl vn x Hx) as (m & Hm' & Hmd & Hlk). exists m. split; [exact Hm'|].
      split; [exact Hmd|]. rewrite lookup_insert. destruct (decide (m = n)) as [->|]; [|exact Hlk].
      exfalso. apply Hne. exact (Hd v vn n n (conj Hn (conj Hm' eq_refl))).
Qed.

Lemma locals_back ctxt l (sl : fmap N (panSem.word_lab a)) tl0 tl (p : list (loopLang.prog a)) :
  locals_rel ctxt l sl tl0 -> comp_syntax_ok l (nested_seq p) ->
  locals_rel ctxt (cut_sets l (nested_seq p)) sl tl -> locals_rel ctxt l sl tl.
Proof.
  intros H0 Ok H1. apply (locals_rel_cutset_prop ctxt l sl tl0 (cut_sets l (nested_seq p)) tl).
  split; [exact H0|]. split; [exact H1|]. apply comp_syn_impl_cut_sets_subspt; exact Ok.
Qed.

Lemma nc_Assign s v e : nc_P (crepLang.Assign v e) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s e) as [w|] eqn:Ee; [|injection H as <- _; congruence].
  destruct (FLOOKUP (crepSem.locals s) v) as [old|] eqn:Ev; [|injection H as <- _; congruence].
  injection H as <- <-.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  destruct (proj2 (proj2 (proj2 R5)) v old Ev) as (n & Hn & Hnd & _).
  cbn [compile]. rewrite Hn.
  destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p [le [tmp nl]]] eqn:C.
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exp_preserves_eval s e w t ctxt (vmax ctxt + 1) l p le tmp nl
              (conj Ee (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck & st & E & Hle & S1 & S2 & S3 & S4 & S5).
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C) as (Ok & _ & El).
  exists ck, NONE, (set_var n (wlab_wloc w) st).
  split.
  { rewrite (ev_nested_app _ _ _ _ E). cbn [nested_seq].
    rewrite ev_Seq, (ev_Assign _ _ _ _ Hle). cbv beta iota. apply ev_Skip. }
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  split; [reflexivity|].
  apply locals_rel_update; [|exact Hn|exact Hnd].
  rewrite El in S5. exact (locals_back ctxt l _ _ _ p R5 Ok S5).
Qed.

Lemma nc_StoreGlob s dst e : nc_P (crepLang.StoreGlob dst e) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s e) as [w|] eqn:Ee; [|injection H as <- _; congruence].
  injection H as <- <-.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p [le [tmp nl]]] eqn:C.
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exp_preserves_eval s e w t ctxt (vmax ctxt + 1) l p le tmp nl
              (conj Ee (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck & st & E & Hle & S1 & S2 & S3 & S4 & S5).
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C) as (Ok & _ & El).
  exists ck, NONE, (set_globals dst (wlab_wloc w) st).
  split.
  { rewrite (ev_nested_app _ _ _ _ E). cbn [nested_seq].
    rewrite ev_Seq. unfold_eval. rewrite Hle. cbv beta iota. apply ev_Skip. }
  split; [exact S1|]. split; [exact S2|].
  split.
  { intros ad x Hx. cbn [crepSem.set_globals crepSem.globals set_globals globals] in *.
    rewrite FLOOKUP_UPDATE in Hx. rewrite FLOOKUP_UPDATE.
    destruct (decide _); [injection Hx as <-; reflexivity|].
    exact (S3 ad x Hx). }
  split; [exact S4|]. split; [reflexivity|].
  rewrite El in S5. exact (locals_back ctxt l _ _ _ p R5 Ok S5).
Qed.

Lemma touched_lt s t ctxt l (e : crepLang.exp a) p le ntmp nl v tmp :
  rels s t ctxt l -> compile_exp ctxt tmp l e = (p, (le, (ntmp, nl))) ->
  crepSem.eval s e = SOME v -> vmax ctxt < tmp ->
  forall k, In k (locals_touched le) -> k < ntmp.
Proof.
  intros Hr C He Hv k Hk.
  assert (Hmax : ctxt_max (vmax ctxt) (vars ctxt)) by apply Hr.
  refine (proj1 (compile_exp_le_tmp_domain ctxt tmp l e p le ntmp nl k
            (conj Hmax (conj C (conj Hv (conj _ (proj2 (MEM_In _ _) Hk))))))).
  intros k' Hk'. apply (var_hyp_of_eval s t ctxt l e v Hr He). apply MEM_In, Hk'.
Qed.

Lemma eval_set_var_notin t (e : loopLang.exp a) n w :
  (forall k, In k (locals_touched e) -> k <> n) -> eval (set_var n w t) e = eval t e.
Proof.
  intros H. apply locals_touched_eq_eval_eq. repeat split; try reflexivity.
  intros k Hk. apply MEM_In, H in Hk. cbn [set_var set_locals locals].
  rewrite lookup_insert. destruct (decide (k = n)); [contradiction|reflexivity].
Qed.

Lemma two_exps s t ctxt l (dst src : crepLang.exp a) p le tmp l1 p' le' tmp' l2 v1 v2 :
  rels s t ctxt l ->
  compile_exp ctxt (vmax ctxt + 1) l dst = (p, (le, (tmp, l1))) ->
  compile_exp ctxt tmp l1 src = (p', (le', (tmp', l2))) ->
  crepSem.eval s dst = SOME v1 -> crepSem.eval s src = SOME v2 ->
  exists ck st, evaluate (nested_seq (p ++ p'), set_clock (clock t + ck) t) = (NONE, st) /\
    eval st le = SOME (wlab_wloc v1) /\ eval st le' = SOME (wlab_wloc v2) /\
    rels s st ctxt l /\
    (forall k, In k (locals_touched le) -> k < tmp) /\
    (forall k, In k (locals_touched le') -> k < tmp') /\
    vmax ctxt < tmp /\ tmp <= tmp'.
Proof.
  intros Hr C1 C2 E1 E2.
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C1) as (Ok1 & Le1 & El1).
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C2) as (Ok2 & Le2 & El2).
  destruct (pe_all dst s v1 t ctxt (vmax ctxt + 1) l p le tmp l1 E1 Hr C1 Hv)
    as (ck1 & st1 & T1 & Hle1 & Hr1).
  assert (Hv1 : vmax ctxt < tmp) by lia.
  destruct (pe_all src s v2 st1 ctxt tmp l1 p' le' tmp' l2 E2 Hr1 C2 Hv1)
    as (ck2 & st2 & T2 & Hle2 & Hr2).
  pose proof (keep_eval ctxt (vmax ctxt + 1) l dst p le tmp l1 p' s t ck1 st1 ck2 st2 _ _ C1 Ok2
                (fun k Hk => proj1 (comp_exp_assigned_vars_tmp_bound _ _ _ _ _ _ _ _ k
                                     (conj C2 (proj2 (MEM_In _ _) Hk))))
                E1 Hr Hv T1 T2 Hle1) as Hle1'.
  exists (ck1 + ck2), st2. split; [exact (ev_combine _ _ _ _ _ _ _ T1 T2)|].
  split; [exact Hle1'|]. split; [exact Hle2|].
  split.
  { destruct Hr2 as (S1 & S2 & S3 & S4 & S5). split; [exact S1|]. split; [exact S2|].
    split; [exact S3|]. split; [exact S4|].
    assert (Ok : comp_syntax_ok l (nested_seq (p ++ p')))
      by (apply comp_syn_ok_nested_seq; split; [exact Ok1|rewrite <- El1; exact Ok2]).
    apply (locals_back ctxt l _ (locals t) _ (p ++ p')); [apply Hr|exact Ok|].
    rewrite cut_sets_nested_seq, <- El1, <- El2. exact S5. }
  split; [exact (touched_lt s t ctxt l dst p le tmp l1 v1 _ Hr C1 E1 Hv)|].
  split; [exact (touched_lt s st1 ctxt l1 src p' le' tmp' l2 v2 _ Hr1 C2 E2 Hv1)|].
  split; lia.
Qed.

Lemma nc_Store s dst src : nc_P (crepLang.Store dst src) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s dst) as [[adr]|] eqn:Ed; [|injection H as <- _; congruence].
  destruct (crepSem.eval s src) as [w|] eqn:Es; [|injection H as <- _; congruence].
  unfold panSem.mem_store in H.
  destruct (classical_dec (adr IN crepSem.memaddrs s)) as [Hin|]; [|injection H as <- _; congruence].
  injection H as <- <-.
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l dst) as [p [le [tmp l1]]] eqn:C1.
  destruct (compile_exp ctxt tmp l1 src) as [p' [le' [tmp' l2]]] eqn:C2.
  destruct (two_exps s t ctxt l dst src p le tmp l1 p' le' tmp' l2 _ _ Hr C1 C2 Ed Es)
    as (ck & st & T & Hle & Hle' & Hrs & Ht1 & Ht2 & Hv & Htt).
  exists ck, NONE,
    (set_memory ((adr =+ wlab_wloc w) (memory st)) (set_var tmp' (wlab_wloc w) st)).
  destruct Hrs as (S1 & S2 & S3 & S4 & S5).
  split.
  { rewrite app_assoc.
    rewrite (ev_nested_app _ _ _ _ T). cbn [nested_seq].
    rewrite ev_Seq, (ev_Assign _ _ _ _ Hle'). cbv beta iota.
    rewrite ev_Seq. unfold_eval.
    rewrite eval_set_var_notin by (intros k Hk; specialize (Ht1 k Hk); lia).
    rewrite Hle. cbn [set_var set_locals locals]. rewrite lookup_insert.
    destruct (decide (tmp' = tmp')) as [_|]; [|congruence]. cbv beta iota.
    cbn [wlab_wloc]. unfold mem_store. cbn [set_var set_locals mdomain]. rewrite <- (proj1 S1).
    destruct (classical_dec (adr IN crepSem.memaddrs s)) as [_|]; [|contradiction].
    cbv beta iota. rewrite ev_Skip. reflexivity. }
  split; [exact S1|]. split.
  { intros ad Had. cbn [crepSem.set_memory crepSem.memory memory set_memory crepSem.memaddrs] in *.
    unfold UPDATE. destruct (decide _); [reflexivity|apply S2; exact Had]. }
  split; [exact S3|]. split; [exact S4|]. split; [reflexivity|].
  apply locals_rel_insert_gt_vmax. split; [exact S5|lia].
Qed.

Lemma nc_Store32 s dst src : nc_P (crepLang.Store32 dst src) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s dst) as [[adr]|] eqn:Ed; [|injection H as <- _; congruence].
  destruct (crepSem.eval s src) as [[w]|] eqn:Es; [|injection H as <- _; congruence].
  destruct (panSem.mem_store_32 _ _ _ adr (w2w w)) as [m|] eqn:Em; [|injection H as <- _; congruence].
  injection H as <- <-.
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l dst) as [p [le [tmp l1]]] eqn:C1.
  destruct (compile_exp ctxt tmp l1 src) as [p' [le' [tmp' l2]]] eqn:C2.
  destruct (two_exps s t ctxt l dst src p le tmp l1 p' le' tmp' l2 _ _ Hr C1 C2 Ed Es)
    as (ck & st & T & Hle & Hle' & Hrs & Ht1 & Ht2 & Hv & Htt).
  destruct Hrs as (S1 & S2 & S3 & S4 & S5).
  assert (Em' : panSem.mem_store_32 (crepSem.memory s) (mdomain st) (be st) adr (w2w w) = SOME m)
    by (rewrite <- (proj1 S1), <- (proj1 (proj2 (proj2 (proj2 S1)))); exact Em).
  rewrite <- (proj1 S1) in Em'.
  destruct (mem_store_32_rel _ _ _ _ _ _ _ S2 Em) as (tm & Etm & Hmr).
  exists ck, NONE,
    (set_memory tm (set_var (tmp' + 1) (Word w) (set_var tmp' (Word adr) st))).
  split.
  { rewrite app_assoc.
    rewrite (ev_nested_app _ _ _ _ T). cbn [nested_seq].
    rewrite ev_Seq, (ev_Assign _ _ _ _ Hle). cbv beta iota.
    rewrite ev_Seq, (ev_Assign _ _ _ (wlab_wloc (panSem.Word w))).
    2: { rewrite eval_set_var_notin by (intros k Hk; specialize (Ht2 k Hk); lia). exact Hle'. }
    cbv beta iota. rewrite ev_Seq. unfold_eval.
    cbn [set_var set_locals locals memory mdomain be wlab_wloc].
    rewrite (lookup_insert (tmp' + 1) _ _ tmp'), (lookup_insert tmp' _ _ tmp').
    destruct (decide (tmp' = tmp' + 1)) as [|_]; [lia|].
    destruct (decide (tmp' = tmp')) as [_|]; [|congruence].
    rewrite (lookup_insert (tmp' + 1) _ _ (tmp' + 1)).
    destruct (decide (tmp' + 1 = tmp' + 1)) as [_|]; [|congruence]. cbv beta iota.
    rewrite <- (proj1 S1), <- (proj1 (proj2 (proj2 (proj2 S1)))), Etm.
    cbv beta iota. rewrite ev_Skip. reflexivity. }
  split; [exact S1|]. split; [exact Hmr|].
  split; [exact S3|]. split; [exact S4|]. split; [reflexivity|].
  apply locals_rel_insert_gt_vmax. split; [|lia].
  apply locals_rel_insert_gt_vmax. split; [exact S5|lia].
Qed.

Lemma nc_StoreByte s dst src : nc_P (crepLang.StoreByte dst src) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s dst) as [[adr]|] eqn:Ed; [|injection H as <- _; congruence].
  destruct (crepSem.eval s src) as [[w]|] eqn:Es; [|injection H as <- _; congruence].
  destruct (panSem.mem_store_byte _ _ _ adr (w2w w)) as [m|] eqn:Em; [|injection H as <- _; congruence].
  injection H as <- <-.
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l dst) as [p [le [tmp l1]]] eqn:C1.
  destruct (compile_exp ctxt tmp l1 src) as [p' [le' [tmp' l2]]] eqn:C2.
  destruct (two_exps s t ctxt l dst src p le tmp l1 p' le' tmp' l2 _ _ Hr C1 C2 Ed Es)
    as (ck & st & T & Hle & Hle' & Hrs & Ht1 & Ht2 & Hv & Htt).
  destruct Hrs as (S1 & S2 & S3 & S4 & S5).
  assert (Em' : panSem.mem_store_byte (crepSem.memory s) (mdomain st) (be st) adr (w2w w) = SOME m)
    by (rewrite <- (proj1 S1), <- (proj1 (proj2 (proj2 (proj2 S1)))); exact Em).
  rewrite <- (proj1 S1) in Em'.
  destruct (mem_store_byte_rel _ _ _ _ _ _ _ S2 Em) as (tm & Etm & Hmr).
  exists ck, NONE,
    (set_memory tm (set_var (tmp' + 1) (Word w) (set_var tmp' (Word adr) st))).
  split.
  { rewrite app_assoc.
    rewrite (ev_nested_app _ _ _ _ T). cbn [nested_seq].
    rewrite ev_Seq, (ev_Assign _ _ _ _ Hle). cbv beta iota.
    rewrite ev_Seq, (ev_Assign _ _ _ (wlab_wloc (panSem.Word w))).
    2: { rewrite eval_set_var_notin by (intros k Hk; specialize (Ht2 k Hk); lia). exact Hle'. }
    cbv beta iota. rewrite ev_Seq. unfold_eval.
    cbn [set_var set_locals locals memory mdomain be wlab_wloc].
    rewrite (lookup_insert (tmp' + 1) _ _ tmp'), (lookup_insert tmp' _ _ tmp').
    destruct (decide (tmp' = tmp' + 1)) as [|_]; [lia|].
    destruct (decide (tmp' = tmp')) as [_|]; [|congruence].
    rewrite (lookup_insert (tmp' + 1) _ _ (tmp' + 1)).
    destruct (decide (tmp' + 1 = tmp' + 1)) as [_|]; [|congruence]. cbv beta iota.
    rewrite <- (proj1 S1), <- (proj1 (proj2 (proj2 (proj2 S1)))), Etm.
    cbv beta iota. rewrite ev_Skip. reflexivity. }
  split; [exact S1|]. split; [exact Hmr|].
  split; [exact S3|]. split; [exact S4|]. split; [reflexivity|].
  apply locals_rel_insert_gt_vmax. split; [|lia].
  apply locals_rel_insert_gt_vmax. split; [exact S5|lia].
Qed.

Lemma lookup_of_locals_rel ctxt l (sl : fmap N (panSem.word_lab a)) tl v x n :
  locals_rel ctxt l sl tl -> FLOOKUP sl v = SOME x -> FLOOKUP (vars ctxt) v = SOME n ->
  lookup n tl = SOME (wlab_wloc x).
Proof.
  intros (_ & _ & _ & Hl) Hx Hn. destruct (Hl v x Hx) as (m & Hm & _ & Hlk).
  rewrite Hn in Hm. injection Hm as <-. exact Hlk.
Qed.

Lemma nc_ShMem s op v ad : nc_P (crepLang.ShMem op v ad) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s ad) as [[addr]|] eqn:Ea; [|injection H as <- _; congruence].
  destruct (FLOOKUP (crepSem.locals s) v) as [[x]|] eqn:Ev;
    [|destruct (is_load op); injection H as <- _; congruence].
  assert (H' : crepSem.sh_mem_op op v addr s = (res, s1)) by (destruct (is_load op); exact H).
  clear H.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  destruct (proj2 (proj2 (proj2 R5)) v _ Ev) as (n & Hn & Hnd & _).
  cbn [compile]. rewrite Hn.
  destruct (compile_exp ctxt (vmax ctxt + 1) l ad) as [p [le [tmp nl]]] eqn:C.
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exp_preserves_eval s ad _ t ctxt (vmax ctxt + 1) l p le tmp nl
              (conj Ea (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck & st & E & Hle & S1 & S2 & S3 & S4 & S5).
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C) as (Ok & _ & El).
  rewrite El in S5. pose proof (locals_back ctxt l _ _ _ p R5 Ok S5) as Hl'.
  pose proof (lookup_of_locals_rel ctxt l _ _ v _ n Hl' Ev Hn) as Hln. cbn [wlab_wloc] in Hln, Hle.
  assert (Hsh : sh_mdomain st = crepSem.sh_memaddrs s) by (symmetry; apply S1).
  assert (Hff : ffi st = crepSem.ffi s) by (symmetry; apply S1).
  assert (Hev : forall q, evaluate (nested_seq (p ++ [ShMem op n le]), set_clock (clock t + ck) t) = q ->
                  evaluate (Seq (ShMem op n le) Skip, st) = q)
    by (intros q Hq; rewrite (ev_nested_app _ _ _ _ E) in Hq; exact Hq).
  destruct op; cbn [crepSem.sh_mem_op] in H'; unfold crepSem.sh_mem_load, crepSem.sh_mem_store in H';
    rewrite ?Ev in H'; cbv beta iota in H';
    repeat match type of H' with
           | context [match ?c with _ => _ end] => let Ec := fresh "Ec" in destruct c eqn:Ec;
               cbv beta iota in H'
           | context [if ?c then _ else _] => let Ec := fresh "Ec" in destruct c eqn:Ec;
               cbv beta iota in H'
           end;
    try (injection H' as <- _; congruence);
    injection H' as <- <-;
    (eexists ck, _, _; split;
     [ rewrite (ev_nested_app _ _ _ _ E); cbn [nested_seq]; rewrite ev_Seq; unfold_eval;
       rewrite Hle; cbv beta iota; rewrite Hln; cbn [is_load]; cbv beta iota;
       cbn [sh_mem_op]; unfold sh_mem_load, sh_mem_store; rewrite ?Hln; cbv beta iota;
       rewrite ?Hsh, ?Hff;
       repeat match goal with
              | Ec : ?c = _ |- context [?c] => rewrite Ec
              end;
       cbv beta iota; rewrite ?ev_Skip; reflexivity
     | ]);
    (split; [srel S1|]); (split; [exact S2|]); (split; [exact S3|]); (split; [exact S4|]);
    (split; [reflexivity|]); cbn [nc_post]; try exact Logic.I;
    try (apply locals_rel_update; [exact Hl'|exact Hn|exact Hnd]);
    exact Hl'.
Qed.

Lemma rhss_rel (rhss : list N) ws (sl : fmap N (panSem.word_lab a)) t ctxt l :
  OPT_MMAP (FLOOKUP sl) rhss = SOME ws -> locals_rel ctxt l sl (locals t) ->
  exists nr, OPT_MMAP (FLOOKUP (vars ctxt)) rhss = SOME nr /\
             get_vars nr t = SOME (MAP wlab_wloc ws).
Proof.
  intros H Hl; revert ws H; induction rhss as [|r rs IHr]; intros ws H.
  - injection H as <-. exists []. split; reflexivity.
  - cbn [OPT_MMAP OPTION_BIND] in H.
    destruct (FLOOKUP sl r) as [x|] eqn:Ex; [|discriminate]. cbn [OPTION_BIND] in H.
    destruct (OPT_MMAP (FLOOKUP sl) rs) as [xs|] eqn:Exs; [|discriminate]. injection H as <-.
    destruct (proj2 (proj2 (proj2 Hl)) r x Ex) as (n & Hn & _ & Hlk).
    destruct (IHr xs eq_refl) as (nr & Enr & Hg).
    exists (n :: nr). cbn [OPT_MMAP OPTION_BIND get_vars MAP]. rewrite Hn, Enr, Hlk, Hg.
    split; reflexivity.
Qed.

Lemma lhss_rel (lhss : list N) (sl : fmap N (panSem.word_lab a)) tl ctxt l :
  EVERY (fun v => IS_SOME (FLOOKUP sl v)) lhss = true -> ALL_DISTINCT lhss = true ->
  locals_rel ctxt l sl tl ->
  exists nl, OPT_MMAP (FLOOKUP (vars ctxt)) lhss = SOME nl /\ LENGTH nl = LENGTH lhss /\
    Forall (fun n => n IN domain l) nl /\ ALL_DISTINCT nl = true.
Proof.
  intros He Hd Hl; induction lhss as [|v vs IHv].
  - exists []. repeat split; constructor.
  - cbn [EVERY ALL_DISTINCT] in He, Hd. apply andb_prop in He as [He1 He2].
    apply andb_prop in Hd as [Hd1 Hd2].
    destruct (FLOOKUP sl v) as [x|] eqn:Ex; [|discriminate].
    destruct (proj2 (proj2 (proj2 Hl)) v x Ex) as (n & Hn & Hnd & _).
    destruct (IHv He2 Hd2) as (nl & Enl & Len & Hdom & Hdist).
    exists (n :: nl). cbn [OPT_MMAP OPTION_BIND]. rewrite Hn, Enl.
    split; [reflexivity|]. split; [cbn [LENGTH]; rewrite Len; reflexivity|].
    split; [constructor; assumption|].
    cbn [ALL_DISTINCT]. rewrite Hdist, Bool.andb_true_r.
    destruct (MEM n nl) eqn:Em; [|reflexivity]. exfalso.
    apply MEM_In in Em. destruct (OPT_MMAP_In_res _ _ _ _ Enl Em) as (v' & Hv' & Hf).
    pose proof (proj1 Hl v v' n n (conj Hn (conj Hf eq_refl))) as ->.
    apply MEM_In in Hv'. rewrite Hv' in Hd1. discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_primop_loop_primop" *)
Theorem crep_primop_loop_primop : forall pop (ws res_ws : list (panSem.word_lab a)),
  crepSem.crep_primop pop ws = SOME res_ws ->
  loop_primop pop (MAP wlab_wloc ws) = SOME (MAP wlab_wloc res_ws).
Proof.
  intros pop ws res_ws. destruct pop. unfold crepSem.crep_primop, loop_primop.
  destruct ws as [|[l] [|[r] [|[c] [|w ws]]]]; cbn; try discriminate.
  - destruct (backend_common.word_add_carry l r c) as [res co]. intros H; injection H as <-.
    reflexivity.
  - destruct (N.eqb_spec (N.succ (N.succ (N.succ (N.succ (LENGTH ws))))) 3); [lia|].
    cbn. discriminate.
Qed.

Lemma alist_insert_insert_notin ns (ws : list (word_loc a)) (m : spt (word_loc a)) n w :
  ~ In n ns -> alist_insert ns ws (insert n w m) = insert n w (alist_insert ns ws m).
Proof.
  revert ws; induction ns as [|k ns IH]; intros [|x ws] Hn; try reflexivity.
  cbn [alist_insert]. rewrite IH by (intros Hc; apply Hn; right; exact Hc).
  apply insert_swap. intros ->. apply Hn; left; reflexivity.
Qed.

Lemma locals_rel_upd_list ctxt l : forall (lhss : list N) nl (vs : list (panSem.word_lab a)) sl tl,
  locals_rel ctxt l sl tl -> OPT_MMAP (FLOOKUP (vars ctxt)) lhss = SOME nl ->
  Forall (fun n => n IN domain l) nl -> ALL_DISTINCT nl = true -> LENGTH lhss = LENGTH vs ->
  locals_rel ctxt l (sl |++ ZIP (lhss, vs)) (alist_insert nl (MAP wlab_wloc vs) tl).
Proof.
  induction lhss as [|x xs IH]; intros nl vs sl tl Hl Enl Hdom Hdist Hlen.
  - injection Enl as <-. destruct vs; [exact Hl|cbn in Hlen; lia].
  - destruct vs as [|v vs]; [cbn in Hlen; lia|].
    cbn [OPT_MMAP OPTION_BIND] in Enl.
    destruct (FLOOKUP (vars ctxt) x) as [n|] eqn:Ex; [|discriminate]. cbn [OPTION_BIND] in Enl.
    destruct (OPT_MMAP (FLOOKUP (vars ctxt)) xs) as [ns|] eqn:Exs; [|discriminate].
    injection Enl as <-.
    inversion Hdom as [|? ? Hnd Hdom']; subst.
    cbn [ALL_DISTINCT] in Hdist. apply andb_prop in Hdist as [Hd1 Hd2].
    assert (Hnin : ~ In n ns) by (intros Hc; apply MEM_In in Hc; rewrite Hc in Hd1; discriminate).
    change (sl |++ ZIP (x :: xs, v :: vs)) with ((sl |+ (x, v)) |++ ZIP (xs, vs)).
    cbn [MAP alist_insert]. rewrite <- alist_insert_insert_notin by exact Hnin.
    apply (IH ns vs); [|reflexivity|exact Hdom'|exact Hd2|cbn in Hlen; lia].
    apply locals_rel_update; assumption.
Qed.

Lemma nc_Primitive s lhss pop rhss : nc_P (crepLang.Primitive lhss pop rhss) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (OPT_MMAP (FLOOKUP (crepSem.locals s)) rhss) as [ws|] eqn:Er;
    [|injection H as <- _; congruence].
  destruct (crepSem.crep_primop pop ws) as [rws|] eqn:Ep; [|injection H as <- _; congruence].
  destruct (LENGTH lhss =? LENGTH rws) eqn:El; [|injection H as <- _; congruence].
  destruct (EVERY _ lhss) eqn:Ee; [|injection H as <- _; congruence].
  destruct (ALL_DISTINCT lhss) eqn:Ed; [|injection H as <- _; congruence].
  cbn [andb] in H. injection H as <- <-.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  destruct (rhss_rel rhss ws _ t ctxt l Er R5) as (nr & Enr & Hg).
  destruct (lhss_rel lhss _ _ ctxt l Ee Ed R5) as (nl & Enl & Len & Hdom & Hdist).
  apply N.eqb_eq in El.
  exists 0, NONE, (set_vars nl (MAP wlab_wloc rws) t).
  rewrite set_clock_add0. split.
  { cbn [compile]. rewrite Enl, Enr. unfold_eval.
    rewrite Hg, (crep_primop_loop_primop _ _ _ Ep).
    replace (LENGTH nl =? LENGTH (MAP wlab_wloc rws)) with true; [reflexivity|].
    symmetry; apply N.eqb_eq. rewrite Len, El, !LENGTH_length, length_map. reflexivity. }
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [reflexivity|].
  apply locals_rel_upd_list; assumption.
Qed.

Lemma read_bytearray_rel {B} (f g : word a -> option B) :
  (forall x b, f x = SOME b -> g x = SOME b) ->
  forall n w bs, read_bytearray w n f = SOME bs -> read_bytearray w n g = SOME bs.
Proof.
  intros Hfg n; induction n as [|n IH] using N.peano_ind; intros w bs H.
  - rewrite (proj1 (read_bytearray_def w f 0)) in H. rewrite (proj1 (read_bytearray_def w g 0)).
    exact H.
  - rewrite (proj2 (read_bytearray_def w f n)) in H. rewrite (proj2 (read_bytearray_def w g n)).
    destruct (f w) as [b|] eqn:Ef; [|discriminate]. rewrite (Hfg _ _ Ef).
    destruct (read_bytearray (w + n2w 1)%w n f) as [bs'|] eqn:Er; [|discriminate].
    rewrite (IH _ _ Er). exact H.
Qed.

Lemma nc_ExtCall s f ptr1 len1 ptr2 len2 : nc_P (crepLang.ExtCall f ptr1 len1 ptr2 len2) s.
Proof.
  intros res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (FLOOKUP (crepSem.locals s) len1) as [[w]|] eqn:E1; [|injection H as <- _; congruence].
  destruct (FLOOKUP (crepSem.locals s) ptr1) as [[w2]|] eqn:E2; [|injection H as <- _; congruence].
  destruct (FLOOKUP (crepSem.locals s) len2) as [[w3]|] eqn:E3; [|injection H as <- _; congruence].
  destruct (FLOOKUP (crepSem.locals s) ptr2) as [[w4]|] eqn:E4; [|injection H as <- _; congruence].
  destruct (read_bytearray w2 (w2n w) _) as [bytes|] eqn:Eb1; [|injection H as <- _; congruence].
  destruct (read_bytearray w4 (w2n w3) _) as [bytes2|] eqn:Eb2; [|injection H as <- _; congruence].
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  destruct (proj2 (proj2 (proj2 R5)) _ _ E1) as (lc & Hlc & _ & Llc).
  destruct (proj2 (proj2 (proj2 R5)) _ _ E2) as (pc & Hpc & _ & Lpc).
  destruct (proj2 (proj2 (proj2 R5)) _ _ E3) as (lc' & Hlc' & _ & Llc').
  destruct (proj2 (proj2 (proj2 R5)) _ _ E4) as (pc' & Hpc' & _ & Lpc').
  cbn [wlab_wloc] in Llc, Lpc, Llc', Lpc'.
  assert (Hsub : domain l SUBSET domain (locals t)) by apply R5.
  assert (Hmem : forall x b, panSem.mem_load_byte (crepSem.memory s) (crepSem.memaddrs s)
                               (crepSem.be s) x = SOME b ->
                 mem_load_byte_aux (memory t) (mdomain t) (be t) x = SOME b).
  { intros x b Hx. rewrite <- (proj1 R1), <- (proj1 (proj2 (proj2 (proj2 R1)))).
    exact (mem_load_byte_rel _ _ _ _ _ _ R2 Hx). }
  pose proof (read_bytearray_rel _ _ Hmem _ _ _ Eb1) as Tb1.
  pose proof (read_bytearray_rel _ _ Hmem _ _ _ Eb2) as Tb2.
  assert (Hff : ffi t = crepSem.ffi s) by (symmetry; apply R1).
  cbn [compile]. rewrite Hpc, Hlc, Hpc', Hlc'.
  destruct (call_FFI (crepSem.ffi s) (ffi.ExtCall f) bytes bytes2) as [nf nb|o] eqn:Ef;
    injection H as <- <-.
  - exists 0, NONE,
      (set_ffi nf (set_memory (write_bytearray w4 nb (memory t) (mdomain t) (be t))
                     (set_locals (inter (locals t) l) t))).
    rewrite set_clock_add0. split.
    { unfold_eval. rewrite Llc, Lpc, Llc', Lpc'. unfold cut_state.
      destruct (classical_dec _) as [_|Hn]; [|contradiction].
      cbv beta iota. cbn [set_locals memory mdomain be ffi]. rewrite Tb1, Tb2, Hff, Ef.
      reflexivity. }
    split; [srel R1|]. split.
    { cbn [crepSem.set_ffi crepSem.set_memory crepSem.memory crepSem.memaddrs crepSem.be
           set_ffi set_memory set_locals memory].
      rewrite (proj1 R1), (proj1 (proj2 (proj2 (proj2 R1)))).
      apply write_bytearray_mem_rel. rewrite <- (proj1 R1). exact R2. }
    split; [exact R3|]. split; [exact R4|]. split; [reflexivity|].
    destruct R5 as (Hd & Hm & Hs & Hl). split; [exact Hd|]. split; [exact Hm|]. split.
    + intros k Hk. unfold pred_set.IN in *. cbn [set_ffi set_memory set_locals locals].
      rewrite domain_inter. split; [exact (Hs k Hk)|exact Hk].
    + intros vn x Hx. destruct (Hl vn x Hx) as (k & Hk & Hkd & Hlk). exists k.
      split; [exact Hk|]. split; [exact Hkd|].
      cbn [set_ffi set_memory set_locals locals]. rewrite lookup_inter_alt.
      destruct (decide _); [exact Hlk|contradiction].
  - exists 0, (SOME (FinalFFI o)), (call_env [] (set_locals (inter (locals t) l) t)).
    rewrite set_clock_add0. split.
    { unfold_eval. rewrite Llc, Lpc, Llc', Lpc'. unfold cut_state.
      destruct (classical_dec _) as [_|Hn]; [|contradiction].
      cbv beta iota. cbn [set_locals memory mdomain be ffi]. rewrite Tb1, Tb2, Hff, Ef.
      reflexivity. }
    split; [srel R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split; [reflexivity|exact Logic.I].
Qed.

Lemma locals_rel_cut ctxt l (sl : fmap N (panSem.word_lab a)) tl :
  locals_rel ctxt l sl tl -> locals_rel ctxt l sl (inter tl l).
Proof.
  intros (Hd & Hm & Hs & Hl). split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk. unfold pred_set.IN in *. rewrite domain_inter. split; [exact (Hs k Hk)|exact Hk].
  - intros vn x Hx. destruct (Hl vn x Hx) as (k & Hk & Hkd & Hlk). exists k.
    split; [exact Hk|]. split; [exact Hkd|].
    rewrite lookup_inter_alt. destruct (decide _); [exact Hlk|contradiction].
Qed.

Lemma ev_add1 (p : loopLang.prog a) t res st k :
  evaluate (p, set_clock (clock t + k) t) = (res, st) -> res <> SOME TimeOut ->
  forall j, evaluate (p, set_clock (clock t + (k + j)) t) = (res, set_clock (clock st + j) st).
Proof.
  intros E Hr j. pose proof (evaluate_add_clock_eq _ _ _ _ j (conj E Hr)) as E'.
  rewrite set_clock_set_clock in E'. cbn [clock set_clock] in E'. rewrite N.add_assoc. exact E'.
Qed.

Lemma nc_If s e c1 c2 :
  (forall p' s', crepSem.eval_lt (p', s') (crepLang.If e c1 c2, s) -> nc_P p' s') ->
  nc_P (crepLang.If e c1 c2) s.
Proof.
  intros IH res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s e) as [[w]|] eqn:Ee; [|injection H as <- _; congruence].
  set (c := if negb (bool_decide (w = n2w 0)) then c1 else c2) in H.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [np [le [tmp nl]]] eqn:C.
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C) as (Ok & Le & El).
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exp_preserves_eval s e _ t ctxt (vmax ctxt + 1) l np le tmp nl
              (conj Ee (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck1 & st & E & Hle & S1 & S2 & S3 & S4 & S5).
  cbn [wlab_wloc] in Hle.
  rewrite El in S5. pose proof (locals_back ctxt l _ _ _ np R5 Ok S5) as Hl'.
  set (st' := set_var tmp (Word w) st).
  assert (Hr' : rels s st' ctxt l).
  { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
    apply locals_rel_insert_gt_vmax. split; [exact Hl'|lia]. }
  destruct (IH c s ltac:(unfold c; destruct (negb _); crepProps.lt_tac) res s1 st' ctxt l H Hne Hr')
    as (ck2 & q & t1 & T & Q1 & Q2 & Q3 & Q4 & Eq & P).
  assert (Hbr : forall k, evaluate (nested_seq (np ++ [Assign tmp le;
                   If NotEqual tmp (Imm (n2w 0)) (compile ctxt l c1) (compile ctxt l c2) l]),
                   set_clock (clock t + (ck1 + k)) t) =
                 let '(r, s0) := cut_res l (evaluate (compile ctxt l c, set_clock (clock st + k) st'))
                 in match r with NONE => evaluate (Skip, s0) | _ => (r, s0) end).
  { intros k. assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
    rewrite (ev_nested_app _ _ _ _ (ev_add1 _ _ _ _ _ E Hnt k)). cbn [nested_seq].
    rewrite ev_Seq, (ev_Assign _ _ _ (Word w)) by (rewrite eval_set_clock; exact Hle).
    cbv beta iota. rewrite ev_Seq. unfold_eval.
    cbn [set_var set_locals set_clock locals get_var_imm]. rewrite lookup_insert.
    destruct (decide (tmp = tmp)) as [_|]; [|congruence]. cbv beta iota zeta.
    cbn [word_cmp]. unfold c. destruct (negb _); reflexivity. }
  destruct res as [r|].
  - exists (ck1 + ck2), q, t1. split.
    + rewrite Hbr. change (clock st) with (clock st'). rewrite T. subst q.
      destruct r; reflexivity.
    + repeat (split; [assumption|]). exact P.
  - cbn [nc_res nc_post] in Eq, P. subst q.
    assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
    pose proof (ev_add1 _ _ _ _ _ T Hnt 1) as T1.
    exists (ck1 + (ck2 + 1)), NONE,
      (dec_clock (set_locals (inter (locals t1) l) (set_clock (clock t1 + 1) t1))).
    split.
    + rewrite Hbr. change (clock st) with (clock st'). rewrite T1.
      cbn [cut_res IS_SOME]. unfold cut_state. cbn [locals set_clock].
      destruct (classical_dec _) as [_|Hn]; [|exfalso; apply Hn; apply P].
      match goal with |- context [(clock ?x =? 0)] =>
        replace (clock x =? 0) with false
          by (symmetry; apply N.eqb_neq; cbn [clock set_clock set_locals]; lia) end.
      cbv beta iota. apply ev_Skip.
    + split.
      { destruct Q1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold state_rel. loop_cbn.
        repeat split; try assumption. lia. }
      split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [reflexivity|].
      apply locals_rel_cut. exact P.
Qed.

Definition dec_ctxt (ctxt : context) (v tmp : N) : context :=
  {| vars := vars ctxt |+ (v, tmp); funcs := funcs ctxt; vmax := tmp; target := target ctxt |}.

Lemma dec_ctxt_max ctxt v tmp :
  ctxt_max (vmax ctxt) (vars ctxt) -> vmax ctxt < tmp ->
  ctxt_max (vmax (dec_ctxt ctxt v tmp)) (vars (dec_ctxt ctxt v tmp)).
Proof.
  intros Hm Hv v' m Hf. cbn [dec_ctxt vars vmax] in *. rewrite FLOOKUP_UPDATE in Hf.
  destruct (decide _); [injection Hf as <-; lia|]. specialize (Hm _ _ Hf). lia.
Qed.

Lemma dec_locals_rel ctxt l (sl : fmap N (panSem.word_lab a)) tl v tmp value :
  locals_rel ctxt l sl tl -> vmax ctxt < tmp ->
  locals_rel (dec_ctxt ctxt v tmp) (insert tmp tt l) (sl |+ (v, value))
    (insert tmp (wlab_wloc value) tl).
Proof.
  intros (Hd & Hm & Hs & Hl) Hv. split; [|split; [|split]].
  - intros x y n m (Hx & Hy & <-). cbn [dec_ctxt vars] in Hx, Hy.
    rewrite FLOOKUP_UPDATE in Hx, Hy.
    destruct (decide (v = x)) as [<-|Hxv]; destruct (decide (v = y)) as [<-|Hyv]; try reflexivity.
    + injection Hx as <-. specialize (Hm _ _ Hy). lia.
    + injection Hy as ->. specialize (Hm _ _ Hx). lia.
    + exact (Hd x y n n (conj Hx (conj Hy eq_refl))).
  - apply dec_ctxt_max; assumption.
  - intros k Hk. unfold pred_set.IN in *. rewrite domain_insert in Hk. rewrite domain_insert.
    destruct Hk as [->|Hk]; [left; reflexivity|right; exact (Hs k Hk)].
  - intros vn x Hx. cbn [dec_ctxt vars]. rewrite FLOOKUP_UPDATE in Hx. rewrite FLOOKUP_UPDATE.
    destruct (decide (v = vn)) as [<-|Hne].
    + injection Hx as <-. exists tmp. split; [reflexivity|]. split.
      * unfold pred_set.IN. rewrite domain_insert. left; reflexivity.
      * rewrite lookup_insert. destruct (decide (tmp = tmp)); [reflexivity|congruence].
    + destruct (Hl vn x Hx) as (n & Hn & Hnd & Hlk). exists n. split; [exact Hn|]. split.
      * unfold pred_set.IN in *. rewrite domain_insert. right; exact Hnd.
      * rewrite lookup_insert. destruct (decide (n = tmp)); [|exact Hlk].
        specialize (Hm _ _ Hn). lia.
Qed.

Lemma dec_post ctxt l v tmp (sl : fmap N (panSem.word_lab a)) tl old :
  distinct_vars (vars ctxt) -> ctxt_max (vmax ctxt) (vars ctxt) -> vmax ctxt < tmp ->
  locals_rel (dec_ctxt ctxt v tmp) (insert tmp tt l) sl tl ->
  (forall pv, old = SOME pv ->
     exists n0, FLOOKUP (vars ctxt) v = SOME n0 /\ n0 IN domain l /\
                lookup n0 tl = SOME (wlab_wloc pv)) ->
  locals_rel ctxt l (crepSem.res_var sl (v, old)) tl.
Proof.
  intros Hd Hm Hv (_ & _ & Hs & Hl) Hold. split; [exact Hd|]. split; [exact Hm|]. split.
  - intros k Hk. apply Hs. unfold pred_set.IN in *. rewrite domain_insert. right; exact Hk.
  - intros vn x Hx. rewrite crepProps.FLOOKUP_res_var in Hx. destruct (decide (vn = v)) as [->|Hne].
    + exact (Hold x Hx).
    + destruct (Hl vn x Hx) as (n & Hn & Hnd & Hlk). cbn [dec_ctxt vars] in Hn.
      rewrite FLOOKUP_UPDATE in Hn. destruct (decide (v = vn)) as [->|_]; [congruence|].
      exists n. split; [exact Hn|]. split; [|exact Hlk].
      unfold pred_set.IN in *. rewrite domain_insert in Hnd. destruct Hnd as [->|Hnd]; [|exact Hnd].
      specialize (Hm _ _ Hn). lia.
Qed.

Lemma nc_Dec s v e prog :
  (forall p' s', crepSem.eval_lt (p', s') (crepLang.Dec v e prog, s) -> nc_P p' s') ->
  nc_P (crepLang.Dec v e prog) s.
Proof.
  intros IH res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s e) as [value|] eqn:Ee; [|injection H as <- _; congruence].
  set (sv := crepSem.set_locals (crepSem.locals s |+ (v, value)) s) in H.
  destruct (crepSem.evaluate (prog, sv)) as [r0 st0] eqn:Ep. injection H as <- <-.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [p [le [tmp nl]]] eqn:C.
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C) as (Ok & Le & El).
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exp_preserves_eval s e _ t ctxt (vmax ctxt + 1) l p le tmp nl
              (conj Ee (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck1 & st & E & Hle & S1 & S2 & S3 & S4 & S5).
  rewrite El in S5. pose proof (locals_back ctxt l _ _ _ p R5 Ok S5) as Hl'.
  set (st1 := set_var tmp (wlab_wloc value) st).
  assert (Hvt : vmax ctxt < tmp) by lia.
  assert (Hr1 : rels sv st1 (dec_ctxt ctxt v tmp) (insert tmp tt l)).
  { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
    apply dec_locals_rel; assumption. }
  destruct (IH prog sv ltac:(unfold sv; crepProps.lt_tac) r0 st0 st1 _ _ Ep Hne Hr1)
    as (ck2 & q & t1 & T & Q1 & Q2 & Q3 & Q4 & Eq & P).
  exists (ck1 + ck2), q, t1. split.
  { rewrite ev_Seq.
    assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
    rewrite (ev_add1 _ _ _ _ _ E Hnt ck2). cbv beta iota.
    rewrite ev_Seq, (ev_Assign _ _ _ (wlab_wloc value)) by (rewrite eval_set_clock; exact Hle).
    cbv beta iota. rewrite set_var_set_clock. change (clock st) with (clock st1).
    exact T. }
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Eq|].
  assert (Hpost : (r0 = NONE \/ (exists n, r0 = SOME (crepSem.Break n)) \/
                   (exists n, r0 = SOME (crepSem.Continue n))) ->
                  locals_rel ctxt l (crepSem.res_var (crepSem.locals st0)
                                       (v, FLOOKUP (crepSem.locals s) v)) (locals t1)).
  { intros Hr0.
    assert (P' : locals_rel (dec_ctxt ctxt v tmp) (insert tmp tt l) (crepSem.locals st0) (locals t1))
      by (destruct Hr0 as [->|[[n ->]|[n ->]]]; exact P).
    apply (dec_post ctxt l v tmp); [apply R5|apply R5|exact Hvt|exact P'|].
    intros pv Hpv. destruct (proj2 (proj2 (proj2 R5)) v pv Hpv) as (n0 & Hn0 & Hn0d & _).
    exists n0. split; [exact Hn0|]. split; [exact Hn0d|].
    pose proof (lookup_of_locals_rel ctxt l _ _ v pv n0 Hl' Hpv Hn0) as Hlk.
    assert (Hn0t : n0 <> tmp) by (pose proof (proj1 (proj2 R5) _ _ Hn0); lia).
    rewrite (unassigned_vars_evaluate_same (compile (dec_ctxt ctxt v tmp) (insert tmp tt l) prog)
                  (set_clock (clock st1 + ck2) st1) q t1 n0 (wlab_wloc pv)).
    - cbn [set_clock locals st1 set_var set_locals]. rewrite lookup_insert.
      destruct (decide (n0 = tmp)); [contradiction|exact Hlk].
    - split; [exact T|]. split.
      { subst q. destruct Hr0 as [->|[[n ->]|[n ->]]]; cbn [nc_res];
          [left; reflexivity|right; right; eexists; reflexivity|right; left; eexists; reflexivity]. }
      split.
      { cbn [set_clock locals st1 set_var set_locals]. rewrite lookup_insert.
        destruct (decide (n0 = tmp)); [contradiction|exact Hlk]. }
      split.
      { apply not_mem_context_assigned_mem_gt. split; [apply dec_ctxt_max; [apply R5|exact Hvt]|].
        split; [|cbn [dec_ctxt vmax]; pose proof (proj1 (proj2 R5) _ _ Hn0); lia].
        intros v' m Hf. cbn [dec_ctxt vars] in Hf. rewrite FLOOKUP_UPDATE in Hf.
        destruct (decide (v = v')) as [->|Hne'].
        - injection Hf as <-. exact Hn0t.
        - intros Heq. apply Hne'. rewrite <- Heq in Hf.
          exact (proj1 R5 v v' n0 n0 (conj Hn0 (conj Hf eq_refl))). }
      apply member_cutset_survives_comp_prog. unfold pred_set.IN in *. rewrite domain_insert.
      right; exact Hn0d. }
  destruct r0 as [[]|]; cbn [nc_post]; try exact Logic.I.
  - congruence.
  - apply Hpost; right; left; eexists; reflexivity.
  - apply Hpost; right; right; eexists; reflexivity.
  - apply Hpost; left; reflexivity.
Qed.

Lemma loop_state_ext (s t : state a ffi_t) :
  locals s = locals t -> globals s = globals t -> memory s = memory t ->
  mdomain s = mdomain t -> sh_mdomain s = sh_mdomain t -> clock s = clock t ->
  code s = code t -> be s = be t -> ffi s = ffi t -> base_addr s = base_addr t ->
  top_addr s = top_addr t -> s = t.
Proof. destruct s, t; cbn; intros; subst; reflexivity. Qed.

Lemma ev_while_body (np : list (loopLang.prog a)) le tmp lp (l : num_set) (u st : state a ffi_t) (w : word a) ck1 :
  evaluate (nested_seq np, set_clock (clock u + ck1) u) = (NONE, st) ->
  eval st le = SOME (Word w) ->
  forall K : N,
  evaluate (nested_seq (np ++ [Assign tmp le;
              If NotEqual tmp (Imm (n2w 0)) (Seq lp (loopLang.Continue 0)) (loopLang.Break 0) l]),
            set_clock (clock u + (ck1 + K)) u) =
  let '(r, s0) := cut_res l (evaluate (if negb (bool_decide (w = n2w 0))
                                        then Seq lp (loopLang.Continue 0) else loopLang.Break 0,
                                        set_clock (clock st + K) (set_var tmp (Word w) st))) in
  match r with NONE => evaluate (Skip, s0) | _ => (r, s0) end.
Proof.
  intros E Hle K. assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
  rewrite (ev_nested_app _ _ _ _ (ev_add1 _ _ _ _ _ E Hnt K)). cbn [nested_seq].
  rewrite ev_Seq, (ev_Assign _ _ _ (Word w)) by (rewrite eval_set_clock; exact Hle).
  cbv beta iota. rewrite ev_Seq. unfold_eval.
  cbn [set_var set_locals set_clock locals get_var_imm]. rewrite lookup_insert.
  destruct (decide (tmp = tmp)) as [_|]; [|congruence]. cbv beta iota zeta.
  cbn [word_cmp]. rewrite <- set_var_set_clock. reflexivity.
Qed.

Lemma ev_Loop_eq (live_in live_out : num_set) (body : loopLang.prog a) t :
  evaluate (Loop live_in body live_out, t) =
  match cut_res live_in (NONE, t) with
  | (NONE, s) =>
      match evaluate (body, s) with
      | (NONE, s) => evaluate (Loop live_in body live_out, s)
      | (SOME (Continue 0), s) => evaluate (Loop live_in body live_out, s)
      | (SOME (Break 0), s) => cut_res live_out (NONE, s)
      | (res, s) => (exit_loop res, s)
      end
  | res => res
  end.
Proof.
  destruct (@evaluate_def a ffi_t) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&HL&_). apply HL.
Qed.

Lemma cut_entry (l : num_set) t ck :
  domain l SUBSET domain (locals t) -> clock t <> 0 ->
  cut_res l (NONE, set_clock (clock t + ck) t) =
  (NONE, set_clock (clock (dec_clock (set_locals (inter (locals t) l) t)) + ck)
           (dec_clock (set_locals (inter (locals t) l) t))).
Proof.
  intros Hs Hc. cbn [cut_res IS_SOME]. unfold cut_state. cbn [locals set_clock].
  destruct (classical_dec _) as [_|Hn]; [|contradiction].
  match goal with |- context [(clock ?x =? 0)] =>
    replace (clock x =? 0) with false
      by (symmetry; apply N.eqb_neq; cbn [clock set_clock set_locals]; lia) end.
  f_equal. apply loop_state_ext; loop_cbn; try reflexivity. lia.
Qed.

Lemma cut_entry2 (l : num_set) t ck :
  domain l SUBSET domain (locals t) ->
  cut_res l (NONE, set_clock (clock t + (ck + 1)) t) =
  (NONE, set_clock (clock (set_locals (inter (locals t) l) t) + ck)
           (set_locals (inter (locals t) l) t)).
Proof.
  intros Hs. cbn [cut_res IS_SOME]. unfold cut_state. cbn [locals set_clock].
  destruct (classical_dec _) as [_|Hn]; [|contradiction].
  match goal with |- context [(clock ?x =? 0)] =>
    replace (clock x =? 0) with false
      by (symmetry; apply N.eqb_neq; cbn [clock set_clock set_locals]; lia) end.
  f_equal. apply loop_state_ext; loop_cbn; try reflexivity. lia.
Qed.

Lemma cut_exit (l : num_set) t :
  domain l SUBSET domain (locals t) ->
  cut_res l (NONE, set_clock (clock t + 1) t) =
  (NONE, set_locals (inter (locals t) l) t).
Proof.
  intros Hs. cbn [cut_res IS_SOME]. unfold cut_state. cbn [locals set_clock].
  destruct (classical_dec _) as [_|Hn]; [|contradiction].
  match goal with |- context [(clock ?x =? 0)] =>
    replace (clock x =? 0) with false
      by (symmetry; apply N.eqb_neq; cbn [clock set_clock set_locals]; lia) end.
  f_equal. apply loop_state_ext; loop_cbn; try reflexivity. lia.
Qed.

Lemma nc_While s e c :
  (forall p' s', crepSem.eval_lt (p', s') (crepLang.While e c, s) -> nc_P p' s') ->
  nc_P (crepLang.While e c) s.
Proof.
  intros IH res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (crepSem.eval s e) as [[w]|] eqn:Ee; [|injection H as <- _; congruence].
  assert (Hk : crepSem.clock s = clock t) by apply (rels_clock _ _ _ _ Hr).
  assert (Hsub : domain l SUBSET domain (locals t)) by apply Hr.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  cbn [compile].
  destruct (compile_exp ctxt (vmax ctxt + 1) l e) as [np [le [tmp nl]]] eqn:C.
  destruct (compile_exp_out_rel _ _ _ _ _ _ _ _ C) as (Ok & Le & El).
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (negb (bool_decide (w = n2w 0))) eqn:Ew.
  - destruct (crepSem.clock s =? 0) eqn:Ec.
    + (* time out *)
      injection H as <- <-. apply N.eqb_eq in Ec.
      exists 0, (SOME TimeOut), (set_locals LN (set_locals (inter (locals t) l) t)).
      rewrite set_clock_add0. split.
      { rewrite ev_Loop_eq. cbn [cut_res IS_SOME]. unfold cut_state.
        destruct (classical_dec _) as [_|Hn]; [|contradiction].
        match goal with |- context [(clock ?x =? 0)] =>
          replace (clock x =? 0) with true
            by (symmetry; apply N.eqb_eq; cbn [clock set_locals]; lia) end.
        reflexivity. }
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
      split; reflexivity.
    + (* iterate *)
      apply N.eqb_neq in Ec.
      set (u := dec_clock (set_locals (inter (locals t) l) t)).
      assert (Hru : rels (crepSem.dec_clock s) u ctxt l).
      { split; [unfold u; pose proof R1 as R1'; srel R1'|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
        apply locals_rel_cut; exact R5. }
      assert (Ee' : crepSem.eval (crepSem.dec_clock s) e = SOME (panSem.Word w))
        by (rewrite crepProps.eval_dec_clock; exact Ee).
      destruct Hru as (U1 & U2 & U3 & U4 & U5).
      destruct (comp_exp_preserves_eval (crepSem.dec_clock s) e _ u ctxt (vmax ctxt + 1) l np le tmp nl
                  (conj Ee' (conj U1 (conj U2 (conj U3 (conj U4 (conj U5 (conj C Hv))))))))
        as (ck1 & st & E & Hle & S1 & S2 & S3 & S4 & S5).
      cbn [wlab_wloc] in Hle.
      rewrite El in S5. pose proof (locals_back ctxt l _ _ _ np U5 Ok S5) as Hl'.
      set (st' := set_var tmp (Word w) st).
      assert (Hr' : rels (crepSem.dec_clock s) st' ctxt l).
      { split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
        apply locals_rel_insert_gt_vmax. split; [exact Hl'|lia]. }
      destruct (crepSem.evaluate (c, crepSem.dec_clock s)) as [r s1'] eqn:Ecv.
      assert (Hrne : r <> SOME crepSem.Error)
        by (intros ->; cbn in H; injection H as <- _; congruence).
      destruct (IH c (crepSem.dec_clock s) ltac:(crepProps.lt_tac) r s1' st' ctxt l Ecv Hrne Hr')
        as (ck2 & q & t2 & T & Q1 & Q2 & Q3 & Q4 & Eq & P).
      pose proof (ev_while_body np le tmp (compile ctxt l c) l u st w ck1 E Hle) as HB.
      rewrite Ew in HB.
      assert (Htop : forall K, evaluate (Loop l (nested_seq (np ++ [Assign tmp le;
                         If NotEqual tmp (Imm (n2w 0)) (Seq (compile ctxt l c) (loopLang.Continue 0))
                            (loopLang.Break 0) l])) l, set_clock (clock t + (ck1 + K)) t) =
                       match (let '(r, s0) := cut_res l (evaluate (Seq (compile ctxt l c) (loopLang.Continue 0),
                                                set_clock (clock st' + K) st')) in
                              match r with NONE => evaluate (Skip, s0) | _ => (r, s0) end) with
                       | (NONE, s) => evaluate (Loop l (nested_seq (np ++ [Assign tmp le;
                         If NotEqual tmp (Imm (n2w 0)) (Seq (compile ctxt l c) (loopLang.Continue 0))
                            (loopLang.Break 0) l])) l, s)
                       | (SOME (Continue 0), s) => evaluate (Loop l (nested_seq (np ++ [Assign tmp le;
                         If NotEqual tmp (Imm (n2w 0)) (Seq (compile ctxt l c) (loopLang.Continue 0))
                            (loopLang.Break 0) l])) l, s)
                       | (SOME (Break 0), s) => cut_res l (NONE, s)
                       | (res, s) => (exit_loop res, s)
                       end).
      { intros K. rewrite ev_Loop_eq, cut_entry by (first [exact Hsub|rewrite <- Hk; exact Ec]).
        cbv beta iota. change (dec_clock (set_locals (inter (locals t) l) t)) with u.
        rewrite HB. reflexivity. }
      assert (Hnt : forall r', q = SOME r' -> r' <> TimeOut ->
                    forall j, evaluate (compile ctxt l c, set_clock (clock st' + (ck2 + j)) st') =
                              (q, set_clock (clock t2 + j) t2))
        by (intros r' -> Hr'' j; apply ev_add1; [exact T|intros Hc; injection Hc as Hc; exact (Hr'' Hc)]).
      destruct r as [[ | | k | k | vs | eid | f]|]; subst q.
      * congruence.
      * (* TimeOut *)
        injection H as <- <-. exists (ck1 + ck2), (SOME TimeOut), t2. split.
        { rewrite Htop, ev_Seq. rewrite T. reflexivity. }
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
      * (* Break *)
        destruct k as [|k].
        -- injection H as <- <-.
           exists (ck1 + (ck2 + 1)), NONE, (set_locals (inter (locals t2) l) t2). split.
           { rewrite Htop, ev_Seq. rewrite (Hnt (Break 0) eq_refl ltac:(discriminate) 1).
             cbn beta iota. cbn [cut_res IS_SOME]. apply cut_exit. apply P. }
           split; [srel Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
           split; [reflexivity|]. apply locals_rel_cut. exact P.
        -- injection H as <- <-. exists (ck1 + ck2), (SOME (Break (N.pos k - 1))), t2. split.
           { rewrite Htop, ev_Seq. replace (clock st' + ck2) with (clock st' + (ck2 + 0)) by lia.
             rewrite (Hnt (Break (N.pos k)) eq_refl ltac:(discriminate) 0). rewrite N.add_0_r, set_clock_id. reflexivity. }
           split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
           split; [reflexivity|exact P].
      * (* Continue *)
        destruct k as [|k].
        -- assert (Hlt : crepSem.eval_lt (crepLang.While e c, s1') (crepLang.While e c, s)).
           { pose proof (crepSem.evaluate_clock _ _ _ _ Ecv) as Hc1.
             unfold crepSem.eval_lt. cbn [fst snd]. left. cbn [crepSem.dec_clock crepSem.set_clock
               crepSem.clock] in Hc1. lia. }
           destruct (IH _ _ Hlt res s1 t2 ctxt l H Hne
                       (conj Q1 (conj Q2 (conj Q3 (conj Q4 P)))))
             as (ck3 & q3 & t3 & T3 & W1 & W2 & W3 & W4 & Eq3 & P3).
           exists (ck1 + (ck2 + ck3)), q3, t3. split.
           { rewrite Htop, ev_Seq. rewrite (Hnt (Continue 0) eq_refl ltac:(discriminate) ck3).
             cbn [nc_res cut_res IS_SOME]. cbv beta iota zeta. cbn [compile] in T3.
             rewrite C in T3. exact T3. }
           repeat (split; [assumption|]). exact P3.
        -- injection H as <- <-. exists (ck1 + ck2), (SOME (Continue (N.pos k - 1))), t2. split.
           { rewrite Htop, ev_Seq. replace (clock st' + ck2) with (clock st' + (ck2 + 0)) by lia.
             rewrite (Hnt (Continue (N.pos k)) eq_refl ltac:(discriminate) 0). rewrite N.add_0_r, set_clock_id. reflexivity. }
           split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
           split; [reflexivity|exact P].
      * (* Return *)
        injection H as <- <-. exists (ck1 + ck2), (SOME (Result (MAP wlab_wloc vs))), t2. split.
        { rewrite Htop, ev_Seq. rewrite T. reflexivity. }
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
      * (* Exception *)
        injection H as <- <-. exists (ck1 + ck2), (SOME (Exception (Word eid))), t2. split.
        { rewrite Htop, ev_Seq. rewrite T. reflexivity. }
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
      * (* FinalFFI *)
        injection H as <- <-. exists (ck1 + ck2), (SOME (FinalFFI f)), t2. split.
        { rewrite Htop, ev_Seq. rewrite T. reflexivity. }
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
      * (* NONE *)
        assert (Hlt : crepSem.eval_lt (crepLang.While e c, s1') (crepLang.While e c, s)).
        { pose proof (crepSem.evaluate_clock _ _ _ _ Ecv) as Hc1.
          unfold crepSem.eval_lt. cbn [fst snd]. left. cbn [crepSem.dec_clock crepSem.set_clock
            crepSem.clock] in Hc1. lia. }
        destruct (IH _ _ Hlt res s1 t2 ctxt l H Hne (conj Q1 (conj Q2 (conj Q3 (conj Q4 P)))))
          as (ck3 & q3 & t3 & T3 & W1 & W2 & W3 & W4 & Eq3 & P3).
        exists (ck1 + (ck2 + ck3)), q3, t3. split.
        { rewrite Htop, ev_Seq.
          assert (Hnt0 : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
          rewrite (ev_add1 _ _ _ _ _ T Hnt0 ck3). cbv beta iota.
          unfold_eval. cbv beta iota. cbn [cut_res IS_SOME]. cbv beta iota zeta.
          cbn [compile] in T3. rewrite C in T3. exact T3. }
        repeat (split; [assumption|]). exact P3.
  - (* condition false *)
    injection H as <- <-.
    set (u := set_locals (inter (locals t) l) t).
    assert (Hru : rels s u ctxt l).
    { split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
      apply locals_rel_cut; exact R5. }
    destruct Hru as (U1 & U2 & U3 & U4 & U5).
    destruct (comp_exp_preserves_eval s e _ u ctxt (vmax ctxt + 1) l np le tmp nl
                (conj Ee (conj U1 (conj U2 (conj U3 (conj U4 (conj U5 (conj C Hv))))))))
      as (ck1 & st & E & Hle & S1 & S2 & S3 & S4 & S5).
    cbn [wlab_wloc] in Hle.
    rewrite El in S5. pose proof (locals_back ctxt l _ _ _ np U5 Ok S5) as Hl'.
    pose proof (ev_while_body np le tmp (compile ctxt l c) l u st w ck1 E Hle) as HB.
    rewrite Ew in HB.
    set (st' := set_var tmp (Word w) st).
    assert (Hl2 : locals_rel ctxt l (crepSem.locals s) (locals st'))
      by (apply locals_rel_insert_gt_vmax; split; [exact Hl'|lia]).
    exists (ck1 + 2), NONE, (set_locals (inter (locals st') l) st'). split.
    { rewrite ev_Loop_eq. replace (clock t + (ck1 + 2)) with (clock t + ((ck1 + 1) + 1)) by lia.
      rewrite cut_entry2 by exact Hsub. cbv beta iota. change (set_locals (inter (locals t) l) t) with u.
      rewrite HB. unfold_eval. cbv beta iota.
      cbn [cut_res IS_SOME]. cbv beta iota.
      change (set_clock (clock st + 1) (set_var tmp (Word w) st)) with (set_clock (clock st' + 1) st').
      apply cut_exit. apply Hl2. }
    split; [unfold st'; srel S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
    split; [reflexivity|]. apply locals_rel_cut; exact Hl2.
Qed.



(** ** Function calls *)


Lemma FLOOKUP_FUPDATE_LIST_ALOOKUP {K V} `{EqDecision K} (al : list (K * V)) (fm : fmap K V) x :
  NoDup (List.map fst al) ->
  FLOOKUP (fm |++ al) x = match ALOOKUP al x with SOME v => SOME v | NONE => FLOOKUP fm x end.
Proof.
  revert fm; induction al as [|[k v] al IH]; intros fm Hd; [reflexivity|].
  cbn [List.map fst] in Hd. inversion Hd as [|? ? Hk Hd']; subst.
  change (fm |++ ((k, v) :: al)) with ((fm |+ (k, v)) |++ al).
  rewrite IH by exact Hd'. cbn [ALOOKUP].
  destruct (decide (k = x)) as [<-|Hne].
  - destruct (ALOOKUP al k) eqn:E.
    + exfalso. apply Hk. apply ALOOKUP_In in E. apply in_map_iff. exists (k, v0). auto.
    + rewrite FLOOKUP_UPDATE. destruct (decide (k = k)); [reflexivity|congruence].
  - destruct (ALOOKUP al x); [reflexivity|]. rewrite FLOOKUP_UPDATE.
    destruct (decide (k = x)); [contradiction|reflexivity].
Qed.

Lemma map_fst_ZIP {A B} (xs : list A) (ys : list B) :
  LENGTH xs = LENGTH ys -> List.map fst (ZIP (xs, ys)) = xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] H; cbn in *; try lia; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma ALOOKUP_ZIP_join (ns : list N) (lns : list N) (args : list (panSem.word_lab a)) x v :
  NoDup lns -> LENGTH ns = LENGTH lns -> LENGTH args = LENGTH lns ->
  ALOOKUP (ZIP (ns, args)) x = SOME v ->
  exists n, ALOOKUP (ZIP (ns, lns)) x = SOME n /\ In n lns /\
            ALOOKUP (ZIP (lns, MAP wlab_wloc args)) n = SOME (wlab_wloc v).
Proof.
  revert lns args; induction ns as [|y ns IH]; intros [|n0 lns] [|a0 args] Hd H1 H2 H; cbn in *;
    try discriminate; try lia.
  inversion Hd as [|? ? Hn0 Hd']; subst.
  destruct (decide (y = x)) as [->|Hne].
  - injection H as <-. exists n0. split; [reflexivity|]. split; [left; reflexivity|].
    destruct (decide (n0 = n0)); [reflexivity|congruence].
  - destruct (IH lns args Hd' ltac:(lia) ltac:(lia) H) as (n & Hn & Hin & Hl).
    exists n. split; [exact Hn|]. split; [right; exact Hin|].
    destruct (decide (n0 = n)) as [->|]; [contradiction|exact Hl].
Qed.

Lemma ALOOKUP_ZIP_inj (ns lns : list N) x y n :
  NoDup lns -> LENGTH ns = LENGTH lns ->
  ALOOKUP (ZIP (ns, lns)) x = SOME n -> ALOOKUP (ZIP (ns, lns)) y = SOME n -> x = y.
Proof.
  revert lns; induction ns as [|z ns IH]; intros [|n0 lns] Hd Hl Hx Hy; cbn in *;
    try discriminate; try lia.
  inversion Hd as [|? ? Hn0 Hd']; subst.
  assert (Hin : forall w m, ALOOKUP (ZIP (ns, lns)) w = SOME m -> In m lns).
  { intros w m Hw. apply ALOOKUP_In in Hw. clear - Hw Hl.
    revert lns Hw Hl; induction ns as [|q ns IHq]; intros [|r lns] Hw Hl; cbn in *;
      try contradiction; try lia.
    destruct Hw as [Hw|Hw]; [injection Hw as -> ->; left; reflexivity|].
    right. apply (IHq lns Hw). lia. }
  destruct (decide (z = x)) as [<-|Hx']; destruct (decide (z = y)) as [<-|Hy']; try reflexivity.
  - injection Hx as <-. exfalso. exact (Hn0 (Hin _ _ Hy)).
  - injection Hy as <-. exfalso. exact (Hn0 (Hin _ _ Hx)).
  - exact (IH lns Hd' ltac:(lia) Hx Hy).
Qed.

Lemma ALOOKUP_ZIP_In (ns lns : list N) x n :
  LENGTH ns = LENGTH lns -> ALOOKUP (ZIP (ns, lns)) x = SOME n -> In n lns.
Proof.
  intros Hl Hx. apply ALOOKUP_In in Hx. revert lns Hx Hl; induction ns as [|q ns IHq];
    intros [|r lns] Hw Hl; cbn in *; try contradiction; try lia.
  destruct Hw as [Hw|Hw]; [injection Hw as -> ->; left; reflexivity|].
  right. apply (IHq lns Hw). lia.
Qed.

Lemma MAX_LIST_In (l : list N) m : In m l -> m <= MAX_LIST l.
Proof.
  induction l as [|x l IH]; intros H; [contradiction|]. cbn [MAX_LIST]. unfold MAX.
  destruct H as [->|H]; [destruct (N.ltb_spec m (MAX_LIST l)); lia|].
  specialize (IH H). destruct (N.ltb_spec x (MAX_LIST l)); lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "call_preserve_state_code_locals_rel" *)
Theorem call_preserve_state_code_locals_rel : forall ns lns (args : list (panSem.word_lab a))
    (s : crepSem.state a ffi_t) (st : loopSem.state a ffi_t) ctxt nl fname
    (argexps : list (crepLang.exp a)) prog loc,
  ALL_DISTINCT ns /\ ALL_DISTINCT lns /\
  LENGTH ns = LENGTH lns /\
  LENGTH args = LENGTH lns /\
  state_rel s st /\
  mem_rel (crepSem.memory s) (memory st) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals st) /\
  code_rel ctxt (crepSem.code s) (code st) /\
  locals_rel ctxt nl (crepSem.locals s) (locals st) /\
  FLOOKUP (crepSem.code s) fname = SOME (ns, prog) /\
  FLOOKUP (funcs ctxt) fname = SOME (loc, LENGTH lns) /\
  MAP (crepSem.eval s) argexps = MAP SOME args ->
  let nctxt := ctxt_fc (target ctxt) (funcs ctxt) ns lns in
  state_rel
    (crepSem.set_clock (crepSem.clock s - 1) (crepSem.set_locals (FEMPTY |++ ZIP (ns, args)) s))
    (set_clock (clock st - 1) (set_locals (fromAList (ZIP (lns, MAP wlab_wloc args))) st)) /\
  code_rel nctxt (crepSem.code s) (code st) /\
  locals_rel nctxt (list_to_num_set lns) (FEMPTY |++ ZIP (ns, args))
    (fromAList (ZIP (lns, MAP wlab_wloc args))).
Proof.
  intros ns lns args s st ctxt nl fname argexps prog loc
    (Hdn & Hdl & Hl1 & Hl2 & R1 & R2 & R3 & R4 & R5 & Hc & Hf & Hm).
  apply ALL_DISTINCT_NoDup_list in Hdn, Hdl. cbv zeta.
  split; [srel R1|]. split; [exact R4|].
  assert (Hfl : forall (xs : list N) (ys : list N) x, LENGTH xs = LENGTH ys -> NoDup xs ->
                  FLOOKUP (FEMPTY |++ ZIP (xs, ys)) x = ALOOKUP (ZIP (xs, ys)) x).
  { intros xs ys x Hl Hd. rewrite FLOOKUP_FUPDATE_LIST_ALOOKUP by (rewrite map_fst_ZIP; assumption).
    destruct (ALOOKUP _ x); reflexivity. }
  assert (Hfa : forall x, FLOOKUP (FEMPTY |++ ZIP (ns, args)) x = ALOOKUP (ZIP (ns, args)) x).
  { intros x. rewrite FLOOKUP_FUPDATE_LIST_ALOOKUP by (rewrite map_fst_ZIP by lia; exact Hdn).
    destruct (ALOOKUP _ x); reflexivity. }
  unfold ctxt_fc; cbn [crep_to_loop.vars crep_to_loop.vmax]. split; [|split; [|split]].
  - intros x y n m (Hx & Hy & <-). change (FLOOKUP (FEMPTY |++ ZIP (ns, lns)) x = SOME n) in Hx.
    change (FLOOKUP (FEMPTY |++ ZIP (ns, lns)) y = SOME n) in Hy.
    rewrite (Hfl _ _ x Hl1 Hdn) in Hx. rewrite (Hfl _ _ y Hl1 Hdn) in Hy.
    exact (ALOOKUP_ZIP_inj ns lns x y n Hdl Hl1 Hx Hy).
  - intros v m Hv. rewrite (Hfl _ _ _ Hl1 Hdn) in Hv. apply MAX_LIST_In.
    exact (ALOOKUP_ZIP_In ns lns v m Hl1 Hv).
  - intros k Hk. unfold pred_set.IN in *. rewrite domain_fromAList. cbv beta.
    rewrite domain_list_to_num_set in Hk. unfold is_true in *. rewrite MEM_In in *.
    rewrite map_fst_ZIP; [exact Hk|]. rewrite !LENGTH_length, length_map, <- !LENGTH_length. lia.
  - intros vn v Hv. rewrite Hfa in Hv.
    destruct (ALOOKUP_ZIP_join ns lns args vn v Hdl Hl1 Hl2 Hv) as (n & Hn & Hin & Hlk).
    exists n. split; [rewrite (Hfl _ _ _ Hl1 Hdn); exact Hn|]. split.
    + unfold pred_set.IN. rewrite domain_list_to_num_set. unfold is_true. apply MEM_In, Hin.
    + rewrite lookup_fromAList. exact Hlk.
Qed.

Lemma call_args (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t) ctxt l (argexps : list (crepLang.exp a)) args p les tmp nl :
  rels s t ctxt l -> OPT_MMAP (crepSem.eval s) argexps = SOME args ->
  compile_exps ctxt (vmax ctxt + 1) l argexps = (p, (les, (tmp, nl))) ->
  exists ck st2,
    (forall extra, evaluate (nested_seq (p ++ MAP2 Assign (gen_temps tmp (LENGTH les)) les),
                             set_clock (clock t + (ck + extra)) t) =
                   (NONE, set_clock (clock st2 + extra) st2)) /\
    get_vars (gen_temps tmp (LENGTH les)) st2 = SOME (MAP wlab_wloc args) /\
    state_rel s st2 /\ mem_rel (crepSem.memory s) (memory st2) (crepSem.memaddrs s) /\
    globals_rel (crepSem.globals s) (globals st2) /\ code_rel ctxt (crepSem.code s) (code st2) /\
    locals_rel ctxt l (crepSem.locals s) (locals st2) /\ LENGTH les = LENGTH argexps.
Proof.
  intros Hr Ees C.
  destruct Hr as (R1 & R2 & R3 & R4 & R5).
  assert (Hv : vmax ctxt < vmax ctxt + 1) by lia.
  destruct (comp_exps_preserves_eval argexps s args t ctxt (vmax ctxt + 1) l p les tmp nl
              (conj Ees (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj C Hv))))))))
    as (ck & st & E & Hles & S1 & S2 & S3 & S4 & S5).
  destruct (compile_exps_out_rel _ _ _ _ _ _ _ _ C) as (Ok & Le & El & Len).
  set (ntmps := gen_temps tmp (LENGTH les)).
  assert (Hlen : LENGTH ntmps = LENGTH les) by (unfold ntmps, gen_temps; apply LENGTH_GENLIST_c).
  assert (Hdist : ALL_DISTINCT ntmps).
  { unfold ntmps, gen_temps. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & Hm). lia. }
  assert (Hlenws : LENGTH les = LENGTH (MAP wlab_wloc args)).
  { rewrite (opt_mmap_length_eq _ _ _ Hles). reflexivity. }
  assert (Hdl : distinct_lists ntmps (FLAT (MAP locals_touched les))).
  { apply distinct_lists_iff. intros x Hx Hx'.
    unfold ntmps, gen_temps in Hx. apply In_GENLIST_iff in Hx as (i & _ & ->).
    pose proof (proj1 (proj2 R5)) as Hmax.
    refine (_ (compile_exps_le_tmp_domain ctxt (vmax ctxt + 1) l argexps p les tmp nl (tmp + i)
                 (conj Hmax (conj C (conj Hv (conj _ (proj2 (MEM_In _ _) Hx'))))))).
    - intros [Hlt _]. lia.
    - intros k Hk. apply (var_hyp_of_evals s t ctxt l argexps args); [|exact Ees|apply MEM_In, Hk].
      exact (conj R1 (conj R2 (conj R3 (conj R4 R5)))). }
  apply opt_mmap_eq_some in Hles.
  rewrite El in S5. pose proof (locals_back ctxt l _ _ _ p R5 Ok S5) as Hl'.
  exists ck, (set_locals (alist_insert ntmps (MAP wlab_wloc args) (locals st)) st).
  split; [|split; [|split; [exact S1|split; [exact S2|split; [exact S3|split; [exact S4|split]]]]]].
  - intros extra.
    assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
    rewrite (ev_nested_app _ _ _ _ (ev_add1 _ _ _ _ _ E Hnt extra)).
    assert (Hles' : MAP (eval (set_clock (clock st + extra) st)) les = MAP SOME (MAP wlab_wloc args))
      by (rewrite eval_set_clock; exact Hles).
    rewrite (loop_eval_nested_assign_distinct_eq les ntmps _ (MAP wlab_wloc args)
               (conj Hles' (conj Hdl (conj Hdist Hlen)))).
    f_equal; apply loop_state_ext; reflexivity.
  - apply get_vars_local_update_some_eq. split; [exact Hdist|rewrite Hlen; exact Hlenws].
  - cbn [set_locals locals]. destruct Hl' as (Hd & Hm & Hs & Hl). split; [exact Hd|].
    split; [exact Hm|]. split.
    + intros k Hk. unfold pred_set.IN in *. rewrite domain_lookup, lookup_alist_insert_any.
      destruct (ALOOKUP _ k); [eexists; reflexivity|apply domain_lookup, Hs, Hk].
    + intros vn x Hx. destruct (Hl vn x Hx) as (n & Hn & Hnd & Hlk). exists n.
      split; [exact Hn|]. split; [exact Hnd|].
      rewrite lookup_alist_insert_any.
      destruct (ALOOKUP (ZIP (ntmps, MAP wlab_wloc args)) n) eqn:Ea; [|exact Hlk].
      exfalso. apply ALOOKUP_In in Ea.
      assert (Hin : In n ntmps).
      { clear - Ea. revert Ea; generalize (MAP wlab_wloc args); induction ntmps as [|y ys IHy];
          intros [|z zs] Ea; cbn in Ea; try contradiction.
        destruct Ea as [Ea|Ea]; [injection Ea as -> _; left; reflexivity|right; eapply IHy; eauto]. } unfold ntmps, gen_temps in Hin. apply In_GENLIST_iff in Hin as (i & _ & ->).
      specialize (Hm _ _ Hn). lia.
  - exact Len.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "all_distinct_ctxt_lookup_all_distinct" *)
Theorem all_distinct_ctxt_lookup_all_distinct : forall (rts : list N) ctxt n,
  ALL_DISTINCT rts /\ distinct_vars (vars ctxt) ->
  ALL_DISTINCT (rt_vars (vars ctxt) rts n).
Proof.
  intros rts ctxt mx [Hr Hd]. unfold is_true in *. unfold rt_vars.
  destruct (OPT_MMAP (FLOOKUP (vars ctxt)) rts) as [m|] eqn:E; [|reflexivity].
  revert m E Hr; induction rts as [|r rs IH]; intros m E Hr; [injection E as <-; reflexivity|].
  cbn [ALL_DISTINCT] in Hr. apply andb_prop in Hr as [H1 H2].
  cbn [OPT_MMAP OPTION_BIND] in E.
  destruct (FLOOKUP (vars ctxt) r) as [n|] eqn:Er; [|discriminate]. cbn [OPTION_BIND] in E.
  destruct (OPT_MMAP (FLOOKUP (vars ctxt)) rs) as [ms|] eqn:Ers; [|discriminate].
  injection E as <-. cbn [ALL_DISTINCT]. rewrite (IH ms eq_refl H2), Bool.andb_true_r.
  destruct (MEM n ms) eqn:Em; [|reflexivity]. exfalso. apply MEM_In in Em.
  destruct (OPT_MMAP_In_res _ _ _ _ Ers Em) as (r' & Hr' & Hf).
  pose proof (Hd r r' n n (conj Er (conj Hf eq_refl))) as <-.
  apply MEM_In in Hr'. rewrite Hr' in H1. discriminate.
Qed.

Lemma ev_Call_None_tail (dest : N) nargs (st2 : state a ffi_t) extra argv env body :
  get_vars nargs (set_clock (clock st2 + extra) st2) = SOME argv ->
  find_code (SOME dest) argv (code (set_clock (clock st2 + extra) st2)) = SOME (env, body) ->
  clock st2 <> 0 ->
  evaluate (Call NONE (SOME dest) nargs NONE, set_clock (clock st2 + extra) st2) =
  match evaluate (body, set_clock (clock st2 - 1 + extra) (set_locals env st2)) with
  | (NONE, s) => (SOME Error, s)
  | (SOME (Continue _), s) => (SOME Error, s)
  | (SOME (Break _), s) => (SOME Error, s)
  | (SOME res, s) => (SOME res, s)
  end.
Proof.
  intros Hg Hf Hc. unfold_eval. rewrite Hg, Hf. cbv beta iota. cbn [IS_SOME].
  match goal with |- context [(clock ?x =? 0)] =>
    replace (clock x =? 0) with false
      by (symmetry; apply N.eqb_neq; cbn [clock set_clock set_locals]; lia) end.
  replace (set_locals env (dec_clock (set_clock (clock st2 + extra) st2)))
    with (set_clock (clock st2 - 1 + extra) (set_locals env st2))
    by (apply loop_state_ext; loop_cbn; try reflexivity; lia).
  reflexivity.
Qed.

Lemma ev_Call_Some_tail (dest : N) nargs rns (l : num_set) (st2 : state a ffi_t) extra argv env body
    en pe :
  get_vars nargs (set_clock (clock st2 + extra) st2) = SOME argv ->
  find_code (SOME dest) argv (code (set_clock (clock st2 + extra) st2)) = SOME (env, body) ->
  clock st2 <> 0 -> ALL_DISTINCT rns = true -> domain l SUBSET domain (locals st2) ->
  evaluate (Call (SOME (rns, l)) (SOME dest) nargs (SOME (en, (pe, (Skip, l)))),
            set_clock (clock st2 + extra) st2) =
  match evaluate (body, set_clock (clock st2 - 1 + extra) (set_locals env st2)) with
  | (SOME (Result retvs), st) =>
      if negb (LENGTH retvs =? LENGTH rns) then (SOME Error, st) else
      cut_res l (evaluate (Skip, set_vars rns retvs (set_locals (inter (locals st2) l) st)))
  | (SOME (Exception exn), st) =>
      cut_res l (evaluate (pe, set_var en exn (set_locals (inter (locals st2) l) st)))
  | (SOME (Continue _), st) => (SOME Error, st)
  | (SOME (Break _), st) => (SOME Error, st)
  | (NONE, st) => (SOME Error, st)
  | res => res
  end.
Proof.
  intros Hg Hf Hc Hd Hs. unfold_eval. rewrite Hg, Hf. cbv beta iota. rewrite Hd. cbn [negb].
  rewrite (cut_entry l st2 extra Hs Hc). cbv beta iota. rewrite fix_clock_evaluate.
  replace (set_locals env (set_clock (clock (dec_clock (set_locals (inter (locals st2) l) st2)) + extra)
                               (dec_clock (set_locals (inter (locals st2) l) st2))))
    with (set_clock (clock st2 - 1 + extra) (set_locals env st2))
    by (apply loop_state_ext; loop_cbn; try reflexivity; lia).
  destruct (evaluate (body, _)) as [[[ | | | | | |]|] st] eqn:E; try reflexivity.
Qed.

Lemma ev_handler_if en (eid' : word a) cpe (l : num_set) (X : state a ffi_t) w :
  lookup en (locals X) = SOME (Word w) ->
  evaluate (If NotEqual en (Imm eid') (Raise en) (Seq Tick cpe) l, X) =
  if negb (bool_decide (w = eid')) then (SOME (Exception (Word w)), call_env [] X)
  else cut_res l (evaluate (Seq Tick cpe, X)).
Proof.
  intros Hl. unfold_eval. rewrite Hl. cbn [get_var_imm]. cbv beta iota zeta. cbn [word_cmp].
  destruct (negb _); [|reflexivity].
  unfold_eval. rewrite Hl. reflexivity.
Qed.

Lemma EVERY_IS_SOME_of_OPT_MMAP {K V} (f : K -> option V) (l : list K) vs :
  OPT_MMAP f l = SOME vs -> EVERY (fun v => IS_SOME (f v)) l = true.
Proof.
  revert vs; induction l as [|x l IH]; intros vs H; [reflexivity|].
  cbn [OPT_MMAP OPTION_BIND] in H. destruct (f x) eqn:E; [|discriminate]. cbn [OPTION_BIND] in H.
  destruct (OPT_MMAP f l) eqn:E2; [|discriminate]. cbn [EVERY]. rewrite E. cbn.
  exact (IH _ eq_refl).
Qed.

Lemma nc_Call s caltyp fname argexps :
  (forall p' s', crepSem.eval_lt (p', s') (crepLang.Call caltyp fname argexps, s) -> nc_P p' s') ->
  nc_P (crepLang.Call caltyp fname argexps) s.
Proof.
  intros IH res s1 t ctxt l H Hne Hr. crep_step H.
  destruct (OPT_MMAP (crepSem.eval s) argexps) as [args|] eqn:Ea;
    [|injection H as <- _; congruence].
  destruct (crepSem.lookup_code (crepSem.code s) fname args (LENGTH args))
    as [[prog0 newlocals]|] eqn:Elc; [|injection H as <- _; congruence].
  unfold crepSem.lookup_code in Elc.
  destruct (FLOOKUP (crepSem.code s) fname) as [[ns prog]|] eqn:Ecode; [|discriminate].
  destruct (LENGTH ns =? LENGTH args) eqn:Elen; [|discriminate].
  destruct (ALL_DISTINCT ns) eqn:Edn; [|discriminate].
  cbn [andb] in Elc. injection Elc as <- <-.
  cbv beta iota in H. rewrite ?crepSem.fix_clock_evaluate in H.
  destruct (match caltyp with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end)
    eqn:Ert; [injection H as <- _; congruence|].
  pose proof Hr as Hr0. destruct Hr as (R1 & R2 & R3 & R4 & R5).
  destruct (proj2 R4 fname ns prog Ecode) as (loc & len & Hf & Hlen & _).
  apply N.eqb_eq in Elen.
  cbn [compile].
  destruct (compile_exps ctxt (vmax ctxt + 1) l argexps) as [p [les [tmp nl]]] eqn:C.
  destruct (call_args s t ctxt l argexps args p les tmp nl Hr0 Ea C)
    as (ck1 & st2 & Eargs & Hgv & S1 & S2 & S3 & S4 & S5 & Hlles).
  assert (Hdest : find_lab ctxt fname = loc) by (unfold find_lab; rewrite Hf; reflexivity).
  rewrite Hdest.
  set (lns := GENLIST I len) in *.
  set (nargs := gen_temps tmp (LENGTH les)) in *.
  set (env := fromAList (ZIP (lns, MAP wlab_wloc args))).
  set (nctxt := ctxt_fc (target ctxt) (funcs ctxt) ns lns).
  set (body := ocompile nctxt (list_to_num_set lns) prog).
  assert (Hlns : LENGTH lns = len) by (unfold lns; apply LENGTH_GENLIST_c).
  assert (Hcode2 : lookup loc (code st2) = SOME (lns, body)).
  { destruct (proj2 S4 fname ns prog Ecode) as (loc' & len' & Hf' & Hlen' & Hlook').
    rewrite Hf in Hf'. injection Hf' as <- <-. exact Hlook'. }
  assert (Hfind : forall k, find_code (SOME loc) (MAP wlab_wloc args) (code (set_clock k st2)) =
                            SOME (env, body)).
  { intros k. cbn [find_code code set_clock]. rewrite Hcode2.
    replace (LENGTH (MAP wlab_wloc args) =? LENGTH lns) with true; [reflexivity|].
    symmetry; apply N.eqb_eq. rewrite Hlns, <- Hlen, Elen, !LENGTH_length, length_map.
    reflexivity. }
  assert (Hgv' : forall k, get_vars nargs (set_clock k st2) = SOME (MAP wlab_wloc args))
    by (intros k; rewrite get_vars_set_clock; exact Hgv).
  assert (Hk : crepSem.clock s = clock st2) by apply S1.
  assert (Hsub : domain l SUBSET domain (locals st2)) by apply S5.
  assert (Hseq : forall extra rt1 rt2,
             evaluate (nested_seq (p ++ MAP2 Assign nargs les ++ [Call rt1 (SOME loc) nargs rt2]),
                       set_clock (clock t + (ck1 + extra)) t) =
             let '(r, s0) := evaluate (Call rt1 (SOME loc) nargs rt2, set_clock (clock st2 + extra) st2) in
             match r with NONE => evaluate (Skip, s0) | _ => (r, s0) end).
  { intros extra rt1 rt2. rewrite app_assoc, (ev_nested_app _ _ _ _ (Eargs extra)).
    cbn [nested_seq]. apply ev_Seq. }
  assert (Hrd : forall rts, ALL_DISTINCT rts = true ->
                ALL_DISTINCT (rt_vars (vars ctxt) rts (vmax ctxt + 1)) = true)
    by (intros rts Hrts; apply all_distinct_ctxt_lookup_all_distinct; split; [exact Hrts|apply R5]).
  destruct (crepSem.clock s =? 0) eqn:Eck.
  { (* time out *)
    injection H as <- <-. apply N.eqb_eq in Eck.
    destruct caltyp as [[rts hdl]|].
    - cbn [negb] in Ert. apply Bool.negb_false_iff in Ert.
      exists ck1, (SOME TimeOut), (set_locals LN (set_locals (inter (locals st2) l) st2)). split.
      + replace ck1 with (ck1 + 0) by lia. cbv beta iota zeta. rewrite Hseq.
        unfold_eval. rewrite Hgv', Hfind. cbv beta iota. rewrite (Hrd rts Ert). cbn [negb].
        cbn [cut_res IS_SOME]. unfold cut_state. cbn [locals set_clock].
        destruct (classical_dec _) as [_|Hn]; [|contradiction].
        match goal with |- context [(clock ?x =? 0)] =>
          replace (clock x =? 0) with true
            by (symmetry; apply N.eqb_eq; cbn [clock set_clock set_locals]; lia) end.
        cbv beta iota. f_equal. apply loop_state_ext; loop_cbn; try reflexivity. lia.
      + split; [srel S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
        split; reflexivity.
    - exists ck1, (SOME TimeOut), (set_locals LN st2). split.
      + replace ck1 with (ck1 + 0) by lia. cbv beta iota zeta. rewrite Hseq.
        unfold_eval. rewrite Hgv', Hfind. cbv beta iota. cbn [IS_SOME].
        match goal with |- context [(clock ?x =? 0)] =>
          replace (clock x =? 0) with true
            by (symmetry; apply N.eqb_eq; cbn [clock set_clock set_locals]; lia) end.
        cbv beta iota. f_equal. apply loop_state_ext; loop_cbn; try reflexivity. lia.
      + split; [srel S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
        split; reflexivity. }
  apply N.eqb_neq in Eck.
  match type of H with context [crepSem.evaluate (prog, ?sb0)] =>
    destruct (crepSem.evaluate (prog, sb0)) as [rb stb] eqn:Eb; set (sb := sb0) in * end.
  set (tb := set_clock (clock st2 - 1) (set_locals env st2)).
  assert (Hrb : rels sb tb nctxt (list_to_num_set lns)).
  { assert (Hdl : ALL_DISTINCT lns = true).
    { unfold lns. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & Hm). exact Hm. }
    assert (Hm : MAP (crepSem.eval s) argexps = MAP SOME args) by (apply opt_mmap_eq_some; exact Ea).
    assert (Hf' : FLOOKUP (funcs ctxt) fname = SOME (loc, LENGTH lns)) by (rewrite Hlns; exact Hf).
    assert (HL1 : LENGTH ns = LENGTH lns) by lia.
    assert (HL2 : LENGTH args = LENGTH lns) by lia.
    destruct (call_preserve_state_code_locals_rel ns lns args s st2 ctxt l fname argexps prog loc
                (conj Edn (conj Hdl (conj HL1 (conj HL2
                  (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj Ecode (conj Hf' Hm))))))))))))
      as (C1 & C2 & C3).
    split; [exact C1|]. split; [exact S2|]. split; [exact S3|]. split; [exact C2|exact C3]. }
  assert (Hrbne : rb <> SOME crepSem.Error).
  { intros ->. cbv beta iota in H. injection H as <- _. congruence. }
  destruct (IH prog sb ltac:(unfold sb; crepProps.lt_tac) rb stb tb nctxt (list_to_num_set lns)
              Eb Hrbne Hrb) as (ck2 & q & t1 & T & Q1 & Q2 & Q3 & Q4 & Eq & P).
  assert (Hq : forall j, q <> NONE -> (forall n, q <> SOME (Break n)) ->
                 (forall n, q <> SOME (Continue n)) -> q <> SOME TimeOut ->
                 evaluate (body, set_clock (clock st2 - 1 + (ck2 + j)) (set_locals env st2)) =
                 (q, set_clock (clock t1 + j) t1)).
  { intros j H1 H2 H3 H4.
    pose proof (ev_add1 _ _ _ _ _ T H4 j) as T'.
    unfold body, ocompile. cbv beta.
    apply loop_liveProof.optimise_correct.
    split; [exact T'|]. split; [subst q; destruct rb as [[]|]; cbn; congruence|].
    split; [exact H2|]. split; [exact H3|exact H1]. }
  assert (Hq0 : q <> NONE -> (forall n, q <> SOME (Break n)) -> (forall n, q <> SOME (Continue n)) ->
                evaluate (body, set_clock (clock st2 - 1 + ck2) (set_locals env st2)) = (q, t1)).
  { intros H1 H2 H3. unfold body, ocompile. cbv beta.
    apply loop_liveProof.optimise_correct.
    split; [exact T|]. split; [subst q; destruct rb as [[]|]; cbn; congruence|].
    split; [exact H2|]. split; [exact H3|exact H1]. }
  destruct rb as [[ | | k | k | retvs | eid | f]|]; cbv beta iota in H; subst q.
  - congruence.
  - (* TimeOut *)
    injection H as <- <-. exists (ck1 + ck2), (SOME TimeOut), t1. split.
    + destruct caltyp as [[rts hdl]|]; cbv beta iota zeta; rewrite Hseq.
      * cbn [negb] in Ert. apply Bool.negb_false_iff in Ert.
        rewrite (ev_Call_Some_tail loc nargs _ l st2 ck2 _ env body _ _ (Hgv' _) (Hfind _)
                   ltac:(lia) (Hrd rts Ert) Hsub).
        rewrite Hq0 by (try discriminate; intros ?n; discriminate). reflexivity.
      * rewrite (ev_Call_None_tail loc nargs st2 ck2 _ env body (Hgv' _) (Hfind _) ltac:(lia)).
        rewrite Hq0 by (try discriminate; intros ?n; discriminate). reflexivity.
    + split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      split; reflexivity.
  - cbn in H. injection H as <- _. congruence.
  - cbn in H. injection H as <- _. congruence.
  - (* Return *)
    destruct caltyp as [[rts hdl]|].
    + cbn [negb] in Ert. apply Bool.negb_false_iff in Ert.
      destruct (LENGTH retvs =? LENGTH rts) eqn:Elr; cbn [negb] in H;
        [|injection H as <- _; congruence].
      destruct (OPT_MMAP (FLOOKUP (crepSem.locals s)) rts) as [vs0|] eqn:Ers;
        [|injection H as <- _; congruence].
      injection H as <- <-. apply N.eqb_eq in Elr.
      destruct (lhss_rel rts _ (locals st2) ctxt l (EVERY_IS_SOME_of_OPT_MMAP _ _ _ Ers) Ert S5)
        as (nl' & Enl & Lnl & Hdom & Hdist).
      assert (Hrv : rt_vars (vars ctxt) rts (vmax ctxt + 1) = nl') by (unfold rt_vars; rewrite Enl; reflexivity).
      pose proof (Hq 1 ltac:(discriminate) ltac:(intros n; discriminate)
                    ltac:(intros n; discriminate) ltac:(discriminate)) as T1.
      set (X := set_vars nl' (MAP wlab_wloc retvs)
                  (set_locals (inter (locals st2) l) (set_clock (clock t1 + 1) t1))).
      assert (HX : domain l SUBSET domain (locals X)).
      { intros k0 Hk0. unfold pred_set.IN in *. unfold X. loop_cbn.
        rewrite domain_lookup, lookup_alist_insert_any.
        destruct (ALOOKUP _ k0); [eexists; reflexivity|].
        apply domain_lookup. rewrite domain_inter. split; [apply Hsub, Hk0|exact Hk0]. }
      exists (ck1 + (ck2 + 1)), NONE, (dec_clock (set_locals (inter (locals X) l) X)). split.
      * cbv beta iota zeta. rewrite Hseq, Hrv.
        rewrite (ev_Call_Some_tail loc nargs nl' l st2 (ck2 + 1) _ env body _ _ (Hgv' _) (Hfind _)
                   ltac:(lia) Hdist Hsub).
        rewrite T1. cbn [nc_res].
        replace (LENGTH (MAP wlab_wloc retvs) =? LENGTH nl') with true
          by (symmetry; apply N.eqb_eq; rewrite Lnl, <- Elr, !LENGTH_length, length_map; reflexivity).
        cbn [negb]. rewrite ev_Skip. fold X.
        cbn [cut_res IS_SOME]. unfold cut_state.
        destruct (classical_dec _) as [_|Hn]; [|contradiction].
        match goal with |- context [(clock ?x =? 0)] =>
          replace (clock x =? 0) with false
            by (symmetry; apply N.eqb_neq; unfold X; cbn [clock set_clock set_locals set_vars]; lia) end.
        cbv beta iota. rewrite ev_Skip. reflexivity.
      * split; [unfold X; srel Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; [reflexivity|]. cbn [nc_post].
        apply locals_rel_cut. unfold X. loop_cbn.
        apply locals_rel_upd_list; [apply locals_rel_cut; exact S5|exact Enl|exact Hdom|exact Hdist|].
        rewrite <- Elr. reflexivity.
    + injection H as <- <-. exists (ck1 + ck2), (SOME (Result (MAP wlab_wloc retvs))), t1. split.
      * cbv beta iota zeta. rewrite Hseq.
        rewrite (ev_Call_None_tail loc nargs st2 ck2 _ env body (Hgv' _) (Hfind _) ltac:(lia)).
        rewrite Hq0 by (try discriminate; intros ?n; discriminate). reflexivity.
      * split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
  - (* Exception *)
    destruct caltyp as [[rts [[eid' ph]|]]|].
    + cbn [negb] in Ert. apply Bool.negb_false_iff in Ert.
      set (en := vmax ctxt + 1).
      set (cpe := compile ctxt l ph).
      set (L2 := inter (locals st2) l).
      assert (Hlook : forall k, lookup en (locals (set_var en (Word eid)
                                 (set_locals L2 (set_clock k t1)))) = SOME (Word eid)).
      { intros k. cbn [set_var set_locals locals]. rewrite lookup_insert.
        destruct (decide (en = en)); [reflexivity|congruence]. }
      destruct (bool_decide (eid = eid')) eqn:Eeq.
      * apply bool_decide_spec in Eeq. subst eid'.
        set (sh := crepSem.set_locals (crepSem.locals s) stb).
        set (th := set_var en (Word eid) (set_locals L2 t1)).
        assert (Hrh : rels sh th ctxt l).
        { split; [unfold th, sh; pose proof Q1 as Q1'; srel Q1'|]. split; [exact Q2|].
          split; [exact Q3|]. split; [exact Q4|].
          apply locals_rel_insert_gt_vmax. split; [apply locals_rel_cut; exact S5|unfold en; lia]. }
        assert (Hlth : crepSem.eval_lt (ph, sh) (crepLang.Call (SOME (rts, SOME (eid, ph))) fname argexps, s)).
        { pose proof (crepSem.evaluate_clock _ _ _ _ Eb) as Hcb.
          unfold crepSem.eval_lt. cbn [fst snd]. left. unfold sh, sb in *.
          cbn [crepSem.set_locals crepSem.clock crepSem.dec_clock crepSem.set_clock] in *. lia. }
        destruct (IH ph sh Hlth res s1 th ctxt l H Hne Hrh)
          as (ck3 & q3 & t3 & T3 & W1 & W2 & W3 & W4 & Eq3 & P3).
        assert (Hev : forall E3, evaluate (Seq Tick cpe,
                         set_var en (Word eid) (set_locals L2 (set_clock (clock t1 + (1 + ck3 + E3)) t1))) =
                       evaluate (cpe, set_clock (clock th + (ck3 + E3)) th)).
        { intros E3. rewrite ev_Seq. unfold_eval.
          cbn [set_var set_locals set_clock clock].
          match goal with |- context [(?x =? 0)] =>
            replace (x =? 0) with false by (symmetry; apply N.eqb_neq; lia) end.
          cbv beta iota.
          match goal with |- evaluate (?p, ?x) = evaluate (?p, ?y) =>
            replace x with y; [reflexivity|] end.
          apply loop_state_ext; unfold th; loop_cbn; try reflexivity. lia. }
        destruct q3 as [q3|].
        -- exists (ck1 + (ck2 + (1 + ck3 + 0))), (SOME q3), t3. split.
           ++ cbv beta iota zeta. rewrite Hseq.
              rewrite (ev_Call_Some_tail loc nargs _ l st2 _ _ env body _ _ (Hgv' _) (Hfind _)
                         ltac:(lia) (Hrd rts Ert) Hsub).
              rewrite (Hq (1 + ck3 + 0)) by (try discriminate; intros ?n; discriminate).
              cbn [nc_res]. rewrite (ev_handler_if en eid cpe l _ eid (Hlook _)).
              unfold bool_decide at 1; destruct (decide (eid = eid)) as [_|Hn]; [|congruence]. cbn [negb].
              rewrite Hev. replace (ck3 + 0) with ck3 by lia. unfold cpe. rewrite T3. reflexivity.
           ++ repeat (split; [assumption|]). exact P3.
        -- assert (Hres : res = NONE) by (destruct res as [[]|]; cbn in Eq3; congruence).
           subst res. cbn [nc_post] in P3.
           assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
           pose proof (ev_add1 _ _ _ _ _ T3 Hnt 2) as T3'.
           set (Y := set_locals (inter (locals t3) l) t3).
           exists (ck1 + (ck2 + (1 + ck3 + 2))), NONE, (set_locals (inter (locals Y) l) Y). split.
           ++ cbv beta iota zeta. rewrite Hseq.
              rewrite (ev_Call_Some_tail loc nargs _ l st2 _ _ env body _ _ (Hgv' _) (Hfind _)
                         ltac:(lia) (Hrd rts Ert) Hsub).
              rewrite (Hq (1 + ck3 + 2)) by (try discriminate; intros ?n; discriminate).
              cbn [nc_res]. rewrite (ev_handler_if en eid cpe l _ eid (Hlook _)).
              unfold bool_decide at 1; destruct (decide (eid = eid)) as [_|Hn]; [|congruence]. cbn [negb].
              rewrite Hev. unfold cpe. rewrite T3'.
              assert (Hs3 : domain l SUBSET domain (locals t3)) by apply P3.
              replace (set_clock (clock t3 + 2) t3) with (set_clock (clock (set_clock (clock t3 + 1) t3) + 1)
                                                            (set_clock (clock t3 + 1) t3))
                by (apply loop_state_ext; loop_cbn; try reflexivity; lia).
              rewrite cut_exit by exact Hs3.
              replace (set_locals (inter (locals (set_clock (clock t3 + 1) t3)) l) (set_clock (clock t3 + 1) t3))
                with (set_clock (clock Y + 1) Y)
                by (apply loop_state_ext; unfold Y; loop_cbn; try reflexivity).
              rewrite cut_exit.
              2: { intros k0 Hk0. unfold pred_set.IN in *. unfold Y. loop_cbn. rewrite domain_inter.
                   split; [apply Hs3, Hk0|exact Hk0]. }
              cbv beta iota. apply ev_Skip.
           ++ split; [unfold Y; srel W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
              split; [reflexivity|]. cbn [nc_post]. unfold Y. loop_cbn.
              apply locals_rel_cut, locals_rel_cut. exact P3.
      * injection H as <- <-.
        exists (ck1 + ck2), (SOME (Exception (Word eid))),
          (call_env [] (set_var en (Word eid) (set_locals L2 (set_clock (clock t1 + 0) t1)))). split.
        -- cbv beta iota zeta. replace (ck1 + ck2) with (ck1 + (ck2 + 0)) by lia. rewrite Hseq.
           rewrite (ev_Call_Some_tail loc nargs _ l st2 _ _ env body _ _ (Hgv' _) (Hfind _)
                      ltac:(lia) (Hrd rts Ert) Hsub).
           rewrite (Hq 0) by (try discriminate; intros ?n; discriminate).
           cbn [nc_res]. rewrite (ev_handler_if en eid' cpe l _ eid (Hlook _)).
           rewrite Eeq. cbn [negb]. reflexivity.
        -- split; [srel Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
           split; reflexivity.
    + cbn [negb] in Ert. apply Bool.negb_false_iff in Ert.
      injection H as <- <-.
      exists (ck1 + ck2), (SOME (Exception (Word eid))),
        (call_env [] (set_var (vmax ctxt + 1) (Word eid)
                        (set_locals (inter (locals st2) l) (set_clock (clock t1 + 0) t1)))). split.
      * cbv beta iota zeta. replace (ck1 + ck2) with (ck1 + (ck2 + 0)) by lia. rewrite Hseq.
        rewrite (ev_Call_Some_tail loc nargs _ l st2 _ _ env body _ _ (Hgv' _) (Hfind _)
                   ltac:(lia) (Hrd rts Ert) Hsub).
        rewrite (Hq 0) by (try discriminate; intros ?n; discriminate).
        cbn [nc_res]. unfold_eval. cbn [set_var set_locals locals]. rewrite lookup_insert.
        destruct (decide _) as [_|]; [|congruence]. reflexivity.
      * split; [srel Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
    + injection H as <- <-. exists (ck1 + ck2), (SOME (Exception (Word eid))), t1. split.
      * cbv beta iota zeta. rewrite Hseq.
        rewrite (ev_Call_None_tail loc nargs st2 ck2 _ env body (Hgv' _) (Hfind _) ltac:(lia)).
        rewrite Hq0 by (try discriminate; intros ?n; discriminate). reflexivity.
      * split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
        split; reflexivity.
  - (* FinalFFI *)
    injection H as <- <-. exists (ck1 + ck2), (SOME (FinalFFI f)), t1. split.
    + destruct caltyp as [[rts hdl]|]; cbv beta iota zeta; rewrite Hseq.
      * cbn [negb] in Ert. apply Bool.negb_false_iff in Ert.
        rewrite (ev_Call_Some_tail loc nargs _ l st2 ck2 _ env body _ _ (Hgv' _) (Hfind _)
                   ltac:(lia) (Hrd rts Ert) Hsub).
        rewrite Hq0 by (try discriminate; intros ?n; discriminate). reflexivity.
      * rewrite (ev_Call_None_tail loc nargs st2 ck2 _ env body (Hgv' _) (Hfind _) ltac:(lia)).
        rewrite Hq0 by (try discriminate; intros ?n; discriminate). reflexivity.
    + split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      split; reflexivity.
  - cbn in H. injection H as <- _. congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct" *)
Theorem ncompile_correct : forall (v : crepLang.prog a) (v1 : crepSem.state a ffi_t) res s1
    (t : loopSem.state a ffi_t) ctxt l,
  crepSem.evaluate (v, v1) = (res, s1) /\ res <> SOME crepSem.Error /\
  state_rel v1 t /\ mem_rel (crepSem.memory v1) (memory t) (crepSem.memaddrs v1) /\
  globals_rel (crepSem.globals v1) (globals t) /\
  code_rel ctxt (crepSem.code v1) (code t) /\
  locals_rel ctxt l (crepSem.locals v1) (locals t) ->
  exists ck res1 t1,
    evaluate (compile ctxt l v, set_clock (clock t + ck) t) = (res1, t1) /\
    state_rel s1 t1 /\ mem_rel (crepSem.memory s1) (memory t1) (crepSem.memaddrs s1) /\
    globals_rel (crepSem.globals s1) (globals t1) /\
    code_rel ctxt (crepSem.code s1) (code t1) /\
    res1 = match res with
           | NONE => NONE
           | SOME (crepSem.Break n) => SOME (Break n)
           | SOME (crepSem.Continue n) => SOME (Continue n)
           | SOME (crepSem.Return vs) => SOME (Result (MAP wlab_wloc vs))
           | SOME (crepSem.Exception eid) => SOME (Exception (Word eid))
           | SOME crepSem.TimeOut => SOME TimeOut
           | SOME (crepSem.FinalFFI f) => SOME (FinalFFI f)
           | SOME crepSem.Error => SOME Error
           end /\
    match res with
    | NONE => locals_rel ctxt l (crepSem.locals s1) (locals t1)
    | SOME (crepSem.Break n) => locals_rel ctxt l (crepSem.locals s1) (locals t1)
    | SOME (crepSem.Continue n) => locals_rel ctxt l (crepSem.locals s1) (locals t1)
    | SOME (crepSem.Return vs) => True
    | SOME crepSem.Error => False
    | _ => True
    end.
Proof.
  intros v v1 res s1 t ctxt l (H & Hne & R1 & R2 & R3 & R4 & R5).
  assert (G : forall x : crepLang.prog a * crepSem.state a ffi_t, nc_P (fst x) (snd x)).
  { intros x; induction x as [[v0 s0] IH] using (well_founded_induction crepSem.eval_lt_wf).
    assert (IH' : forall p' s', crepSem.eval_lt (p', s') (v0, s0) -> nc_P p' s')
      by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
    cbn [fst snd]. destruct v0.
    - apply nc_Skip.
    - apply nc_Dec; exact IH'.
    - apply nc_Assign.
    - apply nc_Primitive.
    - apply nc_Store.
    - apply nc_Store32.
    - apply nc_StoreByte.
    - apply nc_StoreGlob.
    - apply nc_Seq; exact IH'.
    - apply nc_If; exact IH'.
    - apply nc_While; exact IH'.
    - apply nc_Break.
    - apply nc_Continue.
    - apply nc_Call; exact IH'.
    - apply nc_ExtCall.
    - apply nc_Raise.
    - apply nc_Return.
    - apply nc_ShMem.
    - apply nc_Tick. }
  exact (G (v, v1) res s1 t ctxt l H Hne (conj R1 (conj R2 (conj R3 (conj R4 R5))))).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ocompile_correct" *)
Theorem ocompile_correct : forall (p : crepLang.prog a) (s : crepSem.state a ffi_t) res s1
    (t : loopSem.state a ffi_t) ctxt l,
  crepSem.evaluate (p, s) = (res, s1) /\ state_rel s t /\
  mem_rel (crepSem.memory s) (memory t) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals t) /\ code_rel ctxt (crepSem.code s) (code t) /\
  locals_rel ctxt l (crepSem.locals s) (locals t) /\ res <> SOME crepSem.Error /\
  (forall n, res <> SOME (crepSem.Break n)) /\
  (forall n, res <> SOME (crepSem.Continue n)) /\ res <> NONE ->
  exists ck res1 t1,
    evaluate (ocompile ctxt l p, set_clock (clock t + ck) t) = (res1, t1) /\
    state_rel s1 t1 /\ mem_rel (crepSem.memory s1) (memory t1) (crepSem.memaddrs s1) /\
    globals_rel (crepSem.globals s1) (globals t1) /\
    code_rel ctxt (crepSem.code s1) (code t1) /\
    match res with
    | NONE => False
    | SOME crepSem.Error => False
    | SOME crepSem.TimeOut => res1 = SOME TimeOut
    | SOME (crepSem.Break n) => False
    | SOME (crepSem.Continue n) => False
    | SOME (crepSem.Return v) => res1 = SOME (Result (MAP wlab_wloc v))
    | SOME (crepSem.Exception eid) => res1 = SOME (Exception (Word eid))
    | SOME (crepSem.FinalFFI f) => res1 = SOME (FinalFFI f)
    end.
Proof.
  intros p s res s1 t ctxt l (H & R1 & R2 & R3 & R4 & R5 & He & Hb & Hc & Hn).
  destruct (ncompile_correct p s res s1 t ctxt l (conj H (conj He (conj R1 (conj R2 (conj R3 (conj R4 R5)))))))
    as (ck & res1 & t1 & T & S1 & S2 & S3 & S4 & Eq & _).
  exists ck, res1, t1. split.
  - unfold ocompile. cbv beta. apply loop_liveProof.optimise_correct.
    split; [exact T|]. subst res1.
    destruct res as [[]|]; cbn; try congruence;
      try (exfalso; eapply Hb; reflexivity); try (exfalso; eapply Hc; reflexivity);
      repeat split; intros; discriminate.
  - split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
    subst res1. destruct res as [[]|]; cbn; try reflexivity; try congruence;
      try (eapply Hb; reflexivity); try (eapply Hc; reflexivity).
Qed.

End NCompile.

(** ** Whole programs *)

Section Programs.
Context {a : N}.

Lemma GENLIST_shift (c : N) k :
  GENLIST (fun n => n + c) (SUC k) = c :: GENLIST (fun n => n + (c + 1)) k.
Proof.
  rewrite GENLIST_CONS_aux. f_equal. f_equal. apply functional_extensionality; intros i; lia.
Qed.

Definition mf_list (prog : list (mlstring * (list N * crepLang.prog a))) (c : N)
    : list (mlstring * (N * N)) :=
  MAP2 (fun x y => (x, y)) (MAP FST prog)
    (MAP2 (fun x y => (x, y)) (GENLIST (fun n => n + c) (LENGTH prog))
          (MAP (fun x => LENGTH (FST (SND x))) prog)).

Definition cp_list (g : list N -> crepLang.prog a -> loopLang.prog a)
    (prog : list (mlstring * (list N * crepLang.prog a))) (c : N)
    : list (N * (list N * loopLang.prog a)) :=
  MAP2 (fun n '(name, (params, body)) => (n, ((GENLIST I ∘ LENGTH) params, g params body)))
    (GENLIST (fun n => n + c) (LENGTH prog)) prog.

Lemma mf_list_cons x prog c :
  mf_list (x :: prog) c = (FST x, (c, LENGTH (FST (SND x)))) :: mf_list prog (c + 1).
Proof. unfold mf_list. cbn [LENGTH]. rewrite GENLIST_shift. reflexivity. Qed.

Lemma cp_list_cons g name params body prog c :
  cp_list g ((name, (params, body)) :: prog) c =
  (c, (GENLIST I (LENGTH params), g params body)) :: cp_list g prog (c + 1).
Proof. unfold cp_list. cbn [LENGTH]. rewrite GENLIST_shift. reflexivity. Qed.

Lemma mf_list_ge : forall prog c x n r, ALOOKUP (mf_list prog c) x = SOME (n, r) -> c <= n.
Proof.
  induction prog as [|[f [ns p]] prog IH]; intros c x n r H; [discriminate|].
  rewrite mf_list_cons in H. cbn [ALOOKUP FST SND] in H.
  destruct (decide (f = x)); [injection H as <- _; lia|]. apply IH in H. lia.
Qed.

Lemma mf_list_found : forall prog c f ns p0 g,
  ALOOKUP prog f = SOME (ns, p0) ->
  exists i, ALOOKUP (mf_list prog c) f = SOME (i + c, LENGTH ns) /\
            ALOOKUP (cp_list g prog c) (i + c) = SOME (GENLIST I (LENGTH ns), g ns p0).
Proof.
  induction prog as [|[f' [ns' p']] prog IH]; intros c f ns p0 g H; [discriminate|].
  rewrite mf_list_cons, cp_list_cons. cbn [ALOOKUP FST SND] in H |- *.
  destruct (decide (f' = f)) as [->|Hne].
  - injection H as -> ->. exists 0. rewrite N.add_0_l.
    split; [reflexivity|]. destruct (decide (c = c)); [reflexivity|congruence].
  - destruct (IH (c + 1) f ns p0 g H) as (i & H1 & H2). exists (i + 1).
    split; [rewrite H1; f_equal; f_equal; lia|].
    destruct (decide (c = i + 1 + c)); [lia|]. rewrite <- H2. f_equal. lia.
Qed.

Lemma mf_list_inv : forall prog c f v,
  ALOOKUP (mf_list prog c) f = SOME v -> exists ns p0, ALOOKUP prog f = SOME (ns, p0).
Proof.
  induction prog as [|[f' [ns' p']] prog IH]; intros c f v H; [discriminate|].
  rewrite mf_list_cons in H. cbn [ALOOKUP FST SND] in H |- *.
  destruct (decide (f' = f)); [eexists _, _; reflexivity|]. exact (IH _ _ _ H).
Qed.

Lemma mf_list_inj : forall prog c x y n r r',
  ALOOKUP (mf_list prog c) x = SOME (n, r) -> ALOOKUP (mf_list prog c) y = SOME (n, r') -> x = y.
Proof.
  induction prog as [|[f [ns p]] prog IH]; intros c x y n r r' Hx Hy; [discriminate|].
  rewrite mf_list_cons in Hx, Hy. cbn [ALOOKUP FST SND] in Hx, Hy.
  destruct (decide (f = x)) as [<-|Hfx]; destruct (decide (f = y)) as [<-|Hfy]; try reflexivity.
  - injection Hx as <- _. apply mf_list_ge in Hy. lia.
  - injection Hy as <- _. apply mf_list_ge in Hx. lia.
  - exact (IH _ _ _ _ _ _ Hx Hy).
Qed.

Lemma make_funcs_mf (prog : list (mlstring * (list N * crepLang.prog a))) f :
  FLOOKUP (make_funcs prog) f = ALOOKUP (mf_list prog first_name) f.
Proof. unfold make_funcs. cbv zeta. rewrite FLOOKUP_alist_to_fmap. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "distinct_make_funcs" *)
Theorem distinct_make_funcs : forall (crep_code : list (mlstring * (list N * crepLang.prog a))),
  distinct_funcs (make_funcs crep_code).
Proof.
  intros prog x y n m rm rm' (Hx & Hy & <-). rewrite make_funcs_mf in Hx, Hy.
  exact (mf_list_inj _ _ _ _ _ _ _ Hx Hy).
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "map_map2_fst" *)
Theorem map_map2_fst : forall {A B C D E} (xs : list A) (ys : list (B * (list C * D)))
    (h : list C -> D -> E),
  LENGTH xs = LENGTH ys ->
  MAP FST (MAP2 (fun x '(n, (p, b)) => (x, (GENLIST I (LENGTH p), h p b))) xs ys) = xs.
Proof.
  intros A B C D E xs; induction xs as [|x xs IH]; intros [|[n [p b]] ys] h Hl; cbn in *;
    try lia; [reflexivity|]. f_equal. apply IH. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mem_lookup_fromalist_some" *)
Theorem mem_lookup_fromalist_some : forall {A} `{EqDecision A} (xs : list (N * A)) n x,
  ALL_DISTINCT (MAP FST xs) /\ MEM (n, x) xs -> lookup n (fromAList xs) = SOME x.
Proof.
  intros A EA xs n x [Hd Hm]. rewrite lookup_fromAList. apply ALOOKUP_NoDup_In.
  - apply ALL_DISTINCT_NoDup_list in Hd. exact Hd.
  - apply MEM_In, Hm.
Qed.

Lemma cp_list_keys g prog c : MAP FST (cp_list g prog c) = GENLIST (fun n => n + c) (LENGTH prog).
Proof.
  revert c; induction prog as [|[f [ns p]] prog IH]; intros c; [reflexivity|].
  rewrite cp_list_cons. cbn [LENGTH MAP List.map FST]. rewrite IH, GENLIST_shift. reflexivity.
Qed.

Lemma compile_prog_cp c (prog : list (mlstring * (list N * crepLang.prog a))) :
  compile_prog c prog =
  cp_list (fun params body => loop_live.optimise
             (comp_func c (make_funcs prog) params (crep_arith.simp_prog body))) prog first_name.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "first_compile_prog_all_distinct" *)
Theorem first_compile_prog_all_distinct : forall c (crep_code : list (mlstring * (list N * crepLang.prog a))),
  ALL_DISTINCT (MAP FST (compile_prog c crep_code)).
Proof.
  intros c prog. rewrite compile_prog_cp, cp_list_keys. apply ALL_DISTINCT_GENLIST.
  intros m1 m2 (_ & _ & H). lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel2_def" *)
Definition code_rel2 (ctxt : context) (s_code : fmap mlstring (list N * crepLang.prog a))
    (t_code : spt (list N * loopLang.prog a)) : Prop :=
  code_rel ctxt (FMAP_MAP2 (fun '(s, (n, p)) => (n, crep_arith.simp_prog p)) s_code) t_code.

Lemma MAX_LIST_GENLIST_I n : MAX_LIST (GENLIST I n) = n - 1.
Proof.
  assert (HM : forall m k, MAX m k = N.max m k)
    by (intros m k; unfold MAX; destruct (N.ltb_spec m k); lia).
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm I n)), SNOC_app.
  assert (H : forall l x, MAX_LIST (l ++ [x]) = MAX (MAX_LIST l) x).
  { intros l x; induction l as [|y l IHl]; cbn [MAX_LIST app]; rewrite ?IHl, !HM; lia. }
  rewrite H, IH, HM. unfold I. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "mk_ctxt_code_imp_code_rel2" *)
Theorem mk_ctxt_code_imp_code_rel2 : forall c (crep_code : list (mlstring * (list N * crepLang.prog a)))
    start np,
  ALL_DISTINCT (MAP FST crep_code) /\ ALOOKUP crep_code start = SOME ([], np) ->
  code_rel2 (mk_ctxt c FEMPTY (make_funcs crep_code) 0)
            (alist_to_fmap crep_code)
            (fromAList (compile_prog c crep_code)).
Proof.
  intros c prog start np _. unfold code_rel2, code_rel. cbn [mk_ctxt funcs target].
  split; [apply distinct_make_funcs|].
  intros f ns p Hf. rewrite FLOOKUP_FMAP_MAP2, FLOOKUP_alist_to_fmap in Hf.
  destruct (ALOOKUP prog f) as [[ns0 p0]|] eqn:Ef; [|discriminate].
  cbn in Hf. injection Hf as <- <-.
  destruct (mf_list_found prog first_name f ns0 p0
              (fun params body => loop_live.optimise
                 (comp_func c (make_funcs prog) params (crep_arith.simp_prog body))) Ef)
    as (i & H1 & H2).
  exists (i + first_name), (LENGTH ns0). split; [rewrite make_funcs_mf; exact H1|].
  split; [reflexivity|]. cbv zeta.
  rewrite lookup_fromAList, compile_prog_cp, H2. f_equal. f_equal.
  unfold ocompile, comp_func, ctxt_fc, mk_ctxt, make_vmap. cbv beta zeta.
  rewrite MAX_LIST_GENLIST_I. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "make_funcs_domain_compile_prog" *)
Theorem make_funcs_domain_compile_prog : forall start lc
    (crep_code : list (mlstring * (list N * crepLang.prog a))) c,
  FLOOKUP (make_funcs crep_code) start = SOME (lc, 0) ->
  lc IN domain (fromAList (compile_prog c crep_code)).
Proof.
  intros start lc prog c H. rewrite make_funcs_mf in H.
  destruct (mf_list_inv _ _ _ _ H) as (ns & p0 & Ep).
  destruct (mf_list_found prog first_name start ns p0
              (fun params body => loop_live.optimise
                 (comp_func c (make_funcs prog) params (crep_arith.simp_prog body))) Ep)
    as (i & H1 & H2).
  rewrite H1 in H. injection H as <- _.
  unfold pred_set.IN. apply domain_lookup. rewrite lookup_fromAList, compile_prog_cp, H2.
  eexists; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_prog_distinct_params" *)
Theorem compile_prog_distinct_params : forall (prog : list (mlstring * (list N * crepLang.prog a))) c,
  EVERY (fun '(name, (params, body)) => ALL_DISTINCT params) prog ->
  EVERY (fun '(name, (params, body)) => ALL_DISTINCT params) (compile_prog c prog).
Proof.
  intros prog c _. rewrite compile_prog_cp. generalize first_name.
  generalize (fun (params : list N) (body : crepLang.prog a) => loop_live.optimise
                 (comp_func c (make_funcs prog) params (crep_arith.simp_prog body))) as g.
  intros g. induction prog as [|[f [ns p]] prog IH]; intros k; [reflexivity|].
  rewrite cp_list_cons. cbn [EVERY]. unfold is_true. rewrite Bool.andb_true_iff. split.
  - apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & H). exact H.
  - apply IH.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_to_loop_compile_prog_lab_min" *)
Theorem crep_to_loop_compile_prog_lab_min : forall c (cprog : list (mlstring * (list N * crepLang.prog a)))
    lprog,
  compile_prog c cprog = lprog -> EVERY (fun prog => 60 <=? FST prog) lprog.
Proof.
  intros c prog lprog <-. rewrite compile_prog_cp. unfold first_name.
  assert (Hk : 60 <= 64) by lia. revert Hk. generalize 64.
  generalize (fun (params : list N) (body : crepLang.prog a) => loop_live.optimise
                 (comp_func c (make_funcs prog) params (crep_arith.simp_prog body))) as g.
  intros g. induction prog as [|[f [ns p]] prog IH]; intros k Hk; [reflexivity|].
  rewrite cp_list_cons. cbn [EVERY FST]. unfold is_true. rewrite Bool.andb_true_iff. split.
  - apply N.leb_le. lia.
  - apply IH. lia.
Qed.

End Programs.

(** ** Observable semantics *)

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_run_res" *)
Inductive semantics_run_res (A : Type) : Type :=
| RunError : semantics_run_res A
| CompleteResult : A -> semantics_run_res A
| Incomplete : semantics_run_res A.
Arguments RunError {A}. Arguments CompleteResult {A} _. Arguments Incomplete {A}.

#[local] Instance behaviour_inhabited_c : Inhabited behaviour := ffi.Fail.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_wrapper_def" *)
Definition semantics_wrapper (f : N -> semantics_run_res outcome * list io_event) : behaviour :=
  if classical_dec (exists k v, f k = (RunError, v)) then ffi.Fail
  else match some (fun res => exists k r ev, f k = (CompleteResult r, ev) /\ res = Terminate r ev) with
       | SOME res => res
       | NONE => Diverge (build_lprefix_lub (IMAGE (llist.fromList ∘ SND ∘ f) UNIV))
       end.

Section Wrapper.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "crep_sem_is_wrapper" *)
Theorem crep_sem_is_wrapper : forall (s : crepSem.state a ffi_t) start,
  crepSem.semantics s start =
  let prog := crepLang.Call NONE start [] in
  semantics_wrapper (((fun res => match res with
                                  | SOME crepSem.TimeOut => Incomplete
                                  | SOME (crepSem.FinalFFI e) => CompleteResult (FFI_outcome e)
                                  | SOME (crepSem.Return _) => CompleteResult Success
                                  | _ => RunError
                                  end) ## (fun s => io_events (crepSem.ffi s))) ∘
                     (fun k => crepSem.evaluate (prog, crepSem.set_clock k s))).
Proof.
  intros s start. unfold crepSem.semantics, semantics_wrapper. cbv zeta.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P2 with P1
  end.
  2: { apply propositional_extensionality. split.
       - intros [k Hk]. exists k. eexists. unfold PAIR_MAP.
         destruct (fst (crepSem.evaluate _)) as [[]|]; try contradiction; reflexivity.
       - intros [k [v Hk]]. exists k. pose proof (f_equal fst Hk) as Hk'. clear Hk.
         unfold PAIR_MAP in Hk'. cbv beta in Hk'. cbn [fst] in Hk'.
         destruct (fst (crepSem.evaluate _)) as [[]|]; try discriminate; exact Logic.I. }
  destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q2 with Q1
  end.
  2: { apply functional_extensionality; intros res; apply propositional_extensionality. split.
       - intros (k & t & r & out & H1 & H2 & H3). exists k, out, (io_events (crepSem.ffi t)).
         unfold PAIR_MAP. rewrite H1. cbn [fst snd].
         split; [|exact H3]. destruct r as [[]|]; try contradiction; subst out; reflexivity.
       - intros (k & r & ev & H1 & H2).
         pose proof (f_equal snd H1) as H1'. pose proof (f_equal fst H1) as H1''. clear H1.
         unfold PAIR_MAP in H1', H1''. cbn [fst snd] in H1', H1''. rename H1'' into H1.
         exists k, (snd (crepSem.evaluate (crepLang.Call NONE start [], crepSem.set_clock k s))),
           (fst (crepSem.evaluate (crepLang.Call NONE start [], crepSem.set_clock k s))), r.
         split; [apply surjective_pairing|]. rewrite <- H1' in H2.
         split; [|exact H2].
         destruct (fst (crepSem.evaluate _)) as [[]|]; try discriminate; injection H1 as <-;
           reflexivity. }
  reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "loop_sem_is_wrapper" *)
Theorem loop_sem_is_wrapper : forall (s : loopSem.state a ffi_t) start,
  loopSem.semantics s start =
  let prog := @loopLang.Call a NONE (SOME start) [] NONE in
  semantics_wrapper (((fun res => match res with
                                  | SOME TimeOut => Incomplete
                                  | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
                                  | SOME (Result _) => CompleteResult Success
                                  | _ => RunError
                                  end) ## (fun s => io_events (ffi s))) ∘
                     (fun k => evaluate (prog, set_clock k s))).
Proof.
  intros s start. unfold loopSem.semantics, semantics_wrapper. cbv zeta.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P2 with P1
  end.
  2: { apply propositional_extensionality. split.
       - intros [k Hk]. exists k. eexists. unfold PAIR_MAP.
         destruct (fst (evaluate _)) as [[]|]; try contradiction; reflexivity.
       - intros [k [v Hk]]. exists k. pose proof (f_equal fst Hk) as Hk'. clear Hk.
         unfold PAIR_MAP in Hk'. cbv beta in Hk'. cbn [fst] in Hk'.
         destruct (fst (evaluate _)) as [[]|]; try discriminate; exact Logic.I. }
  destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q2 with Q1
  end.
  2: { apply functional_extensionality; intros res; apply propositional_extensionality. split.
       - intros (k & t & r & out & H1 & H2 & H3). exists k, out, (io_events (ffi t)).
         unfold PAIR_MAP. rewrite H1. cbn [fst snd].
         split; [|exact H3]. destruct r as [[]|]; try contradiction; subst out; reflexivity.
       - intros (k & r & ev & H1 & H2).
         pose proof (f_equal snd H1) as H1'. pose proof (f_equal fst H1) as H1''. clear H1.
         unfold PAIR_MAP in H1', H1''. cbn [fst snd] in H1', H1''. rename H1'' into H1.
         exists k, (snd (evaluate (@loopLang.Call a NONE (SOME start) [] NONE, set_clock k s))),
           (fst (evaluate (@loopLang.Call a NONE (SOME start) [] NONE, set_clock k s))), r.
         split; [apply surjective_pairing|]. rewrite <- H1' in H2.
         split; [|exact H2].
         destruct (fst (evaluate _)) as [[]|]; try discriminate; injection H1 as <-;
           reflexivity. }
  reflexivity.
Qed.

End Wrapper.

Lemma lnth_prefix (l1 l2 : list io_event) n x :
  isPREFIX l1 l2 = true -> LNTH n (llist.fromList l1) = SOME x -> LNTH n (llist.fromList l2) = SOME x.
Proof.
  intros Hp. assert (Hl : LPREFIX (llist.fromList l1) (llist.fromList l2))
    by (apply LPREFIX_fromList; rewrite toList_fromList; exact Hp).
  apply LPREFIX_pfx in Hl. apply Hl.
Qed.

(** HOL's [IS_PREFIX ev ev'] (that is, [ev'] is a prefix of [ev]) is
    written [isPREFIX ev' ev]. *)
(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_wrapper_eq" *)
Theorem semantics_wrapper_eq : forall absf concf,
  semantics_wrapper absf <> ffi.Fail ->
  (forall k r ev, absf k = (r, ev) /\ r <> RunError -> exists k', concf (k + k') = (r, ev)) ->
  (forall k k' r ev, concf k = (r, ev) -> r <> Incomplete -> concf (k + k') = (r, ev)) ->
  (forall k k' r ev, absf k = (r, ev) -> r <> Incomplete -> absf (k + k') = (r, ev)) ->
  (forall k k' ev, absf (k + k') = (Incomplete, ev) ->
     exists r' ev', absf k = (r', ev') /\ isPREFIX ev' ev) ->
  (forall k k' ev, concf (k + k') = (Incomplete, ev) ->
     exists r' ev', concf k = (r', ev') /\ isPREFIX ev' ev) ->
  semantics_wrapper concf = semantics_wrapper absf.
Proof.
  intros absf concf HF H2 H3 H4 H5 H6. unfold semantics_wrapper in HF |- *.
  assert (nRI : (RunError : semantics_run_res outcome) <> Incomplete) by discriminate.
  assert (nCI : forall r, (CompleteResult r : semantics_run_res outcome) <> Incomplete) by discriminate.
  assert (nCR : forall r, (CompleteResult r : semantics_run_res outcome) <> RunError) by discriminate.
  assert (nIR : (Incomplete : semantics_run_res outcome) <> RunError) by discriminate.
  destruct (classical_dec (exists k v, absf k = (RunError, v))) as [Ha|Ha]; [contradiction|].
  clear HF.
  assert (Hcr : forall k r ev, concf k = (r, ev) -> r <> Incomplete -> absf k = (r, ev)).
  { intros k r ev Hc Hr. destruct (absf k) as [ra eva] eqn:Ea.
    assert (Hra : ra <> RunError) by (intros ->; apply Ha; eexists _, _; exact Ea).
    destruct (H2 k ra eva (conj Ea Hra)) as [k' Hk'].
    rewrite (H3 k k' r ev Hc Hr) in Hk'. injection Hk' as -> ->. reflexivity. }
  destruct (classical_dec (exists k v, concf k = (RunError, v))) as [Hc|Hc].
  { exfalso. destruct Hc as (k & v & Hk). apply Ha. exists k, v.
    exact (Hcr k RunError v Hk nRI). }
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q1 with Q2
  end.
  2: { apply functional_extensionality; intros res; apply propositional_extensionality. split.
       - intros (k & r & ev & Hk & ->). destruct (H2 k (CompleteResult r) ev (conj Hk (nCR r))) as [k' Hk'].
         exists (k + k'), r, ev. split; [exact Hk'|reflexivity].
       - intros (k & r & ev & Hk & ->). exists k, r, ev.
         split; [exact (Hcr k _ ev Hk (nCI r))|reflexivity]. }
  destruct (some _) eqn:Es; [reflexivity|].
  assert (Hnc : forall k r ev, absf k <> (CompleteResult r, ev)).
  { intros k r ev Hk. unfold some in Es. destruct (classical_dec _) as [_|Hn]; [discriminate|].
    apply Hn. exists (Terminate r ev), k, r, ev. split; [exact Hk|reflexivity]. }
  assert (HaI : forall k, absf k = (Incomplete, SND (absf k))).
  { intros k. destruct (absf k) as [[|r|] ev] eqn:E.
    - exfalso; apply Ha; eexists _, _; exact E.
    - exfalso; exact (Hnc k r ev E).
    - reflexivity. }
  assert (HcI : forall k, concf k = (Incomplete, SND (concf k))).
  { intros k. destruct (concf k) as [[|r|] ev] eqn:E.
    - exfalso; apply Hc; eexists _, _; exact E.
    - exfalso. pose proof (Hcr k _ ev E (nCI r)) as Ea. exact (Hnc k r ev Ea).
    - reflexivity. }
  assert (Pre : forall (f : N -> semantics_run_res outcome * list io_event),
             (forall k k' ev, f (k + k') = (Incomplete, ev) ->
                exists r' ev', f k = (r', ev') /\ isPREFIX ev' ev) ->
             (forall k, f k = (Incomplete, SND (f k))) ->
             forall k1 k2, k1 <= k2 -> isPREFIX (SND (f k1)) (SND (f k2))).
  { intros f Hf HI k1 k2 Hle. replace k2 with (k1 + (k2 - k1)) by lia.
    destruct (Hf k1 (k2 - k1) _ (HI (k1 + (k2 - k1)))) as (r' & ev' & E1 & Hp).
    rewrite E1. exact Hp. }
  assert (Chain : forall (f : N -> semantics_run_res outcome * list io_event),
             (forall k1 k2, k1 <= k2 -> isPREFIX (SND (f k1)) (SND (f k2))) ->
             lprefix_chain (IMAGE (llist.fromList ∘ SND ∘ f) UNIV)).
  { intros f Hp.
    change (IMAGE (llist.fromList ∘ SND ∘ f) UNIV) with (IMAGE (llist.fromList ∘ (SND ∘ f)) UNIV).
    rewrite IMAGE_COMPOSE. apply prefix_chain_lprefix_chain.
    intros l1 l2 [H1 H2']. apply IN_IMAGE in H1 as (k1 & -> & _). apply IN_IMAGE in H2' as (k2 & -> & _).
    destruct (N.le_ge_cases k1 k2); [left; apply Hp; lia|right; apply Hp; lia]. }
  pose proof (Pre absf H5 HaI) as Pa. pose proof (Pre concf H6 HcI) as Pc.
  assert (E : equiv_lprefix_chain (IMAGE (llist.fromList ∘ SND ∘ concf) UNIV)
                                  (IMAGE (llist.fromList ∘ SND ∘ absf) UNIV)).
  { apply equiv_lprefix_chain_thm; [split; apply Chain; assumption|]. split.
    - intros ll1 n x [Hl Hx]. apply IN_IMAGE in Hl as (k & -> & _).
      destruct (H2 k Incomplete (SND (absf k)) (conj (HaI k) nIR)) as [k' Hk'].
      exists (llist.fromList (SND (absf k))). split.
      + apply IN_IMAGE. exists k. split; [reflexivity|exact Logic.I].
      + apply (lnth_prefix (SND (concf k))); [|exact Hx].
        destruct (H6 k k' _ Hk') as (r' & ev' & Ec & Hp). rewrite Ec. exact Hp.
    - intros ll2 n x [Hl Hx]. apply IN_IMAGE in Hl as (k & -> & _).
      destruct (H2 k Incomplete (SND (absf k)) (conj (HaI k) nIR)) as [k' Hk'].
      exists (llist.fromList (SND (concf (k + k')))). split.
      + apply IN_IMAGE. exists (k + k'). split; [reflexivity|exact Logic.I].
      + rewrite Hk'. exact Hx. }
  f_equal. unfold build_lprefix_lub, build_lprefix_lub_f. f_equal.
  apply functional_extensionality; intros n. rewrite (E n). reflexivity.
Qed.

Section SemanticsProof.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "evaluate_Seq_Skip" *)
Theorem evaluate_Seq_Skip : forall (prog : loopLang.prog a) (s : loopSem.state a ffi_t),
  evaluate (Seq prog Skip, s) = evaluate (prog, s).
Proof.
  intros p s. rewrite ev_Seq. destruct (evaluate (p, s)) as [[r|] t]; [reflexivity|apply ev_Skip].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel_evaluate_call_correct" *)
Theorem code_rel_evaluate_call_correct : forall nctxt s_code t_code start
    (s : crepSem.state a ffi_t) res s' (t : loopSem.state a ffi_t)
    (crep_code : list (mlstring * (list N * crepLang.prog a))) lc prog,
  code_rel2 nctxt s_code t_code ->
  crepSem.evaluate (crepLang.Call NONE start [], s) = (res, s') ->
  crepSem.be s = be t /\ crepSem.sh_memaddrs s = sh_mdomain t /\
  crepSem.memaddrs s = mdomain t /\ crepSem.clock s = clock t /\
  crepSem.ffi s = ffi t /\ crepSem.base_addr s = base_addr t /\
  crepSem.top_addr s = top_addr t /\
  mem_rel (crepSem.memory s) (memory t) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals t) /\
  crepSem.locals s = FEMPTY /\
  crepSem.code s = s_code /\ code t = t_code ->
  FLOOKUP (make_funcs crep_code) start = SOME (find_lab nctxt start, 0) ->
  find_lab nctxt start = lc /\
  crepSem.code s = alist_to_fmap crep_code /\
  funcs nctxt = make_funcs crep_code /\
  ALOOKUP crep_code start = SOME ([], prog) /\
  distinct_vars (vars nctxt) /\ ctxt_max (vmax nctxt) (vars nctxt) ->
  res <> SOME crepSem.Error ->
  exists k res' t',
    evaluate (Call NONE (SOME (find_lab nctxt start)) [] NONE, set_clock (clock t + k) t) =
      (res', t') /\
    state_rel s' t' /\
    res' = match res with
           | NONE => NONE
           | SOME (crepSem.Break n) => SOME (Break n)
           | SOME (crepSem.Continue n) => SOME (Continue n)
           | SOME (crepSem.Return vs) => SOME (Result (MAP wlab_wloc vs))
           | SOME (crepSem.Exception eid) => SOME (Exception (Word eid))
           | SOME crepSem.TimeOut => SOME TimeOut
           | SOME (crepSem.FinalFFI f) => SOME (FinalFFI f)
           | SOME crepSem.Error => SOME Error
           end.
Proof.
  intros nctxt s_code t_code start s res s' t crep_code lc prog Hc He
    (Hbe & Hsh & Hmd & Hck & Hff & Hba & Hta & Hm & Hg & Hl & Hsc & Htc) _ (_ & _ & _ & _ & Hd & Hmx) Hne.
  pose proof (crep_arithProof.simp_prog_correct _ _ _ _ He Hne) as Hs. cbn in Hs.
  set (m := FMAP_MAP2 (fun '(s0, (n, p)) => (n, crep_arith.simp_prog p))) in Hs.
  destruct (ncompile_correct (crepLang.Call NONE start []) (crepSem.set_code (m (crepSem.code s)) s)
              res (crepSem.set_code (m (crepSem.code s')) s') t nctxt LN)
    as (ck & res1 & t1 & T & S1 & _ & _ & _ & Eq & _).
  { split; [exact Hs|]. split; [exact Hne|].
    split; [repeat split; assumption|]. split; [exact Hm|]. split; [exact Hg|].
    split; [cbn [crepSem.set_code crepSem.code]; rewrite Hsc, Htc; exact Hc|].
    split; [exact Hd|]. split; [exact Hmx|]. split.
    - intros k Hk. unfold pred_set.IN in Hk. cbn in Hk. contradiction.
    - intros vn v Hv. cbn [crepSem.set_code crepSem.locals] in Hv. rewrite Hl in Hv. discriminate. }
  exists ck, res1, t1. split.
  - cbn [compile compile_exps] in T.
    match type of T with context [gen_temps ?x ?y] => change (gen_temps x y) with (@nil N) in T end.
    cbn [MAP2 app nested_seq] in T.
    rewrite evaluate_Seq_Skip in T. exact T.
  - split; [exact S1|exact Eq].
Qed.

(*! HOL "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics : forall (s : crepSem.state a ffi_t) (t : loopSem.state a ffi_t)
    (crep_code : list (mlstring * (list N * crepLang.prog a))) start lc c,
  crepSem.memaddrs s = mdomain t /\
  crepSem.be s = be t /\ crepSem.sh_memaddrs s = sh_mdomain t /\
  crepSem.ffi s = ffi t /\ crepSem.base_addr s = base_addr t /\ crepSem.top_addr s = top_addr t /\
  mem_rel (crepSem.memory s) (memory t) (crepSem.memaddrs s) /\
  globals_rel (crepSem.globals s) (globals t) /\
  ALL_DISTINCT (MAP FST crep_code) /\
  crepSem.code s = alist_to_fmap crep_code /\
  code t = fromAList (compile_prog c crep_code) /\
  crepSem.locals s = FEMPTY /\
  FLOOKUP (make_funcs crep_code) start = SOME (lc, 0) /\
  crepSem.semantics s start <> ffi.Fail ->
  loopSem.semantics t lc = crepSem.semantics s start.
Proof.
  intros s t prog start lc c
    (Hmd & Hbe & Hsh & Hff & Hba & Hta & Hm & Hg & Hdist & Hsc & Htc & Hl & Hf & Hsem).
  rewrite crep_sem_is_wrapper in Hsem |- *. rewrite loop_sem_is_wrapper. cbv zeta in Hsem |- *.
  set (absf := ((fun res => match res with
                            | SOME crepSem.TimeOut => Incomplete
                            | SOME (crepSem.FinalFFI e) => CompleteResult (FFI_outcome e)
                            | SOME (crepSem.Return _) => CompleteResult Success
                            | _ => RunError
                            end) ## (fun s => io_events (crepSem.ffi s))) ∘
                (fun k => crepSem.evaluate (crepLang.Call NONE start [], crepSem.set_clock k s)))
    in Hsem |- *.
  set (concf := ((fun res => match res with
                             | SOME TimeOut => Incomplete
                             | SOME (FinalFFI e) => CompleteResult (FFI_outcome e)
                             | SOME (Result _) => CompleteResult Success
                             | _ => RunError
                             end) ## (fun s => io_events (ffi s))) ∘
                 (fun k => evaluate (@loopLang.Call a NONE (SOME lc) [] NONE, set_clock k t))).
  assert (HRE : forall k, fst (absf k) <> RunError).
  { intros k Hk. apply Hsem. unfold semantics_wrapper.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|]. exfalso; apply Hn.
    exists k, (snd (absf k)). rewrite <- Hk. apply surjective_pairing. }
  assert (Hprog : exists p, ALOOKUP prog start = SOME ([], p)).
  { pose proof (HRE 1) as H1. unfold absf, PAIR_MAP in H1. cbv beta in H1. cbn [fst] in H1.
    rewrite crep_unfold in H1. cbn [crepSem.evaluate_body OPT_MMAP crepSem.lookup_code
                                   crepSem.code crepSem.set_clock LENGTH] in H1.
    unfold crepSem.lookup_code in H1. rewrite Hsc, FLOOKUP_alist_to_fmap in H1.
    destruct (ALOOKUP prog start) as [[ns p]|]; [|exfalso; apply H1; reflexivity].
    destruct ns as [|n0 ns]; [eexists; reflexivity|].
    exfalso; apply H1. cbn [LENGTH]. destruct (N.eqb_spec (N.succ (LENGTH ns)) 0); [lia|].
    reflexivity. }
  destruct Hprog as [p Hp].
  set (nctxt := mk_ctxt c FEMPTY (make_funcs prog) 0).
  assert (Hlab : find_lab nctxt start = lc)
    by (unfold find_lab, nctxt, mk_ctxt; cbn [crep_to_loop.funcs]; rewrite Hf; reflexivity).
  assert (Hcr : code_rel2 nctxt (alist_to_fmap prog) (fromAList (compile_prog c prog)))
    by (apply (mk_ctxt_code_imp_code_rel2 c prog start p); split; assumption).
  apply semantics_wrapper_eq; [exact Hsem| | | | |].
  - intros k r ev (Hk & Hr).
    destruct (crepSem.evaluate (crepLang.Call NONE start [], crepSem.set_clock k s)) as [res s'] eqn:E.
    assert (Hres : res <> SOME crepSem.Error).
    { intros ->. unfold absf, PAIR_MAP in Hk. cbv beta in Hk. rewrite E in Hk. cbn in Hk.
      injection Hk as <- _. congruence. }
    destruct (code_rel_evaluate_call_correct nctxt (alist_to_fmap prog) (fromAList (compile_prog c prog))
                start (crepSem.set_clock k s) res s' (set_clock k t) prog lc p Hcr E)
      as (k' & res' & t' & T & S1 & Eq).
    + cbn [crepSem.set_clock crepSem.be crepSem.sh_memaddrs crepSem.memaddrs crepSem.clock crepSem.ffi
           crepSem.base_addr crepSem.top_addr crepSem.memory crepSem.globals crepSem.locals crepSem.code
           set_clock be sh_mdomain mdomain clock ffi base_addr top_addr memory globals code].
      repeat split; assumption.
    + rewrite Hlab. exact Hf.
    + split; [exact Hlab|]. split; [exact Hsc|]. split; [reflexivity|]. split; [exact Hp|].
      split; [intros x y n m (Hx & _); discriminate|intros v m Hv; discriminate].
    + exact Hres.
    + exists k'. rewrite Hlab in T. cbn [clock set_clock] in T.
      replace (set_clock (k + k') (set_clock k t)) with (set_clock (k + k') t) in T
        by (destruct t; reflexivity).
      unfold concf, absf, PAIR_MAP in Hk |- *. cbv beta in Hk |- *. rewrite T. rewrite E in Hk.
      cbn [fst snd] in Hk |- *. injection Hk as <- <-. subst res'.
      destruct S1 as (_ & _ & _ & _ & Hff' & _). rewrite Hff'.
      destruct res as [[]|]; reflexivity.
  - intros k k' r ev Hk Hr.
    unfold concf, PAIR_MAP in Hk |- *. cbv beta in Hk |- *.
    destruct (evaluate (@loopLang.Call a NONE (SOME lc) [] NONE, set_clock k t)) as [q u] eqn:E.
    cbn [fst snd] in Hk. injection Hk as Hq Hu.
    assert (Hqt : q <> SOME TimeOut) by (intros ->; apply Hr; rewrite <- Hq; reflexivity).
    pose proof (evaluate_add_clock_eq _ _ _ _ k' (conj E Hqt)) as E'.
    cbn [clock set_clock] in E'. replace (set_clock (k + k') (set_clock k t)) with (set_clock (k + k') t)
      in E' by (destruct t; reflexivity).
    rewrite E'. cbn [fst snd ffi set_clock]. rewrite Hq, Hu. reflexivity.
  - intros k k' r ev Hk Hr.
    unfold absf, PAIR_MAP in Hk |- *. cbv beta in Hk |- *.
    destruct (crepSem.evaluate (crepLang.Call NONE start [], crepSem.set_clock k s)) as [q u] eqn:E.
    cbn [fst snd] in Hk. injection Hk as Hq Hu.
    assert (Hqt : q <> SOME crepSem.TimeOut) by (intros ->; apply Hr; rewrite <- Hq; reflexivity).
    pose proof (crepProps.evaluate_add_clock_eq _ _ _ _ k' (conj E Hqt)) as E'.
    cbn [crepSem.clock crepSem.set_clock] in E'.
    replace (crepSem.set_clock (k + k') (crepSem.set_clock k s)) with (crepSem.set_clock (k + k') s)
      in E' by (destruct s; reflexivity).
    rewrite E'. cbn [fst snd crepSem.ffi crepSem.set_clock]. rewrite Hq, Hu. reflexivity.
  - intros k k' ev Hk.
    exists (fst (absf k)), (snd (absf k)). split; [apply surjective_pairing|].
    unfold absf, PAIR_MAP in Hk |- *. cbv beta in Hk |- *. cbn [snd] in Hk |- *.
    injection Hk as _ <-.
    pose proof (crepProps.evaluate_add_clock_io_events_mono (crepLang.Call NONE start [])
                  (crepSem.set_clock k s) k') as P.
    cbn [crepSem.clock crepSem.set_clock] in P.
    replace (crepSem.set_clock (k + k') (crepSem.set_clock k s)) with (crepSem.set_clock (k + k') s)
      in P by (destruct s; reflexivity).
    exact P.
  - intros k k' ev Hk.
    exists (fst (concf k)), (snd (concf k)). split; [apply surjective_pairing|].
    unfold concf, PAIR_MAP in Hk |- *. cbv beta in Hk |- *. cbn [snd] in Hk |- *.
    injection Hk as _ <-.
    pose proof (evaluate_add_clock_io_events_mono (@loopLang.Call a NONE (SOME lc) [] NONE)
                  (set_clock k t) k') as P.
    cbn [clock set_clock] in P.
    replace (set_clock (k + k') (set_clock k t)) with (set_clock (k + k') t)
      in P by (destruct t; reflexivity).
    exact P.
Qed.

End SemanticsProof.
