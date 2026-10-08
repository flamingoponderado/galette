(** * Pancake [loop_liveProof]: correctness of [loop_live]

    Port of [cakeml/pancake/proofs/loop_liveProofScript.sml].

    Proof notes: HOL's [recInduct evaluate_ind] is well-founded induction on
    [eval_lt] ([loopSem]).  Inside the proofs, HOL's
    [subspt (inter m X) n] is restated as the Galette-only predicate
    [agree X m n] (keys of [X] bound in [m] are bound to the same value in
    [n]), and the case analysis of [compile_correct]'s conclusion as
    [post]; these, [state_ext] and the [domain] helpers below have no HOL
    original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
Import wordLang(word_loc(..)).
From Galette.cakeml.pancake Require Import loopLang loop_call loop_live.
From Galette.cakeml.pancake.semantics Require Import loopSem loopProps.
From Galette.cakeml.pancake.proofs Require loop_callProof.
#[local] Abbreviation list_delete := backend_common.list_delete.
Open Scope N_scope.

(** ** Galette-only helpers *)

Section Helpers.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma state_ext s t :
  locals s = locals t -> globals s = globals t -> memory s = memory t ->
  mdomain s = mdomain t -> sh_mdomain s = sh_mdomain t -> clock s = clock t ->
  code s = code t -> be s = be t -> ffi s = ffi t -> base_addr s = base_addr t ->
  top_addr s = top_addr t -> s = t.
Proof. destruct s, t; cbn; intros; subst; reflexivity. Qed.

End Helpers.

Section Agree.
Context {A B : Type} {EA : EqDecision A}.

(** [agree X m n]: HOL's [subspt (inter m X) n]. *)
Definition agree (X : spt B) (m n : spt A) : Prop :=
  forall k y, domain X k -> lookup k m = SOME y -> lookup k n = SOME y.

Lemma subspt_inter_agree (m n : spt A) (X : spt B) :
  subspt (inter m X) n <-> agree X m n.
Proof.
  rewrite subspt_lookup; unfold agree; split.
  - intros H k y Hk Hm; apply H; rewrite lookup_inter_alt.
    destruct (decide (domain X k)); [exact Hm|contradiction].
  - intros H k y Hm; rewrite lookup_inter_alt in Hm.
    destruct (decide (domain X k)) as [Hk|]; [exact (H k y Hk Hm)|discriminate].
Qed.

Lemma agree_dom X m n k : agree X m n -> domain X k -> domain m k -> domain n k.
Proof.
  intros H Hx Hm; rewrite domain_lookup in Hm |- *; destruct Hm as [y Hy].
  exists y; exact (H k y Hx Hy).
Qed.

Lemma dom_fromAList_tt (args : list N) k :
  domain (fromAList (MAP (fun x => (x, tt)) args)) k <-> In k args.
Proof.
  rewrite domain_fromAList; cbn beta. unfold is_true; rewrite MEM_In.
  induction args as [|x xs IH]; cbn; [tauto|]. rewrite IH; intuition.
Qed.

Lemma dom_list_delete (vs : list N) (t : spt A) k :
  domain (list_delete vs t) k <-> domain t k /\ ~ In k vs.
Proof.
  rewrite !domain_lookup, backend_common.lookup_list_delete.
  destruct (MEM k vs) eqn:E.
  - apply MEM_In in E; split; [intros [y Hy]; discriminate|tauto].
  - assert (~ In k vs) by (intros Hc; apply MEM_In in Hc; congruence). tauto.
Qed.

Lemma lookup_inter_some (m : spt A) (X : spt B) k y :
  lookup k (inter m X) = SOME y <-> lookup k m = SOME y /\ domain X k.
Proof.
  rewrite lookup_inter_alt; destruct (decide (domain X k)); intuition congruence.
Qed.

End Agree.

(** Rewrite [domain] of [sptree] operations into propositions. *)
Ltac dom_simp :=
  repeat first
    [ rewrite domain_union in * | rewrite domain_inter in * | rewrite domain_insert in *
    | rewrite domain_delete in * ];
  cbv beta in *;
  repeat match goal with
         | H : context [domain (fromAList (MAP (fun x => (x, tt)) ?l)) ?k] |- _ =>
             rewrite dom_fromAList_tt in H
         | |- context [domain (fromAList (MAP (fun x => (x, tt)) ?l)) ?k] =>
             rewrite dom_fromAList_tt
         | H : context [domain (list_delete ?l ?t) ?k] |- _ => rewrite dom_list_delete in H
         | |- context [domain (list_delete ?l ?t) ?k] => rewrite dom_list_delete
         | H : context [domain (list_insert ?l ?t) ?k] |- _ => rewrite domain_list_insert in H
         | |- context [domain (list_insert ?l ?t) ?k] => rewrite domain_list_insert
         end.

Section Proofs.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** ** Liveness of expressions *)

Lemma vars_of_exp_dom : forall (e : exp a) (l : num_set) k,
  domain (vars_of_exp e l) k <-> In k (locals_touched e) \/ domain l k.
Proof.
  intros e; induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2| |] using exp_nested_ind;
    intros l k; cbn [vars_of_exp locals_touched In]; try tauto.
  - rewrite domain_insert; cbv beta; intuition.
  - exact (IH l k).
  - revert l k; induction IH as [|x xs Hx Hxs IHxs]; intros l k; cbn [MAP FLAT In]; [tauto|].
    rewrite Hx, IHxs, in_app_iff; tauto.
  - rewrite IH1, IH2, in_app_iff; tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "vars_of_exp_acc" *)
Theorem vars_of_exp_acc : forall (exp : exp a) l,
  domain (vars_of_exp exp l) = domain (union (vars_of_exp exp LN) l).
Proof.
  intros e l; apply set_ext; intros k; rewrite domain_union; cbv beta.
  rewrite !vars_of_exp_dom. assert (HLN : ~ domain (@LN unit) k) by (cbn; tauto). intuition.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "vars_of_exp_mono" *)
Theorem vars_of_exp_mono : forall (exp : exp a) l, subspt l (vars_of_exp exp l).
Proof.
  intros e l; apply subspt_lookup; intros k [] Hk.
  assert (Hd : domain (vars_of_exp e l) k)
    by (apply vars_of_exp_dom; right; apply domain_lookup; eauto).
  apply domain_lookup in Hd as [[] Hd]; exact Hd.
Qed.

Lemma the_words_agree (es : list (exp a)) s (L : spt (word_loc a)) ws :
  Forall (fun e => forall w, eval s e = SOME w -> eval (set_locals L s) e = SOME w) es ->
  the_words (MAP (eval s) es) = SOME ws -> the_words (MAP (eval (set_locals L s)) es) = SOME ws.
Proof.
  intros HF; revert ws; induction HF as [|e es He _ IH]; intros ws H; [exact H|].
  cbn [MAP the_words] in H |- *.
  destruct (eval s e) as [[w|]|] eqn:E; try discriminate.
  destruct (the_words (MAP (eval s) es)) as [xs|] eqn:E2; [|discriminate].
  rewrite (He _ eq_refl), (IH xs eq_refl). exact H.
Qed.

Lemma eval_touched (e : exp a) s (L : spt (word_loc a)) w :
  (forall k y, In k (locals_touched e) -> lookup k (locals s) = SOME y -> lookup k L = SOME y) ->
  eval s e = SOME w -> eval (set_locals L s) e = SOME w.
Proof.
  revert w; induction e as [c|n|n|e IH|op es IH|sh e1 e2 IH1 IH2| |] using exp_nested_ind;
    intros w HL H; cbn [eval locals_touched] in *; try exact H.
  - apply HL; [left; reflexivity|exact H].
  - destruct (eval s e) as [[v|]|] eqn:E; try discriminate.
    rewrite (IH (Word v) HL eq_refl). exact H.
  - destruct (the_words (MAP (eval s) es)) as [ws|] eqn:E; [|discriminate].
    rewrite (the_words_agree es s L ws); [exact H| |exact E].
    rewrite Forall_forall in IH |- *. intros x Hx v Hv. apply (IH x Hx v); [|exact Hv].
    intros k y Hk; apply HL. apply in_concat. exists (locals_touched x); split; [|exact Hk].
    apply in_map; exact Hx.
  - destruct (eval s e1) as [[v1|]|] eqn:E1; try discriminate.
    destruct (eval s e2) as [[v2|]|] eqn:E2; try discriminate.
    rewrite (IH1 (Word v1)), (IH2 (Word v2)); try reflexivity; try exact H;
      intros k y Hk; apply HL; apply in_or_app; auto.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "eval_lemma'" *)
Theorem eval_lemma' : forall locals s (exp : exp a) w (l : num_set),
  eval s exp = SOME w /\ subspt (loopSem.locals s) locals ->
  eval (set_locals locals s) exp = SOME w.
Proof.
  intros L s e w l [H Hs]. apply eval_touched; [|exact H].
  intros k y _ Hk. rewrite subspt_lookup in Hs. exact (Hs k y Hk).
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "eval_lemma" *)
Theorem eval_lemma : forall locals s (exp : exp a) w l,
  eval s exp = SOME w /\ subspt (inter (loopSem.locals s) (vars_of_exp exp l)) locals ->
  eval (set_locals locals s) exp = SOME w.
Proof.
  intros L s e w l [H Hs]. rewrite subspt_inter_agree in Hs.
  apply eval_touched; [|exact H].
  intros k y Hk Hy. apply (Hs k y); [apply vars_of_exp_dom; left; exact Hk|exact Hy].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "domain_list_delete" *)
Theorem domain_list_delete : forall {A} vs (s : spt A),
  domain (list_delete vs s) = domain s DIFF set vs.
Proof.
  intros A vs t; apply set_ext; intros k; rewrite dom_list_delete.
  unfold pred_set.DIFF; rewrite IN_set. unfold pred_set.IN. tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "dom_vars_of_exp_in" *)
Theorem dom_vars_of_exp_in : forall v (l : num_set) (x : exp a),
  v IN domain l -> v IN domain (vars_of_exp x l).
Proof. intros v l x H; unfold pred_set.IN in *; apply vars_of_exp_dom; right; exact H. Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "subspt_IMP_domain" *)
Theorem subspt_IMP_domain : forall {A} `{EqDecision A} (l1 l2 : spt A),
  subspt l1 l2 -> domain l1 SUBSET domain l2.
Proof.
  intros A EA l1 l2 H k Hk; unfold pred_set.IN in *; rewrite subspt_def in H; apply H; exact Hk.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "subspt_inter_domain_cut" *)
Theorem subspt_inter_domain_cut : forall {A B} `{EqDecision A} (X : spt B) (m1 m2 : spt A),
  domain X SUBSET domain m1 /\ subspt (inter m1 X) m2 ->
  domain X SUBSET domain m2.
Proof.
  intros A B EA X m1 m2 [H1 H2] k Hk; unfold pred_set.IN in *. rewrite subspt_inter_agree in H2.
  exact (agree_dom _ _ _ _ H2 Hk (H1 k Hk)).
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "subspt_inter_union_R" *)
Theorem subspt_inter_union_R : forall {T U} `{EqDecision T} (A : spt T) (B C : spt U) D,
  subspt (inter A (union B C)) D -> subspt (inter A C) D.
Proof.
  intros T U ET A B C D; rewrite !subspt_inter_agree; intros H k y Hk Hy.
  apply (H k y); [rewrite domain_union; right; exact Hk|exact Hy].
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "get_vars_subspt" *)
Theorem get_vars_subspt : forall rhss ws s (extra : num_set) locals,
  get_vars rhss s = SOME ws /\
  subspt (inter (loopSem.locals s) (list_insert rhss extra)) locals ->
  get_vars rhss (set_locals locals s) = SOME ws.
Proof.
  intros rhss ws s extra L [H Hs]; rewrite subspt_inter_agree in Hs.
  revert ws H; induction rhss as [|r rs IH]; intros ws H; [exact H|].
  cbn [get_vars] in H |- *; state_cbn.
  destruct (lookup r (locals s)) as [y|] eqn:E; [|discriminate].
  destruct (get_vars rs s) as [ys|] eqn:E2; [|discriminate].
  rewrite (Hs r y); [|rewrite domain_list_insert; left; apply MEM_In; left; reflexivity|exact E].
  assert (Hs' : agree (list_insert rs extra) (locals s) L).
  { intros k z Hk Hz; apply (Hs k z); [|exact Hz].
    rewrite domain_list_insert in Hk |- *. unfold is_true in *. rewrite !MEM_In in *.
    cbn [In]. tauto. }
  clear Hs; specialize (IH Hs').
  rewrite (IH ys eq_refl). exact H.
Qed.

(** ** [compile_correct] *)

Lemma cut_state_tgt (X : num_set) (L : spt (word_loc a)) s :
  domain X SUBSET domain L -> cut_state X (set_locals L s) = SOME (set_locals (inter L X) s).
Proof.
  intros H; unfold cut_state; cbn [locals set_locals].
  destruct (classical_dec _) as [_|Hn]; [reflexivity|contradiction].
Qed.

Lemma cut_agree live (X l0 : num_set) t (n : spt (word_loc a)) res t1 :
  (forall k, domain X k <-> domain l0 k /\ domain live k) ->
  cut_res live (NONE, t) = (res, t1) -> res <> SOME Error -> agree X (locals t) n ->
  exists nl, cut_res X (NONE, set_locals n t) = (res, set_locals nl t1) /\
    (res = NONE -> agree l0 (locals t1) nl) /\ (res <> NONE -> nl = locals t1).
Proof.
  intros HX H Hne Ha. cbn [cut_res IS_SOME] in H |- *.
  unfold cut_state in H.
  destruct (classical_dec (domain live SUBSET domain (locals t))) as [Hd|Hd];
    [|injection H as <- _; congruence].
  rewrite cut_state_tgt.
  2: { intros k Hk; unfold pred_set.IN in *. apply HX in Hk as Hk'; destruct Hk' as [Hk1 Hk2].
       eapply agree_dom; [exact Ha|exact Hk|apply Hd; exact Hk2]. }
  cbn [clock set_locals] in H |- *.
  destruct (clock t =? 0) eqn:Ec.
  - injection H as <- <-. exists LN. split; [f_equal; apply state_ext; reflexivity|].
    split; [discriminate|intros _; reflexivity].
  - injection H as <- <-. exists (inter n X). split; [f_equal; apply state_ext; reflexivity|].
    split; [|congruence].
    intros _ k y Hk Hy. cbn [locals dec_clock set_clock set_locals] in Hy.
    apply lookup_inter_some in Hy as [Hy Hl]. apply lookup_inter_some.
    split; [apply Ha; [apply HX; auto|exact Hy]|apply HX; auto].
Qed.

(** The case analysis of [compile_correct]'s conclusion, with [agree]. *)
Definition post (lt : list (num_set * num_set)) (l0 : num_set) (res : option (result a))
    (sl nl : spt (word_loc a)) : Prop :=
  match res with
  | NONE => agree l0 sl nl
  | SOME (Break n) => match oEL n lt with SOME (_, brk) => agree brk sl nl | NONE => True end
  | SOME (Continue n) => match oEL n lt with SOME (cont, _) => agree cont sl nl | NONE => True end
  | SOME _ => nl = sl
  end.

Lemma post_refl lt l0 r (sl : spt (word_loc a)) : post lt l0 (SOME r) sl sl.
Proof.
  destruct r; cbn [post]; try reflexivity;
    match goal with |- match ?x with _ => _ end => destruct x as [[]|] end;
    cbn beta iota; try exact Logic.I; intros k y _ Hy; exact Hy.
Qed.

Lemma ALOOKUP_ZIP_None (xs : list N) (ys : list (word_loc a)) k :
  LENGTH xs = LENGTH ys -> ALOOKUP (ZIP (xs, ys)) k = NONE -> ~ In k xs.
Proof.
  revert ys; induction xs as [|x xs IHx]; intros [|y ys] Hlen H; cbn in *; try tauto; try lia.
  destruct (decide (x = k)) as [->|Hne]; [discriminate|].
  intros [->|Hin]; [congruence|]. apply (IHx ys); [lia|exact H|exact Hin].
Qed.

Lemma get_vars_agree args (X : num_set) s (L : spt (word_loc a)) ws :
  (forall k, In k args -> domain X k) -> agree X (locals s) L ->
  get_vars args s = SOME ws -> get_vars args (set_locals L s) = SOME ws.
Proof.
  intros HX Ha; revert ws; induction args as [|r rs IHr]; intros ws H; [exact H|].
  cbn [get_vars] in H |- *.
  destruct (lookup r (locals s)) as [y|] eqn:E; [|discriminate].
  destruct (get_vars rs s) as [ys|] eqn:E2; [|discriminate].
  cbn [locals set_locals]. rewrite (Ha r y (HX r (or_introl eq_refl)) E).
  rewrite (IHr (fun k Hk => HX k (or_intror Hk)) ys eq_refl). exact H.
Qed.

Lemma set_locals_id s : set_locals (locals s) s = s.
Proof. destruct s; reflexivity. Qed.

Lemma alist_agree (X : num_set) ns (vs : list (word_loc a)) m n :
  LENGTH vs = LENGTH ns -> agree (list_delete ns X) m n ->
  agree X (alist_insert ns vs m) (alist_insert ns vs n).
Proof.
  intros Hlen Ha k y Hk Hy. rewrite lookup_alist_insert_any in Hy |- *.
  destruct (ALOOKUP (ZIP (ns, vs)) k) eqn:Ea; [exact Hy|].
  apply Ha; [|exact Hy]. apply dom_list_delete. split; [exact Hk|].
  eapply ALOOKUP_ZIP_None; [symmetry; exact Hlen|exact Ea].
Qed.

Lemma mem_store_tgt adr w s st (L : spt (word_loc a)) :
  mem_store adr w s = SOME st -> mem_store adr w (set_locals L s) = SOME (set_locals L st).
Proof.
  unfold mem_store; cbn [mdomain set_locals].
  destruct (classical_dec _); intros H; inversion H; reflexivity.
Qed.

End Proofs.

Ltac st_cbn_goal :=
  cbn [locals globals memory mdomain sh_mdomain clock code be ffi base_addr top_addr
       set_locals set_memory set_clock set_ffi set_var set_vars set_globals dec_clock
       call_env].

(** Finish a case: the target state is the source state with locals [?nl]. *)
Ltac fin := eexists; split; [f_equal; apply state_ext; st_cbn_goal; reflexivity|cbn [post]];
  try (st_cbn_goal; reflexivity).

Ltac dsolve := solve [rewrite ?vars_of_exp_dom in *; dom_simp; rewrite ?vars_of_exp_dom in *; unfold is_true in *; rewrite ?MEM_In in *; cbn [In] in *;
                      intuition (try congruence; auto)].

(** Rewrite target lookups [lookup r L] using [Hl : agree _ (locals s) L]. *)
Ltac lk Hl :=
  repeat match goal with
         | E : lookup ?r (locals ?s0) = SOME ?y |- context [lookup ?r ?L'] =>
             rewrite (Hl r y ltac:(dsolve) E)
         end.

Ltac rw_eqs :=
  repeat match goal with
         | E : ?x = _ |- context [?x] =>
             tryif is_var x then fail else
             lazymatch x with evaluate _ => fail | _ => rewrite E end
         end.

Ltac ev Hl :=
  repeat match goal with
         | E : eval ?s0 ?e = SOME ?w |- context [eval (set_locals ?L' ?s0) ?e] =>
             rewrite (eval_touched e s0 L' w
                        ltac:(let k := fresh "k" in let y := fresh "y" in
                              let Hk := fresh "Hk" in let Hy := fresh "Hy" in
                              intros k y Hk Hy; apply Hl; [dsolve|exact Hy]) E)
         end.

(** Unfold one step of the target [evaluate] and resolve its lookups. *)
Ltac tgt2 Hl :=
  cbn [loop_arith sh_mem_op is_load]; unfold mem_store, sh_mem_load, sh_mem_store;
  state_cbn; ev Hl; lk Hl; cbn beta iota zeta; rw_eqs; cbn beta iota zeta.
Ltac tgt Hl := unfold_eval; tgt2 Hl.

(** Case split the side hypotheses produced by [split_eval]. *)
Ltac split_side :=
  repeat match goal with
         | Hx : (if _ then _ else _) = _ |- _ => split_nonrec Hx
         | Hx : (match _ with _ => _ end) = _ |- _ => split_nonrec Hx
         | Hx : SOME _ = SOME _ |- _ => injection Hx as Hx; subst
         end;
  try discriminate.

Ltac ag Hl :=
  let k := fresh "k" in let y := fresh "y" in let Hk := fresh "Hk" in let Hy := fresh "Hy" in
  intros k y Hk Hy; st_cbn_goal; cbn [locals set_locals set_var set_ffi set_memory set_globals
                                     dec_clock set_clock] in Hy;
  rewrite ?lookup_insert, ?lookup_inter_alt in *;
  repeat match goal with
         | |- context [decide ?P] => destruct (decide P); subst
         | H : context [decide ?P] |- _ => destruct (decide P); subst
         end;
  try congruence;
  try (apply Hl; [dsolve|congruence]);
  try (exfalso; dsolve).

Section Main.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma compile_correct_aux : forall (x : prog a * state a ffi_t) lt L prog1 l1 l0 res s1,
  evaluate x = (res, s1) -> res <> SOME Error ->
  shrink lt (fst x) l0 = (prog1, l1) -> agree l1 (locals (snd x)) L ->
  exists nl, evaluate (prog1, set_locals L (snd x)) = (res, set_locals nl s1) /\
             post lt l0 res (locals s1) nl.
Proof.
  intros x; induction x as [[v s] IH] using (well_founded_induction eval_lt_wf).
  intros lt L prog1 l1 l0 res s1 H Hne Hc Hl; cbn [fst snd] in *.
  assert (IH' : forall p' s', eval_lt (p', s') (v, s) -> forall lt L prog1 l1 l0 res s1,
             evaluate (p', s') = (res, s1) -> res <> SOME Error ->
             shrink lt p' l0 = (prog1, l1) -> agree l1 (locals s') L ->
             exists nl, evaluate (prog1, set_locals L s') = (res, set_locals nl s1) /\
                        post lt l0 res (locals s1) nl)
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  clear IH; rename IH' into IH.
  destruct v as [ | | | | | | | | | | q1 q2 | c r1 ri p1 p2 live | li body lo
                 | | | | | | | | | | ret dest args handler | ].
  - (* Skip *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H; injection H as <- <-.
    exists L; split; [unfold_eval; reflexivity|exact Hl].
  - (* Assign *)
    cbn [shrink] in Hc. unfold_eval_in H.
    destruct (eval s e) as [w|] eqn:Ev; [|injection H as <- _; congruence].
    injection H as <- <-.
    destruct (lookup n l0) as [u|] eqn:En; injection Hc as <- <-.
    + unfold_eval. st_cbn_goal.
      rewrite (eval_touched e s L w); [|intros k y Hk Hy; apply Hl; [dsolve|exact Hy]|exact Ev].
      fin. ag Hl.
    + unfold_eval. fin. ag Hl.
      exfalso. assert (Hd : domain l0 n) by exact Hk. apply domain_lookup in Hd as [? ?]; congruence.
  - (* Primitive *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. eqb_facts.
    unfold_eval. st_cbn_goal.
    rewrite (get_vars_subspt l2 l1 s (list_delete l l0) L);
      [|split; [eassumption|apply subspt_inter_agree; exact Hl]].
    rw_eqs. rewrite N.eqb_refl.
    fin. intros k y Hk Hy. st_cbn_goal. cbn [locals set_vars set_locals] in Hy.
    rewrite lookup_alist_insert_any in Hy |- *.
    destruct (ALOOKUP (ZIP (l, l3)) k) eqn:Ea; [exact Hy|].
    apply Hl; [|exact Hy]. rewrite domain_list_insert, dom_list_delete.
    right; split; [exact Hk|]. eapply ALOOKUP_ZIP_None; eassumption.
  - (* Arith *)
    cbn [shrink] in Hc; injection Hc as <- <-. unfold arith_vars in Hl.
    unfold_eval_in H.
    destruct (loop_arith s l) as [s'|] eqn:Ea; [|injection H as <- _; congruence].
    injection H as <- <-.
    destruct l; cbn [loop_arith] in Ea; split_eval Ea; try discriminate;
      injection Ea as <-; tgt Hl; fin; ag Hl.
  - (* Store *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. unfold mem_store in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. split_side. tgt Hl. fin. ag Hl.
  - (* SetGlobal *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. tgt Hl. fin. ag Hl.
  - (* Load32 *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. tgt Hl. fin. ag Hl.
  - (* LoadByte *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. tgt Hl. fin. ag Hl.
  - (* Store32 *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. tgt Hl. fin. ag Hl.
  - (* StoreByte *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. tgt Hl. fin. ag Hl.
  - (* Seq *)
    cbn [shrink] in Hc.
    destruct (shrink lt q2 l0) as [p2' l'] eqn:C2.
    destruct (shrink lt q1 l') as [p1' l''] eqn:C1.
    injection Hc as <- <-.
    unfold_eval_in H. destruct (evaluate (q1, s)) as [r1 t1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error) by (intros ->; injection H as <- _; congruence).
    destruct (IH q1 s ltac:(prove_lt) lt L p1' l'' l' r1 t1 E1 Hr1 C1 Hl) as [nl1 [T1 P1]].
    destruct r1 as [r1|].
    + injection H as <- <-. exists nl1. split; [unfold_eval; rewrite T1; reflexivity|].
      destruct r1; exact P1.
    + cbn [post] in P1.
      destruct (IH q2 t1 ltac:(prove_lt) lt nl1 p2' l' l0 res s1 H Hne C2 P1) as [nl2 [T2 P2]].
      exists nl2; split; [unfold_eval; rewrite T1; exact T2|exact P2].
  - (* If *)
    cbn [shrink] in Hc.
    destruct (shrink lt p1 (inter l0 live)) as [p1' la] eqn:C1.
    destruct (shrink lt p2 (inter l0 live)) as [p2' lb] eqn:C2.
    injection Hc as <- <-.
    unfold_eval_in H.
    destruct (lookup r1 (locals s)) as [[x|]|] eqn:Er; try (injection H as <- _; congruence).
    destruct (get_var_imm ri s) as [[y|]|] eqn:Eri; try (injection H as <- _; congruence).
    cbn zeta in H.
    assert (Hr : lookup r1 L = SOME (Word x)) by (apply (Hl r1); [dsolve|exact Er]).
    assert (Hri : get_var_imm ri (set_locals L s) = SOME (Word y)).
    { destruct ri; cbn [get_var_imm] in Eri |- *; [|exact Eri].
      apply (Hl _ _); [cbn iota; dsolve|exact Eri]. }
    unfold_eval. change (locals (set_locals L s)) with L. rewrite Hr, Hri. cbn zeta.
    match type of Hl with agree ?L1 _ _ =>
      assert (Hsub : forall X : num_set, (forall k, domain X k -> domain L1 k) -> agree X (locals s) L)
        by (intros X HX k z Hk Hz; apply Hl; [apply HX; exact Hk|exact Hz]) end.
    destruct (word_cmp c x y).
    + destruct (evaluate (p1, s)) as [rb tb] eqn:Eb.
      assert (Hrb : rb <> SOME Error) by (intros ->; cbn in H; injection H as <- _; congruence).
      destruct (IH p1 s ltac:(prove_lt) lt L p1' la (inter l0 live) rb tb Eb Hrb C1
                  (Hsub la ltac:(intros k Hk; dsolve))) as [nb [Tb Pb]].
      rewrite Tb.
      destruct rb as [rb|].
      * cbn [cut_res IS_SOME] in H |- *. injection H as <- <-. exists nb.
        split; [reflexivity|]. destruct rb; exact Pb.
      * cbn [post] in Pb.
        destruct (cut_agree live (inter l0 live) l0 tb nb res s1
                    ltac:(intros k; rewrite domain_inter; tauto) H Hne Pb) as [nl [Tc [P1 P2]]].
        exists nl. split; [exact Tc|].
        destruct res as [r'|]; [rewrite (P2 ltac:(discriminate)); apply post_refl|exact (P1 eq_refl)].
    + destruct (evaluate (p2, s)) as [rb tb] eqn:Eb.
      assert (Hrb : rb <> SOME Error) by (intros ->; cbn in H; injection H as <- _; congruence).
      destruct (IH p2 s ltac:(prove_lt) lt L p2' lb (inter l0 live) rb tb Eb Hrb C2
                  (Hsub lb ltac:(intros k Hk; dsolve))) as [nb [Tb Pb]].
      rewrite Tb.
      destruct rb as [rb|].
      * cbn [cut_res IS_SOME] in H |- *. injection H as <- <-. exists nb.
        split; [reflexivity|]. destruct rb; exact Pb.
      * cbn [post] in Pb.
        destruct (cut_agree live (inter l0 live) l0 tb nb res s1
                    ltac:(intros k; rewrite domain_inter; tauto) H Hne Pb) as [nl [Tc [P1 P2]]].
        exists nl. split; [exact Tc|].
        destruct res as [r'|]; [rewrite (P2 ltac:(discriminate)); apply post_refl|exact (P1 eq_refl)].
  - (* Loop *)
    pose proof Hc as Hc0.
    rewrite (proj1 (proj2 shrink_def)) in Hc. cbn zeta in Hc.
    assert (Shape : exists b lb (B : num_set), prog1 = Loop l1 b (inter lo l0) /\
              (forall k, domain l1 k -> domain li k) /\
              (forall k, domain li k -> domain lb k -> domain l1 k) /\
              (forall k, domain (inter lo l0) k -> domain B k) /\
              shrink ((l1, B) :: lt) body (union li (inter lo l0)) = (b, lb)).
    { destruct (fixedpoint lt li LN (union li (inter lo l0)) body) as [[b l0']|] eqn:Ef.
      - injection Hc as <- <-. exists b, l0', (union li (inter lo l0)). apply fixedpoint_thm in Ef.
        split; [reflexivity|]. split; [intros k Hk; dsolve|].
        split; [intros k Hk1 Hk2; dsolve|]. split; [intros k Hk; dsolve|exact Ef].
      - destruct (shrink ((li, inter lo l0) :: lt) body (union li (inter lo l0))) as [b lb] eqn:Es.
        injection Hc as <- <-. exists b, lb, (inter lo l0).
        split; [reflexivity|]. split; [auto|]. split; [auto|]. split; [auto|exact Es]. }
    clear Hc. destruct Shape as (b & lb & B & -> & Hl1 & Hlb & HB & Hsb).
    unfold_eval_in H.
    destruct (cut_res li (NONE, s)) as [cr s'] eqn:Ecut.
    destruct (cut_agree li l1 l1 s L cr s' ltac:(intros k; split; [intros Hk; split; auto|tauto])
                Ecut ltac:(destruct cr; [injection H as <- _; exact Hne|discriminate]) Hl)
      as [nl0 [Tc [Pc1 Pc2]]].
    destruct cr as [cr|].
    { injection H as <- <-. exists nl0. split; [unfold_eval; rewrite Tc; reflexivity|].
      rewrite (Pc2 ltac:(discriminate)). apply post_refl. }
    specialize (Pc1 eq_refl).
    assert (Hs' : forall k y, lookup k (locals s') = SOME y -> domain li k).
    { apply cut_res_NONE_eq in Ecut as (-> & _ & _). intros k y Hy.
      cbn [locals dec_clock set_clock set_locals] in Hy. apply lookup_inter_some in Hy; tauto. }
    assert (Hbody : agree lb (locals s') nl0).
    { intros k y Hk Hy. apply Pc1; [apply Hlb; [eapply Hs'; exact Hy|exact Hk]|exact Hy]. }
    rewrite fix_clock_evaluate in H.
    destruct (evaluate (body, s')) as [rb tb] eqn:Eb.
    assert (Hrb : rb <> SOME Error) by (intros ->; injection H as <- _; cbn in Hne; congruence).
    destruct (IH body s' ltac:(prove_lt) _ nl0 b lb _ rb tb Eb Hrb Hsb Hbody) as [nb [Tb Pb]].
    unfold_eval. rewrite Tc. cbn beta iota. rewrite fix_clock_evaluate, Tb.
    assert (Hrec : agree l1 (locals tb) nb -> evaluate (Loop li body lo, tb) = (res, s1) ->
              exists nl, evaluate (Loop l1 b (inter lo l0), set_locals nb tb) = (res, set_locals nl s1) /\
                         post lt l0 res (locals s1) nl).
    { intros Ha He. exact (IH (Loop li body lo) tb ltac:(prove_lt) lt nb _ l1 l0 res s1 He Hne Hc0 Ha). }
    destruct rb as [rb|].
    + destruct rb as [ | | k | k | | | ]; cbn [post oEL] in Pb.
      * injection H as <- <-. exists nb. split; [reflexivity|exact Pb].
      * injection H as <- <-. exists nb. split; [reflexivity|exact Pb].
      * destruct k as [|k]; cbn beta iota in H |- *.
        -- destruct (cut_agree lo (inter lo l0) l0 tb nb res s1
                       ltac:(intros k; rewrite domain_inter; tauto) H Hne
                       ltac:(intros k y Hk Hy; apply Pb; [apply HB; exact Hk|exact Hy]))
             as [nl [Tc2 [P1 P2]]].
           exists nl. split; [exact Tc2|].
           destruct res as [r'|]; [rewrite (P2 ltac:(discriminate)); apply post_refl|exact (P1 eq_refl)].
        -- injection H as <- <-. exists nb. split; [reflexivity|]. exact Pb.
      * destruct k as [|k]; cbn beta iota in H |- *.
        -- exact (Hrec Pb H).
        -- injection H as <- <-. exists nb. split; [reflexivity|]. exact Pb.
      * injection H as <- <-. exists nb. split; [reflexivity|exact Pb].
      * injection H as <- <-. exists nb. split; [reflexivity|exact Pb].
      * injection H as <- <-. exists nb. split; [reflexivity|exact Pb].
    + cbn [post] in Pb. apply Hrec; [|exact H].
      intros k y Hk Hy. apply Pb; [dsolve|exact Hy].
  - (* Break *)
    cbn [shrink] in Hc; injection Hc as <- <-. unfold_eval_in H; injection H as <- <-.
    exists L; split; [unfold_eval; reflexivity|]. cbn [post].
    destruct (oEL n lt) as [[c0 b0]|]; [exact Hl|exact Logic.I].
  - (* Continue *)
    cbn [shrink] in Hc; injection Hc as <- <-. unfold_eval_in H; injection H as <- <-.
    exists L; split; [unfold_eval; reflexivity|]. cbn [post].
    destruct (oEL n lt) as [[c0 b0]|]; [exact Hl|exact Logic.I].
  - (* Raise *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. tgt Hl. fin.
  - (* Return *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; try (injection H as <- _; congruence).
    injection H as <- <-. unfold_eval.
    match goal with E : get_vars ?ns s = SOME ?ws |- _ =>
      rewrite (get_vars_subspt ns ws s LN L); [|split; [exact E|apply subspt_inter_agree; exact Hl]] end.
    fin.
  - (* ShMem *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. destruct m; cbn [sh_mem_op is_load] in H; unfold sh_mem_load, sh_mem_store in H;
      split_eval H; try (injection H as <- _; congruence); injection H as <- <-;
      tgt Hl; fin; ag Hl.
  - (* Tick *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H. split_eval H; injection H as <- <-; tgt Hl; fin; ag Hl.
  - (* Mark *)
    cbn [shrink] in Hc. unfold_eval_in H.
    exact (IH v s ltac:(prove_lt) lt L prog1 l1 l0 res s1 H Hne Hc Hl).
  - (* Fail *)
    unfold_eval_in H; injection H as <- _; congruence.
  - (* LocValue *)
    cbn [shrink] in Hc. unfold_eval_in H.
    split_eval H; try (injection H as <- _; congruence). injection H as <- <-.
    destruct (lookup n l0) as [u|] eqn:En; injection Hc as <- <-.
    + tgt Hl. fin. ag Hl.
    + unfold_eval. fin. ag Hl.
      exfalso. assert (Hd : domain l0 n) by exact Hk. apply domain_lookup in Hd as [? ?]; congruence.
  - (* Call *)
    unfold_eval_in H.
    destruct (get_vars args s) as [vs|] eqn:Eg; [|injection H as <- _; congruence].
    destruct (find_code dest vs (code s)) as [[env prog0]|] eqn:Ef;
      [|injection H as <- _; congruence].
    assert (Ha0 : forall X : num_set, (forall k, In k args -> domain X k) -> agree X (locals s) L ->
                  get_vars args (set_locals L s) = SOME vs)
      by (intros X HX Ha; exact (get_vars_agree args X s L vs HX Ha Eg)).
    cbn [shrink] in Hc. cbn zeta in Hc.
    destruct ret as [[ns lr]|].
    + destruct (ALL_DISTINCT ns) eqn:Ead; cbn [negb] in H; [|injection H as <- _; congruence].
      destruct (cut_res lr (NONE, s)) as [cr s'] eqn:Ecut.
      (* the continuation after a returning call with a handler *)
      assert (Hcont : forall pp pp' lp t0 nl lo' (t1 : state a ffi_t) res1,
                 eval_lt (pp, t0) (Call (SOME (ns, lr)) dest args handler, s) ->
                 shrink lt pp l0 = (pp', lp) -> agree lp (locals t0) nl ->
                 cut_res lo' (evaluate (pp, t0)) = (res1, t1) -> res1 <> SOME Error ->
                 exists nl', cut_res (inter l0 lo') (evaluate (pp', set_locals nl t0)) =
                               (res1, set_locals nl' t1) /\ post lt l0 res1 (locals t1) nl').
      { intros pp pp' lp t0 nl lo' t1 res1 Hlt Hs Ha He Hne1.
        destruct (evaluate (pp, t0)) as [rr t2] eqn:Ee.
        assert (Hrr : rr <> SOME Error) by (intros ->; cbn in He; injection He as <- _; congruence).
        destruct (IH pp t0 Hlt lt nl pp' lp l0 rr t2 Ee Hrr Hs Ha) as [nr [Tr Pr]].
        rewrite Tr. destruct rr as [rr|].
        - cbn [cut_res IS_SOME] in He |- *. injection He as <- <-. exists nr.
          split; [reflexivity|]. destruct rr; exact Pr.
        - cbn [post] in Pr.
          destruct (cut_agree lo' (inter l0 lo') l0 t2 nr res1 t1
                      ltac:(intros k; rewrite domain_inter; tauto) He Hne1
                      ltac:(intros k y Hk Hy; apply Pr; [rewrite domain_inter in Hk; apply Hk|exact Hy])) as [nl' [Tc [P1 P2]]].
          exists nl'. split; [exact Tc|].
          destruct res1 as [r'|]; [rewrite (P2 ltac:(discriminate)); apply post_refl|exact (P1 eq_refl)]. }
      assert (Hrest : forall (X l0' : num_set),
                 (forall k, domain X k <-> domain l0' k /\ domain lr k) -> agree X (locals s) L ->
                 exists nl0, cut_res X (NONE, set_locals L s) = (cr, set_locals nl0 s') /\
                   (cr = NONE -> agree l0' (locals s') nl0) /\ (cr <> NONE -> nl0 = locals s')).
      { intros X l0' HX Ha. apply (cut_agree lr X l0' s L cr s' HX Ecut); [|exact Ha].
        destruct cr; [injection H as <- _; exact Hne|discriminate]. }
      destruct handler as [[e [h [r lo']]]|].
      * destruct (shrink lt r l0) as [r' l2] eqn:Cr.
        destruct (shrink lt h l0) as [h' l3] eqn:Ch.
        injection Hc as <- <-.
        destruct (Hrest (inter lr (union (list_delete ns l2) (delete e l3)))
                    (union (list_delete ns l2) (delete e l3))
                    ltac:(intros k; rewrite domain_inter; tauto)
                    ltac:(intros k y Hk Hy; apply Hl; [rewrite domain_union; right; exact Hk|exact Hy])) as [nl0 [Tc [P1 P2]]].
        unfold_eval. rewrite (Ha0 _ ltac:(intros k Hk; rewrite domain_union; left; apply dom_fromAList_tt; exact Hk) Hl).
        change (code (set_locals L s)) with (code s). rewrite Ef, Ead. cbn [negb].
        rewrite Tc.
        destruct cr as [cr|].
        { injection H as <- <-. exists nl0. split; [reflexivity|].
          rewrite (P2 ltac:(discriminate)). apply post_refl. }
        specialize (P1 eq_refl). cbn beta iota in H |- *.
        rewrite fix_clock_evaluate in H |- *.
        assert (Eenv : set_locals env (set_locals nl0 s') = set_locals env s')
          by (apply state_ext; reflexivity).
        rewrite Eenv. change (locals (set_locals nl0 s')) with nl0.
        destruct (evaluate (prog0, set_locals env s')) as [rr st] eqn:Ee.
        destruct rr as [[retvs|exn| | | | |]|]; cbn beta iota in H |- *;
          try (injection H as <- _; congruence).
        -- destruct (LENGTH retvs =? LENGTH ns) eqn:Elen; cbn [negb] in H |- *;
             [|injection H as <- _; congruence].
           apply N.eqb_eq in Elen.
           assert (Est : set_vars ns retvs (set_locals nl0 st) =
                         set_locals (alist_insert ns retvs nl0)
                           (set_vars ns retvs (set_locals (locals s') st)))
             by (apply state_ext; reflexivity).
           rewrite Est.
           eapply Hcont; [prove_lt|exact Cr| |exact H|exact Hne].
           cbn [locals set_vars set_locals]. apply alist_agree; [exact Elen|].
           intros k y Hk Hy. apply P1; [rewrite domain_union; left; exact Hk|exact Hy].
        -- assert (Est : set_var e exn (set_locals nl0 st) =
                         set_locals (insert e exn nl0) (set_var e exn (set_locals (locals s') st)))
             by (apply state_ext; reflexivity).
           rewrite Est.
           eapply Hcont; [prove_lt|exact Ch| |exact H|exact Hne].
           intros k y Hk Hy. cbn [locals set_var set_locals] in Hy |- *.
           rewrite lookup_insert in Hy |- *. destruct (decide (k = e)); [exact Hy|].
           apply P1; [rewrite domain_union, domain_delete; right; split; assumption|exact Hy].
        -- injection H as <- <-. exists (locals st). split; [rewrite set_locals_id; reflexivity|reflexivity].
        -- injection H as <- <-. exists (locals st). split; [rewrite set_locals_id; reflexivity|reflexivity].
      * injection Hc as <- <-.
        destruct (Hrest (list_delete ns (inter l0 lr)) (list_delete ns l0)
                    ltac:(intros k; rewrite dom_list_delete, dom_list_delete, domain_inter; tauto)
                    ltac:(intros k y Hk Hy; apply Hl; [rewrite domain_union; right; exact Hk|exact Hy])) as [nl0 [Tc [P1 P2]]].
        unfold_eval. rewrite (Ha0 _ ltac:(intros k Hk; rewrite domain_union; left; apply dom_fromAList_tt; exact Hk) Hl).
        change (code (set_locals L s)) with (code s). rewrite Ef, Ead. cbn [negb].
        rewrite Tc.
        destruct cr as [cr|].
        { injection H as <- <-. exists nl0. split; [reflexivity|].
          rewrite (P2 ltac:(discriminate)). apply post_refl. }
        specialize (P1 eq_refl). cbn beta iota in H |- *.
        rewrite fix_clock_evaluate in H |- *.
        assert (Eenv : set_locals env (set_locals nl0 s') = set_locals env s')
          by (apply state_ext; reflexivity).
        rewrite Eenv. change (locals (set_locals nl0 s')) with nl0.
        destruct (evaluate (prog0, set_locals env s')) as [rr st] eqn:Ee.
        destruct rr as [[retvs|exn| | | | |]|]; cbn beta iota in H |- *;
          try (injection H as <- _; congruence).
        -- destruct (LENGTH retvs =? LENGTH ns) eqn:Elen; cbn [negb] in H |- *;
             [|injection H as <- _; congruence].
           apply N.eqb_eq in Elen.
           injection H as <- <-. eexists. split.
           ++ f_equal. apply state_ext; reflexivity.
           ++ cbn [post locals set_vars set_locals]. apply alist_agree; [exact Elen|exact P1].
        -- injection H as <- <-. exists LN. split; [f_equal; apply state_ext; reflexivity|reflexivity].
        -- injection H as <- <-. exists (locals st). split; [rewrite set_locals_id; reflexivity|reflexivity].
        -- injection H as <- <-. exists (locals st). split; [rewrite set_locals_id; reflexivity|reflexivity].
    + destruct handler as [hd|]; [cbn [IS_SOME] in H; injection H as <- _; congruence|].
      cbn [IS_SOME] in H. injection Hc as <- <-.
      unfold_eval. rewrite (Ha0 _ ltac:(intros k Hk; rewrite domain_union; left; apply dom_fromAList_tt; exact Hk) Hl).
      change (code (set_locals L s)) with (code s). rewrite Ef. cbn [IS_SOME].
      change (clock (set_locals L s)) with (clock s).
      destruct (clock s =? 0).
      * injection H as <- <-. exists LN. split; [f_equal; apply state_ext; reflexivity|reflexivity].
      * assert (Eenv : set_locals env (dec_clock (set_locals L s)) = set_locals env (dec_clock s))
          by (apply state_ext; reflexivity).
        rewrite Eenv.
        destruct (evaluate (prog0, set_locals env (dec_clock s))) as [rr st] eqn:Ee.
        destruct rr as [rr|]; [|injection H as <- _; congruence].
        destruct rr; injection H as <- <-; try congruence;
          exists (locals st); (split; [rewrite set_locals_id; reflexivity|reflexivity]).
  - (* FFI *)
    cbn [shrink] in Hc; injection Hc as <- <-.
    unfold_eval_in H.
    split_eval H; try (injection H as <- _; congruence).
    all: unfold cut_state in *; split_side.
    all: unfold_eval;
      match goal with Hs : domain ?cs SUBSET domain (locals _) |- _ =>
        rewrite cut_state_tgt;
        [|intros k Hk; unfold pred_set.IN in *;
          eapply agree_dom; [exact Hl|dsolve|apply Hs; dsolve]] end;
      injection H as <- <-; tgt2 Hl; fin; ag Hl.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall (v : prog a) (v1 : state a ffi_t) res s1 lt locals prog1 l1 l0,
  evaluate (v, v1) = (res, s1) /\ res <> SOME Error /\
  shrink lt v l0 = (prog1, l1) /\ subspt (inter (loopSem.locals v1) l1) locals ->
  exists new_locals,
    evaluate (prog1, set_locals locals v1) = (res, set_locals new_locals s1) /\
    match res with
    | NONE => is_true (subspt (inter (loopSem.locals s1) l0) new_locals)
    | SOME (Result v5) => new_locals = loopSem.locals s1
    | SOME (Exception v6) => new_locals = loopSem.locals s1
    | SOME (Break n) => match oEL n lt with
                        | SOME (_, brk) => is_true (subspt (inter (loopSem.locals s1) brk) new_locals)
                        | NONE => True
                        end
    | SOME (Continue n) => match oEL n lt with
                           | SOME (cont, _) =>
                               is_true (subspt (inter (loopSem.locals s1) cont) new_locals)
                           | NONE => True
                           end
    | SOME TimeOut => new_locals = loopSem.locals s1
    | SOME (FinalFFI v7) => new_locals = loopSem.locals s1
    | SOME Error => new_locals = loopSem.locals s1
    end.
Proof.
  intros v v1 res s1 lt L prog1 l1 l0 (H & Hne & Hc & Hs).
  rewrite subspt_inter_agree in Hs.
  destruct (compile_correct_aux (v, v1) lt L prog1 l1 l0 res s1 H Hne Hc Hs) as [nl [T P]].
  exists nl; split; [exact T|].
  destruct res as [[ | | k | k | | | ]|]; cbn [post] in P; try exact P;
    try (apply subspt_inter_agree; exact P);
    destruct (oEL k lt) as [[c0 b0]|]; try exact Logic.I; apply subspt_inter_agree; exact P.
Qed.

Lemma evaluate_Mark (p : prog a) s : evaluate (Mark p, s) = evaluate (p, s).
Proof. unfold_eval. reflexivity. Qed.

Lemma evaluate_mark_if (b : bool) (p : prog a) s :
  evaluate (if b then Mark p else p, s) = evaluate (p, s).
Proof. destruct b; [apply evaluate_Mark|reflexivity]. Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "mark_correct" *)
Theorem mark_correct : forall (prog : prog a) (s : state a ffi_t) res s1,
  evaluate (prog, s) = (res, s1) -> evaluate (FST (mark_all prog), s) = (res, s1).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res s1,
            evaluate x = (res, s1) -> evaluate (FST (mark_all (fst x)), snd x) = (res, s1))
    by (intros p s res s1 H; exact (G (p, s) res s1 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res s1 H; cbn [fst snd] in *.
  assert (IH' : forall p' s', eval_lt (p', s') (p, s) -> forall res s1,
             evaluate (p', s') = (res, s1) -> evaluate (FST (mark_all p'), s') = (res, s1))
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  clear IH; rename IH' into IH.
  destruct p as [  |  |  |  |  |  |  |  |  |  | q1 q2 | c r1 ri p1 p2 live | li body lo |  |  |  |  |  |  | mq |  |  | ret dest args handler |  ];
    cbn [mark_all]; try (cbn [fst]; rewrite evaluate_Mark; exact H).
  - (* Seq *)
    destruct (mark_all q1) as [q1' t1] eqn:M1. destruct (mark_all q2) as [q2' t2] eqn:M2.
    cbn [fst]. rewrite evaluate_mark_if.
    unfold_eval_in H. unfold_eval.
    destruct (evaluate (q1, s)) as [r1 u1] eqn:E1.
    pose proof (IH q1 s ltac:(prove_lt) _ _ E1) as E1'. rewrite M1 in E1'. cbn [fst] in E1'.
    rewrite E1'. destruct r1; [exact H|].
    pose proof (IH q2 u1 ltac:(prove_lt) _ _ H) as E2. rewrite M2 in E2. exact E2.
  - (* If *)
    destruct (mark_all p1) as [p1' t1] eqn:M1. destruct (mark_all p2) as [p2' t2] eqn:M2.
    cbn [fst]. rewrite evaluate_mark_if.
    unfold_eval_in H. unfold_eval.
    destruct (lookup r1 (locals s)) as [[x|]|]; try exact H.
    destruct (get_var_imm ri s) as [[y|]|]; try exact H.
    cbn zeta in H |- *. destruct (word_cmp c x y).
    + destruct (evaluate (p1, s)) as [rb tb] eqn:Eb.
      pose proof (IH p1 s ltac:(prove_lt) _ _ Eb) as E'. rewrite M1 in E'. cbn [fst] in E'.
      rewrite E'. exact H.
    + destruct (evaluate (p2, s)) as [rb tb] eqn:Eb.
      pose proof (IH p2 s ltac:(prove_lt) _ _ Eb) as E'. rewrite M2 in E'. cbn [fst] in E'.
      rewrite E'. exact H.
  - (* Loop *)
    destruct (mark_all body) as [body' t1] eqn:M1. cbn [fst].
    pose proof H as H0.
    unfold_eval_in H. unfold_eval.
    destruct (cut_res li (NONE, s)) as [[cr|] s'] eqn:Ecut; [exact H|].
    rewrite fix_clock_evaluate in H |- *.
    destruct (evaluate (body, s')) as [rb tb] eqn:Eb.
    pose proof (IH body s' ltac:(prove_lt) _ _ Eb) as E'. rewrite M1 in E'. cbn [fst] in E'.
    rewrite E'.
    assert (Hrec : evaluate (Loop li body lo, tb) = (res, s1) ->
                   evaluate (Loop li body' lo, tb) = (res, s1)).
    { intros He. pose proof (IH (Loop li body lo) tb ltac:(prove_lt) _ _ He) as E2.
      cbn [mark_all] in E2. rewrite M1 in E2. exact E2. }
    destruct rb as [[ | | k | k | | | ]|]; try exact H.
    + destruct k; exact (Hrec H) || exact H.
    + exact (Hrec H).
  - (* Mark *)
    unfold_eval_in H. exact (IH mq s ltac:(prove_lt) _ _ H).
  - (* Call *)
    destruct handler as [[n [p1 [p2 l]]]|]; [|cbn [fst]; rewrite evaluate_Mark; exact H].
    destruct (mark_all p1) as [p1' t1] eqn:M1. destruct (mark_all p2) as [p2' t2] eqn:M2.
    cbn [fst]. rewrite evaluate_mark_if.
    unfold_eval_in H. unfold_eval.
    destruct (get_vars args s); [|exact H].
    destruct (find_code dest l0 (code s)) as [[env prog0]|]; [|exact H].
    destruct ret as [[ns lr]|]; [|exact H].
    destruct (ALL_DISTINCT ns); [|exact H]. cbn [negb] in H |- *.
    destruct (cut_res lr (NONE, s)) as [[cr|] s'] eqn:Ecut; [exact H|].
    rewrite fix_clock_evaluate in H |- *.
    destruct (evaluate (prog0, set_locals env s')) as [[rr|] st] eqn:Ee; [|exact H].
    destruct rr; try exact H.
    + destruct (negb (LENGTH l1 =? LENGTH ns)); [exact H|].
      destruct (evaluate (p2, set_vars ns l1 (set_locals (locals s') st))) as [rb tb] eqn:Eb.
      pose proof (IH p2 (set_vars ns l1 (set_locals (locals s') st)) ltac:(unfold eval_lt; cbn [fst snd psize]; pose proof (evaluate_clock _ _ _ _ Ee); pose proof (cut_res_NONE_clock _ _ _ Ecut); state_cbn; lia) _ _ Eb) as E'.
      rewrite M2 in E'. cbn [fst] in E'.
      rewrite E'. exact H.
    + destruct (evaluate (p1, set_var n w (set_locals (locals s') st))) as [rb tb] eqn:Eb.
      pose proof (IH p1 (set_var n w (set_locals (locals s') st)) ltac:(unfold eval_lt; cbn [fst snd psize]; pose proof (evaluate_clock _ _ _ _ Ee); pose proof (cut_res_NONE_clock _ _ _ Ecut); state_cbn; lia) _ _ Eb) as E'.
      rewrite M1 in E'. cbn [fst] in E'.
      rewrite E'. exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "comp_correct" *)
Theorem comp_correct : forall (prog : prog a) (s : state a ffi_t) res s1,
  evaluate (prog, s) = (res, s1) /\
  res <> SOME Error /\
  (forall n, res <> SOME (Break n)) /\
  (forall n, res <> SOME (Continue n)) /\
  res <> NONE ->
  evaluate (comp prog, s) = (res, s1).
Proof.
  intros p s res s1 (H & He & Hb & Hc & Hn).
  unfold comp. apply mark_correct.
  destruct (shrink [] p LN) as [p1 l1] eqn:Hs.
  destruct (compile_correct_aux (p, s) [] (locals s) p1 l1 LN res s1 H He Hs
              ltac:(intros k y _ Hy; exact Hy)) as [nl [T P]].
  rewrite set_locals_id in T. cbn [fst snd] in T.
  destruct res as [r|]; [|congruence].
  destruct r; cbn [post] in P;
    try (exfalso; eapply Hb; reflexivity); try (exfalso; eapply Hc; reflexivity);
    rewrite P, set_locals_id in T; exact T.
Qed.

(*! HOL "cakeml/pancake/proofs/loop_liveProofScript.sml" "optimise_correct" *)
Theorem optimise_correct : forall (prog : prog a) (s : state a ffi_t) res s1,
  evaluate (prog, s) = (res, s1) /\
  res <> SOME Error /\
  (forall n, res <> SOME (Break n)) /\
  (forall n, res <> SOME (Continue n)) /\
  res <> NONE ->
  evaluate (optimise prog, s) = (res, s1).
Proof.
  intros p s res s1 (H & He & Hb & Hc & Hn).
  unfold optimise. cbv beta.
  destruct (loop_call.comp LN p) as [q nl] eqn:Hq. cbn [fst].
  destruct (loop_callProof.compile_correct p s res s1 LN q nl
              (conj H (conj He (conj Hq (loop_callProof.labels_in_LN _))))) as [E _].
  apply comp_correct; repeat split; assumption.
Qed.

End Main.
