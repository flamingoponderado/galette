(** * CakeML [word_allocProof]: SSA expression, renaming and loop lemmas

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    6212-7666): [ssa_cc_trans_exp_correct], the [force_rename] lemmas,
    [evaluate_ssa_reconcile], [lt_ok], [loop_setup_correct] and
    [ssa_cc_trans_Loop_helper].

    Notes: as in [ssa_props.v].  HOL's [FILTER (λ(a,b). a ≠ b)] is
    [FILTER (fun '(a0, b) => negb (a0 =? b))] (the form used by
    [ssa_reconcile]); HOL [EVERY] with a [Prop]-valued predicate is
    [EVERY (fun x => bool_decide (...))]. *)

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
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring ssa_props.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "PAIR_ZIP_MEM" *)
Theorem PAIR_ZIP_MEM : forall {A B} `{EqDecision A, EqDecision B} (c0 : list A) (d0 : list B) a0 b0,
  LENGTH c0 = LENGTH d0 /\ MEM (a0, b0) (ZIP (c0, d0)) -> MEM a0 c0 /\ MEM b0 d0.
Proof.
  intros A B EA EB c0 d0 a0 b0 [_ H]. rewrite !MEM_iff' in *. rewrite ZIP_combine' in H.
  split; [eapply in_combine_l|eapply in_combine_r]; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_ZIP_MEM" *)
Theorem ALOOKUP_ZIP_MEM : forall {A B} `{EqDecision A, EqDecision B} (a0 : list A) (b0 : list B) x y,
  LENGTH a0 = LENGTH b0 /\ ALOOKUP (ZIP (a0, b0)) x = SOME y -> MEM x a0 /\ MEM y b0.
Proof.
  intros A B EA EB a0 b0 x y [Hl H]. apply ALOOKUP_MEM in H. apply (PAIR_ZIP_MEM a0 b0). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_ALL_DISTINCT_REMAP" *)
Theorem ALOOKUP_ALL_DISTINCT_REMAP : forall {A B C} `{EqDecision A, EqDecision B, Inhabited A}
    (ls : list A) (x : list C) (f : A -> B) y n,
  LENGTH ls = LENGTH x /\ ALL_DISTINCT (MAP f ls) /\ n < LENGTH ls /\
  ALOOKUP (ZIP (ls, x)) (EL n ls) = SOME y ->
  ALOOKUP (ZIP (MAP f ls, x)) (f (EL n ls)) = SOME y.
Proof.
  intros A B C EA EB IA ls; induction ls as [|h ls IH]; intros x f y n (Hl & Hd & Hn & H);
    [cbn [LENGTH] in Hn; lia|].
  destruct x as [|x0 x]; [cbn [LENGTH] in Hl; lia|].
  cbn [MAP List.map] in *. cbn [ZIP ALOOKUP] in *.
  apply ALL_DISTINCT_cons' in Hd as [Hh Hd].
  destruct (N.eq_dec n 0) as [->|Hn0].
  - unfold EL in *; cbn in *. rewrite decide_True' in H by reflexivity. rewrite decide_True' by reflexivity. exact H.
  - pose proof (N.succ_pred_pos n ltac:(lia)) as E. rewrite <- E in H |- *. rewrite EL_SUC in H |- *.
    cbn [TL] in *. set (e := EL (N.pred n) ls) in *.
    assert (He : In e ls).
    { unfold e. rewrite EL_nth by (cbn [LENGTH] in Hn; lia). apply nth_In. cbn [LENGTH] in Hn. rewrite LENGTH_length in Hn. lia. }
    assert (Hc : h = e \/ h <> e) by (destruct (decide (h = e)); auto). destruct Hc as [->|Hne].
    + rewrite decide_True' in H by reflexivity. rewrite decide_True' by reflexivity. exact H.
    + rewrite decide_False' in H by exact Hne. rewrite decide_False'.
      * apply IH. split; [cbn [LENGTH] in Hl; lia|split; [exact Hd|split; [cbn [LENGTH] in Hn; lia|exact H]]].
      * intros E'. apply Hh. rewrite MEM_iff', E'. apply in_map, He.
Qed.

Section SSA2.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_exp_correct" *)
Theorem ssa_cc_trans_exp_correct : forall (st : state) (w : exp a) (cst : state) ssa na res,
  word_exp st w = SOME res /\
  word_state_eq_rel st cst /\
  ssa_locals_rel na ssa (locals st) (locals cst) ->
  word_exp cst (ssa_cc_trans_exp ssa w) = SOME res.
Proof.
  intros st w; induction w as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros cst ssa na res (H & Heq & Hs); cbn [word_exp ssa_cc_trans_exp] in *;
    pose proof Heq as Heq'; unfold word_state_eq_rel in Heq; destr_conj.
  - exact H.
  - apply (ssa_locals_rel_get_var na ssa st cst). split; [exact Hs|exact H].
  - unfold get_store in *. congruence.
  - destruct (word_exp st e) as [[w|]|] eqn:E; try discriminate.
    rewrite (IH cst ssa na (Word w) (conj eq_refl (conj Heq' Hs))).
    unfold mem_load in *. rewrite H7, H8. exact H.
  - destruct (the_words (MAP (word_exp st) es)) as [ws|] eqn:Ews; [|discriminate].
    assert (Hmap : MAP (word_exp cst) (MAP (ssa_cc_trans_exp ssa) es) = MAP (word_exp st) es).
    { rewrite List.map_map. apply map_ext_in. intros e He.
      pose proof (the_words_EVERY_IS_SOME _ _ Ews) as Hev. unfold is_true in Hev.
      rewrite EVERY_Forall, Forall_map, Forall_forall in Hev. specialize (Hev e He).
      destruct (word_exp st e) as [r|] eqn:Ee; [|discriminate].
      rewrite Forall_forall in IH. apply (IH e He cst ssa na r). auto. }
    rewrite Hmap, Ews. exact H.
  - destruct (word_exp st e1) as [[w1|]|] eqn:E1; try discriminate.
    destruct (word_exp st e2) as [[w2|]|] eqn:E2; try discriminate.
    rewrite (IH1 cst ssa na (Word w1) (conj eq_refl (conj Heq' Hs))).
    rewrite (IH2 cst ssa na (Word w2) (conj eq_refl (conj Heq' Hs))). exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_var_set_vars_notin" *)
Theorem get_var_set_vars_notin : forall v ls (vs : list (word_loc a)) (st : state),
  ~ MEM v ls /\ LENGTH ls = LENGTH vs ->
  get_var v (set_vars ls vs st) = get_var v st.
Proof.
  intros v ls vs st [Hm _]. unfold get_var, set_vars. rewrite locals_set_locals.
  apply alist_insert_notin. rewrite <- MEM_iff'. exact Hm.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_delete_left" *)
Theorem ssa_locals_rel_delete_left : forall {A} na ssa (stl cstl : num_map A) n,
  ssa_locals_rel na ssa stl cstl -> ssa_locals_rel na ssa (delete n stl) cstl.
Proof.
  intros A na ssa stl cstl n [R1 R2]. split; [exact R1|].
  intros x y Hx. rewrite lookup_delete in Hx. destruct (decide (x = n)); [discriminate|apply R2, Hx].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_delete_right" *)
Theorem ssa_locals_rel_delete_right : forall {A} na ssa (stl cstl : num_map A) n,
  ssa_map_ok na ssa /\ ssa_locals_rel na ssa stl cstl /\ is_phy_var n ->
  ssa_locals_rel na ssa stl (delete n cstl).
Proof.
  intros A na ssa stl cstl n (Hok & [R1 R2] & Hp). split.
  - intros x y Hx. destruct (Hok _ _ Hx) as [Hy _]. apply domain_lookup.
    rewrite lookup_delete, decide_False' by (intros ->; contradiction). apply domain_lookup, (R1 _ _ Hx).
  - intros x y Hx. destruct (R2 _ _ Hx) as (Hd & Hl & Ha). split; [exact Hd|split; [|exact Ha]].
    apply domain_lookup in Hd as [z Hz]. rewrite Hz in Hl |- *. cbn [THE] in *.
    destruct (Hok _ _ Hz) as [Hz' _]. rewrite lookup_delete, decide_False' by (intros ->; contradiction). exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lookup_force_rename" *)
Theorem lookup_force_rename : forall x ls ssa,
  lookup x (force_rename ls ssa) =
  match ALOOKUP (REVERSE ls) x with NONE => lookup x ssa | SOME y => SOME y end.
Proof.
  intros x ls; induction ls as [|[k v] ls IH]; intros ssa; [reflexivity|].
  cbn [force_rename REVERSE List.rev]. rewrite IH, ALOOKUP_APPEND.
  destruct (ALOOKUP (rev ls) x); [reflexivity|]. cbn [ALOOKUP]. rewrite lookup_insert'.
  destruct (decide (x = k)) as [->|Hne]; [rewrite decide_True' by reflexivity; reflexivity|].
  rewrite decide_False' by congruence. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lookup_force_rename_aux" *)
Theorem lookup_force_rename_aux : forall x ls ssa,
  lookup x (force_rename (REVERSE ls) ssa) =
  match ALOOKUP ls x with NONE => lookup x ssa | SOME y => SOME y end.
Proof. intros x ls ssa. rewrite lookup_force_rename, rev_involutive. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_force_rename" *)
Theorem domain_force_rename : forall ls ssa,
  domain (force_rename ls ssa) = domain ssa UNION set (MAP FST ls).
Proof.
  induction ls as [|[k v] ls IH]; intros ssa; cbn [force_rename MAP List.map].
  - apply set_ext; intros x; set_simp; tauto.
  - rewrite IH, domain_insert. apply set_ext; intros x. unfold pred_set.UNION, pred_set.IN.
    cbn [LIST_TO_SET FST fst]. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_force_rename" *)
Theorem ssa_locals_rel_force_rename : forall {A} `{EqDecision A} na ssa (st1 st2 : num_map A) ls,
  ssa_locals_rel na ssa st1 st2 /\
  EVERY (fun x => bool_decide (lookup (FST x) st1 = lookup (SND x) st2)) ls /\
  set (MAP SND ls) SUBSET domain st2 ->
  ssa_locals_rel na (force_rename ls ssa) st1 st2.
Proof.
  intros A EA na ssa st1 st2 ls; revert ssa; induction ls as [|[k v] ls IH]; intros ssa (Hr & He & Hs);
    [exact Hr|].
  cbn [force_rename]. cbn [EVERY] in He. apply andb_prop in He as [Hh He]. apply bool_decide_spec in Hh.
  cbn [FST SND fst snd] in Hh. apply IH. split; [|split; [exact He|intros z Hz; apply Hs; right; exact Hz]].
  destruct Hr as [R1 R2]. split.
  - intros x y Hx. rewrite lookup_insert' in Hx. destruct (decide (x = k)).
    + injection Hx as <-. apply Hs. left; reflexivity.
    + eapply R1; exact Hx.
  - intros x y Hx. destruct (R2 _ _ Hx) as (Hd & Hl & Ha). rewrite domain_insert, lookup_insert'.
    split; [right; exact Hd|split; [|exact Ha]].
    destruct (decide (x = k)) as [->|]; [cbn [THE]; rewrite <- Hh; exact Hx|exact Hl].
Qed.

Lemma NoDup_map_inj' {A B} (f : A -> B) l x y :
  NoDup (List.map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|h l IH]; intros Hd Hx Hy E; [destruct Hx|]. inversion Hd as [|? ? Hn Hd']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hn. rewrite E. apply in_map, Hy.
  - exfalso; apply Hn. rewrite <- E. apply in_map, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_distinct" *)
Theorem list_next_var_rename_move_distinct : forall ssa na ls (mov : prog a) ssa' na' x y,
  list_next_var_rename_move ssa na ls = (mov, (ssa', na')) /\
  ALL_DISTINCT ls /\ MEM x ls /\ MEM y ls /\
  option_lookup ssa' x = option_lookup ssa' y -> x = y.
Proof.
  intros ssa na ls mov ssa' na' x y (E & Hd & Hx & Hy & Exy). unfold list_next_var_rename_move in E.
  destruct (list_next_var_rename ls ssa na) as [l [s n]] eqn:E1. injection E as _ <- <-.
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E1) as (Hd' & _).
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E1 Hd) as (Hl & _ & _ & Hex).
  rewrite Hl in Hd'. apply ALL_DISTINCT_iff' in Hd'.
  destruct (Hex x Hx) as [vx Hvx]. destruct (Hex y Hy) as [vy Hvy].
  apply (NoDup_map_inj' _ _ _ _ Hd'); [apply MEM_iff', Hx|apply MEM_iff', Hy|].
  unfold option_lookup in Exy. rewrite Hvx, Hvy in *. cbn [THE]. exact Exy.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_NOT_MEM" *)
Theorem get_vars_NOT_MEM : forall h xs h' ys (cs : state),
  ~ MEM h xs ->
  get_vars xs (set_locals (insert h h' ys) cs) = get_vars xs (set_locals ys cs).
Proof.
  intros h xs h' ys cs; induction xs as [|x xs IH]; intros Hm; [reflexivity|].
  apply not_MEM_cons in Hm as [Hm1 Hm2]. cbn [get_vars]. unfold get_var. rewrite !locals_set_locals.
  rewrite lookup_insert', decide_False' by (intros ->; apply Hm1; reflexivity). rewrite IH by exact Hm2.
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_eq_alist_insert" *)
Theorem get_vars_eq_alist_insert : forall (st : state) rest regs l,
  ALL_DISTINCT regs /\ LENGTH regs = LENGTH l /\
  (forall x, MEM x regs -> lookup x (locals st) = lookup x (alist_insert regs l rest)) ->
  get_vars regs st = SOME l.
Proof.
  intros st rest regs; induction regs as [|r regs IH]; intros l (Hd & Hl & H).
  - destruct l; [reflexivity|cbn [LENGTH] in Hl; lia].
  - destruct l as [|v l]; [cbn [LENGTH] in Hl; lia|]. apply ALL_DISTINCT_cons' in Hd as [Hr Hd].
    cbn [get_vars]. unfold get_var. rewrite (H r) by (rewrite MEM_iff'; left; reflexivity).
    cbn [alist_insert]. rewrite lookup_insert1. rewrite (IH l); [reflexivity|].
    split; [exact Hd|split; [cbn [LENGTH] in Hl; lia|]].
    intros x Hx. rewrite H by (rewrite MEM_iff' in *; right; exact Hx). cbn [alist_insert].
    rewrite lookup_insert', decide_False'; [reflexivity|]. intros ->; contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_envs_domain_SUBSET" *)
Theorem cut_envs_domain_SUBSET : forall {A} x1 x2 (locs : num_map A) x,
  cut_envs (x1, x2) locs = SOME x ->
  domain x1 SUBSET domain locs /\ domain x2 SUBSET domain locs.
Proof.
  intros A x1 x2 locs x H. unfold cut_envs, cut_names in H. cbn [FST SND fst snd] in H.
  destruct (classical_dec (domain x1 SUBSET domain locs)); [|discriminate].
  destruct (classical_dec (domain x2 SUBSET domain locs)); [|discriminate]. auto.
Qed.

Lemma NoDup_filter' {A} (P : A -> bool) l : NoDup l -> NoDup (List.filter P l).
Proof. apply NoDup_filter. Qed.

Lemma NoDup_toAList_keys {B} (t : num_map B) : NoDup (MAP FST (toAList t)).
Proof. apply ALL_DISTINCT_iff', ALL_DISTINCT_MAP_FST_toAList. Qed.

Lemma In_toAList_keys {B} (t : num_map B) x : In x (MAP FST (toAList t)) <-> domain t x.
Proof. rewrite <- MEM_iff'. apply MEM_toAList_dom. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_distinct_lemma" *)
Theorem ssa_reconcile_distinct_lemma : forall (f g : N -> N) (ns : num_set),
  INJ f (domain ns) UNIV ->
  ALL_DISTINCT (MAP FST
    (FILTER (fun '(a0, b) => negb (a0 =? b))
      (MAP (fun v => (f v, g v)) (MAP FST (toAList ns))))).
Proof.
  intros f g ns [_ Hi]. apply ALL_DISTINCT_iff'.
  assert (Hnd := NoDup_toAList_keys ns).
  assert (Hin : forall v, In v (MAP FST (toAList ns)) -> domain ns v) by (intros v; apply In_toAList_keys).
  revert Hnd Hin. generalize (MAP FST (toAList ns)) as L. induction L as [|v L IH]; intros Hnd Hin; [constructor|].
  inversion Hnd as [|? ? Hn Hnd']; subst. cbn [MAP List.map List.filter].
  destruct (negb (f v =? g v)); [|apply IH; auto; intros; apply Hin; right; assumption].
  cbn [List.map FST fst]. constructor; [|apply IH; auto; intros; apply Hin; right; assumption].
  intros Hm. apply in_map_iff in Hm as [[x y] [Ex Hm]]. cbn [fst] in Ex.
  apply filter_In in Hm as [Hm _]. apply in_map_iff in Hm as [w [Ew Hw]]. injection Ew as E1 E2.
  rewrite <- E1 in Ex. assert (w = v) as ->; [|contradiction].
  apply Hi; [split; apply Hin; [right; exact Hw|left; reflexivity]|exact Ex].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_moves_eq" *)
Theorem ssa_reconcile_moves_eq : forall (m : num_map N) (f : N -> N) L,
  FILTER (fun '(a0, b) => negb (a0 =? b))
    (FLAT (MAP (fun v => match lookup v m with None => [] | Some cv => [(f v, cv)] end) L)) =
  MAP (fun v => (f v, THE (lookup v m)))
    (FILTER (fun v => match lookup v m with None => false | Some cv => negb (f v =? cv) end) L).
Proof.
  intros m f; induction L as [|v L IH]; [reflexivity|].
  cbn [MAP List.map List.concat List.filter]. rewrite filter_app, IH.
  destruct (lookup v m) as [cv|] eqn:E; cbn [List.filter app]; [|reflexivity].
  destruct (negb (f v =? cv)); cbn [List.map MAP]; rewrite ?E; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_filtered_all_distinct" *)
Theorem ssa_reconcile_filtered_all_distinct : forall (cur_ssa tgt_ssa : num_map N) (ns : num_set),
  ALL_DISTINCT (FILTER (fun v => match lookup v cur_ssa with
                                 | None => false
                                 | Some cv => negb (option_lookup tgt_ssa v =? cv) end)
                  (MAP FST (toAList ns))).
Proof. intros. apply ALL_DISTINCT_iff', NoDup_filter', NoDup_toAList_keys. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_filtered_in_dom" *)
Theorem ssa_reconcile_filtered_in_dom : forall (cur_ssa tgt_ssa : num_map N) (ns : num_set) v,
  MEM v (FILTER (fun v => match lookup v cur_ssa with
                          | None => false
                          | Some cv => negb (option_lookup tgt_ssa v =? cv) end)
           (MAP FST (toAList ns))) ->
  v IN domain ns /\
  exists cv, lookup v cur_ssa = SOME cv /\ option_lookup tgt_ssa v <> cv /\ THE (lookup v cur_ssa) = cv.
Proof.
  intros cur_ssa tgt_ssa ns v Hm. rewrite MEM_iff' in Hm. apply filter_In in Hm as [Hm Hp].
  split; [apply In_toAList_keys, Hm|].
  destruct (lookup v cur_ssa) as [cv|]; [|discriminate]. exists cv.
  apply Bool.negb_true_iff, N.eqb_neq in Hp. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_reconcile_get_vars_lemma" *)
Theorem ssa_reconcile_get_vars_lemma : forall ls cur_ssa (cst : state),
  ALL_DISTINCT ls /\
  (forall v, MEM v ls -> exists val, lookup (THE (lookup v cur_ssa)) (locals cst) = SOME val) ->
  exists vs, get_vars (MAP (fun v => THE (lookup v cur_ssa)) ls) cst = SOME vs /\
    LENGTH vs = LENGTH ls /\
    forall i, i < LENGTH ls ->
      lookup (THE (lookup (EL i ls) cur_ssa)) (locals cst) = SOME (EL i vs).
Proof.
  induction ls as [|h ls IH]; intros cur_ssa cst [Hd H].
  - exists []. split; [reflexivity|split; [reflexivity|intros i Hi; cbn [LENGTH] in Hi; lia]].
  - apply ALL_DISTINCT_cons' in Hd as [_ Hd].
    destruct (IH cur_ssa cst) as (vs & Hg & Hl & Hi).
    { split; [exact Hd|intros v Hv; apply H; rewrite MEM_iff' in *; right; exact Hv]. }
    destruct (H h) as [val Hval]; [rewrite MEM_iff'; left; reflexivity|].
    exists (val :: vs). cbn [MAP List.map get_vars]. unfold get_var. rewrite Hval.
    change (List.map (fun v => THE (lookup v cur_ssa)) ls) with (MAP (fun v => THE (lookup v cur_ssa)) ls).
    rewrite Hg. split; [reflexivity|split; [cbn [LENGTH]; lia|]].
    intros i Hi'. destruct (N.eq_dec i 0) as [->|Hn0]; [exact Hval|].
    rewrite <- (N.succ_pred_pos i) by lia. rewrite !EL_SUC. cbn [TL]. apply Hi. cbn [LENGTH] in Hi'. lia.
Qed.

Lemma EL_map' {A B} `{Inhabited A, Inhabited B} (f : A -> B) l i :
  i < LENGTH l -> EL i (MAP f l) = f (EL i l).
Proof.
  intros Hi. rewrite !EL_nth by (rewrite ?LENGTH_MAP'; exact Hi).
  rewrite LENGTH_length in Hi. change (MAP f l) with (List.map f l).
  rewrite nth_indep with (d' := f ARB) by (rewrite length_map; lia). apply map_nth.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "alookup_zip_map_some" *)
Theorem alookup_zip_map_some : forall {B} `{EqDecision B, Inhabited B} (ls : list N) (vs : list B) i (f : N -> N),
  ALL_DISTINCT (MAP f ls) /\ i < LENGTH ls /\ LENGTH vs = LENGTH ls ->
  ALOOKUP (ZIP (MAP f ls, vs)) (f (EL i ls)) = SOME (EL i vs).
Proof.
  intros B EB IB ls vs i f (Hd & Hi & Hl). apply ALOOKUP_ALL_DISTINCT_MEM. split.
  - rewrite MAP_FST_ZIP' by (rewrite LENGTH_MAP'; lia). exact Hd.
  - rewrite MEM_iff', ZIP_combine'. rewrite <- (EL_map' f ls i Hi).
    rewrite !EL_nth by (rewrite ?LENGTH_MAP'; lia). rewrite <- combine_nth.
    + apply nth_In. rewrite length_combine, length_map; rewrite !LENGTH_length in *; lia.
    + rewrite length_map. rewrite !LENGTH_length in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "alookup_zip_map_option_lookup_none" *)
Theorem alookup_zip_map_option_lookup_none : forall {B} `{EqDecision B} (ls : list N) (vs : list B) n (ns : num_set) (f : N -> N),
  INJ f (domain ns) UNIV /\ n IN domain ns /\ ~ MEM n ls /\
  (forall v, MEM v ls -> v IN domain ns) /\ LENGTH vs = LENGTH ls ->
  ALOOKUP (ZIP (MAP f ls, vs)) (f n) = NONE.
Proof.
  intros B EB ls vs n ns f ([_ Hi] & Hn & Hm & Hv & Hl). apply ALOOKUP_NONE.
  rewrite MAP_FST_ZIP' by (rewrite LENGTH_MAP'; lia). rewrite MEM_iff'. intros Hin.
  apply in_map_iff in Hin as [w [Ew Hw]]. apply Hm. rewrite MEM_iff'.
  replace n with w; [exact Hw|]. apply Hi; [split; [apply Hv, MEM_iff', Hw|exact Hn]|exact Ew].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_ssa_reconcile" *)
Theorem evaluate_ssa_reconcile : forall na cur_ssa (st_locs : num_map (word_loc a)) (cst : state) tgt_ssa ns,
  ssa_locals_rel na cur_ssa st_locs (locals cst) /\
  INJ (option_lookup tgt_ssa) (domain ns) UNIV ->
  exists cst',
    evaluate (ssa_reconcile cur_ssa tgt_ssa ns, cst) = (NONE, cst') /\
    word_state_eq_rel cst cst' /\
    strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs (locals cst').
Proof.
  intros na cur_ssa st_locs cst tgt_ssa ns ([R1 R2] & Hinj).
  set (f := option_lookup tgt_ssa). set (g := fun v => THE (lookup v cur_ssa)).
  set (P := fun v => match lookup v cur_ssa with None => false | Some cv => negb (f v =? cv) end).
  set (fv := FILTER P (MAP FST (toAList ns))).
  assert (Hmoves : FILTER (fun '(a0, b) => negb (a0 =? b))
     (FLAT (MAP (fun v => match lookup v cur_ssa with None => [] | Some cv => [(option_lookup tgt_ssa v, cv)] end)
        (MAP FST (toAList ns)))) = MAP (fun v => (f v, g v)) fv)
    by apply ssa_reconcile_moves_eq.
  assert (Hfv : forall v, In v fv -> domain ns v /\ exists cv, lookup v cur_ssa = Some cv /\ f v <> cv /\ g v = cv).
  { intros v Hv. apply (ssa_reconcile_filtered_in_dom cur_ssa tgt_ssa ns v). rewrite MEM_iff'. exact Hv. }
  assert (Hnotfv : forall v, domain ns v -> ~ In v fv -> domain cur_ssa v -> f v = g v).
  { intros v Hv Hn Hd. apply domain_lookup in Hd as [cv Hcv]. unfold g; rewrite Hcv; cbn [THE].
    destruct (N.eq_dec (f v) cv) as [E|E]; [exact E|]. exfalso; apply Hn. apply filter_In.
    split; [apply In_toAList_keys, Hv|]. unfold P; rewrite Hcv. apply Bool.negb_true_iff, N.eqb_neq, E. }
  assert (Hsl : forall n v, n IN domain ns /\ lookup n st_locs = Some v -> lookup (g n) (locals cst) = Some v /\ domain cur_ssa n).
  { intros n v [_ Hn]. destruct (R2 _ _ Hn) as (Hd & Hl & _). auto. }
  unfold ssa_reconcile. rewrite Hmoves. fold fv.
  assert (Hc : fv = [] \/ fv <> []) by (destruct fv; [left|right]; congruence).
  destruct Hc as [Efv|Efv].
  - rewrite Efv. exists cst. rewrite evaluate_eqn; cbn [evaluate_body MAP List.map].
    split; [reflexivity|split; [apply word_state_eq_rel_refl|]].
    intros n v [Hn Hv]. destruct (Hsl n v (conj Hn Hv)) as [Hl Hd].
    rewrite (Hnotfv n Hn ltac:(rewrite Efv; intros [])) by exact Hd. exact Hl.
  - set (moves := MAP (fun v => (f v, g v)) fv).
    assert (Hmv : match moves with [] => @Skip a | _ => Move 1 moves end = Move 1 moves)
      by (unfold moves; destruct fv; [contradiction|reflexivity]).
    rewrite Hmv. clear Hmv.
    assert (Hnd : NoDup fv) by (apply NoDup_filter', NoDup_toAList_keys).
    assert (Hndf : NoDup (List.map f fv)).
    { apply NoDup_map_inj; [exact Hnd|]. intros x y Hx Hy E. destruct Hinj as [_ Hi].
      apply Hi; [split; [apply (proj1 (Hfv x Hx))|apply (proj1 (Hfv y Hy))]|exact E]. }
    destruct (get_vars_exists' (MAP g fv) cst) as [vs Hvs].
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. destruct (Hfv x Hx) as (_ & cv & Hcv & _ & Hg).
      rewrite Hg. apply domain_lookup, (R1 x cv Hcv). }
    exists (set_vars (MAP f fv) vs cst).
    rewrite evaluate_eqn; cbn [evaluate_body].
    replace (MAP FST moves) with (MAP f fv) by (unfold moves; rewrite List.map_map; reflexivity).
    replace (MAP SND moves) with (MAP g fv) by (unfold moves; rewrite List.map_map; reflexivity).
    rewrite (proj2 (ALL_DISTINCT_iff' _) Hndf), Hvs.
    split; [reflexivity|split; [unfold set_vars; apply wser_sl|]].
    intros n v [Hn Hv]. destruct (Hsl n v (conj Hn Hv)) as [Hl Hd].
    unfold set_vars. rewrite locals_set_locals.
    destruct (decide (In n fv)) as [Hin|Hin].
    + rewrite (alist_insert_map_lookup f g fv vs cst (locals cst) n Hndf Hin Hvs). exact Hl.
    + rewrite alist_insert_notin.
      * rewrite (Hnotfv n Hn Hin Hd). exact Hl.
      * intros Hm. apply in_map_iff in Hm as [w [Ew Hw]]. apply Hin. replace n with w; [exact Hw|].
        destruct Hinj as [_ Hi]. apply Hi; [split; [apply (proj1 (Hfv w Hw))|exact Hn]|exact Ew].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lt_ok_def" *)
Definition lt_ok (lt : list (num_map N * (num_set * num_set))) : Prop :=
  EVERY (fun '(tgt_ssa, (names, exit_names)) =>
    bool_decide (INJ (option_lookup tgt_ssa) (domain names) UNIV /\
                 INJ (option_lookup tgt_ssa) (domain exit_names) UNIV)) lt.

Lemma lt_ok_oEL lt n tgt names exit_names :
  lt_ok lt -> oEL n lt = Some (tgt, (names, exit_names)) ->
  INJ (option_lookup tgt) (domain names) UNIV /\ INJ (option_lookup tgt) (domain exit_names) UNIV.
Proof.
  revert n; induction lt as [|[t [nm ex]] lt IH]; intros n Hl E; [discriminate|].
  unfold lt_ok in Hl; cbn [EVERY] in Hl. apply andb_prop in Hl as [Hh Hl].
  cbn [oEL] in E. destruct (n =? 0).
  - injection E as <- <- <-. apply bool_decide_spec in Hh. exact Hh.
  - eapply IH; eassumption.
Qed.

Lemma lt_ok_cons t nm ex lt :
  lt_ok lt -> INJ (option_lookup t) (domain nm) UNIV -> INJ (option_lookup t) (domain ex) UNIV ->
  lt_ok ((t, (nm, ex)) :: lt).
Proof.
  intros Hl H1 H2. unfold lt_ok; cbn [EVERY]. apply andb_true_intro; split; [|exact Hl].
  apply bool_decide_spec. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "foldr_insert_const_swap" *)
Theorem foldr_insert_const_swap : forall rs h (v : word_loc a) m,
  FOLDR (fun r loc => insert r v loc) (insert h v m) rs =
  insert h v (FOLDR (fun r loc => insert r v loc) m rs).
Proof.
  induction rs as [|r rs IH]; intros h v m; [reflexivity|]. cbn [FOLDR]. rewrite IH.
  destruct (decide (r = h)) as [->|Hne]; [reflexivity|].
  apply insert_swap, Hne.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_fake_const_chain" *)
Theorem evaluate_fake_const_chain : forall rs (cst : state),
  evaluate (FOLDR Seq Skip (MAP (fun r => fake_move r) rs), cst) =
  (NONE, set_locals (FOLDR (fun r loc => insert r (Word (n2w 0)) loc) (locals cst) rs) cst).
Proof.
  induction rs as [|r rs IH]; intros cst; cbn [FOLDR MAP List.map].
  - rewrite evaluate_eqn; cbn [evaluate_body]. rewrite set_locals_eta. reflexivity.
  - rewrite (eval_Seq_none _ _ _ _ (eval_fake_move r cst)), IH. unfold set_var.
    rewrite locals_set_locals, sl_sl, foldr_insert_const_swap. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_fake_const_chain_locals" *)
Theorem evaluate_fake_const_chain_locals : forall rs (cst : state),
  let rcst := SND (evaluate (FOLDR Seq Skip (MAP (fun r => fake_move r) rs), cst)) in
  word_state_eq_rel cst rcst /\
  domain (locals rcst) = domain (locals cst) UNION set rs /\
  (forall r, ~ MEM r rs -> lookup r (locals rcst) = lookup r (locals cst)) /\
  (forall r, MEM r rs -> lookup r (locals rcst) = SOME (Word (n2w 0))).
Proof.
  intros rs cst. cbv zeta. rewrite evaluate_fake_const_chain. cbn [SND snd]. rewrite locals_set_locals.
  split; [apply wser_sl|]. induction rs as [|r rs IH]; cbn [FOLDR].
  - split; [apply set_ext; intros x; set_simp; tauto|split; [reflexivity|intros r Hr; discriminate Hr]].
  - destruct IH as (Hd & Hf & Hm). split; [|split].
    + rewrite domain_insert, Hd. apply set_ext; intros x. unfold pred_set.UNION, pred_set.IN. cbn [LIST_TO_SET]. tauto.
    + intros x Hx. apply not_MEM_cons in Hx as [Hx1 Hx2]. rewrite lookup_insert', decide_False' by exact Hx1. apply Hf, Hx2.
    + intros x Hx. rewrite lookup_insert'. destruct (decide (x = r)); [reflexivity|].
      apply Hm. rewrite MEM_iff' in *. destruct Hx; [congruence|assumption].
Qed.

Lemma In_lnvr_range ls ssa na l s n y :
  list_next_var_rename ls ssa na = (l, (s, n)) -> In y l -> na <= y /\ y < n.
Proof.
  intros E Hy. destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E) as (_ & Hl & Hn).
  rewrite Hl in Hy. apply in_map_iff in Hy as [i [<- Hi]]. apply In_COUNT_LIST in Hi. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "loop_setup_correct" *)
Theorem loop_setup_correct : forall (st cst : state) ssa na names exit_names
    setup_prog ssa_refreshed na_refreshed,
  word_state_eq_rel st cst /\
  ssa_locals_rel na ssa (locals st) (locals cst) /\
  ssa_map_ok na ssa /\
  is_alloc_var na /\
  loop_setup names exit_names ssa na = (setup_prog, (ssa_refreshed, na_refreshed)) ->
  exists rcst,
    evaluate (setup_prog, cst) = (NONE, rcst) /\
    word_state_eq_rel st rcst /\
    ssa_locals_rel na_refreshed ssa_refreshed (locals st) (locals rcst) /\
    na <= na_refreshed /\
    is_alloc_var na_refreshed /\
    ssa_map_ok na_refreshed ssa_refreshed /\
    domain ssa_refreshed = domain ssa UNION domain (union names exit_names) /\
    INJ (option_lookup ssa_refreshed) (domain names) UNIV /\
    INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV /\
    (forall v, v IN domain ssa_refreshed -> option_lookup ssa_refreshed v IN domain (locals rcst)).
Proof.
  intros st cst ssa na names exit_names setup_prog ssa_r na_r (Hw & Hr & Hok & Ha & E).
  unfold loop_setup in E.
  set (all := MAP FST (toAList (union names exit_names))) in E.
  set (ext := FILTER (fun v => bool_decide (lookup v ssa = None)) all) in E.
  set (rf := FILTER (fun v => IS_SOME (lookup v ssa)) all) in E.
  destruct (list_next_var_rename ext ssa na) as [fresh [sext next]] eqn:E1.
  destruct (list_next_var_rename_move sext next rf) as [rm [sr nr]] eqn:E2.
  injection E as <- <- <-.
  assert (Hall : forall v, In v all <-> domain (union names exit_names) v) by (intros v; apply In_toAList_keys).
  assert (Hext : forall v, In v ext <-> In v all /\ lookup v ssa = None).
  { intros v. unfold ext. rewrite filter_In. split; intros [H1 H2]; split; auto.
    - apply bool_decide_spec in H2; exact H2.
    - apply bool_decide_spec; exact H2. }
  assert (Hrf : forall v, In v rf <-> In v all /\ lookup v ssa <> None).
  { intros v. unfold rf. rewrite filter_In. destruct (lookup v ssa); cbn; intuition congruence. }
  assert (Hdext : ALL_DISTINCT ext) by (apply ALL_DISTINCT_iff', NoDup_filter', NoDup_toAList_keys).
  assert (Hdrf : ALL_DISTINCT rf) by (apply ALL_DISTINCT_iff', NoDup_filter', NoDup_toAList_keys).
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E1) as (Hdf & _ & _).
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E1 Hdext) as (Hfm & Hdom1 & Hfr1 & Hex1).
  destruct (lnvr_Inv _ _ _ _ _ _ E1 (conj Hok Ha)) as (Hle1 & HI1).
  pose proof (evaluate_fake_const_chain_locals fresh cst) as Fk. cbv zeta in Fk.
  rewrite evaluate_fake_const_chain in Fk. cbn [SND snd] in Fk.
  set (cst1 := set_locals (FOLDR (fun r loc => insert r (Word (n2w 0)) loc) (locals cst) fresh) cst) in Fk.
  destruct Fk as (Hw1 & Hd1 & Hf1 & Hm1).
  assert (Hr1 : ssa_locals_rel next sext (locals st) (locals cst1)).
  { destruct Hr as [R1 R2]. split.
    - intros x y Hxy. destruct (decide (In x ext)) as [Hx|Hx].
      + assert (Hy : In y fresh) by (rewrite Hfm; apply in_map_iff; exists x; rewrite Hxy; auto).
        apply domain_lookup. rewrite Hm1 by (apply MEM_iff', Hy). eauto.
      + rewrite Hfr1 in Hxy by (rewrite MEM_iff'; exact Hx). rewrite Hd1. left. eapply R1; exact Hxy.
    - intros x y Hxy. destruct (R2 _ _ Hxy) as (Hxd & Hxl & Hxa).
      apply domain_lookup in Hxd as [z Hz].
      assert (Hx : ~ In x ext) by (rewrite Hext; intros [_ E']; congruence).
      rewrite Hdom1. split; [left; apply domain_lookup; eauto|split; [|intros Hal; specialize (Hxa Hal); lia]].
      rewrite Hfr1 by (rewrite MEM_iff'; exact Hx). rewrite Hz in Hxl |- *. cbn [THE] in *.
      destruct (Hok _ _ Hz) as [_ Hzn]. rewrite Hf1; [exact Hxl|].
      rewrite MEM_iff'. intros Hin. destruct (In_lnvr_range _ _ _ _ _ _ _ E1 Hin). lia. }
  assert (Hw1' : word_state_eq_rel st cst1) by (eapply word_state_eq_rel_trans; [exact Hw|exact Hw1]).
  pose proof (lnvrm_core st cst1 sext next rf Hr1) as C.
  rewrite E2 in C. destruct (evaluate (rm, cst1)) as [res rcst] eqn:Erm.
  destruct C as (-> & Hrr & Hwr & _ & _); [|exact Hdrf|exact (proj1 HI1)|exact Hw1'|].
  { intros x Hx. rewrite Hdom1. left. apply Hrf in Hx as [_ Hx]. apply domain_lookup.
      destruct (lookup x ssa); [eauto|contradiction]. }
  exists rcst.
  destruct (lnvrm_Inv _ _ _ _ _ _ E2 HI1) as (Hle2 & Hok2 & Ha2).
  unfold list_next_var_rename_move in E2.
  destruct (list_next_var_rename rf sext next) as [l2 [s2 n2]] eqn:E3. injection E2 as _ <- <-.
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E3) as (Hdl2 & _ & _).
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E3 Hdrf) as (Hl2 & Hdom2 & Hfr2 & Hex2).
  assert (Hdom : domain s2 = domain ssa UNION domain (union names exit_names)).
  { rewrite Hdom2, Hdom1. apply set_ext; intros v. unfold pred_set.UNION, pred_set.IN.
    change (LIST_TO_SET ext v) with (v IN set ext). change (LIST_TO_SET rf v) with (v IN set rf).
    rewrite !IN_set, Hext, Hrf, Hall. destruct (lookup v ssa) eqn:Ev.
    - assert (domain ssa v) by (apply domain_lookup; eauto). split; [tauto|intros _]. left; left; assumption.
    - split; [intros [[H|[H _]]|[H _]]; [left; exact H|right; exact H|right; exact H]|].
      intros [H|H]; [apply lookup_NONE_domain in Ev; contradiction|]. left; right; split; [exact H|reflexivity]. }
  assert (Hinj : INJ (option_lookup s2) (domain (union names exit_names)) UNIV).
  { split; [intros; exact Logic.I|]. intros x y [Hx Hy] Exy.
    apply (proj2 (Hall x)) in Hx. apply (proj2 (Hall y)) in Hy.
    assert (Hval : forall v, In v all ->
      (In v ext /\ option_lookup s2 v = THE (lookup v sext) /\ In (THE (lookup v sext)) fresh) \/
      (In v rf /\ option_lookup s2 v = THE (lookup v s2) /\ In (THE (lookup v s2)) l2)).
    { intros v Hv. destruct (lookup v ssa) eqn:Ev.
      - right. assert (Hvr : In v rf) by (apply Hrf; split; [exact Hv|congruence]).
        destruct (Hex2 v (proj2 (MEM_iff' _ _) Hvr)) as [w Hw'].
        split; [exact Hvr|split; [unfold option_lookup; rewrite Hw'; reflexivity|]].
        rewrite Hl2. apply (in_map (fun x => THE (lookup x s2))), Hvr.
      - left. assert (Hve : In v ext) by (apply Hext; auto).
        assert (Hvr : ~ In v rf) by (rewrite Hrf; intros [_ H]; contradiction).
        destruct (Hex1 v (proj2 (MEM_iff' _ _) Hve)) as [w Hw'].
        split; [exact Hve|split; [unfold option_lookup; rewrite Hfr2 by (rewrite MEM_iff'; exact Hvr); rewrite Hw'; reflexivity|]].
        rewrite Hfm. apply (in_map (fun x => THE (lookup x sext))), Hve. }
    destruct (Hval x Hx) as [(Hx1 & Hx2 & Hx3)|(Hx1 & Hx2 & Hx3)], (Hval y Hy) as [(Hy1 & Hy2 & Hy3)|(Hy1 & Hy2 & Hy3)];
      rewrite Hx2, Hy2 in Exy.
    - rewrite Hfm in Hdf. apply ALL_DISTINCT_iff' in Hdf. exact (NoDup_map_inj' _ _ _ _ Hdf Hx1 Hy1 Exy).
    - destruct (In_lnvr_range _ _ _ _ _ _ _ E1 Hx3). destruct (In_lnvr_range _ _ _ _ _ _ _ E3 Hy3). lia.
    - destruct (In_lnvr_range _ _ _ _ _ _ _ E3 Hx3). destruct (In_lnvr_range _ _ _ _ _ _ _ E1 Hy3). lia.
    - rewrite Hl2 in Hdl2. apply ALL_DISTINCT_iff' in Hdl2. exact (NoDup_map_inj' _ _ _ _ Hdl2 Hx1 Hy1 Exy). }
  split; [rewrite (eval_Seq_none _ _ _ _ (evaluate_fake_const_chain fresh cst)); exact Erm|].
  split; [exact Hwr|split; [exact Hrr|split; [lia|split; [exact Ha2|split; [exact Hok2|split; [exact Hdom|]]]]]].
  split; [eapply INJ_less; split; [exact Hinj|]; intros v Hv; rewrite domain_union; left; exact Hv|].
  split; [eapply INJ_less; split; [exact Hinj|]; intros v Hv; rewrite domain_union; right; exact Hv|].
  intros v Hv. apply domain_lookup in Hv as [w Hw']. unfold option_lookup. rewrite Hw'.
  destruct Hrr as [R1 _]. eapply R1; exact Hw'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_seq_collapse" *)
Theorem evaluate_seq_collapse : forall (P Q : prog a) (s t : state),
  evaluate (P, s) = (NONE, t) -> evaluate (Seq P Q, s) = evaluate (Q, t).
Proof. intros P Q s t; apply eval_Seq_none. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_env_fromAList_LN" *)
Theorem cut_env_fromAList_LN : forall (a0 : num_set) (g : N * unit -> N * unit) (v : num_map (word_loc a)),
  cut_env (a0, fromAList (MAP g (toAList (LN : num_set)))) v = cut_env (a0, LN) v.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cut_inter_lemma" *)
Theorem ssa_cut_inter_lemma : forall (ssa' : num_map N) (x1 x2 : num_set) xx,
  domain ssa' INTER domain (union x1 x2) = domain x1 UNION domain x2 ->
  xx IN domain (union x1 x2) -> xx IN domain ssa'.
Proof.
  intros ssa' x1 x2 xx E Hx. pose proof (f_equal (fun P => P xx) E) as E'. cbv beta in E'.
  rewrite domain_union in Hx, E'. unfold pred_set.INTER, pred_set.UNION, pred_set.IN in *.
  assert (H : domain x1 xx \/ domain x2 xx) by exact Hx. rewrite <- E' in H. apply H.
Qed.
(** ** The [ssa_cc_trans] correctness statement (Galette-only names) *)

Definition ssa_post (lt : list (num_map N * (num_set * num_set))) (na' : N) (ssa' : num_map N)
    (res : option (result a)) (rst rcst : state) : Prop :=
  match res with
  | NONE => ssa_locals_rel na' ssa' (locals rst) (locals rcst)
  | SOME (Break n) =>
      match oEL n lt with
      | NONE => True
      | SOME (tgt_ssa, (_, exit_names)) =>
          strong_locals_rel (option_lookup tgt_ssa) (domain exit_names) (locals rst) (locals rcst)
      end
  | SOME (Continue n) =>
      match oEL n lt with
      | NONE => True
      | SOME (tgt_ssa, (names, _)) =>
          strong_locals_rel (option_lookup tgt_ssa) (domain names) (locals rst) (locals rcst)
      end
  | SOME _ => locals rst = locals rcst
  end.

Definition ssa_hyp (prog : prog a) (st cst : state) ssa na lt : Prop :=
  word_state_eq_rel st cst /\ ssa_locals_rel na ssa (locals st) (locals cst) /\
  is_alloc_var na /\ every_var (fun x => x <? na) prog /\ ssa_map_ok na ssa /\ lt_ok lt.

Definition ssa_concl (prog : prog a) (st cst : state) ssa na lt : Prop :=
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    res = SOME Error \/
    let '(prog', (ssa', na')) := ssa_cc_trans prog ssa na lt in
    let '(res', rcst) := evaluate (prog', cst) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na' ssa' res rst rcst.

Lemma is_Skip_eq (p : prog a) : is_Skip p = true -> p = Skip.
Proof. destruct p; cbn; congruence. Qed.

Lemma body_final_eval (body' : prog a) ssa' ssa_r names (cs t1 t1' : state) r1 na' :
  evaluate (body', cs) = (r1, t1') ->
  (r1 = NONE -> ssa_locals_rel na' ssa' (locals t1) (locals t1')) ->
  INJ (option_lookup ssa_r) (domain names) UNIV ->
  exists tb,
    evaluate (if is_Skip (@ssa_reconcile a ssa' ssa_r names) then body'
              else Seq body' (ssa_reconcile ssa' ssa_r names), cs) = (r1, tb) /\
    word_state_eq_rel t1' tb /\
    (r1 = NONE -> strong_locals_rel (option_lookup ssa_r) (domain names) (locals t1) (locals tb)) /\
    (r1 <> NONE -> tb = t1').
Proof.
  intros E Hr Hi. destruct r1 as [r|].
  - exists t1'. split; [|split; [apply word_state_eq_rel_refl|split; [discriminate|reflexivity]]].
    destruct (is_Skip _); [exact E|]. rewrite evaluate_Seq_eq', E. reflexivity.
  - destruct (evaluate_ssa_reconcile na' ssa' (locals t1) t1' ssa_r names (conj (Hr eq_refl) Hi))
      as (cst' & Ec & Hw & Hs).
    exists cst'. split; [|split; [exact Hw|split; [intros _; exact Hs|congruence]]].
    destruct (is_Skip _) eqn:Es.
    + apply is_Skip_eq in Es. rewrite Es in Ec. rewrite evaluate_eqn in Ec; cbn [evaluate_body] in Ec.
      injection Ec as <-. exact E.
    + rewrite (eval_Seq_none _ _ _ _ E). exact Ec.
Qed.

Lemma oEL_cons_pred {B} n (x : B) l : n <> 0 -> oEL n (x :: l) = oEL (n - 1) l.
Proof. intros H. cbn [oEL]. destruct (n =? 0) eqn:E; [apply N.eqb_eq in E; contradiction|reflexivity]. Qed.

Lemma loop_cut_rel na' (ssa_r : num_map N) (names : num_set) (env2 : num_map (word_loc a)) (y2 : num_map (word_loc a)) na_r :
  domain names SUBSET domain ssa_r ->
  is_true (EVERY (fun x => x <? na_r) (MAP FST (toAList names))) -> na_r <= na' ->
  domain y2 = IMAGE (option_lookup ssa_r) (domain env2) ->
  strong_locals_rel (option_lookup ssa_r) (domain names UNION domain (LN : num_set)) env2 y2 ->
  domain env2 = domain names UNION domain (LN : num_set) ->
  ssa_locals_rel na' (inter ssa_r names) env2 y2.
Proof.
  intros Hsub Hev Hle Dy Sy Dx.
  assert (Hdn : forall x, domain env2 x <-> domain names x).
  { intros x. rewrite Dx. unfold pred_set.UNION, pred_set.IN. cbn [domain]. tauto. }
  split.
  - intros x z Hxz. rewrite lookup_inter in Hxz.
    destruct (lookup x ssa_r) as [z'|] eqn:Ex, (lookup x names) eqn:Exn; try discriminate.
    injection Hxz as <-. rewrite Dy. exists x. split; [unfold option_lookup; rewrite Ex; reflexivity|].
    apply Hdn, domain_lookup; eauto.
  - intros x v Hxv. assert (Hx : domain names x) by (apply Hdn, domain_lookup; eauto).
    assert (Hxs : domain ssa_r x) by (apply Hsub, Hx).
    apply domain_lookup in Hxs as [z Hz]. pose proof Hx as Hx'. apply domain_lookup in Hx' as [u Hu].
    rewrite domain_inter. split; [split; apply domain_lookup; eauto|split].
    + rewrite lookup_inter, Hz, Hu. cbn [THE].
      assert (Hf : option_lookup ssa_r x = z) by (unfold option_lookup; rewrite Hz; reflexivity).
      rewrite <- Hf. apply Sy. split; [left; exact Hx|exact Hxv].
    + intros _. unfold is_true in Hev. rewrite EVERY_Forall, Forall_forall in Hev.
      specialize (Hev x (proj2 (In_toAList_keys names x) Hx)). apply N.ltb_lt in Hev. lia.
Qed.
Lemma ssa_Loop_gen (body : prog a) names exit_names lt ssa_r na_r body' ssa' na' :
  (forall st' cst' ssa'' na'' lt', ssa_hyp body st' cst' ssa'' na'' lt' -> ssa_concl body st' cst' ssa'' na'' lt') ->
  ssa_map_ok na_r ssa_r -> is_alloc_var na_r -> every_var (fun x => x <? na_r) body ->
  INJ (option_lookup ssa_r) (domain names) UNIV -> INJ (option_lookup ssa_r) (domain exit_names) UNIV ->
  domain names SUBSET domain ssa_r -> domain exit_names SUBSET domain ssa_r ->
  is_true (EVERY (fun x => x <? na_r) (MAP FST (toAList names))) ->
  is_true (EVERY (fun x => x <? na_r) (MAP FST (toAList exit_names))) ->
  lt_ok lt ->
  ssa_cc_trans body (inter ssa_r names) na_r ((ssa_r, (names, exit_names)) :: lt) = (body', (ssa', na')) ->
  forall (st cst : state), word_state_eq_rel st cst ->
  strong_locals_rel (option_lookup ssa_r) (domain names) (locals st) (locals cst) ->
  exists perm',
    let '(res, rst) := evaluate (Loop names body exit_names, set_permute perm' st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Loop (apply_nummap_key (option_lookup ssa_r) names)
          (if is_Skip (@ssa_reconcile a ssa' ssa_r names) then body' else Seq body' (ssa_reconcile ssa' ssa_r names))
          (apply_nummap_key (option_lookup ssa_r) exit_names), cst) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na' (inter ssa_r exit_names) res rst rcst.
Proof.
  intros IH Hok Ha Hev Hin Hex Hsn Hse Hkn Hke Hlt Eb st.
  assert (Hle' : na_r <= na').
  { destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Eb (conj (ssa_map_ok_inter _ _ _ Hok) Ha)) as [H _]. exact H. }
  set (f := option_lookup ssa_r) in *.
  remember (N.to_nat (clock st)) as k eqn:Hk. revert st Hk.
  induction k as [k IHk] using (well_founded_induction lt_wf). intros st Hk cst Heq Hs.
  destruct (cut_env (names, LN) (locals st)) as [env|] eqn:Ec.
  2:{ exists (permute st). rewrite evaluate_Loop_eq. unfold cut_state. rewrite locals_set_permute, Ec.
      left; reflexivity. }
  destruct (cut_env_lemma f (names, LN) (locals st) (locals cst) env) as (y & Ey & Dy & Sy & Iy & Dx).
  { cbn [FST SND fst snd]. split; [|split; [exact Ec|]].
    - eapply INJ_less; split; [exact Hin|]. intros x [Hx|Hx]; [exact Hx|cbn [domain] in Hx; contradiction].
    - eapply strong_locals_rel_subset; split; [|exact Hs]. intros x [Hx|Hx]; [exact Hx|cbn [domain] in Hx; contradiction]. }
  rewrite apply_nummaps_key_LN in Ey.
  set (s := set_locals env st). set (cs := set_locals y cst).
  assert (Hlt' : lt_ok ((ssa_r, (names, exit_names)) :: lt)) by (apply lt_ok_cons; auto).
  destruct (IH s cs (inter ssa_r names) na_r ((ssa_r, (names, exit_names)) :: lt)) as [perm1 Hp1].
  { split; [subst s cs; apply word_state_eq_rel_locals, Heq|].
    split; [change (locals s) with env; change (locals cs) with y;
            apply (loop_cut_rel na_r ssa_r names env y na_r); auto; lia|].
    split; [exact Ha|split; [exact Hev|split; [apply ssa_map_ok_inter, Hok|exact Hlt']]]. }
  rewrite Eb in Hp1.
  assert (Hcs : cut_state (apply_nummap_key f names, LN) cst = SOME cs) by (unfold cut_state; rewrite Ey; reflexivity).
  assert (Hst : forall p, cut_state (names, LN) (set_permute p st) = SOME (set_permute p s))
    by (intros p; unfold cut_state; rewrite locals_set_permute, Ec; reflexivity).
  destruct (evaluate (body, set_permute perm1 s)) as [r1 t1] eqn:E1.
  destruct Hp1 as [->|Hp1].
  { exists perm1. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. left; reflexivity. }
  destruct (evaluate (body', cs)) as [r1' t1'] eqn:E1'.
  destruct Hp1 as (<- & Hw1 & Hpost1).
  destruct (body_final_eval body' ssa' ssa_r names cs t1 t1' r1 na' E1') as (tb & Eb' & Hwb & Hnb & Hob).
  { intros ->. exact Hpost1. } { exact Hin. }
  assert (Hw1b : word_state_eq_rel t1 tb) by (eapply word_state_eq_rel_trans; eassumption).
  assert (Hck : clock tb = clock t1) by (destruct Hw1b; destr_conj; congruence).
  assert (Hclk : (clock t1 <= clock st)%N).
  { apply evaluate_clock in E1 as [E1 _]. rewrite clock_set_permute in E1. exact E1. }
  assert (Htarget : evaluate (Loop (apply_nummap_key f names)
          (if is_Skip (@ssa_reconcile a ssa' ssa_r names) then body' else Seq body' (ssa_reconcile ssa' ssa_r names))
          (apply_nummap_key f exit_names), cst) =
    if cont_loop r1 then
      (if clock tb =? 0 then (SOME TimeOut, flush_state true tb)
       else evaluate (Loop (apply_nummap_key f names)
          (if is_Skip (@ssa_reconcile a ssa' ssa_r names) then body' else Seq body' (ssa_reconcile ssa' ssa_r names))
          (apply_nummap_key f exit_names), dec_clock tb))
    else if bool_decide (r1 = SOME (Break 0)) then
      match cut_state (apply_nummap_key f exit_names, LN) tb with
      | NONE => (SOME Error, tb)
      | SOME s2 => (NONE, s2)
      end
    else (exit_loop r1, tb)).
  { rewrite evaluate_Loop_eq, Hcs, Eb'. reflexivity. }
  assert (Hrec : cont_loop r1 = true -> clock t1 <> 0 ->
            strong_locals_rel f (domain names) (locals t1) (locals tb) ->
            exists perm',
    let '(res, rst) := evaluate (Loop names body exit_names, set_permute perm' st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Loop (apply_nummap_key f names)
          (if is_Skip (@ssa_reconcile a ssa' ssa_r names) then body' else Seq body' (ssa_reconcile ssa' ssa_r names))
          (apply_nummap_key f exit_names), cst) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na' (inter ssa_r exit_names) res rst rcst).
  { intros Hcl Hc1 Hsn'.
    destruct (IHk (N.to_nat (clock (dec_clock t1))) ltac:(unfold dec_clock; cbn_ws; lia) (dec_clock t1) eq_refl
                (dec_clock tb)) as [perm2 Hp2].
    { unfold dec_clock; wser. } { unfold dec_clock; cbn_ws. exact Hsn'. }
    pose proof (permute_swap_lemma body (set_permute perm1 s) perm2) as H3. rewrite E1 in H3.
    assert (Hne : r1 <> SOME Error) by (destruct r1 as [[]|]; cbn in Hcl; congruence).
    destruct (H3 Hne) as [perm3 E3]. rewrite set_permute_set_permute in E3.
    exists perm3. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E3, Hcl, clock_set_permute.
    destruct (clock t1 =? 0) eqn:Ez; [apply N.eqb_eq in Ez; contradiction|].
    rewrite Hck, Ez, dec_clock_set_permute. exact Hp2. }
  assert (Hzero : cont_loop r1 = true -> clock t1 = 0 ->
            exists perm',
    let '(res, rst) := evaluate (Loop names body exit_names, set_permute perm' st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Loop (apply_nummap_key f names)
          (if is_Skip (@ssa_reconcile a ssa' ssa_r names) then body' else Seq body' (ssa_reconcile ssa' ssa_r names))
          (apply_nummap_key f exit_names), cst) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na' (inter ssa_r exit_names) res rst rcst).
  { intros Hcl Hc1. exists perm1. rewrite Htarget, evaluate_Loop_eq, Hst, E1, Hcl, Hck, Hc1, N.eqb_refl. cbn beta iota.
    right. split; [reflexivity|split; [unfold flush_state; wser|]]. cbn [ssa_post]. unfold flush_state; cbn_ws. reflexivity. }
  destruct r1 as [[x ys|x y'|n|n| | |ou|]|].
  - (* Result *) exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. rewrite (Hob ltac:(discriminate)).
    cbn [exit_loop]. auto.
  - (* Exception *) exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. rewrite (Hob ltac:(discriminate)).
    cbn [exit_loop]. auto.
  - (* Break *)
    rewrite (Hob ltac:(discriminate)) in *.
    destruct (n =? 0) eqn:En.
    + apply N.eqb_eq in En; subst n. exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop].
      rewrite bd_true' by reflexivity. cbn beta iota.
      cbn [ssa_post oEL N.eqb] in Hpost1.
      destruct (cut_state (exit_names, LN) t1) as [t2|] eqn:Ec2; [|left; reflexivity]. right.
      unfold cut_state in Ec2 |- *. destruct (cut_env (exit_names, LN) (locals t1)) as [env2|] eqn:Ee2; [|discriminate].
      injection Ec2 as <-.
      destruct (cut_env_lemma f (exit_names, LN) (locals t1) (locals t1') env2) as (y2 & Ey2 & Dy2 & Sy2 & _ & Dx2).
      { cbn [FST SND fst snd]. split; [|split; [exact Ee2|]].
        - eapply INJ_less; split; [exact Hex|]. intros z [Hz|Hz]; [exact Hz|cbn [domain] in Hz; contradiction].
        - eapply strong_locals_rel_subset; split; [|exact Hpost1]. intros z [Hz|Hz]; [exact Hz|cbn [domain] in Hz; contradiction]. }
      rewrite apply_nummaps_key_LN in Ey2. rewrite Ey2. cbn [ssa_post].
      split; [reflexivity|split; [apply word_state_eq_rel_locals, Hw1|]]. rewrite !locals_set_locals.
      apply (loop_cut_rel na' ssa_r exit_names env2 y2 na_r); auto.
    + exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop].
      rewrite bd_false' by (intros E; injection E as ->; discriminate). cbn beta iota. right. cbn [exit_loop].
      split; [reflexivity|split; [exact Hw1|]]. cbn [ssa_post] in *.
      rewrite oEL_cons_pred in Hpost1 by (apply N.eqb_neq, En). exact Hpost1.
  - (* Continue *)
    destruct (n =? 0) eqn:En.
    + apply N.eqb_eq in En; subst n.
      cbn [ssa_post oEL N.eqb] in Hpost1. rewrite <- (Hob ltac:(discriminate)) in Hpost1.
      destruct (clock t1 =? 0) eqn:Ez; [apply N.eqb_eq in Ez; apply Hzero; [reflexivity|exact Ez]|].
      apply Hrec; [reflexivity|apply N.eqb_neq, Ez|exact Hpost1].
    + rewrite (Hob ltac:(discriminate)) in *.
      exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop]. rewrite En.
      rewrite bd_false' by discriminate. cbn beta iota. right. cbn [exit_loop].
      split; [reflexivity|split; [exact Hw1|]]. cbn [ssa_post] in *.
      rewrite oEL_cons_pred in Hpost1 by (apply N.eqb_neq, En). exact Hpost1.
  - (* TimeOut *) exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. rewrite (Hob ltac:(discriminate)).
    cbn [exit_loop]. auto.
  - (* NotEnoughSpace *) exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. rewrite (Hob ltac:(discriminate)).
    cbn [exit_loop]. auto.
  - (* FinalFFI *) exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. rewrite (Hob ltac:(discriminate)).
    cbn [exit_loop]. auto.
  - (* Error *) exists perm1. rewrite Htarget. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. left. reflexivity.
  - (* NONE *)
    destruct (clock t1 =? 0) eqn:Ez; [apply N.eqb_eq in Ez; apply Hzero; [reflexivity|exact Ez]|].
    apply Hrec; [reflexivity|apply N.eqb_neq, Ez|exact (Hnb eq_refl)].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_Loop_helper" *)
Theorem ssa_cc_trans_Loop_helper : forall (st cst : state) ssa_refreshed na_refreshed
    names body exit_names lt body' ssa' na',
  word_state_eq_rel st cst /\
  strong_locals_rel (option_lookup ssa_refreshed) (domain names) (locals st) (locals cst) /\
  (forall v, v IN domain names -> option_lookup ssa_refreshed v IN domain (locals cst)) /\
  ssa_map_ok na_refreshed ssa_refreshed /\
  is_alloc_var na_refreshed /\
  every_var (fun x => x <? na_refreshed) body /\
  INJ (option_lookup ssa_refreshed) (domain names) UNIV /\
  INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV /\
  domain names SUBSET domain ssa_refreshed /\
  domain exit_names SUBSET domain ssa_refreshed /\
  EVERY (fun x => x <? na_refreshed) (MAP FST (toAList names)) /\
  EVERY (fun x => x <? na_refreshed) (MAP FST (toAList exit_names)) /\
  lt_ok lt /\
  ssa_cc_trans body (inter ssa_refreshed names) na_refreshed
    ((ssa_refreshed, (names, exit_names)) :: lt) = (body', (ssa', na')) /\
  (forall (st' cst' : state) ssa'' na'' lt',
     word_state_eq_rel st' cst' /\
     ssa_locals_rel na'' ssa'' (locals st') (locals cst') /\
     is_alloc_var na'' /\
     every_var (fun x => x <? na'') body /\
     ssa_map_ok na'' ssa'' /\
     lt_ok lt' ->
     exists perm',
       let '(res, rst) := evaluate (body, set_permute perm' st') in
       res = SOME Error \/
       let '(prog', (ssaB, naB)) := ssa_cc_trans body ssa'' na'' lt' in
       let '(res', rcst) := evaluate (prog', cst') in
       res = res' /\ word_state_eq_rel rst rcst /\
       match res with
       | NONE => ssa_locals_rel naB ssaB (locals rst) (locals rcst)
       | SOME (Break n) =>
           match oEL n lt' with
           | NONE => True
           | SOME (tgt_ssa, (_, exit_names)) =>
               strong_locals_rel (option_lookup tgt_ssa) (domain exit_names) (locals rst) (locals rcst)
           end
       | SOME (Continue n') =>
           match oEL n' lt' with
           | NONE => True
           | SOME (tgt_ssa, (names, _)) =>
               strong_locals_rel (option_lookup tgt_ssa) (domain names) (locals rst) (locals rcst)
           end
       | SOME _ => locals rst = locals rcst
       end) ->
  let back_moves := ssa_reconcile ssa' ssa_refreshed names in
  let body_final := if is_Skip back_moves then body' else Seq body' back_moves in
  let ssa_names := apply_nummap_key (option_lookup ssa_refreshed) names in
  let ssa_exit := apply_nummap_key (option_lookup ssa_refreshed) exit_names in
  forall res' rcst,
    evaluate (Loop ssa_names body_final ssa_exit, cst) = (res', rcst) ->
    exists perm',
      (fun '(res, rst) =>
         res = SOME Error \/
         res = res' /\ word_state_eq_rel rst rcst /\
         match res with
         | NONE => ssa_locals_rel na' (inter ssa_refreshed exit_names) (locals rst) (locals rcst)
         | SOME (Break n) =>
             match oEL n lt with
             | NONE => True
             | SOME (tgt_ssa, (_, exit_names)) =>
                 strong_locals_rel (option_lookup tgt_ssa) (domain exit_names) (locals rst) (locals rcst)
             end
         | SOME (Continue n') =>
             match oEL n' lt with
             | NONE => True
             | SOME (tgt_ssa, (names, _)) =>
                 strong_locals_rel (option_lookup tgt_ssa) (domain names) (locals rst) (locals rcst)
             end
         | SOME _ => locals rst = locals rcst
         end)
      (evaluate (Loop names body exit_names, set_permute perm' st)).
Proof.
  intros st cst ssa_r na_r names body exit_names lt body' ssa' na'
    (Hw & Hs & _ & Hok & Ha & Hev & Hin & Hex & Hsn & Hse & Hkn & Hke & Hlt & Eb & IH).
  cbv zeta. intros res' rcst Ev.
  destruct (ssa_Loop_gen body names exit_names lt ssa_r na_r body' ssa' na' IH Hok Ha Hev Hin Hex Hsn Hse Hkn Hke Hlt Eb st cst Hw Hs)
    as [perm Hp].
  exists perm. rewrite Ev in Hp. destruct (evaluate (Loop names body exit_names, set_permute perm st)) as [res rst].
  exact Hp.
Qed.
End SSA2.
