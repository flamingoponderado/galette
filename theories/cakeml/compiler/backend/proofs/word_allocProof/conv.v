(** * CakeML [word_allocProof]: syntactic conventions

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    10377-11484): the SSA transformation sets up [pre_alloc_conventions],
    [distinct_tar_reg] and [full_inst_ok_less]; colouring preserves the
    variable conventions; [word_alloc] establishes
    [post_alloc_conventions].

    Notes: as in [ssa_props.v].  HOL's [let (a,b,c,d,e) = fake_moves ...]
    binds [(a0, (b0, (c0, (d0, e0))))].  The commented-out HOL theorem
    [lookup_undir_g_insert_existing] is not ported. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.reg_allocProof Require Import check_clash_tree.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang word_alloc.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring clash ssa_props ssa_loop ssa ssa_full.
Open Scope N_scope.

Section Conv.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_conventions" *)
Theorem fake_moves_conventions : forall prio ls ssaL ssaR na,
  let '(a0, (b0, (c0, (d0, e0)))) := @fake_moves a prio ls ssaL ssaR na in
  every_stack_var is_stack_var a0 /\ every_stack_var is_stack_var b0 /\
  call_arg_convention a0 /\ call_arg_convention b0.
Proof.
  intros prio; induction ls as [|h ls IH]; intros ssaL ssaR na; cbn [fake_moves].
  - repeat split.
  - specialize (IH ssaL ssaR na). destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
    destruct IH as (H1 & H2 & H3 & H4).
    destruct (lookup h sL), (lookup h sR); cbn [every_stack_var call_arg_convention fake_move inst_arg_convention];
      unfold is_true in *; rewrite ?H1, ?H2, ?H3, ?H4; repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fix_inconsistencies_conventions" *)
Theorem fix_inconsistencies_conventions : forall ssaL ssaR na prio,
  let '(a0, (b0, (c0, d0))) := @fix_inconsistencies a prio ssaL ssaR na in
  every_stack_var is_stack_var a0 /\ every_stack_var is_stack_var b0 /\
  call_arg_convention a0 /\ call_arg_convention b0.
Proof.
  intros ssaL ssaR na prio. unfold fix_inconsistencies.
  destruct (merge_moves _ ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  pose proof (fake_moves_conventions prio (MAP FST (toAList (union ssaL ssaR))) sL sR n') as H.
  destruct (fake_moves prio _ sL sR n') as [fL [fR [n'' [sL' sR']]]].
  destruct H as (H1 & H2 & H3 & H4). cbn [every_stack_var call_arg_convention].
  unfold is_true in *. rewrite H1, H2, H3, H4. repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_name_def2" *)
Theorem every_name_def2 : forall (P : N -> bool) (t : cutsets),
  every_name P t = EVERY P (MAP FST (toAList (union (FST t) (SND t)))).
Proof.
  intros P [t1 t2]. unfold every_name. cbn [FST SND fst snd].
  apply Bool.eq_true_iff_eq. unfold is_true. rewrite Bool.andb_true_iff, !EVERY_Forall, !Forall_forall.
  split.
  - intros [H1 H2] x Hx. apply In_toAList_keys in Hx. rewrite domain_union in Hx.
    destruct Hx as [Hx|Hx]; [apply H1|apply H2]; apply In_toAList_keys, Hx.
  - intros H; split; intros x Hx; apply H, In_toAList_keys; rewrite domain_union;
      apply In_toAList_keys in Hx; [left|right]; exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "union_apply_nummaps_key" *)
Theorem union_apply_nummaps_key : forall {B} (f : N -> N) (p : num_map B * num_map B),
  domain (union (FST (apply_nummaps_key f p)) (SND (apply_nummaps_key f p))) =
  domain (apply_nummap_key f (union (FST p) (SND p))).
Proof.
  intros B f [p1 p2]. cbn [apply_nummaps_key FST SND fst snd].
  fold (apply_nummap_key f p1) (apply_nummap_key f p2).
  rewrite domain_union, !apply_nummap_key_domain, domain_union.
  apply set_ext; intros x. unfold pred_set.IMAGE, pred_set.IN. split.
  - intros [[y [-> Hy]]|[y [-> Hy]]]; exists y; split; auto.
  - intros [y [-> [Hy|Hy]]]; [left|right]; exists y; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_seq_pre_alloc_conventions" *)
Theorem fake_seq_pre_alloc_conventions : forall ls,
  pre_alloc_conventions (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof.
  induction ls as [|r ls IH]; [reflexivity|]. unfold pre_alloc_conventions in *.
  cbn [FOLDR MAP List.map every_stack_var call_arg_convention fake_move inst_arg_convention].
  unfold is_true in *. apply andb_prop in IH as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_seq_every_inst_distinct_tar_reg" *)
Theorem fake_seq_every_inst_distinct_tar_reg : forall ls,
  every_inst distinct_tar_reg (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof.
  induction ls as [|r ls IH]; [reflexivity|]. cbn [FOLDR MAP List.map every_inst fake_move distinct_tar_reg].
  exact IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_seq_full_inst_ok_less" *)
Theorem fake_seq_full_inst_ok_less : forall (c : asm_config a) ls,
  full_inst_ok_less c (FOLDR Seq Skip (MAP (fun r => @fake_move a r) ls)).
Proof.
  intros c; induction ls as [|r ls IH]; [reflexivity|]. cbn [FOLDR MAP List.map full_inst_ok_less fake_move inst_ok_less].
  exact IH.
Qed.

Lemma loop_setup_shape names exit_names ssa na (setup_prog : prog a) ssa_r na_r :
  loop_setup names exit_names ssa na = (setup_prog, (ssa_r, na_r)) ->
  exists fresh ms, setup_prog = Seq (FOLDR Seq Skip (MAP (fun r => fake_move r) fresh)) (Move 0 ms).
Proof.
  unfold loop_setup. destruct (list_next_var_rename _ ssa na) as [fresh [s1 n1]].
  destruct (list_next_var_rename_move s1 n1 _) as [mv [s2 n2]] eqn:E2.
  destruct (lnvrm_is_move _ _ _ _ _ E2) as [ms ->]. intros E; injection E as <- _ _. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "loop_setup_pre_alloc_conventions" *)
Theorem loop_setup_pre_alloc_conventions : forall names exit_names ssa na (setup_prog : prog a) ssa_refreshed na_refreshed,
  loop_setup names exit_names ssa na = (setup_prog, (ssa_refreshed, na_refreshed)) ->
  pre_alloc_conventions setup_prog.
Proof.
  intros names exit_names ssa na setup_prog ssa_r na_r E.
  destruct (loop_setup_shape _ _ _ _ _ _ _ E) as (fresh & ms & ->).
  pose proof (fake_seq_pre_alloc_conventions fresh) as H. unfold pre_alloc_conventions in *.
  cbn [every_stack_var call_arg_convention]. unfold is_true in *. apply andb_prop in H as [H1 H2].
  rewrite H1, H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "loop_setup_props_local" *)
Theorem loop_setup_props_local : forall names exit_names ssa na (setup_prog : prog a) ssa_refreshed na_refreshed,
  loop_setup names exit_names ssa na = (setup_prog, (ssa_refreshed, na_refreshed)) /\
  ssa_map_ok na ssa /\ is_alloc_var na ->
  is_alloc_var na_refreshed /\ ssa_map_ok na_refreshed ssa_refreshed /\ na <= na_refreshed.
Proof.
  intros names exit_names ssa na setup_prog ssa_r na_r (E & Hok & Ha).
  destruct (loop_setup_Inv _ _ _ _ _ _ _ E (conj Hok Ha)) as (H1 & H2 & H3). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "loop_setup_every_inst_distinct_tar_reg" *)
Theorem loop_setup_every_inst_distinct_tar_reg : forall names exit_names ssa na (setup_prog : prog a) ssa_refreshed na_refreshed,
  loop_setup names exit_names ssa na = (setup_prog, (ssa_refreshed, na_refreshed)) ->
  every_inst distinct_tar_reg setup_prog.
Proof.
  intros names exit_names ssa na setup_prog ssa_r na_r E.
  destruct (loop_setup_shape _ _ _ _ _ _ _ E) as (fresh & ms & ->).
  cbn [every_inst]. rewrite (fake_seq_every_inst_distinct_tar_reg fresh). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "loop_setup_full_inst_ok_less" *)
Theorem loop_setup_full_inst_ok_less : forall names exit_names ssa na (setup_prog : prog a) ssa_refreshed na_refreshed (c : asm_config a),
  loop_setup names exit_names ssa na = (setup_prog, (ssa_refreshed, na_refreshed)) ->
  full_inst_ok_less c setup_prog.
Proof.
  intros names exit_names ssa na setup_prog ssa_r na_r c E.
  destruct (loop_setup_shape _ _ _ _ _ _ _ E) as (fresh & ms & ->).
  cbn [full_inst_ok_less]. rewrite (fake_seq_full_inst_ok_less c fresh). reflexivity.
Qed.

Lemma stack_set_stack_vars ssa na (n1 n2 : num_set) (mov : prog a) ssa' na' :
  list_next_var_rename_move ssa (na + 2) (MAP FST (toAList (union n1 n2))) = (mov, (ssa', na')) ->
  is_alloc_var na -> every_name is_stack_var (apply_nummaps_key (option_lookup ssa') (n1, n2)).
Proof.
  intros E Ha. rewrite every_name_def2. unfold is_true. rewrite EVERY_Forall, Forall_forall.
  intros k Hk. apply In_toAList_keys in Hk.
  change (k IN domain (union (FST (apply_nummaps_key (option_lookup ssa') (n1, n2)))
                              (SND (apply_nummaps_key (option_lookup ssa') (n1, n2))))) in Hk.
  rewrite union_apply_nummaps_key, apply_nummap_key_domain in Hk. destruct Hk as [x [-> Hx]].
  cbn [FST SND fst snd] in Hx.
  unfold list_next_var_rename_move in E.
  destruct (list_next_var_rename _ ssa (na + 2)) as [l [s m]] eqn:E1. injection E as _ <- <-.
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E1) as (_ & Hl & _).
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E1 ltac:(apply ALL_DISTINCT_MAP_FST_toAList))
    as (Hm & _ & _ & Hex).
  assert (Hxl : In x (MAP FST (toAList (union n1 n2)))) by (apply In_toAList_keys, Hx).
  destruct (Hex x (proj2 (MEM_iff' _ _) Hxl)) as [y Hy].
  assert (Hin : In y l).
  { rewrite Hm. apply in_map_iff. exists x. rewrite Hy. auto. }
  rewrite Hl in Hin. apply In_map_4 in Hin as [i Hi].
  unfold option_lookup. rewrite Hy. subst y. unfold is_stack_var. apply N.eqb_eq.
  unfold is_alloc_var in Ha. apply N.eqb_eq in Ha.
  replace (4 * i + (na + 2)) with ((na + 2) + i * 4) by lia. rewrite N.Div0.mod_add, mod4_add2, Ha. reflexivity.
Qed.

Lemma GENLIST_rets_eq (l : list N) :
  bool_decide (GENLIST (fun x => 2 * (x + 1)) (LENGTH l) =
               GENLIST (fun x => 2 * (x + 1)) (LENGTH (GENLIST (fun x => 2 * (x + 1)) (LENGTH l)))) = true.
Proof. apply bool_decide_spec. rewrite LENGTH_GENLIST'. reflexivity. Qed.

Lemma GENLIST_args_eq (l : list N) :
  bool_decide (GENLIST (fun x => 2 * x) (LENGTH l) =
               GENLIST (fun x => 2 * x) (LENGTH (GENLIST (fun x => 2 * x) (LENGTH l)))) = true.
Proof. apply bool_decide_spec. rewrite LENGTH_GENLIST'. reflexivity. Qed.

Lemma reconcile_pac ssa' ssa_r (names : num_set) :
  pre_alloc_conventions (@ssa_reconcile a ssa' ssa_r names).
Proof. unfold ssa_reconcile. destruct (FILTER _ _); reflexivity. Qed.

Lemma pac_seq (p1 p2 : prog a) :
  pre_alloc_conventions (Seq p1 p2) = pre_alloc_conventions p1 && pre_alloc_conventions p2.
Proof.
  unfold pre_alloc_conventions. cbn [every_stack_var call_arg_convention].
  destruct (every_stack_var _ p1), (every_stack_var _ p2), (call_arg_convention p1), (call_arg_convention p2); reflexivity.
Qed.

Ltac moves_shape :=
  repeat match goal with
  | E : list_next_var_rename_move _ _ _ = (?p, _) |- _ =>
      is_var p; let ms := fresh "ms" in destruct (lnvrm_is_move _ _ _ _ _ E) as [ms ->]
  end.

Lemma inst_pac (i : asm.inst a) ssa na (p : prog a) s n :
  ssa_cc_trans_inst i ssa na = (p, (s, n)) -> pre_alloc_conventions p.
Proof.
  intros E. destruct_inst i; cbn [ssa_cc_trans_inst next_var_rename] in E;
    repeat match type of E with
           | context [if ?b then _ else _] => destruct b
           | context [match ?r with Reg _ => _ | Imm _ => _ end] => destruct r
           end;
    injection E as <- _ _; unfold pre_alloc_conventions; reflexivity.
Qed.

Ltac pac_simp :=
  unfold pre_alloc_conventions in *; cbn [every_stack_var call_arg_convention inst_arg_convention fake_move] in *;
  unfold is_true in *; rewrite ?Bool.andb_true_iff in *; repeat match goal with |- _ /\ _ => split end;
  try reflexivity.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_pre_alloc_conventions" *)
Theorem ssa_cc_trans_pre_alloc_conventions : forall (prog : prog a) ssa na lt,
  is_alloc_var na /\ ssa_map_ok na ssa ->
  let '(prog', (ssa', na')) := ssa_cc_trans prog ssa na lt in
  pre_alloc_conventions prog'.
Proof.
  intros prog. cut (forall ssa na lt, Inv na ssa ->
    let '(prog', (ssa', na')) := ssa_cc_trans prog ssa na lt in pre_alloc_conventions prog').
  { intros H ssa na lt [Ha Hok]. apply H. split; assumption. }
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros ssa na lt HI; cbn [ssa_cc_trans next_var_rename]; destr_lets_goal; moves_shape.
  all: try (pac_simp; fail).
  (* Inst *)
  - exact (inst_pac _ _ _ _ _ _ Ex).
  (* MustTerminate *)
  - pose proof (IH ssa na lt HI) as H. rewrite Ex in H. pac_simp; tauto.
  (* Call *)
  - destruct ret as [[rv [[c1 c2] [rh [l1 l2]]]]|]; cbn beta iota zeta; destr_lets_goal; moves_shape;
      [|pac_simp; apply GENLIST_args_eq].
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    destruct (lnvrm_stack_Inv _ _ _ _ _ _ Ex0 H3 (ssa_map_ok_inter _ _ _ H2)) as (H4 & HI4).
    destruct (lnvr_Inv _ _ _ _ _ _ Ex1 HI4) as (H5 & HI5).
    pose proof (IHr _ _ lt HI5) as Hr. rewrite Ex2 in Hr.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex2 HI5) as (H6 & H6a & H6o).
    pose proof (stack_set_stack_vars ssa na c1 c2 _ _ _ Ex (proj2 HI)) as Hst.
    destruct h as [[hn [hp [l1' l2']]]|]; cbn beta iota zeta; destr_lets_goal; moves_shape.
    + assert (HI7 : Inv (n2 + 4) (insert hn n2 s0)).
      { apply Inv_step. split; [apply (Inv_more _ _ _ HI4); lia|exact H6a]. }
      pose proof (IHh _ _ lt HI7) as Hh. rewrite Ex3 in Hh.
      match goal with E : fix_inconsistencies ?P ?A ?B ?C = _ |- _ =>
        pose proof (fix_inconsistencies_conventions A B C P) as Hf; rewrite E in Hf end. destruct Hf as (Hf1 & Hf2 & Hf3 & Hf4).
      pac_simp; try tauto; try (apply GENLIST_args_eq || apply GENLIST_rets_eq);
        try (cbn [every_name] in Hst; unfold is_true in Hst; rewrite Bool.andb_true_iff in Hst; tauto);
        try (apply bool_decide_spec; rewrite LENGTH_GENLIST'; reflexivity).
    + pac_simp; try tauto; try (apply GENLIST_args_eq || apply GENLIST_rets_eq);
        try (cbn [every_name] in Hst; unfold is_true in Hst; rewrite Bool.andb_true_iff in Hst; tauto);
        try (apply bool_decide_spec; rewrite LENGTH_GENLIST'; reflexivity).
  (* Seq *)
  - pose proof (IH1 ssa na lt HI) as H1. rewrite Ex in H1.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex HI) as (Hle & Ha1 & Hok1).
    pose proof (IH2 s n lt (conj Hok1 Ha1)) as H2. rewrite Ex0 in H2.
    rewrite pac_seq. unfold is_true in *. rewrite H1, H2. reflexivity.
  (* If *)
  - pose proof (IH1 ssa na lt HI) as H1. rewrite Ex in H1.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex HI) as (Hle & Ha1 & Hok1).
    pose proof (IH2 ssa n lt (conj (Inv_more _ _ _ HI Hle) Ha1)) as H2. rewrite Ex0 in H2.
    pose proof (fix_inconsistencies_conventions s s0 n0 (mk_prio p p0)) as Hf. rewrite Ex1 in Hf.
    destruct Hf as (Hf1 & Hf2 & Hf3 & Hf4). pac_simp; tauto.
  (* Loop *)
  - pose proof (loop_setup_pre_alloc_conventions _ _ _ _ _ _ _ Ex) as Hs.
    destruct (loop_setup_Inv _ _ _ _ _ _ _ Ex HI) as [Hle HI1].
    pose proof (IH (inter s n1) n ((s, (n1, n2)) :: lt) (conj (ssa_map_ok_inter _ _ _ (proj1 HI1)) (proj2 HI1))) as Hb.
    rewrite Ex0 in Hb.
    rewrite pac_seq. unfold is_true in Hs |- *. rewrite Hs. cbn [andb].
    destruct (is_Skip _); [pac_simp; tauto|].
    pose proof (reconcile_pac s0 s n1) as Hr. rewrite pac_seq in Hr || idtac. pac_simp; tauto.
  (* Alloc *)
  - pose proof (stack_set_stack_vars ssa na (FST names) (SND names) _ _ _ Ex (proj2 HI)) as Hst.
    destruct names as [c1 c2]. cbn [FST SND fst snd] in *.
    pac_simp; cbn [every_name] in Hst; unfold is_true in Hst; rewrite ?Bool.andb_true_iff in Hst; tauto.
  (* Return *)
  - pac_simp. apply GENLIST_rets_eq.
  (* Break *)
  - destruct (oEL n lt) as [[tgt [nm ex]]|]; cbn beta iota zeta; [|pac_simp].
    destruct (is_Skip _); [pac_simp|]. pose proof (reconcile_pac ssa tgt ex) as Hr. pac_simp; tauto.
  (* Continue *)
  - destruct (oEL n lt) as [[tgt [nm ex]]|]; cbn beta iota zeta; [|pac_simp].
    destruct (is_Skip _); [pac_simp|]. pose proof (reconcile_pac ssa tgt nm) as Hr. pac_simp; tauto.
  (* Install *)
  - pose proof (stack_set_stack_vars ssa na (FST names) (SND names) _ _ _ Ex (proj2 HI)) as Hst.
    destruct names as [c1 c2]. cbn [FST SND fst snd] in *.
    pac_simp; cbn [every_name] in Hst; unfold is_true in Hst; rewrite ?Bool.andb_true_iff in Hst; tauto.
  (* FFI *)
  - pose proof (stack_set_stack_vars ssa na (FST names) (SND names) _ _ _ Ex (proj2 HI)) as Hst.
    destruct names as [c1 c2]. cbn [FST SND fst snd] in *.
    pac_simp; cbn [every_name] in Hst; unfold is_true in Hst; rewrite ?Bool.andb_true_iff in Hst; tauto.
  (* ShareInst *)
  - destruct (bool_decide _); destr_lets_goal; pac_simp.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "setup_ssa_props_2" *)
Theorem setup_ssa_props_2 : forall lim n (prog : prog a),
  is_alloc_var lim ->
  let '(mov, (ssa, na)) := setup_ssa n lim prog in
  ssa_map_ok na ssa /\ is_alloc_var na /\ pre_alloc_conventions mov /\ lim <= na.
Proof.
  intros lim n prog Ha. unfold setup_ssa.
  destruct (list_next_var_rename (even_list n) LN lim) as [nl [ssa' na']] eqn:E.
  assert (Hok0 : ssa_map_ok lim (LN : num_map N)) by (intros x y Hx; cbn in Hx; discriminate Hx).
  destruct (lnvr_Inv _ _ _ _ _ _ E (conj Hok0 Ha)) as (Hle & Hok & Ha').
  split; [exact Hok|split; [exact Ha'|split; [reflexivity|exact Hle]]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "full_ssa_cc_trans_pre_alloc_conventions" *)
Theorem full_ssa_cc_trans_pre_alloc_conventions : forall n (prog : prog a),
  pre_alloc_conventions (full_ssa_cc_trans n prog).
Proof.
  intros n prog. unfold full_ssa_cc_trans. cbv zeta.
  destruct (limit_var_props prog (limit_var prog) eq_refl) as [Ha _].
  pose proof (setup_ssa_props_2 (limit_var prog) n prog Ha) as S.
  destruct (setup_ssa n (limit_var prog) prog) as [mov [ssa na]].
  destruct S as (Hok & Ha' & Hp & _).
  pose proof (ssa_cc_trans_pre_alloc_conventions prog ssa na [] (conj Ha' Hok)) as H.
  destruct (ssa_cc_trans prog ssa na []) as [p' [s' n']].
  rewrite pac_seq. unfold is_true in *. rewrite Hp, H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_distinct_tar_reg" *)
Theorem fake_moves_distinct_tar_reg : forall prio ls ssal ssar na (l r : prog a) a0 b c0,
  fake_moves prio ls ssal ssar na = (l, (r, (a0, (b, c0)))) ->
  every_inst distinct_tar_reg l /\ every_inst distinct_tar_reg r.
Proof.
  intros prio; induction ls as [|h ls IH]; intros ssal ssar na l r a0 b c0 E; cbn [fake_moves] in E.
  - injection E as <- <- _ _ _. split; reflexivity.
  - destruct (fake_moves prio ls ssal ssar na) as [mL [mR [n' [sL sR]]]] eqn:E1.
    destruct (IH _ _ _ _ _ _ _ _ E1) as [H1 H2].
    destruct (lookup h sL), (lookup h sR); injection E as <- <- _ _ _;
      cbn [every_inst fake_move distinct_tar_reg]; unfold is_true in *; rewrite ?H1, ?H2; split; reflexivity.
Qed.

Lemma ol_ne_na ssa na x : ssa_map_ok na ssa -> is_alloc_var na -> option_lookup ssa x <> na.
Proof.
  intros Hok Ha E. unfold option_lookup in E. destruct (lookup x ssa) as [y|] eqn:Ey.
  - destruct (Hok _ _ Ey). lia.
  - subst na. discriminate Ha.
Qed.

Lemma alloc_ne_phy na p : is_alloc_var na -> is_phy_var p = true -> na <> p.
Proof. intros Ha Hp ->. rewrite is_alloc_var_not_phy in Hp by exact Ha. discriminate. Qed.

Lemma inst_dtr (i : asm.inst a) ssa na (p : prog a) s n :
  ssa_map_ok na ssa -> is_alloc_var na ->
  ssa_cc_trans_inst i ssa na = (p, (s, n)) -> every_inst distinct_tar_reg p.
Proof.
  intros Hok Ha E. destruct_inst i; cbn [ssa_cc_trans_inst next_var_rename] in E;
    repeat match type of E with
           | context [if ?b then _ else _] => destruct b
           | context [match ?r with Reg _ => _ | Imm _ => _ end] => destruct r
           end;
    injection E as <- _ _; cbn [every_inst distinct_tar_reg]; try reflexivity;
    unfold is_true; rewrite ?Bool.andb_true_iff, ?Bool.negb_true_iff, ?N.eqb_neq;
    repeat split; try reflexivity;
    try (apply bd_false'; intros E; injection E as E; first [exact (ol_ne_na ssa na _ Hok Ha E)
                                                            | exact (ol_ne_na ssa na _ Hok Ha (eq_sym E))
                                                            | exact (alloc_ne_phy na 8 Ha eq_refl (eq_sym E))]; fail);
    try (intros E; first [exact (ol_ne_na ssa na _ Hok Ha E) | exact (ol_ne_na ssa na _ Hok Ha (eq_sym E))
                         | exact (alloc_ne_phy na 0 Ha eq_refl E)]; fail).
Qed.

Lemma fix_inconsistencies_dtr prio ssaL ssaR na (cL cR : prog a) n s :
  fix_inconsistencies prio ssaL ssaR na = (cL, (cR, (n, s))) ->
  every_inst distinct_tar_reg cL /\ every_inst distinct_tar_reg cR.
Proof.
  unfold fix_inconsistencies. destruct (merge_moves _ ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  destruct (fake_moves prio _ sL sR n') as [fL [fR [n'' [sL' sR']]]] eqn:Ef.
  intros E; injection E as <- <- _ _. destruct (fake_moves_distinct_tar_reg _ _ _ _ _ _ _ _ _ _ Ef) as [H1 H2].
  cbn [every_inst]. split; assumption.
Qed.

Lemma reconcile_dtr ssa' ssa_r (names : num_set) : every_inst distinct_tar_reg (@ssa_reconcile a ssa' ssa_r names).
Proof. unfold ssa_reconcile. destruct (FILTER _ _); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_distinct_tar_reg" *)
Theorem ssa_cc_trans_distinct_tar_reg : forall (prog : prog a) ssa na lt,
  is_alloc_var na /\ every_var (fun x => x <? na) prog /\ ssa_map_ok na ssa ->
  every_inst distinct_tar_reg (FST (ssa_cc_trans prog ssa na lt)).
Proof.
  intros prog. cut (forall ssa na lt, Inv na ssa -> every_inst distinct_tar_reg (FST (ssa_cc_trans prog ssa na lt))).
  { intros H ssa na lt (Ha & _ & Hok). apply H. split; assumption. }
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros ssa na lt HI; cbn [ssa_cc_trans next_var_rename]; destr_lets_goal; moves_shape; cbn [FST fst];
    cbn [every_inst]; try reflexivity; unfold is_true; rewrite ?Bool.andb_true_iff.
  (* Inst *)
  - exact (inst_dtr _ _ _ _ _ _ (proj1 HI) (proj2 HI) Ex).
  (* MustTerminate *)
  - pose proof (IH ssa na lt HI) as H. rewrite Ex in H. exact H.
  (* Call *)
  - destruct ret as [[rv [[c1 c2] [rh [l1 l2]]]]|]; cbn beta iota zeta; destr_lets_goal; moves_shape;
      cbn [FST fst every_inst]; [|reflexivity].
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    destruct (lnvrm_stack_Inv _ _ _ _ _ _ Ex0 H3 (ssa_map_ok_inter _ _ _ H2)) as (H4 & HI4).
    destruct (lnvr_Inv _ _ _ _ _ _ Ex1 HI4) as (H5 & HI5).
    pose proof (IHr _ _ lt HI5) as Hr. rewrite Ex2 in Hr. cbn [FST fst] in Hr.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex2 HI5) as (H6 & H6a & H6o).
    destruct h as [[hn [hp [l1' l2']]]|]; cbn beta iota zeta; destr_lets_goal; moves_shape;
      cbn [FST fst every_inst]; unfold is_true; rewrite ?Bool.andb_true_iff.
    + assert (HI7 : Inv (n2 + 4) (insert hn n2 s0)).
      { apply Inv_step. split; [apply (Inv_more _ _ _ HI4); lia|exact H6a]. }
      pose proof (IHh _ _ lt HI7) as Hh. rewrite Ex3 in Hh. cbn [FST fst] in Hh.
      match goal with E : fix_inconsistencies _ _ _ _ = _ |- _ => destruct (fix_inconsistencies_dtr _ _ _ _ _ _ _ _ E) as [F1 F2] end.
      repeat split; try reflexivity; assumption.
    + repeat split; try reflexivity; exact Hr.
  (* Seq *)
  - pose proof (IH1 ssa na lt HI) as H1. rewrite Ex in H1. cbn [FST fst] in H1.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex HI) as (Hle & Ha1 & Hok1).
    pose proof (IH2 s n lt (conj Hok1 Ha1)) as H2. rewrite Ex0 in H2. cbn [FST fst] in H2. auto.
  (* If *)
  - pose proof (IH1 ssa na lt HI) as H1. rewrite Ex in H1. cbn [FST fst] in H1.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex HI) as (Hle & Ha1 & Hok1).
    pose proof (IH2 ssa n lt (conj (Inv_more _ _ _ HI Hle) Ha1)) as H2. rewrite Ex0 in H2. cbn [FST fst] in H2.
    destruct (fix_inconsistencies_dtr _ _ _ _ _ _ _ _ Ex1) as [F1 F2]. auto.
  (* Loop *)
  - pose proof (loop_setup_every_inst_distinct_tar_reg _ _ _ _ _ _ _ Ex) as Hs.
    destruct (loop_setup_Inv _ _ _ _ _ _ _ Ex HI) as [Hle HI1].
    pose proof (IH (inter s n1) n ((s, (n1, n2)) :: lt) (conj (ssa_map_ok_inter _ _ _ (proj1 HI1)) (proj2 HI1))) as Hb.
    rewrite Ex0 in Hb. cbn [FST fst] in Hb. split; [exact Hs|].
    destruct (is_Skip _); [exact Hb|]. cbn [every_inst]. rewrite Hb, reconcile_dtr. reflexivity.
  (* Break *)
  - destruct (oEL n lt) as [[tgt [nm ex]]|]; cbn beta iota zeta; [|reflexivity].
    destruct (is_Skip _); cbn [FST fst every_inst]; [reflexivity|]. rewrite reconcile_dtr. reflexivity.
  (* Continue *)
  - destruct (oEL n lt) as [[tgt [nm ex]]|]; cbn beta iota zeta; [|reflexivity].
    destruct (is_Skip _); cbn [FST fst every_inst]; [reflexivity|]. rewrite reconcile_dtr. reflexivity.
  (* OpCurrHeap *)
  - cbn [distinct_tar_reg]. apply Bool.negb_true_iff, bd_false'. intros E; injection E as E.
    exact (ol_ne_na ssa na _ (proj1 HI) (proj2 HI) E).
  (* ShareInst *)
  - destruct (bool_decide _); destr_lets_goal; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "full_ssa_cc_trans_distinct_tar_reg" *)
Theorem full_ssa_cc_trans_distinct_tar_reg : forall n (prog : prog a),
  every_inst distinct_tar_reg (full_ssa_cc_trans n prog).
Proof.
  intros n prog. unfold full_ssa_cc_trans. cbv zeta.
  destruct (limit_var_props prog (limit_var prog) eq_refl) as [Ha Hev].
  pose proof (setup_ssa_props_2 (limit_var prog) n prog Ha) as S.
  pose proof (ssa_cc_trans_distinct_tar_reg prog) as T.
  destruct (setup_ssa n (limit_var prog) prog) as [mov [ssa na]] eqn:Es.
  destruct S as (Hok & Ha' & _ & Hle).
  specialize (T ssa na []). destruct (ssa_cc_trans prog ssa na []) as [p' [s' n']].
  cbn [FST fst] in T. cbn [every_inst]. unfold setup_ssa in Es.
  destruct (list_next_var_rename _ LN _) as [? [? ?]]. injection Es as <- _ _. cbn [every_inst andb].
  apply T. split; [exact Ha'|split; [|exact Hok]].
  apply (every_var_mono (fun x => x <? limit_var prog)). split; [|exact Hev].
  intros x Hx. unfold is_true in *. apply N.ltb_lt in Hx. apply N.ltb_lt. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "exp_to_addr_ShareInst" *)
Theorem exp_to_addr_ShareInst : forall (exp : exp a) n c0,
  exp_to_addr exp = SOME (Addr n c0) <->
  ((exp = Var n /\ c0 = n2w 0) \/ (exp = Op asm.Add [Var n; Const c0])).
Proof.
  intros exp n c0. split.
  - destruct exp as [w|v|v|e|op es|sh e1 e2]; unfold exp_to_addr; try discriminate.
    + intros E; injection E as -> ->. left; auto.
    + destruct op; destruct es as [|e1 [|e2 [|e3 es]]]; try destruct e1; try destruct e2;
        intros E; try discriminate E; injection E as -> ->; right; reflexivity.
  - intros [[-> ->] | ->]; reflexivity.
Qed.

Lemma exp_to_addr_ssa ssa (e : exp a) :
  exp_to_addr (ssa_cc_trans_exp ssa e) =
  match exp_to_addr e with Some (Addr n w) => Some (Addr (option_lookup ssa n) w) | None => None end.
Proof.
  destruct e as [w|v|v|e|op es|sh e1 e2]; cbn [ssa_cc_trans_exp]; unfold exp_to_addr; try reflexivity.
  destruct op; try reflexivity. destruct es as [|e1 [|e2 [|e3 es]]]; try reflexivity;
    destruct e1; try reflexivity; destruct e2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_conventions2" *)
Theorem fake_moves_conventions2 : forall prio ls ssal ssar na (l r : prog a) a0 b c0 conf,
  fake_moves prio ls ssal ssar na = (l, (r, (a0, (b, c0)))) ->
  full_inst_ok_less conf l /\ full_inst_ok_less conf r /\
  every_inst distinct_tar_reg l /\ every_inst distinct_tar_reg r.
Proof.
  intros prio; induction ls as [|h ls IH]; intros ssal ssar na l r a0 b c0 conf E; cbn [fake_moves] in E.
  - injection E as <- <- _ _ _. repeat split.
  - destruct (fake_moves prio ls ssal ssar na) as [mL [mR [n' [sL sR]]]] eqn:E1.
    destruct (IH _ _ _ _ _ _ _ _ conf E1) as (H1 & H2 & H3 & H4).
    destruct (lookup h sL), (lookup h sR); injection E as <- <- _ _ _;
      cbn [every_inst full_inst_ok_less fake_move distinct_tar_reg inst_ok_less]; unfold is_true in *;
      rewrite ?H1, ?H2, ?H3, ?H4; repeat split.
Qed.

Lemma fix_inconsistencies_fiol prio ssaL ssaR na (cL cR : prog a) n s conf :
  fix_inconsistencies prio ssaL ssaR na = (cL, (cR, (n, s))) ->
  full_inst_ok_less conf cL /\ full_inst_ok_less conf cR.
Proof.
  unfold fix_inconsistencies. destruct (merge_moves _ ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  destruct (fake_moves prio _ sL sR n') as [fL [fR [n'' [sL' sR']]]] eqn:Ef.
  intros E; injection E as <- <- _ _. destruct (fake_moves_conventions2 _ _ _ _ _ _ _ _ _ _ conf Ef) as (H1 & H2 & _).
  cbn [full_inst_ok_less]. split; assumption.
Qed.

Lemma reconcile_fiol ssa' ssa_r (names : num_set) conf : full_inst_ok_less conf (@ssa_reconcile a ssa' ssa_r names).
Proof. unfold ssa_reconcile. destruct (FILTER _ _); reflexivity. Qed.

Lemma implb_r x y : y = true -> implb x y = true.
Proof. intros ->. destruct x; reflexivity. Qed.

Lemma implb_l x y : x = false -> implb x y = true.
Proof. intros ->. reflexivity. Qed.

Lemma negb_eqb_ne x y : x <> y -> negb (x =? y) = true.
Proof. intros H. apply Bool.negb_true_iff, N.eqb_neq, H. Qed.

Lemma dim64_not32 : (dimindex a =? 64) = true -> (dimindex a =? 32) = false.
Proof. intros H. apply N.eqb_eq in H. rewrite H. reflexivity. Qed.

Lemma inst_fiol (i : asm.inst a) ssa na (p : prog a) s n conf :
  ssa_map_ok na ssa -> is_alloc_var na -> inst_ok_less conf i ->
  ssa_cc_trans_inst i ssa na = (p, (s, n)) -> full_inst_ok_less conf p.
Proof.
  intros Hok Ha H E. destruct_inst i; cbn [ssa_cc_trans_inst next_var_rename] in E;
    repeat match type of E with
           | context [if ?b then _ else _] => let Eb := fresh "Eb" in destruct b eqn:Eb
           | context [match ?r with Reg _ => _ | Imm _ => _ end] => destruct r
           end;
    injection E as <- _ _; cbn [full_inst_ok_less inst_ok_less] in *; try exact H; try reflexivity;
    unfold is_true in *; rewrite ?Bool.andb_true_iff in *; try tauto.
  all: repeat split; try reflexivity; try (apply implb_r; reflexivity).
  - apply implb_r. rewrite !negb_eqb_ne; [reflexivity| |].
    + apply (alloc_ne_phy na 0 Ha); reflexivity.
    + intros E; exact (ol_ne_na ssa na _ Hok Ha (eq_sym E)).
  - apply implb_r, negb_eqb_ne. intros E; exact (ol_ne_na ssa na _ Hok Ha (eq_sym E)).
  - apply implb_r, negb_eqb_ne. intros E; exact (ol_ne_na ssa na _ Hok Ha (eq_sym E)).
  - apply implb_l, dim64_not32, Eb.
  - tauto.
  - apply implb_r, negb_eqb_ne. lia.
  - tauto.
  - apply implb_l, dim64_not32, Eb.
  - tauto.
  - apply implb_r, negb_eqb_ne. exact (ol_ne_na ssa na _ Hok Ha).
  - tauto.
  - apply implb_r. rewrite Eb0. reflexivity.
  - tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_full_inst_ok_less" *)
Theorem ssa_cc_trans_full_inst_ok_less : forall (prog : prog a) ssa na lt c,
  every_var (fun x => x <? na) prog /\ is_alloc_var na /\ ssa_map_ok na ssa /\ full_inst_ok_less c prog ->
  full_inst_ok_less c (FST (ssa_cc_trans prog ssa na lt)).
Proof.
  intros prog. cut (forall ssa na lt conf, Inv na ssa -> full_inst_ok_less conf prog ->
    full_inst_ok_less conf (FST (ssa_cc_trans prog ssa na lt))).
  { intros H ssa na lt conf (_ & Ha & Hok & Hf). apply H; [split; assumption|exact Hf]. }
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros ssa na lt conf HI Hf; cbn [full_inst_ok_less] in Hf; cbn [ssa_cc_trans next_var_rename]; destr_lets_goal; moves_shape;
    cbn [FST fst]; cbn [full_inst_ok_less]; try reflexivity; unfold is_true in *; rewrite ?Bool.andb_true_iff in *.
  (* Inst *)
  - exact (inst_fiol _ _ _ _ _ _ conf (proj1 HI) (proj2 HI) Hf Ex).
  (* MustTerminate *)
  - pose proof (IH ssa na lt conf HI Hf) as H. rewrite Ex in H. exact H.
  (* Call *)
  - destruct ret as [[rv [[c1 c2] [rh [l1 l2]]]]|]; cbn beta iota zeta; destr_lets_goal; moves_shape;
      cbn [FST fst full_inst_ok_less]; [|reflexivity].
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    destruct (lnvrm_stack_Inv _ _ _ _ _ _ Ex0 H3 (ssa_map_ok_inter _ _ _ H2)) as (H4 & HI4).
    destruct (lnvr_Inv _ _ _ _ _ _ Ex1 HI4) as (H5 & HI5).
    destruct h as [[hn [hp [l1' l2']]]|]; cbn beta iota zeta in Hf |- *; rewrite ?Bool.andb_true_iff in Hf.
    + destruct Hf as [Hfr Hfh].
      pose proof (IHr _ _ lt conf HI5 Hfr) as Hr. rewrite Ex2 in Hr. cbn [FST fst] in Hr.
      destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex2 HI5) as (H6 & H6a & H6o).
      destr_lets_goal; moves_shape; cbn [FST fst full_inst_ok_less]; unfold is_true; rewrite ?Bool.andb_true_iff.
      assert (HI7 : Inv (n2 + 4) (insert hn n2 s0)).
      { apply Inv_step. split; [apply (Inv_more _ _ _ HI4); lia|exact H6a]. }
      pose proof (IHh _ _ lt conf HI7 Hfh) as Hh. rewrite Ex3 in Hh. cbn [FST fst] in Hh.
      match goal with E : fix_inconsistencies _ _ _ _ = _ |- _ => destruct (fix_inconsistencies_fiol _ _ _ _ _ _ _ _ conf E) as [F1 F2] end.
      repeat split; try reflexivity; assumption.
    + pose proof (IHr _ _ lt conf HI5 (proj1 Hf)) as Hr. rewrite Ex2 in Hr. cbn [FST fst] in Hr.
      destr_lets_goal; moves_shape; cbn [FST fst full_inst_ok_less]; unfold is_true; rewrite ?Bool.andb_true_iff.
      repeat split; try reflexivity; exact Hr.
  (* Seq *)
  - destruct Hf as [Hf1 Hf2].
    pose proof (IH1 ssa na lt conf HI Hf1) as H1. rewrite Ex in H1. cbn [FST fst] in H1.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex HI) as (Hle & Ha1 & Hok1).
    pose proof (IH2 s n lt conf (conj Hok1 Ha1) Hf2) as H2. rewrite Ex0 in H2. cbn [FST fst] in H2. auto.
  (* If *)
  - destruct Hf as [Hf1 Hf2].
    pose proof (IH1 ssa na lt conf HI Hf1) as H1. rewrite Ex in H1. cbn [FST fst] in H1.
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ex HI) as (Hle & Ha1 & Hok1).
    pose proof (IH2 ssa n lt conf (conj (Inv_more _ _ _ HI Hle) Ha1) Hf2) as H2. rewrite Ex0 in H2. cbn [FST fst] in H2.
    destruct (fix_inconsistencies_fiol _ _ _ _ _ _ _ _ conf Ex1) as [F1 F2]. auto.
  (* Loop *)
  - pose proof (loop_setup_full_inst_ok_less _ _ _ _ _ _ _ conf Ex) as Hs.
    destruct (loop_setup_Inv _ _ _ _ _ _ _ Ex HI) as [Hle HI1].
    pose proof (IH (inter s n1) n ((s, (n1, n2)) :: lt) conf (conj (ssa_map_ok_inter _ _ _ (proj1 HI1)) (proj2 HI1)) Hf) as Hb.
    rewrite Ex0 in Hb. cbn [FST fst] in Hb. split; [exact Hs|].
    destruct (is_Skip _); [exact Hb|]. cbn [full_inst_ok_less]. rewrite Hb, reconcile_fiol. reflexivity.
  (* Break *)
  - destruct (oEL n lt) as [[tgt [nm ex]]|]; cbn beta iota zeta; [|reflexivity].
    destruct (is_Skip _); cbn [FST fst full_inst_ok_less]; [reflexivity|]. rewrite reconcile_fiol. reflexivity.
  (* Continue *)
  - destruct (oEL n lt) as [[tgt [nm ex]]|]; cbn beta iota zeta; [|reflexivity].
    destruct (is_Skip _); cbn [FST fst full_inst_ok_less]; [reflexivity|]. rewrite reconcile_fiol. reflexivity.
  (* ShareInst *)
  - destruct (bool_decide _); destr_lets_goal; cbn [FST fst full_inst_ok_less]; rewrite exp_to_addr_ssa;
      destruct (exp_to_addr e) as [[n0 w]|]; exact Hf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "full_ssa_cc_trans_full_inst_ok_less" *)
Theorem full_ssa_cc_trans_full_inst_ok_less : forall (prog : prog a) n c,
  full_inst_ok_less c prog -> full_inst_ok_less c (full_ssa_cc_trans n prog).
Proof.
  intros prog n c Hf. unfold full_ssa_cc_trans. cbv zeta.
  destruct (limit_var_props prog (limit_var prog) eq_refl) as [Ha Hev].
  pose proof (setup_ssa_props_2 (limit_var prog) n prog Ha) as S.
  pose proof (ssa_cc_trans_full_inst_ok_less prog) as T.
  destruct (setup_ssa n (limit_var prog) prog) as [mov [ssa na]] eqn:Es.
  destruct S as (Hok & Ha' & _ & Hle).
  specialize (T ssa na [] c). destruct (ssa_cc_trans prog ssa na []) as [p' [s' n']].
  cbn [FST fst] in T. cbn [full_inst_ok_less]. unfold setup_ssa in Es.
  destruct (list_next_var_rename _ LN _) as [? [? ?]]. injection Es as <- _ _. cbn [full_inst_ok_less andb].
  apply T. split; [|split; [exact Ha'|split; [exact Hok|exact Hf]]].
  apply (every_var_mono (fun x => x <? limit_var prog)). split; [|exact Hev].
  intros x Hx. unfold is_true in *. apply N.ltb_lt in Hx. apply N.ltb_lt. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_inst_apply_colour_inst" *)
Theorem every_var_inst_apply_colour_inst : forall (P : N -> bool) (inst : asm.inst a) (Q : N -> bool) f,
  every_var_inst P inst /\ (forall x, P x -> Q (f x)) ->
  every_var_inst Q (apply_colour_inst f inst).
Proof.
  intros P i Q f [H HPQ]. destruct_inst i; cbn [apply_colour_inst every_var_inst every_var_imm apply_colour_imm] in *;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try reflexivity; unfold is_true in *; rewrite ?Bool.andb_true_iff in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_exp_apply_colour_exp" *)
Theorem every_var_exp_apply_colour_exp : forall (P : N -> bool) (exp : exp a) (Q : N -> bool) f,
  every_var_exp P exp /\ (forall x, P x -> Q (f x)) ->
  every_var_exp Q (apply_colour_exp f exp).
Proof.
  intros P exp Q f [H HPQ]. induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [apply_colour_exp every_var_exp] in *; try reflexivity; auto.
  - unfold is_true in *. rewrite EVERY_Forall, Forall_forall in *. rewrite ?Forall_forall in IH.
    intros e' He'. apply in_map_iff in He' as [e [<- He]]. apply IH; auto.
  - unfold is_true in *. rewrite Bool.andb_true_iff in *. destruct H; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_apply_nummap_key_helper" *)
Theorem every_apply_nummap_key_helper : forall (f : N -> N) (names : num_set) (P Q : N -> bool),
  EVERY P (MAP FST (toAList names)) /\ (forall x, P x -> Q (f x)) ->
  EVERY Q (MAP FST (toAList (fromAList (MAP (fun '(x, y) => (f x, y)) (toAList names))))).
Proof.
  intros f names P Q [H HPQ]. unfold is_true in *. rewrite EVERY_Forall, Forall_forall in *.
  intros k Hk. apply In_toAList_keys in Hk. rewrite domain_fromAList in Hk. cbv beta in Hk.
  apply MEM_iff' in Hk. apply in_map_iff in Hk as [[k' u] [Ek Hk]]. cbn [fst] in Ek.
  apply in_map_iff in Hk as [[x y] [Exy Hx]]. injection Exy as <- <-. subst k.
  apply HPQ, H. apply (in_map fst) in Hx. exact Hx.
Qed.

Lemma every_name_apply (P Q : N -> bool) f (names : cutsets) :
  every_name P names -> (forall x, P x -> Q (f x)) -> every_name Q (apply_nummaps_key f names).
Proof.
  destruct names as [n1 n2]. unfold every_name. cbn [apply_nummaps_key FST SND fst snd].
  unfold is_true. rewrite !Bool.andb_true_iff. intros [H1 H2] HPQ.
  split; eapply every_apply_nummap_key_helper; split; eassumption.
Qed.

Lemma combine_map2 {A B C} (g : A -> B) (h : A -> C) l :
  combine (List.map g l) (List.map h l) = List.map (fun m => (g m, h m)) l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_apply_colour" *)
Theorem every_var_apply_colour : forall (P : N -> bool) (prog : prog a) (Q : N -> bool) f,
  every_var P prog /\ (forall x, P x -> Q (f x)) ->
  every_var Q (apply_colour f prog).
Proof.
  intros P prog Q f [H HPQ].
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [apply_colour every_var] in *; try reflexivity; unfold is_true in *;
    rewrite ?Bool.andb_true_iff in *; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; auto.
  all: try (eapply every_var_inst_apply_colour_inst; split; eassumption).
  all: try (eapply every_var_exp_apply_colour_exp; split; eassumption).
  all: try (eapply every_name_apply; eassumption).
  all: try (eapply every_apply_nummap_key_helper; split; eassumption).
  all: try (rewrite EVERY_Forall, Forall_forall in *; intros y Hy; apply in_map_iff in Hy as [x [<- Hx]]; auto; fail).
  - rewrite MAP_FST_ZIP' by (rewrite !LENGTH_MAP'; reflexivity). rewrite EVERY_Forall, Forall_forall in *.
    intros y Hy. apply in_map_iff in Hy as [m [<- Hm]]. apply HPQ, H, (in_map FST), Hm.
  - rewrite MAP_SND_ZIP' by (rewrite !LENGTH_MAP'; reflexivity). rewrite EVERY_Forall, Forall_forall in *.
    intros y Hy. apply in_map_iff in Hy as [m [<- Hm]]. apply HPQ, H0, (in_map SND), Hm.
  - destruct ret as [[vs [cs [rh [l1 l2]]]]|]; [|reflexivity]. cbn beta iota in *.
    rewrite ?Bool.andb_true_iff in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split.
    + rewrite EVERY_Forall, Forall_forall in *. intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. auto.
    + eapply every_name_apply; eassumption.
    + apply IHr; assumption.
    + destruct h as [[hv [hp [l1' l2']]]|]; [|reflexivity]. cbn beta iota in *.
      apply andb_prop in H1 as [Hh1 Hh2]. apply andb_true_intro. split; [apply HPQ, Hh1|apply IHh, Hh2].
  - destruct ri; cbn [apply_colour_imm every_var_imm] in *; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_stack_var_apply_colour" *)
Theorem every_stack_var_apply_colour : forall (P : N -> bool) (prog : prog a) (Q : N -> bool) f,
  every_stack_var P prog /\ (forall x, P x -> Q (f x)) ->
  every_stack_var Q (apply_colour f prog).
Proof.
  intros P prog Q f [H HPQ].
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [apply_colour every_stack_var] in *; try reflexivity; unfold is_true in *;
    rewrite ?Bool.andb_true_iff in *; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; auto.
  all: try (eapply every_name_apply; eassumption).
  destruct ret as [[vs [cs [rh [l1 l2]]]]|]; [|reflexivity]. cbn beta iota in *.
  rewrite ?Bool.andb_true_iff in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split.
  - eapply every_name_apply; eassumption.
  - apply IHr; assumption.
  - destruct h as [[hv [hp [l1' l2']]]|]; [|reflexivity]. cbn beta iota in *. apply IHh; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_exp_get_reads_exp" *)
Theorem every_var_exp_get_reads_exp : forall (exp : exp a),
  every_var_exp (fun x => MEM x (get_reads_exp exp)) exp.
Proof.
  intros exp. apply (every_var_exp_mono (fun x => ⌜x IN domain (get_live_exp exp)⌝)).
  split; [|apply every_var_exp_get_live_exp]. intros x Hx. apply bool_decide_spec in Hx.
  unfold is_true. apply MEM_iff'. rewrite <- get_reads_exp_get_live_exp in Hx. apply IN_set, Hx.
Qed.

Lemma ict_mono (P : N -> bool) (p : prog a) (Q : N -> Prop) :
  every_var P p -> (forall x, P x -> Q x) -> every_var (fun x => ⌜Q x⌝) p.
Proof. intros H HPQ. apply (every_var_mono P). split; [|exact H]. intros x Hx. apply bool_decide_spec, HPQ, Hx. Qed.

Lemma ict_exp_mono (e : exp a) (Q : N -> Prop) :
  (forall x, is_true (MEM x (get_reads_exp e)) -> Q x) -> every_var_exp (fun x => ⌜Q x⌝) e.
Proof.
  intros HPQ. apply (every_var_exp_mono (fun x => MEM x (get_reads_exp e))). split; [|apply every_var_exp_get_reads_exp].
  intros x Hx. apply bool_decide_spec, HPQ, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_in_get_clash_tree" *)
Theorem every_var_in_get_clash_tree : forall (prog : prog a) lt,
  every_var (fun x => ⌜in_clash_tree (get_clash_tree prog lt) x⌝) prog.
Proof.
  intros prog. induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros lt; cbn [every_var get_clash_tree in_clash_tree] in *; try reflexivity; unfold is_true;
    rewrite ?Bool.andb_true_iff; repeat match goal with |- _ /\ _ => split end.
  all: try (apply bool_decide_spec; rewrite ?MEM_In, ?MEM_iff'; cbn [In]; tauto).
  all: try (apply ict_exp_mono; intros y Hy; unfold is_true in *; rewrite ?MEM_In in *; cbn [In] in *; tauto).
  all: try (rewrite EVERY_Forall, Forall_forall; intros y Hy; apply bool_decide_spec; rewrite ?MEM_In;
            cbn [In]; first [tauto | (rewrite in_app_iff; tauto) | (apply In_toAList_keys in Hy; tauto)]).
  (* Inst *)
  - destruct_inst i; cbn [every_var_inst get_delta_inst every_var_imm];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      unfold is_true; rewrite ?Bool.andb_true_iff; repeat split; try reflexivity;
      apply bool_decide_spec; cbn [in_clash_tree]; rewrite ?MEM_In, ?MEM_iff'; cbn [In]; tauto.
  (* MustTerminate *)
  - exact (IH lt).
  (* Call *)
  - destruct ret as [[vs [[c1 c2] [rh [l1 l2]]]]|]; [destruct h as [[hv [hp [l1' l2']]]|]|];
      cbn [FST SND fst snd in_clash_tree]; rewrite EVERY_Forall, Forall_forall; intros y Hy;
      apply bool_decide_spec; cbn [in_clash_tree];
      rewrite ?domain_union, ?domain_numset_list_insert; unfold pred_set.UNION, pred_set.IN; cbn beta;
      change (LIST_TO_SET args y) with (y IN set args); rewrite IN_set; cbn [domain]; tauto.
  - destruct ret as [[vs [[c1 c2] [rh [l1 l2]]]]|]; [|reflexivity]. cbn beta iota.
    destruct h as [[hv [hp [l1' l2']]]|]; cbn [FST SND fst snd in_clash_tree]; unfold is_true;
      rewrite ?Bool.andb_true_iff; repeat split.
    + rewrite EVERY_Forall, Forall_forall; intros y Hy. apply bool_decide_spec. cbn [in_clash_tree].
      rewrite ?domain_numset_list_insert. unfold pred_set.UNION, pred_set.IN. cbn beta.
      change (LIST_TO_SET vs y) with (y IN set vs). rewrite IN_set. tauto.
    + unfold every_name. cbn [FST SND fst snd]. unfold is_true; rewrite Bool.andb_true_iff.
      split; rewrite EVERY_Forall, Forall_forall; intros y Hy; apply In_toAList_keys in Hy; apply bool_decide_spec;
        cbn [in_clash_tree]; rewrite ?domain_union, ?domain_numset_list_insert, ?domain_insert;
        unfold pred_set.UNION, pred_set.IN; cbn beta; tauto.
    + apply (ict_mono _ _ _ (IHr lt)). intros y Hy. apply bool_decide_spec in Hy. cbn [in_clash_tree]. tauto.
    + apply bool_decide_spec. cbn [in_clash_tree]. rewrite domain_insert. unfold pred_set.IN. tauto.
    + apply (ict_mono _ _ _ (IHh lt)). intros y Hy. apply bool_decide_spec in Hy. cbn [in_clash_tree]. tauto.
    + rewrite EVERY_Forall, Forall_forall; intros y Hy. apply bool_decide_spec. cbn [in_clash_tree].
      rewrite ?domain_numset_list_insert. unfold pred_set.UNION, pred_set.IN. cbn beta.
      change (LIST_TO_SET vs y) with (y IN set vs). rewrite IN_set. tauto.
    + unfold every_name. cbn [FST SND fst snd]. unfold is_true; rewrite Bool.andb_true_iff.
      split; rewrite EVERY_Forall, Forall_forall; intros y Hy; apply In_toAList_keys in Hy; apply bool_decide_spec;
        cbn [in_clash_tree]; rewrite ?domain_union, ?domain_numset_list_insert, ?domain_insert;
        unfold pred_set.UNION, pred_set.IN; cbn beta; tauto.
    + apply (ict_mono _ _ _ (IHr lt)). intros y Hy. apply bool_decide_spec in Hy. cbn [in_clash_tree]. tauto.
  (* Seq *)
  - apply (ict_mono _ _ _ (IH1 lt)). intros y Hy. apply bool_decide_spec in Hy. tauto.
  - apply (ict_mono _ _ _ (IH2 lt)). intros y Hy. apply bool_decide_spec in Hy. tauto.
  (* If *)
  - destruct ri; apply bool_decide_spec; cbn [in_clash_tree]; rewrite ?MEM_In, ?MEM_iff'; cbn [In]; tauto.
  - destruct ri; cbn [every_var_imm]; [|reflexivity]. apply bool_decide_spec; cbn [in_clash_tree]; rewrite ?MEM_In, ?MEM_iff'; cbn [In]; tauto.
  - apply (ict_mono _ _ _ (IH1 lt)). intros y Hy. apply bool_decide_spec in Hy. destruct ri; cbn [in_clash_tree]; tauto.
  - apply (ict_mono _ _ _ (IH2 lt)). intros y Hy. apply bool_decide_spec in Hy. destruct ri; cbn [in_clash_tree]; tauto.
  (* Loop *)
  - apply (ict_mono _ _ _ (IH ((n1, n2) :: lt))). intros y Hy. apply bool_decide_spec in Hy. tauto.
  (* Alloc, Install, FFI *)
  - destruct names as [c1 c2]. unfold every_name. cbn [FST SND fst snd]. unfold is_true; rewrite Bool.andb_true_iff.
    split; rewrite EVERY_Forall, Forall_forall; intros y Hy; apply In_toAList_keys in Hy; apply bool_decide_spec;
      rewrite domain_union; unfold pred_set.UNION, pred_set.IN; cbn beta; tauto.
  - destruct names as [c1 c2]. unfold every_name. cbn [FST SND fst snd]. unfold is_true; rewrite Bool.andb_true_iff.
    split; rewrite EVERY_Forall, Forall_forall; intros y Hy; apply In_toAList_keys in Hy; apply bool_decide_spec;
      rewrite domain_union; unfold pred_set.UNION, pred_set.IN; cbn beta; tauto.
  - destruct names as [c1 c2]. unfold every_name. cbn [FST SND fst snd]. unfold is_true; rewrite Bool.andb_true_iff.
    split; rewrite EVERY_Forall, Forall_forall; intros y Hy; apply In_toAList_keys in Hy; apply bool_decide_spec;
      rewrite domain_union; unfold pred_set.UNION, pred_set.IN; cbn beta; tauto.
  (* ShareInst *)
  - destruct (is_store_op op); apply bool_decide_spec; cbn [in_clash_tree]; rewrite ?MEM_In, ?MEM_iff'; cbn [In]; tauto.
  - apply ict_exp_mono. intros y Hy. destruct (is_store_op op); cbn [in_clash_tree];
      unfold is_true in *; rewrite ?MEM_In, ?MEM_iff' in *; cbn [In]; tauto.
Qed.

Lemma MAP_id_phy (f : N -> N) (l : list N) :
  (forall x, In x l -> is_phy_var x = true -> f x = x) -> (forall x, In x l -> is_phy_var x = true) ->
  MAP f l = l.
Proof.
  induction l as [|x l IH]; intros H Hp; [reflexivity|]. cbn [MAP List.map].
  rewrite (H x (or_introl eq_refl) (Hp x (or_introl eq_refl))). f_equal. apply IH.
  - intros y Hy. apply H; right; exact Hy.
  - intros y Hy. apply Hp; right; exact Hy.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "call_arg_convention_preservation" *)
Theorem call_arg_convention_preservation : forall (prog : prog a) f,
  every_var (fun x => implb (is_phy_var x) (f x =? x)) prog /\ call_arg_convention prog ->
  call_arg_convention (apply_colour f prog).
Proof.
  intros prog f [H Hc].
  assert (Hf : forall x, is_true (implb (is_phy_var x) (f x =? x)) -> is_phy_var x = true -> f x = x).
  { intros x Hx Hp. unfold is_true in Hx. rewrite Hp in Hx. cbn in Hx. apply N.eqb_eq, Hx. }
  assert (Hev : forall l, is_true (EVERY (fun x => implb (is_phy_var x) (f x =? x)) l) ->
              forall x, In x l -> is_phy_var x = true -> f x = x).
  { intros l Hl x Hx. unfold is_true in Hl. rewrite EVERY_Forall, Forall_forall in Hl. apply Hf, Hl, Hx. }
  assert (Hgen : forall g l, (forall i, is_phy_var (g i) = true) ->
            is_true (EVERY (fun x => implb (is_phy_var x) (f x =? x)) l) ->
            is_true (bool_decide (l = GENLIST g (LENGTH l))) ->
            is_true (bool_decide (MAP f l = GENLIST g (LENGTH (MAP f l))))).
  { intros g l Hg Hl Heq. unfold is_true in Heq. apply bool_decide_spec in Heq.
    rewrite (MAP_id_phy f l (Hev l Hl)).
    - apply bool_decide_spec. exact Heq.
    - intros x Hx. rewrite Heq in Hx. apply In_GENLIST_iff in Hx as (i & _ & ->). apply Hg. }
  assert (Hg1 : forall i, is_phy_var (2 * (i + 1)) = true).
  { intros i. unfold is_phy_var. apply N.eqb_eq. replace (2 * (i + 1)) with (0 + (i + 1) * 2) by lia.
    rewrite N.Div0.mod_add. reflexivity. }
  assert (Hg0 : forall i, is_phy_var (2 * i) = true).
  { intros i. unfold is_phy_var. apply N.eqb_eq. replace (2 * i) with (0 + i * 2) by lia.
    rewrite N.Div0.mod_add. reflexivity. }
  assert (Hlit : forall k, is_true (implb (is_phy_var k) (f k =? k)) -> is_phy_var k = true -> f k = k)
    by exact Hf.
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [apply_colour call_arg_convention every_var] in *; try reflexivity; unfold is_true in *;
    rewrite ?Bool.andb_true_iff in *; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end; auto.
  all: try (match goal with Hk : (?x =? ?k) = true |- (?g ?x =? ?k) = true =>
              apply N.eqb_eq in Hk; subst x; rewrite (Hf k ltac:(assumption) eq_refl); apply N.eqb_refl end).
  - destruct_inst i; cbn [apply_colour_inst inst_arg_convention every_var_inst every_var_imm apply_colour_imm] in *;
      repeat match goal with H : context [if ?b then _ else _] |- _ => destruct b end;
      try reflexivity; unfold is_true in *; rewrite ?Bool.andb_true_iff in *;
      repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split;
      match goal with Hk : (?x =? ?k) = true |- (?g ?x =? ?k) = true =>
        apply N.eqb_eq in Hk; subst x; rewrite (Hf k ltac:(assumption) eq_refl); apply N.eqb_refl end.
  - destruct ret as [[vs [cs [rh [l1 l2]]]]|]; cbn beta iota in *.
    + destruct h as [[hv [hp [l1' l2']]]|]; cbn beta iota in *; rewrite ?Bool.andb_true_iff in *;
        repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; auto;
        try (apply Hgen; assumption);
        try (match goal with Hk : (?x =? ?k) = true |- (?g ?x =? ?k) = true =>
              apply N.eqb_eq in Hk; subst x; rewrite (Hf k ltac:(assumption) eq_refl); apply N.eqb_refl end).
    + apply Hgen; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_T" *)
Theorem every_var_T : forall (prog : prog a), every_var (fun x => true) prog.
Proof.
  intros prog. apply (every_var_mono (fun x => x <=? max_var prog)). split; [intros; reflexivity|].
  apply max_var_max.
Qed.

Lemma total_colour_phy col x : is_phy_var (total_colour col x) = true.
Proof.
  unfold total_colour. destruct (lookup x col) as [y|].
  - unfold is_phy_var. apply N.eqb_eq. replace (2 * y) with (0 + y * 2) by lia. rewrite N.Div0.mod_add. reflexivity.
  - destruct (is_phy_var x) eqn:E; [exact E|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_is_phy_var_total_colour" *)
Theorem every_var_is_phy_var_total_colour : forall col (prog : prog a),
  every_var is_phy_var (apply_colour (total_colour col) prog).
Proof.
  intros col prog. apply (every_var_apply_colour (fun x => true)). split; [apply every_var_T|].
  intros x _. apply total_colour_phy.
Qed.

Lemma total_colour_even col x :
  every_even_colour col -> is_phy_var x = true -> total_colour col x = x.
Proof.
  intros He Hp. unfold total_colour. destruct (lookup x col) as [y|] eqn:Ey; [|rewrite Hp; reflexivity].
  unfold every_even_colour, is_true in He. rewrite EVERY_Forall, Forall_forall in He.
  assert (Hin : In (x, y) (toAList col)) by (apply MEM_iff', MEM_toAList; exact Ey).
  specialize (He _ Hin). cbv beta iota in He. rewrite Hp in He. apply N.eqb_eq in He. subst y.
  unfold is_phy_var in Hp. apply N.eqb_eq in Hp. pose proof (N.div_mod x 2 ltac:(lia)). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "oracle_colour_ok_conventions" *)
Theorem oracle_colour_ok_conventions : forall k col_opt (prog : prog a) lt ls x,
  pre_alloc_conventions prog /\
  oracle_colour_ok k col_opt (get_clash_tree prog lt) prog ls = SOME x ->
  post_alloc_conventions k x.
Proof.
  intros k col_opt prog lt ls x [Hpre E]. unfold oracle_colour_ok in E.
  destruct col_opt as [col|]; [|discriminate].
  destruct (every_even_colour col && _) eqn:E1; [|discriminate]. apply andb_prop in E1 as [Hev _].
  destruct (every_stack_var _ _ && _) eqn:E2; [|discriminate]. apply andb_prop in E2 as [Hsv _].
  injection E as <-. unfold post_alloc_conventions, pre_alloc_conventions in *. apply andb_prop in Hpre as [_ Hc].
  rewrite every_var_is_phy_var_total_colour, Hsv. cbn [andb].
  apply call_arg_convention_preservation. split; [|exact Hc].
  apply (every_var_mono (fun x => true)). split; [|apply every_var_T].
  intros y _. destruct (is_phy_var y) eqn:Ep; [|reflexivity]. cbn [implb].
  rewrite (total_colour_even col y Hev Ep). apply N.eqb_refl.
Qed.

Lemma exp_to_addr_colour f (e : exp a) :
  exp_to_addr (apply_colour_exp f e) =
  match exp_to_addr e with Some (Addr n w) => Some (Addr (f n) w) | None => None end.
Proof.
  destruct e as [w|v|v|e|op es|sh e1 e2]; cbn [apply_colour_exp]; unfold exp_to_addr; try reflexivity.
  destruct op; try reflexivity. destruct es as [|e1 [|e2 [|e3 es]]]; try reflexivity;
    destruct e1; try reflexivity; destruct e2; reflexivity.
Qed.

Ltac dec_isa :=
  repeat match goal with
  | |- context [bool_decide ?P] =>
      first [ rewrite (bd_true' P) by (repeat (first [left; reflexivity | right]); reflexivity)
            | rewrite (bd_false' P) by (let HH := fresh in intros HH; repeat destruct HH as [HH|HH]; discriminate) ]
  | H : context [bool_decide ?P] |- _ =>
      first [ rewrite (bd_true' P) in H by (repeat (first [left; reflexivity | right]); reflexivity)
            | rewrite (bd_false' P) in H by (let HH := fresh in intros HH; repeat destruct HH as [HH|HH]; discriminate) ]
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "word_alloc_full_inst_ok_less_lem" *)
Theorem word_alloc_full_inst_ok_less_lem : forall f (prog : prog a) c,
  full_inst_ok_less c prog /\
  EVERY (fun '(x, y) => negb (f x =? f y)) (get_forced c prog []) ->
  full_inst_ok_less c (apply_colour f prog).
Proof.
  intros f prog c [Hf Hg].
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [apply_colour full_inst_ok_less get_forced] in *; try reflexivity; unfold is_true in *;
    rewrite ?Bool.andb_true_iff in *; repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with |- _ /\ _ => split end.
  - destruct_inst i; cbn [apply_colour_inst inst_ok_less get_forced] in *; try exact Hf; try reflexivity;
      destruct (ISA c); dec_isa; cbn [orb andb implb negb] in *;
      repeat match goal with
             | H : context [if ?b then _ else _] |- _ => let E := fresh "E" in destruct b eqn:E
             | |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
             end;
      cbn [EVERY app negb orb andb implb List.app] in *; unfold is_true in *; rewrite ?Bool.andb_true_iff in *;
      repeat match goal with H : _ /\ _ |- _ => destruct H end; try exact Hf; try reflexivity; try tauto;
      repeat split; try reflexivity; try assumption; try discriminate.
    all: destruct (dimindex a =? 32) eqn:Ed; cbn [implb andb] in *; try reflexivity;
      repeat match goal with H : context [(dimindex a =? 32)] |- _ => rewrite Ed in H end;
      cbn [andb implb] in *; try congruence; try assumption.
  - apply IH; assumption.
  - destruct ret as [[vs [cs [rh [l1 l2]]]]|]; cbn beta iota in *; [|reflexivity].
    destruct h as [[hv [hp [l1' l2']]]|]; cbn beta iota in *; rewrite ?Bool.andb_true_iff in *.
    + rewrite EVERY_get_forced, Bool.andb_true_iff in Hg. destruct Hf as [Hf1 Hf2]. destruct Hg as [Hg1 Hg2].
      split; [apply IHr; assumption|apply IHh; assumption].
    + split; [apply IHr; [apply Hf|assumption]|reflexivity].
  - rewrite EVERY_get_forced, Bool.andb_true_iff in Hg. apply IH1; [assumption|tauto].
  - rewrite EVERY_get_forced, Bool.andb_true_iff in Hg. apply IH2; [assumption|tauto].
  - rewrite EVERY_get_forced, Bool.andb_true_iff in Hg. apply IH1; [assumption|tauto].
  - rewrite EVERY_get_forced, Bool.andb_true_iff in Hg. apply IH2; [assumption|tauto].
  - apply IH; assumption.
  - rewrite exp_to_addr_colour. destruct (exp_to_addr e) as [[n w]|]; exact Hf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "forced_distinct_col" *)
Theorem forced_distinct_col : forall spcol (ls : list (N * N)),
  EVERY (fun '(x, y) => ⌜sp_default spcol x = sp_default spcol y -> x = y⌝) ls /\
  EVERY (fun '(x, y) => negb (x =? y)) ls ->
  EVERY (fun '(x, y) => negb (total_colour spcol x =? total_colour spcol y)) ls.
Proof.
  intros spcol ls [H1 H2]. unfold is_true in *. rewrite EVERY_Forall, Forall_forall in *.
  intros [x y] Hxy. specialize (H1 _ Hxy). specialize (H2 _ Hxy). cbv beta iota in *.
  apply bool_decide_spec in H1. apply Bool.negb_true_iff, N.eqb_neq in H2.
  apply Bool.negb_true_iff, N.eqb_neq. rewrite total_colour_alt'. cbv beta. intros E.
  apply H2, H1. lia.
Qed.

(** [pre_post_conventions_word_alloc] and [word_alloc_full_inst_ok_less],
    from [linear_scanProof]'s correctness theorem (Galette-only). *)
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "pre_post_conventions_word_alloc" *)
Theorem pre_post_conventions_word_alloc : forall fc (c0 : asm_config a) alg (prog : prog a) k col_opt,
  pre_alloc_conventions prog -> post_alloc_conventions k (word_alloc fc c0 alg k prog col_opt).
Proof.
  intros fc c0 alg prog k col_opt Hpre. unfold word_alloc. cbv zeta.
  destruct (oracle_colour_ok k col_opt (get_clash_tree prog []) prog (get_forced c0 prog [])) as [x|] eqn:Eo.
  { exact (oracle_colour_ok_conventions k col_opt prog [] _ x (conj Hpre Eo)). }
  destruct (get_heuristics alg fc prog) as [heu_moves spillcosts].
  destruct (select_reg_alloc_correct alg spillcosts k heu_moves (get_clash_tree prog [])
              (get_forced c0 prog []) (get_stack_only prog) (get_forced_in_get_clash_tree prog [] c0))
    as (spcol & livein & flivein & Es & _ & Hin & _ & _).
  rewrite Es. set (tree := get_clash_tree prog []) in *.
  pose proof (every_var_in_get_clash_tree prog []) as Hct. fold tree in Hct.
  unfold pre_alloc_conventions, post_alloc_conventions in *. apply andb_prop in Hpre as [Hsv Hc].
  unfold is_true. rewrite !Bool.andb_true_iff. split; [split|].
  - apply every_var_is_phy_var_total_colour.
  - apply (every_stack_var_apply_colour (fun x => ⌜in_clash_tree tree x⌝ && is_stack_var x)). split.
    + apply every_stack_var_conj. split; [apply every_var_imp_every_stack_var, Hct|exact Hsv].
    + intros x Hx. apply andb_prop in Hx as [Hx1 Hx2]. apply bool_decide_spec in Hx1.
      destruct (Hin x Hx1) as [_ Hs].
      assert (Hnp : is_phy_var x = false).
      { unfold is_stack_var, is_phy_var in *. apply N.eqb_eq in Hx2. apply N.eqb_neq. intros E.
        pose proof (N.div_mod x 4 ltac:(lia)). pose proof (N.div_mod x 2 ltac:(lia)). lia. }
      rewrite Hnp, Hx2 in Hs. apply N.leb_le. rewrite total_colour_alt'. cbv beta. lia.
  - apply call_arg_convention_preservation. split; [|exact Hc].
    apply (every_var_mono (fun x => ⌜in_clash_tree tree x⌝)). split; [|exact Hct].
    intros x Hx. apply bool_decide_spec in Hx. destruct (is_phy_var x) eqn:Ep; [|reflexivity]. cbn [implb].
    destruct (Hin x Hx) as [_ Hs]. rewrite Ep in Hs. apply N.eqb_eq. rewrite total_colour_alt'. cbv beta.
    rewrite Hs. unfold is_phy_var in Ep. apply N.eqb_eq in Ep. pose proof (N.div_mod x 2 ltac:(lia)). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "word_alloc_full_inst_ok_less" *)
Theorem word_alloc_full_inst_ok_less : forall fc alg k (prog : prog a) col_opt c0,
  full_inst_ok_less c0 prog -> full_inst_ok_less c0 (word_alloc fc c0 alg k prog col_opt).
Proof.
  intros fc alg k prog col_opt c0 Hf. unfold word_alloc. cbv zeta.
  destruct (oracle_colour_ok k col_opt (get_clash_tree prog []) prog (get_forced c0 prog [])) as [x|] eqn:Eo.
  { unfold oracle_colour_ok in Eo. destruct col_opt as [col|]; [|discriminate].
    destruct (every_even_colour col && _); [|discriminate].
    destruct (every_stack_var _ _ && _) eqn:E2; [|discriminate]. apply andb_prop in E2 as [_ Hf2].
    injection Eo as <-. apply word_alloc_full_inst_ok_less_lem. split; [exact Hf|exact Hf2]. }
  destruct (get_heuristics alg fc prog) as [heu_moves spillcosts].
  destruct (select_reg_alloc_correct alg spillcosts k heu_moves (get_clash_tree prog [])
              (get_forced c0 prog []) (get_stack_only prog) (get_forced_in_get_clash_tree prog [] c0))
    as (spcol & livein & flivein & Es & _ & _ & _ & Hfd).
  rewrite Es. apply word_alloc_full_inst_ok_less_lem. split; [exact Hf|].
  apply forced_distinct_col. split; [exact Hfd|].
  apply get_forced_pairwise_distinct. reflexivity.
Qed.

End Conv.









