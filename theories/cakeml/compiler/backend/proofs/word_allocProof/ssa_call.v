(** * CakeML [word_allocProof]: SSA correctness for returning calls

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml]: the
    [Call_returning] case of [ssa_cc_trans_correct] (HOL lines 8298-9228),
    as Galette-only lemmas.  The skeleton [ssa_gcall] follows
    [colouring.v]'s [eac_Call_Some]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set extra.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
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
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring ssa_props ssa_loop ssa.
Open Scope N_scope.

Section SSA4.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types (st cst : state).

Definition hnd_of (st : state) (h : option (N * (prog a * (N * N)))) : option (N * (N * N)) :=
  match h with None => None | Some (_, (_, (a1, a2))) => Some (handler st, (a1, a2)) end.

(** The returning-call skeleton (Galette-only). *)
Lemma ssa_gcall rv (n1 n2 : num_set) rh l1 l2 dest args h regs trh conv th
    (st tcs : state) (f : N -> N) lt naF ssaF xs :
  word_state_eq_rel st tcs ->
  get_vars args st = SOME xs -> get_vars conv tcs = SOME xs ->
  bad_dest_args dest conv = bad_dest_args dest args ->
  ALL_DISTINCT regs = true -> LENGTH regs = LENGTH rv ->
  INJ f (domain n1 UNION domain n2) UNIV ->
  strong_locals_rel f (domain n1 UNION domain n2) (locals st) (locals tcs) ->
  match h with
  | None => th = None
  | Some (_, (_, (l1', l2'))) => match th with None => False | Some (_, (_, (c0, d))) => c0 = l1' /\ d = l2' end
  end ->
  (forall (s1p cs1p : state) ys,
     word_state_eq_rel s1p cs1p -> strong_locals_rel f (domain n1 UNION domain n2) (locals s1p) (locals cs1p) ->
     domain (locals s1p) = domain n1 UNION domain n2 -> LENGTH ys = LENGTH rv -> ALL_DISTINCT rv = true ->
     exists prh,
       let '(res, rst) := evaluate (rh, set_permute prh (set_vars rv ys s1p)) in
       res = SOME Error \/
       let '(res', rcst) := evaluate (trh, set_vars regs ys cs1p) in
       res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naF ssaF res rst rcst) ->
  match h, th with
  | Some (hn, (hp, _)), Some (tn, (thp, _)) =>
      forall (s2 cs2 : state) y,
        word_state_eq_rel s2 cs2 -> strong_locals_rel f (domain n1 UNION domain n2) (locals s2) (locals cs2) ->
        domain (locals s2) = domain n1 UNION domain n2 ->
        exists php,
          let '(res, rst) := evaluate (hp, set_permute php (set_var hn y s2)) in
          res = SOME Error \/
          let '(res', rcst) := evaluate (thp, set_var tn y cs2) in
          res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naF ssaF res rst rcst
  | _, _ => True
  end ->
  exists perm,
    let '(res, rst) := evaluate (Call (Some (rv, ((n1, n2), (rh, (l1, l2))))) dest args h, set_permute perm st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Call (Some (regs, (apply_nummaps_key f (n1, n2), (trh, (l1, l2))))) dest conv th, tcs) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naF ssaF res rst rcst.
Proof.
  intros Heq Eg Eg' Ebdc Hdr Hlr Hi1 Hs Hth CR CE.
  pose proof Heq as Heq'. destruct Heq' as (Hfp & Hstore & Hls & Hstack & Hsl & Hsm & Hss & Hmem & Hmd & Hsmd
    & Hgc & Hh & Hclk & Hcode & Hffi & Hbe & Htd & Hcomp & Hco & Hcb & Hdb).
  assert (Herr : forall perm, FST (evaluate (Call (Some (rv, ((n1, n2), (rh, (l1, l2))))) dest args h, set_permute perm st)) = SOME Error ->
     exists perm,
    let '(res, rst) := evaluate (Call (Some (rv, ((n1, n2), (rh, (l1, l2))))) dest args h, set_permute perm st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Call (Some (regs, (apply_nummaps_key f (n1, n2), (trh, (l1, l2))))) dest conv th, tcs) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naF ssaF res rst rcst).
  { intros perm H. exists perm. destruct (evaluate _) as [r t]. cbn in H. left; exact H. }
  destruct (bad_dest_args dest args) eqn:Ebd.
  { apply (Herr (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body].
    rewrite Eg, Ebd. reflexivity. }
  destruct (find_code dest (Loc l1 l2 :: xs) (code st) (state_stack_size st)) as [[args1 [prog ss]]|] eqn:Ef.
  2:{ apply (Herr (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body add_ret_loc].
      rewrite Eg, Ebd, Ef. reflexivity. }
  destruct (⌜domain n1 = {}⌝ || negb (ALL_DISTINCT rv)) eqn:Ecd.
  { apply (Herr (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body add_ret_loc].
    rewrite Eg, Ebd, Ef. cbn [FST fst]. rewrite Ecd. reflexivity. }
  assert (Hrvd : ALL_DISTINCT rv = true)
    by (apply orb_false_iff in Ecd as [_ E]; apply Bool.negb_false_iff in E; exact E).
  destruct (cut_envs (n1, n2) (locals st)) as [[x0 x1]|] eqn:Ec.
  2:{ apply (Herr (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body add_ret_loc].
      rewrite Eg, Ebd, Ef. cbn [FST fst]. rewrite Ecd, Ec. reflexivity. }
  assert (Ef' : find_code dest (Loc l1 l2 :: xs) (code tcs) (state_stack_size tcs) = SOME (args1, (prog, ss)))
    by (rewrite Hcode, Hss; exact Ef).
  assert (Ecd' : (⌜domain (FST (apply_nummaps_key f (n1, n2))) = {}⌝ || negb (ALL_DISTINCT regs)) = false).
  { apply orb_false_iff in Ecd as [Ecd1 Ecd2]. apply orb_false_iff. split.
    - apply bd_false'. cbn [apply_nummaps_key FST fst]. fold (apply_nummap_key f n1).
      rewrite apply_nummap_key_domain. intros E. rewrite bd_true' in Ecd1; [discriminate|].
      apply set_ext; intros x; split; [|intros []]. intros Hx.
      assert (Hfx : f x IN IMAGE f (domain n1)) by (exists x; split; [reflexivity|exact Hx]).
      rewrite E in Hfx. destruct Hfx.
    - rewrite Hdr. reflexivity. }
  destruct (cut_envs_lemma f n1 n2 (locals st) (locals tcs) x0 x1) as
    (y1 & y2 & Ecy & D1 & D2 & S1 & S2 & I1 & I2 & X1 & X2).
  { split; [inj_less Hi1|split; [inj_less Hi1|split; [exact Ec|split]]];
      eapply strong_locals_rel_subset; (split; [|exact Hs]); set_solve. }
  assert (Ebd' : bad_dest_args dest conv = false) by exact Ebdc.
  assert (Htgt : (clock tcs =? 0) = false ->
    evaluate (Call (Some (regs, (apply_nummaps_key f (n1, n2), (trh, (l1, l2))))) dest conv th, tcs) =
    call_cont regs trh l1 l2 th (y1, y2)
      (evaluate (prog, call_env args1 ss (push_env (y1, y2) th (dec_clock tcs))))).
  { intros Hz. exact (evaluate_Call_Some_eq regs (apply_nummaps_key f (n1, n2)) trh l1 l2 dest conv th tcs xs args1 prog ss (y1, y2) Eg' Ebd' Ef' Ecd' Ecy Hz). }
  assert (Hthn : h = None <-> th = None).
  { destruct h as [[? [? [? ?]]]|]; [destruct th as [[? [? [? ?]]]|]; [split; discriminate|contradiction]|].
    rewrite Hth. split; reflexivity. }
  assert (Hhnd : forall (s : state), hnd_of s h = match th with None => None | Some (_, (_, (a1, a2))) => Some (handler s, (a1, a2)) end).
  { intros s. destruct h as [[? [? [? ?]]]|]; [destruct th as [[? [? [? ?]]]|]; [|contradiction]|].
    - destruct Hth as [-> ->]. reflexivity.
    - rewrite Hth. reflexivity. }
  destruct (clock st =? 0) eqn:Eck.
  { exists (permute st). rewrite set_permute_permute.
    rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc]. rewrite Eg, Ebd, Ef. cbn [FST fst].
    rewrite Ecd, Ec, Eck. cbn beta iota. right.
    rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc]. rewrite Eg', Ebd', Ef'.
    rewrite Ecd', Ecy, Hclk, Eck. cbn beta iota. cbn [ssa_post].
    split; [reflexivity|split; [|reflexivity]].
    unfold flush_state; cbn_ws. unfold word_state_eq_rel; cbn_ws.
    rewrite (stack_max_call_env_push_env args1 ss (y1, y2) (x0, x1) th h tcs st) by
      (first [assumption | split; intros E; apply Hthn; exact E]).
    repeat split; congruence. }
  set (s' := dec_clock st). set (cs' := dec_clock tcs).
  destruct (push_env_s_val_eq s' cs' x1 y2 x0 y1 f h th (fun k => permute tcs (k + 1)))
    as [P0 [Hpe Hsv]].
  { subst s' cs'. unfold dec_clock; cbn_ws.
    split; [congruence|split; [congruence|split; [congruence|]]].
    rewrite X2, X1. split; [exact D2|split; [rewrite <- X2; exact I2|split; [exact D1|split; [rewrite <- X1; exact I1|split; [exact S2|]]]]].
    exact Hth. }
  set (st2 := call_env args1 ss (push_env (x0, x1) h (set_permute P0 s'))).
  set (cst2 := call_env args1 ss (push_env (y1, y2) th cs')).
  change (permute cs') with (permute tcs) in Hpe.
  destruct (env_to_list y2 (permute tcs)) as [l pc] eqn:El.
  destruct (env_to_list x1 P0) as [l' pc'] eqn:El'.
  destruct Hpe as (Hpc & Hml & Hinj).
  assert (Hpc2 : pc = fun k => permute tcs (k + 1)) by (unfold env_to_list in El; injection El as _ <-; reflexivity).
  assert (Hst2 : stack st2 = StackFrame (locals_size st) (toAList x0) l' (hnd_of st h) :: stack st).
  { subst st2 s'. unfold call_env, push_env, hnd_of. destruct h as [[? [? [? ?]]]|]; cbn [FST SND fst snd];
      rewrite permute_set_permute, El'; reflexivity. }
  assert (Hcst2 : stack cst2 = StackFrame (locals_size st) (toAList y1) l (hnd_of st h) :: stack st).
  { rewrite Hhnd. subst cst2 cs'. unfold call_env, push_env. destruct th as [[? [? [? ?]]]|]; cbn [FST SND fst snd];
      unfold dec_clock; cbn_ws; rewrite El; cbn_ws; rewrite Hls, Hstack, ?Hh; reflexivity. }
  assert (Hsv2 : s_val_eq (stack st2) (stack cst2)).
  { subst st2 cst2. unfold call_env. cbn_ws. exact Hsv. }
  assert (Hcs2 : cst2 = set_stack (stack cst2) st2).
  { pose proof (s_val_eq_stack_size _ _ Hsv2) as Hsz. rewrite Hst2, Hcst2 in Hsz.
    apply state_component_equality. repeat split.
    all: try (rewrite stack_set_stack; reflexivity).
    all: subst st2 cst2 s' cs'; unfold call_env, push_env, dec_clock;
      destruct h as [[? [? [? ?]]]|]; [destruct th as [[? [? [? ?]]]|]; [destruct Hth as [-> ->]|contradiction]|rewrite Hth];
      cbn [FST SND fst snd hnd_of] in *; cbn_ws; rewrite ?El, ?El'; cbn_ws.
    all: first [congruence | (rewrite <- Hsm, <- Hstack, <- Hls, <- ?Hh; rewrite Hsz; reflexivity)
               | (rewrite <- Hsm, <- Hstack, <- Hls, <- ?Hh; rewrite <- Hsz; reflexivity)]. }
  assert (EQ1 : forall q, evaluate (Call (Some (rv, ((n1, n2), (rh, (l1, l2))))) dest args h,
                                    set_permute (perm_cons (P0 0) q) st) =
                          call_cont rv rh l1 l2 h (x0, x1) (evaluate (prog, set_permute q st2))).
  { intros q. rewrite (evaluate_Call_Some_eq rv (n1, n2) rh l1 l2 dest args h _ xs args1 prog ss (x0, x1));
      rewrite ?get_vars_set_permute, ?code_set_permute, ?state_stack_size_set_permute,
              ?locals_set_permute, ?clock_set_permute; try assumption.
    f_equal. f_equal. rewrite dec_clock_set_permute. fold s'.
    replace (set_permute (perm_cons (P0 0) q) s') with
      (set_permute (perm_cons (permute (set_permute P0 s') 0) q) (set_permute P0 s'))
      by (rewrite permute_set_permute, set_permute_set_permute; reflexivity).
    rewrite push_env_perm_cons, call_env_set_permute. reflexivity. }
  assert (Hgoal : exists q, let '(res, rst) := call_cont rv rh l1 l2 h (x0, x1) (evaluate (prog, set_permute q st2)) in
     res = SOME Error \/
     (let '(res', rcst) := call_cont regs trh l1 l2 th (y1, y2) (evaluate (prog, cst2)) in
      res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naF ssaF res rst rcst)).
  { apply (permute_swap_lemma4 prog st2 (fun r => let '(res, rst) := call_cont rv rh l1 l2 h (x0, x1) r in
     res = SOME Error \/
     (let '(res', rcst) := call_cont regs trh l1 l2 th (y1, y2) (evaluate (prog, cst2)) in
      res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naF ssaF res rst rcst))).
    split; [intros st' _; cbn [call_cont]; left; reflexivity|].
    pose proof (evaluate_stack_swap prog st2) as SW.
    destruct (evaluate (prog, st2)) as [r1 s1] eqn:E1.
    unfold PAIR_MAP, I; cbn [FST SND fst snd].
    destruct r1 as [[x ys|x y'|k|k| | |ou|]|].
    - (* Result *)
      destruct SW as (SK & SH & SWf).
      destruct (SWf (stack cst2) Hsv2) as (st_ & Ecs & SV & SK2).
      rewrite <- Hcs2 in Ecs. rewrite Ecs. cbn [call_cont]. rewrite Hlr.
      destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH rv)) eqn:Echk;
        [exists P0; left; reflexivity|].
      rewrite Hst2 in SK. destruct (stack s1) as [|[m ex0 lx hx] rx] eqn:Es1; cbn [s_key_eq] in SK; [contradiction|].
      destruct SK as [SKr SKf]. apply s_frame_key_eq_def2 in SKf as (Kfst & <- & <- & <-).
      destruct st_ as [|[m' ey0 ly hy] ry]; cbn [s_val_eq] in SV; [contradiction|].
      destruct SV as [SVr SVf]. apply s_frame_val_eq_def2 in SVf as (Vsnd & <- & <-).
      rewrite Hcst2 in SK2. cbn [s_key_eq] in SK2. destruct SK2 as [SK2r SK2f].
      apply s_frame_key_eq_def2 in SK2f as (Kfst2 & _ & <- & _).
      set (hnd := hnd_of st h) in *.
      assert (Ep1 : pop_env s1 = SOME (set_locals_size (locals_size st) (set_stack rx
                      (set_locals (union (fromAList lx) (fromAList (toAList x0))) (match hnd with None => s1 | Some (hn, _) => set_handler hn s1 end))))).
      { unfold pop_env. rewrite Es1. destruct hnd as [[hn [? ?]]|]; reflexivity. }
      assert (Ep2 : pop_env (set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: ry) s1) =
                    SOME (set_locals_size (locals_size st) (set_stack ry
                      (set_locals (union (fromAList ly) (fromAList (toAList y1)))
                        (match hnd with None => set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: ry) s1
                         | Some (hn, _) => set_handler hn (set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: ry) s1) end))))).
      { unfold pop_env. rewrite stack_set_stack. destruct hnd as [[hn [? ?]]|]; reflexivity. }
      assert (Hrr : ry = rx).
      { symmetry; apply s_val_and_key_eq; split; [exact SVr|].
        apply (s_key_eq_trans _ (stack st)); split; [apply s_key_eq_sym; exact SKr|exact SK2r]. }
      subst ry.
      assert (Hdc : ⌜domain (union (fromAList ly) (fromAList (toAList y1))) =
                     domain (FST (y1, y2)) UNION domain (SND (y1, y2))⌝ = true).
      { apply bd_true'. cbn [FST SND fst snd]. eapply dom_union_frame; [|exact El]. exact Kfst2. }
      apply orb_false_iff in Echk as [_ Elen]. apply Bool.negb_false_iff, N.eqb_eq in Elen.
      destruct (⌜domain (union (fromAList lx) (fromAList (toAList x0))) =
                domain (FST (x0, x1)) UNION domain (SND (x0, x1))⌝) eqn:Edc.
      2:{ exists P0. rewrite pop_env_set_permute, Ep1. cbn [OPTION_MAP option_map].
          rewrite locals_set_permute. cbn_ws. rewrite Edc. left; reflexivity. }
      apply bool_decide_spec in Edc. cbn [FST SND fst snd] in Edc.
      set (s1p := set_locals_size (locals_size st) (set_stack rx
                      (set_locals (union (fromAList lx) (fromAList (toAList x0))) (match hnd with None => s1 | Some (hn, _) => set_handler hn s1 end)))) in *.
      set (cs1p := set_locals_size (locals_size st) (set_stack rx
                      (set_locals (union (fromAList ly) (fromAList (toAList y1)))
                        (match hnd with None => set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: rx) s1
                         | Some (hn, _) => set_handler hn (set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: rx) s1) end)))) in *.
      assert (Hl1 : strong_locals_rel f (domain n1 UNION domain n2) (locals s1p) (locals cs1p)).
      { subst s1p cs1p. cbn_ws. apply union_fromAList_rel.
        - exact Vsnd.
        - rewrite <- Kfst2, <- Kfst. symmetry; apply key_map_implies; exact Hml.
        - rewrite X1; exact S1.
        - pose proof (env_to_list_keys x1 P0) as Hk. rewrite El' in Hk. rewrite <- Kfst, Hk, X1, X2.
          eapply INJ_less; split; [exact Hi1|]. set_solve. }
      assert (Hw1 : word_state_eq_rel s1p cs1p).
      { subst s1p cs1p. destruct hnd as [[? [? ?]]|]; unfold word_state_eq_rel; cbn_ws; repeat split; reflexivity. }
      destruct (CR s1p cs1p ys Hw1 Hl1 ltac:(subst s1p; cbn_ws; rewrite Edc, X1, X2; reflexivity) Elen Hrvd)
        as [prh Hrh].
      exists prh. rewrite pop_env_set_permute, Ep1, Ep2. cbn [OPTION_MAP option_map].
      fold s1p. fold cs1p. rewrite locals_set_permute.
      replace (locals s1p) with (union (fromAList lx) (fromAList (toAList x0))) by reflexivity.
      replace (locals cs1p) with (union (fromAList ly) (fromAList (toAList y1))) by reflexivity.
      rewrite Hdc, bd_true' by (cbn [FST SND fst snd]; exact Edc).
      rewrite set_vars_set_permute. exact Hrh.
    - (* Exception *)
      destruct SW as (Hhl & e0 & e & nn & ls & m & lss & HL & Hm & (Hfe & Hloc) & SKs & Hhd & SWf).
      destruct h as [[n' [hp [l1' l2']]]|].
      + (* with a handler *)
        destruct th as [[tn [thp [tl1 tl2]]]|]; [|contradiction]. destruct Hth as [-> ->].
        assert (Hh2 : handler st2 = LENGTH (stack st)).
        { subst st2 s'. unfold call_env, push_env. cbn [FST SND fst snd].
          rewrite permute_set_permute, El'. cbn_ws. reflexivity. }
        rewrite Hh2, Hst2, LASTN_LENGTH2 in HL. injection HL as Hm0 He0 He Hnn Hls0.
        subst m e0 e nn ls.
        destruct (SWf (stack cst2) (toAList y1) l (stack st)) as (st_ & locs & Ecs & (lss' & Hfe' & Hlocs & Hsnd') & SVs & SKs2).
        { split; [|exact Hsv2]. rewrite Hh2, Hcst2, LASTN_LENGTH2. reflexivity. }
        rewrite <- Hcs2 in Ecs. rewrite Ecs. unfold call_env.
        set (cs1 := set_locals locs (set_handler (let '(a0, _) := (handler st, (l1', l2')) in a0) (set_stack st_ s1))).
        destruct (negb ⌜x = Loc l1' l2'⌝) eqn:Ex.
        { exists P0. unfold call_cont; cbn beta iota. rewrite Ex. left; reflexivity. }
        assert (Hdc : ⌜domain (locals cs1) = domain (FST (y1, y2)) UNION domain (SND (y1, y2))⌝ = true).
        { apply bd_true'. subst cs1. cbn_ws. rewrite Hlocs. cbn [FST SND fst snd].
          eapply dom_union_frame; [|exact El]. exact Hfe'. }
        destruct (⌜domain (locals s1) = domain (FST (x0, x1)) UNION domain (SND (x0, x1))⌝) eqn:Edc.
        2:{ exists P0. unfold call_cont; cbn beta iota. rewrite Ex, locals_set_permute, Edc. left; reflexivity. }
        apply bool_decide_spec in Edc. cbn [FST SND fst snd] in Edc.
        assert (Hss1 : st_ = stack s1).
        { symmetry; apply s_val_and_key_eq; split; [exact SVs|].
          apply (s_key_eq_trans _ (stack st)); split; [exact SKs|exact SKs2]. }
        assert (Hl1 : strong_locals_rel f (domain n1 UNION domain n2) (locals s1) (locals cs1)).
        { subst cs1. cbn_ws. rewrite Hloc, Hlocs. apply union_fromAList_rel.
          - exact Hsnd'.
          - rewrite <- Hfe', <- Hfe. symmetry; apply key_map_implies; exact Hml.
          - rewrite X1; exact S1.
          - pose proof (env_to_list_keys x1 P0) as Hk. rewrite El' in Hk. rewrite <- Hfe, Hk, X1, X2.
            eapply INJ_less; split; [exact Hi1|]. set_solve. }
        assert (Hw1 : word_state_eq_rel s1 cs1).
        { subst cs1. rewrite Hss1. unfold word_state_eq_rel; cbn_ws. rewrite Hhd. repeat split. }
        destruct (CE s1 cs1 y' Hw1 Hl1 ltac:(rewrite Edc, X1, X2; reflexivity)) as [php Hhp].
        exists php. unfold call_cont; cbn beta iota. rewrite Ex, locals_set_permute.
        rewrite bd_true' by (cbn [FST SND fst snd]; exact Edc). fold cs1. rewrite Hdc.
        rewrite set_var_set_permute. exact Hhp.
      + (* no handler *)
        rewrite Hth in *.
        assert (Hh2 : handler st2 = handler st).
        { subst st2 s'. unfold call_env, push_env. cbn [FST SND fst snd].
          rewrite permute_set_permute, El'. cbn_ws. reflexivity. }
        rewrite Hh2, Hst2 in Hhl. rewrite Hh2 in HL, SWf. rewrite Hst2 in HL.
        assert (Hlt : handler st + 1 <= LENGTH (stack st)).
        { destruct (N.eq_dec (handler st) (LENGTH (stack st))) as [E|E].
          - exfalso. rewrite E, LASTN_LENGTH2 in HL. discriminate HL.
          - rewrite !LENGTH_length in *. cbn [length] in Hhl. lia. }
        rewrite LASTN_cons_le in HL by exact Hlt.
        destruct (SWf (stack cst2) e0 e ls) as (st_ & locs & Ecs & (lss' & Hfe' & Hlocs & Hsnd') & SVs & SKs2).
        { split; [|exact Hsv2]. rewrite Hcst2, LASTN_cons_le by exact Hlt. exact HL. }
        rewrite <- Hcs2 in Ecs. rewrite Ecs. exists (permute s1). rewrite set_permute_permute.
        unfold call_cont; cbn beta iota. right.
        assert (Hlss : lss' = lss) by (apply pair_list_eq; [rewrite <- Hfe, <- Hfe'; reflexivity|symmetry; exact Hsnd']).
        subst lss'.
        assert (Hss1 : st_ = stack s1).
        { symmetry; apply s_val_and_key_eq; split; [exact SVs|].
          apply (s_key_eq_trans _ ls); split; [exact SKs|exact SKs2]. }
        split; [reflexivity|split].
        * rewrite Hss1. unfold word_state_eq_rel; cbn_ws. rewrite Hhd. repeat split.
        * cbn [ssa_post]. cbn_ws. rewrite Hloc, Hlocs. reflexivity.
    - exists P0; left; reflexivity.
    - exists P0; left; reflexivity.
    - (* TimeOut *)
      destruct SW as (Hs1 & Hl1 & SWf). pose proof (SWf (stack cst2) Hsv2) as E2.
      rewrite <- Hcs2 in E2. rewrite E2. exists (permute s1). rewrite set_permute_permute.
      unfold call_cont; cbn beta iota. right. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    - (* NotEnoughSpace *)
      destruct SW as (Hs1 & Hl1 & SWf). pose proof (SWf (stack cst2) Hsv2) as E2.
      rewrite <- Hcs2 in E2. rewrite E2. exists (permute s1). rewrite set_permute_permute.
      unfold call_cont; cbn beta iota. right. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    - (* FinalFFI *)
      destruct SW as (Hs1 & Hl1 & SWf). pose proof (SWf (stack cst2) Hsv2) as E2.
      rewrite <- Hcs2 in E2. rewrite E2. exists (permute s1). rewrite set_permute_permute.
      unfold call_cont; cbn beta iota. right. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    - exists P0; left; reflexivity.
    - exists P0; left; reflexivity. }
  destruct Hgoal as [q Hq]. exists (perm_cons (P0 0) q). rewrite EQ1.
  rewrite (Htgt ltac:(rewrite Hclk; exact Eck)). exact Hq.
Qed.

Lemma ret_cont rh rv (n1 n2 : num_set) ssa1 na1 rmov ssa2 na2 ret' ssa3 na3 rh' ssa4 na4 lt na
    (s1p cs1p : state) ys :
  @ssa_IH a c ffi_t rh -> lt_ok lt -> ssa_map_ok na1 ssa1 -> is_stack_var na1 -> na <= na1 ->
  is_true (EVERY (fun x => x <? na) rv) -> is_true (every_var (fun x => x <? na) rh) ->
  (forall x, domain (union n1 n2) x -> domain ssa1 x) -> (forall x, domain (union n1 n2) x -> x < na) ->
  list_next_var_rename_move (inter ssa1 (union n1 n2)) (na1 + 2) (MAP FST (toAList (union n1 n2))) = (rmov, (ssa2, na2)) ->
  list_next_var_rename rv ssa2 na2 = (ret', (ssa3, na3)) ->
  ssa_cc_trans rh ssa3 na3 lt = (rh', (ssa4, na4)) ->
  word_state_eq_rel s1p cs1p -> strong_locals_rel (option_lookup ssa1) (domain n1 UNION domain n2) (locals s1p) (locals cs1p) ->
  domain (locals s1p) = domain n1 UNION domain n2 -> LENGTH ys = LENGTH rv -> ALL_DISTINCT rv = true ->
  exists prh,
    let '(res, rst) := evaluate (rh, set_permute prh (set_vars rv ys s1p)) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Seq rmov (Seq (Move 1 (ZIP (ret', GENLIST (fun x => 2 * (x + 1)) (LENGTH rv)))) rh'),
                                   set_vars (GENLIST (fun x => 2 * (x + 1)) (LENGTH rv)) ys cs1p) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na4 ssa4 res rst rcst.
Proof.
  intros IHr Hlt Hok1 Hst1 Hle1 Hevrv Hevrh Hsub Hlt' Erm Erv Erh Hw Hs Hd Hly Hrvd.
  set (regs := GENLIST (fun x => 2 * (x + 1)) (LENGTH rv)).
  destruct (GENLIST_rets_props (LENGTH rv)) as [Hndr Hphr]. fold regs in Hndr, Hphr.
  assert (Hlr : LENGTH regs = LENGTH rv) by (unfold regs; apply LENGTH_GENLIST').
  set (all := union n1 n2) in *. set (ls := MAP FST (toAList all)) in *.
  assert (Hdls : ALL_DISTINCT ls) by apply ALL_DISTINCT_MAP_FST_toAList.
  assert (Han1 : is_alloc_var (na1 + 2)) by (apply is_stack_var_flip, Hst1).
  assert (Hokc : ssa_map_ok (na1 + 2) (inter ssa1 all))
    by (apply ssa_map_ok_inter, (ssa_map_ok_more na1); split; [exact Hok1|lia]).
  assert (Hrc : ssa_locals_rel (na1 + 2) (inter ssa1 all) (locals s1p) (locals cs1p)).
  { apply rel_cut; [exact Hsub| | |].
    - rewrite Hd. unfold all. rewrite domain_union. reflexivity.
    - eapply strong_locals_rel_subset; split; [|exact Hs]. intros x Hx. unfold all in Hx. rewrite domain_union in Hx. exact Hx.
    - intros x Hx. specialize (Hlt' x Hx). lia. }
  assert (Hrc' : ssa_locals_rel (na1 + 2) (inter ssa1 all) (locals s1p) (locals (set_vars regs ys cs1p))).
  { unfold set_vars. rewrite locals_set_locals. apply (ssa_locals_rel_ignore_list_insert _ _ s1p cs1p).
    split; [exact Hokc|split; [exact Hrc|split; [|lia]]].
    unfold is_true; rewrite EVERY_Forall, Forall_forall. intros y Hy. apply Hphr, Hy. }
  pose proof (lnvrm_core s1p (set_vars regs ys cs1p) (inter ssa1 all) (na1 + 2) ls Hrc') as C2.
  rewrite Erm in C2. destruct (evaluate (rmov, set_vars regs ys cs1p)) as [r3 c3] eqn:E3.
  destruct C2 as (-> & Hr3 & Hw3 & Hph & _).
  { intros x Hx. apply In_toAList_keys in Hx. rewrite domain_inter. split; [apply Hsub, Hx|exact Hx]. }
  { exact Hdls. } { exact Hokc. } { unfold set_vars; eapply word_state_eq_rel_trans; [exact Hw|apply wser_sl]. }
  specialize (Hph ltac:(rewrite is_alloc_var_not_phy by exact Han1; discriminate)).
  destruct (lnvrm_Inv _ _ _ _ _ _ Erm (conj Hokc Han1)) as (Hle2 & Hok2 & Ha2).
  destruct (lnvr_Inv _ _ _ _ _ _ Erv (conj Hok2 Ha2)) as (Hle3 & Hok3 & Ha3).
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ Erv) as (Hdret & Hret & _).
  assert (Hlret : LENGTH ret' = LENGTH regs).
  { rewrite Hret, LENGTH_MAP', LENGTH_COUNT_LIST. symmetry; exact Hlr. }
  assert (Hg : get_vars regs c3 = Some ys).
  { apply (get_vars_eq_alist_insert c3 (locals cs1p)). split; [apply ALL_DISTINCT_iff', Hndr|split; [lia|]].
    intros x Hx. rewrite Hph by (apply Hphr, MEM_iff', Hx). unfold set_vars. rewrite locals_set_locals. reflexivity. }
  assert (Em : evaluate (Move 1 (ZIP (ret', regs)), c3) = (NONE, set_vars ret' ys c3)).
  { rewrite evaluate_eqn; cbn [evaluate_body]. rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlret.
    rewrite Hdret, Hg. reflexivity. }
  destruct (IHr (set_vars rv ys s1p) (set_vars ret' ys c3) ssa3 na3 lt) as [prh Hrh].
  { split; [unfold set_vars; apply word_state_eq_rel_locals, Hw3|].
    split; [unfold set_vars; rewrite !locals_set_locals|].
    - apply (ssa_locals_rel_list_next_var_rename rv ssa2 na2 _ _ ret' ssa3 na3 ys).
      split; [exact Erv|split; [exact Hr3|split; [exact Hok2|split; [lia|split; [|split; [exact Hrvd|]]]]]].
      + apply (EVERY_lt_mono _ na); [exact Hevrv|lia].
      + rewrite is_alloc_var_not_phy by exact Ha2. discriminate.
    - split; [exact Ha3|split; [apply (every_var_lt_mono _ na); [exact Hevrh|lia]|split; [exact Hok3|exact Hlt]]]. }
  rewrite Erh in Hrh. exists prh.
  destruct (evaluate (rh, set_permute prh (set_vars rv ys s1p))) as [res rst].
  destruct Hrh as [Hrh|Hrh]; [left; exact Hrh|right].
  rewrite (eval_Seq_none _ _ _ _ E3), (eval_Seq_none _ _ _ _ Em). exact Hrh.
Qed.

Lemma exc_cont hp hn (n1 n2 : num_set) ssa1 na1 rmov ssa2 na2 na4 hp' ssa5 na5 lt na (s2 cs2 : state) y :
  @ssa_IH a c ffi_t hp -> lt_ok lt -> ssa_map_ok na1 ssa1 -> is_stack_var na1 -> na <= na1 -> na2 <= na4 -> is_alloc_var na4 ->
  hn < na -> is_true (every_var (fun x => x <? na) hp) ->
  (forall x, domain (union n1 n2) x -> domain ssa1 x) -> (forall x, domain (union n1 n2) x -> x < na) ->
  list_next_var_rename_move (inter ssa1 (union n1 n2)) (na1 + 2) (MAP FST (toAList (union n1 n2))) = (rmov, (ssa2, na2)) ->
  ssa_cc_trans hp (insert hn na4 ssa2) (na4 + 4) lt = (hp', (ssa5, na5)) ->
  word_state_eq_rel s2 cs2 -> strong_locals_rel (option_lookup ssa1) (domain n1 UNION domain n2) (locals s2) (locals cs2) ->
  domain (locals s2) = domain n1 UNION domain n2 ->
  exists php,
    let '(res, rst) := evaluate (hp, set_permute php (set_var hn y s2)) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (Seq rmov (Seq (Move 1 [(na4, 2)]) hp'), set_var 2 y cs2) in
    res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na5 ssa5 res rst rcst.
Proof.
  intros IHh Hlt Hok1 Hst1 Hle1 Hle24 Ha4 Hhn Hevhp Hsub Hlt' Erm Ehp Hw Hs Hd.
  set (all := union n1 n2) in *. set (ls := MAP FST (toAList all)) in *.
  assert (Hdls : ALL_DISTINCT ls) by apply ALL_DISTINCT_MAP_FST_toAList.
  assert (Han1 : is_alloc_var (na1 + 2)) by (apply is_stack_var_flip, Hst1).
  assert (Hokc : ssa_map_ok (na1 + 2) (inter ssa1 all))
    by (apply ssa_map_ok_inter, (ssa_map_ok_more na1); split; [exact Hok1|lia]).
  assert (Hrc : ssa_locals_rel (na1 + 2) (inter ssa1 all) (locals s2) (locals cs2)).
  { apply rel_cut; [exact Hsub| | |].
    - rewrite Hd. unfold all. rewrite domain_union. reflexivity.
    - eapply strong_locals_rel_subset; split; [|exact Hs]. intros x Hx. unfold all in Hx. rewrite domain_union in Hx. exact Hx.
    - intros x Hx. specialize (Hlt' x Hx). lia. }
  assert (Hrc' : ssa_locals_rel (na1 + 2) (inter ssa1 all) (locals s2) (locals (set_var 2 y cs2))).
  { unfold set_var. rewrite locals_set_locals. apply ssa_locals_rel_ignore_insert.
    split; [exact Hokc|split; [exact Hrc|reflexivity]]. }
  pose proof (lnvrm_core s2 (set_var 2 y cs2) (inter ssa1 all) (na1 + 2) ls Hrc') as C2.
  rewrite Erm in C2. destruct (evaluate (rmov, set_var 2 y cs2)) as [r3 c3] eqn:E3.
  destruct C2 as (-> & Hr3 & Hw3 & Hph & _).
  { intros x Hx. apply In_toAList_keys in Hx. rewrite domain_inter. split; [apply Hsub, Hx|exact Hx]. }
  { exact Hdls. } { exact Hokc. } { unfold set_var; eapply word_state_eq_rel_trans; [exact Hw|apply wser_sl]. }
  specialize (Hph ltac:(rewrite is_alloc_var_not_phy by exact Han1; discriminate)).
  destruct (lnvrm_Inv _ _ _ _ _ _ Erm (conj Hokc Han1)) as (Hle2 & Hok2 & Ha2).
  assert (H2 : lookup 2 (locals c3) = Some y)
    by (rewrite Hph by reflexivity; unfold set_var; rewrite locals_set_locals; apply lookup_insert1).
  pose proof (eval_move1 1 na4 2 c3 y H2) as Em.
  destruct (IHh (set_var hn y s2) (set_locals (insert na4 y (locals c3)) c3) (insert hn na4 ssa2) (na4 + 4) lt) as [php Hhp].
  { split; [unfold set_var; apply word_state_eq_rel_locals, Hw3|].
    split; [unfold set_var; rewrite !locals_set_locals|].
    - apply ssa_locals_rel_insert. split; [apply (ssa_locals_rel_more na2); split; [exact Hr3|lia]|].
      split; [apply (ssa_map_ok_more na2); split; [exact Hok2|lia]|lia].
    - split; [apply is_alloc_var_add, Ha4|split; [apply (every_var_lt_mono _ na); [exact Hevhp|lia]|split; [|exact Hlt]]].
      apply ssa_map_ok_extend. split; [apply (ssa_map_ok_more na2); split; [exact Hok2|lia]|].
      rewrite is_alloc_var_not_phy by exact Ha4. discriminate. }
  rewrite Ehp in Hhp. exists php.
  destruct (evaluate (hp, set_permute php (set_var hn y s2))) as [res rst].
  destruct Hhp as [Hhp|Hhp]; [left; exact Hhp|right].
  rewrite (eval_Seq_none _ _ _ _ E3), (eval_Seq_none _ _ _ _ Em). exact Hhp.
Qed.

Lemma seq_fixL (p1 : prog a) prio ssa4 ssa5 na4 na5 cL cR naf ssaf lt (cs rst : state) res :
  fix_inconsistencies prio ssa4 ssa5 na5 = (cL, (cR, (naf, ssaf))) -> is_alloc_var na5 -> ssa_map_ok na4 ssa4 ->
  na4 <= na5 ->
  (let '(res', rcst) := evaluate (p1, cs) in res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na4 ssa4 res rst rcst) ->
  let '(res', rcst) := evaluate (Seq p1 cL, cs) in
  res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naf ssaf res rst rcst.
Proof.
  intros Ef Ha5 Hok4 Hle H. destruct (evaluate (p1, cs)) as [r1 c1] eqn:E1. destruct H as (<- & Hw & Hp).
  rewrite evaluate_Seq_eq', E1. destruct res as [r|].
  - rewrite bd_false' by discriminate. split; [reflexivity|split; [exact Hw|eapply ssa_post_some; [discriminate|exact Hp]]].
  - rewrite bd_true' by reflexivity. cbn [ssa_post] in Hp.
    pose proof (@fix_inconsistencies_correctL a c ffi_t prio na5 ssa4 ssa5
                  (conj Ha5 (ssa_map_ok_more na4 ssa4 na5 (conj Hok4 Hle)))) as FL.
    rewrite Ef in FL. specialize (FL rst c1 (ssa_locals_rel_more na4 ssa4 _ _ na5 (conj Hp Hle))).
    destruct (evaluate (cL, c1)) as [r2 c2]. destruct FL as (-> & Hrel & Hw2).
    split; [reflexivity|split; [eapply word_state_eq_rel_trans; eassumption|exact Hrel]].
Qed.

Lemma seq_fixR (p1 : prog a) prio ssa4 ssa5 na5 cL cR naf ssaf lt (cs rst : state) res :
  fix_inconsistencies prio ssa4 ssa5 na5 = (cL, (cR, (naf, ssaf))) -> is_alloc_var na5 -> ssa_map_ok na5 ssa5 ->
  (let '(res', rcst) := evaluate (p1, cs) in res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt na5 ssa5 res rst rcst) ->
  let '(res', rcst) := evaluate (Seq p1 cR, cs) in
  res = res' /\ word_state_eq_rel rst rcst /\ ssa_post lt naf ssaf res rst rcst.
Proof.
  intros Ef Ha5 Hok5 H. destruct (evaluate (p1, cs)) as [r1 c1] eqn:E1. destruct H as (<- & Hw & Hp).
  rewrite evaluate_Seq_eq', E1. destruct res as [r|].
  - rewrite bd_false' by discriminate. split; [reflexivity|split; [exact Hw|eapply ssa_post_some; [discriminate|exact Hp]]].
  - rewrite bd_true' by reflexivity. cbn [ssa_post] in Hp.
    pose proof (@fix_inconsistencies_correctR a c ffi_t na5 ssa4 ssa5 prio (conj Ha5 Hok5)) as FR.
    rewrite Ef in FR. specialize (FR rst c1 Hp).
    destruct (evaluate (cR, c1)) as [r2 c2]. destruct FR as (-> & Hrel & Hw2).
    split; [reflexivity|split; [eapply word_state_eq_rel_trans; eassumption|exact Hrel]].
Qed.

Lemma stack_moves_eval2 (cs : state) sl L ssa na (n1 n2 : num_set) smov ssa' na' :
  ssa_locals_rel na ssa sl L -> ssa_map_ok na ssa -> is_alloc_var na ->
  (forall x, domain (union n1 n2) x -> domain sl x) ->
  list_next_var_rename_move ssa (na + 2) (MAP FST (toAList (union n1 n2))) = (smov, (ssa', na')) ->
  exists L1, evaluate (smov, set_locals L cs) = (NONE, set_locals L1 cs) /\
    ssa_locals_rel na' ssa' sl L1 /\ ssa_map_ok na' ssa' /\ na + 2 <= na' /\ is_stack_var na' /\
    INJ (option_lookup ssa') (domain n1 UNION domain n2) UNIV /\
    (forall x, domain (union n1 n2) x -> domain ssa' x) /\
    (forall x y, lookup x sl = SOME y -> lookup (THE (lookup x ssa)) L1 = SOME y).
Proof.
  intros Hr Hok Ha Hsub E1. set (ls := MAP FST (toAList (union n1 n2))) in *.
  assert (Hdls : ALL_DISTINCT ls) by apply ALL_DISTINCT_MAP_FST_toAList.
  assert (Hls : forall x, In x ls <-> domain (union n1 n2) x) by (intros x; apply In_toAList_keys).
  assert (Hall_ssa : forall x, In x ls -> domain ssa x).
  { intros x Hx. apply Hls, Hsub in Hx. apply domain_lookup in Hx as [v Hv]. destruct Hr as [_ R2].
    apply (R2 _ _ Hv). }
  pose proof (list_next_var_rename_move_props_2 _ _ _ _ _ _ E1 (conj (or_introl Ha) Hok)) as (Hle1 & Hst1 & _ & Hok1).
  assert (Hle2 : na <= na + 2) by lia.
  pose proof (lnvrm_core (set_locals sl cs) (set_locals L cs) ssa (na + 2) ls
                (ssa_locals_rel_more na ssa sl L (na + 2) (conj Hr Hle2))
                Hall_ssa Hdls (ssa_map_ok_more na ssa (na + 2) (conj Hok Hle2)) (wser_sl' cs L sl)) as C1.
  rewrite E1 in C1. destruct (evaluate (smov, set_locals L cs)) as [r1 c1] eqn:Es1.
  destruct C1 as (-> & Hr1 & _ & _ & Hpres).
  destruct (lnvrm_is_move _ _ _ _ _ E1) as [ms ->].
  pose proof (eval_move_sl _ _ _ _ _ Es1) as Hc1.
  exists (locals c1). split; [f_equal; exact Hc1|split; [exact Hr1|split; [exact Hok1|split; [lia|split; [exact (Hst1 Ha)|split]]]]].
  - eapply INJ_less; split; [exact (lnvrm_inj _ _ _ _ _ _ E1 Hdls)|]. intros x Hx. apply Hls.
    rewrite domain_union. exact Hx.
  - split; [intros x Hx; apply (lnvrm_dom _ _ _ _ _ _ x E1 Hdls), Hls, Hx|exact Hpres].
Qed.

Lemma get_vars_old (args : list N) xs (st cs : state) na ssa L1 :
  get_vars args st = SOME xs -> ssa_locals_rel na ssa (locals st) (locals cs) ->
  (forall x y, lookup x (locals st) = SOME y -> lookup (THE (lookup x ssa)) L1 = SOME y) ->
  get_vars (MAP (option_lookup ssa) args) (set_locals L1 cs) = SOME xs.
Proof.
  intros Hg [_ R2] Hp. revert xs Hg; induction args as [|x args IH]; intros xs Hg; [exact Hg|].
  cbn [get_vars MAP List.map] in *. destruct (get_var x st) as [v|] eqn:Ev; [|discriminate].
  destruct (get_vars args st) as [vs|] eqn:Evs; [|discriminate]. injection Hg as <-.
  unfold get_var in Ev |- *. rewrite locals_set_locals.
  destruct (R2 _ _ Ev) as (Hd & _). apply domain_lookup in Hd as [z Hz].
  assert (E : option_lookup ssa x = THE (lookup x ssa)) by (unfold option_lookup; rewrite Hz; reflexivity).
  rewrite E, (Hp x v Ev). change (List.map (option_lookup ssa) args) with (MAP (option_lookup ssa) args).
  rewrite (IH vs eq_refl). reflexivity.
Qed.

Lemma ssa_Call_Some rv names rh l1 l2 dest args h st cst ssa na lt :
  @ssa_IH a c ffi_t rh -> (match h with Some (_, (p, _)) => @ssa_IH a c ffi_t p | None => True end) ->
  ssa_hyp (Call (Some (rv, (names, (rh, (l1, l2))))) dest args h) st cst ssa na lt ->
  ssa_concl (Call (Some (rv, (names, (rh, (l1, l2))))) dest args h) st cst ssa na lt.
Proof.
  intros IHr IHh (Heq & Hr & Ha & Hev & Hok & Hlt). destruct names as [n1 n2].
  cbn [every_var] in Hev. apply andb_prop in Hev as [Hevargs Hev].
  apply andb_prop in Hev as [Hev Hevh]. apply andb_prop in Hev as [Hev Hevrh].
  apply andb_prop in Hev as [Hevrv Hevn].
  assert (Hnl : forall x, domain (union n1 n2) x -> x < na) by (intros x Hx; exact (every_name_lt n1 n2 na x Hevn Hx)).
  unfold ssa_concl. cbn [ssa_cc_trans FST SND fst snd next_var_rename].
  set (all := union n1 n2) in *. set (ls := MAP FST (toAList all)).
  destruct (list_next_var_rename_move ssa (na + 2) ls) as [smov [ssa1 na1]] eqn:Es.
  destruct (list_next_var_rename_move (inter ssa1 all) (na1 + 2) ls) as [rmov [ssa2 na2]] eqn:Erm.
  destruct (list_next_var_rename rv ssa2 na2) as [ret' [ssa3 na3]] eqn:Erv.
  destruct (ssa_cc_trans rh ssa3 na3 lt) as [rh' [ssa4 na4]] eqn:Erh.
  (* source failures *)
  destruct (get_vars args st) as [xs|] eqn:Eg.
  2:{ exists (permute st). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body]. rewrite Eg.
      destruct h as [[? [? [? ?]]]|]; destr_lets_goal; left; reflexivity. }
  assert (Hpre : forall perm, (cut_envs (n1, n2) (locals st) = NONE) ->
            FST (evaluate (Call (Some (rv, ((n1, n2), (rh, (l1, l2))))) dest args h, set_permute perm st)) = SOME Error).
  { intros perm Ec. rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc]. rewrite get_vars_set_permute, Eg.
    destruct (bad_dest_args dest args); [reflexivity|].
    destruct (find_code _ _ _ _) as [[? [? ?]]|]; [|reflexivity]. cbn [FST fst].
    destruct (_ || _); [reflexivity|]. rewrite locals_set_permute, Ec. reflexivity. }
  destruct (cut_envs (n1, n2) (locals st)) as [[x0 x1]|] eqn:Ec.
  2:{ exists (permute st). specialize (Hpre (permute st) eq_refl).
      destruct (evaluate (Call _ _ _ _, set_permute (permute st) st)) as [r t]. cbn in Hpre. left; exact Hpre. }
  destruct (cut_envs_domain_SUBSET _ _ _ _ Ec) as [Hs1 Hs2].
  assert (Hsub : forall x, domain all x -> domain (locals st) x).
  { intros x Hx. unfold all in Hx. rewrite domain_union in Hx. destruct Hx; [apply Hs1|apply Hs2]; assumption. }
  (* target prefix *)
  destruct (stack_moves_eval2 cst (locals st) (locals cst) ssa na n1 n2 smov ssa1 na1 Hr Hok Ha Hsub Es)
    as (L1 & Es1 & Hr1 & Hok1 & Hle1 & Hst1 & Hinj & Hdom1 & Hpres).
  rewrite set_locals_eta in Es1.
  set (conv := GENLIST (fun x => 2 * (x + 1)) (LENGTH (MAP (option_lookup ssa) args))).
  destruct (GENLIST_rets_props (LENGTH (MAP (option_lookup ssa) args))) as [Hndc Hphc]. fold conv in Hndc, Hphc.
  assert (Hlc : LENGTH conv = LENGTH (MAP (option_lookup ssa) args)) by (unfold conv; apply LENGTH_GENLIST').
  assert (Hlx : LENGTH xs = LENGTH conv)
    by (rewrite Hlc, LENGTH_MAP'; exact (get_vars_length_lemma _ _ _ Eg)).
  assert (Hg1 : get_vars (MAP (option_lookup ssa) args) (set_locals L1 cst) = SOME xs)
    by (exact (get_vars_old args xs st cst na ssa L1 Eg Hr Hpres)).
  set (L2 := alist_insert conv xs L1).
  assert (Em : evaluate (Move 1 (ZIP (conv, MAP (option_lookup ssa) args)), set_locals L1 cst) = (NONE, set_locals L2 cst)).
  { rewrite evaluate_eqn; cbn [evaluate_body]. rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlc.
    rewrite (proj2 (ALL_DISTINCT_iff' conv) Hndc : ALL_DISTINCT conv = true), Hg1. unfold set_vars, L2.
    rewrite sl_sl, locals_set_locals. reflexivity. }
  set (tcs := set_locals L2 cst).
  assert (Hwt : word_state_eq_rel st tcs) by (unfold tcs; eapply word_state_eq_rel_trans; [exact Heq|apply wser_sl]).
  assert (Hgt : get_vars conv tcs = SOME xs).
  { unfold tcs, L2. replace (set_locals (alist_insert conv xs L1) cst) with (set_vars conv xs (set_locals L1 cst))
      by (unfold set_vars; rewrite sl_sl, locals_set_locals; reflexivity).
    apply get_vars_set_vars_eq. split; [apply ALL_DISTINCT_iff', Hndc|exact Hlx]. }
  assert (Hbd : bad_dest_args dest conv = bad_dest_args dest args)
    by (unfold conv; rewrite bad_dest_args_GENLIST, bad_dest_args_MAP; reflexivity).
  set (regs := GENLIST (fun x => 2 * (x + 1)) (LENGTH rv)).
  destruct (GENLIST_rets_props (LENGTH rv)) as [Hndr Hphr]. fold regs in Hndr, Hphr.
  assert (Hlr : LENGTH regs = LENGTH rv) by (unfold regs; apply LENGTH_GENLIST').
  assert (Hdr : ALL_DISTINCT regs = true) by (apply ALL_DISTINCT_iff', Hndr).
  assert (Hrt : ssa_locals_rel na1 ssa1 (locals st) L2).
  { unfold L2. apply (ssa_locals_rel_ignore_list_insert na1 ssa1 st (set_locals L1 cst)).
    rewrite locals_set_locals. split; [exact Hok1|split; [exact Hr1|split; [|lia]]].
    unfold is_true; rewrite EVERY_Forall, Forall_forall. intros y Hy. apply Hphc, Hy. }
  assert (Hst : strong_locals_rel (option_lookup ssa1) (domain n1 UNION domain n2) (locals st) (locals tcs))
    by (unfold tcs; rewrite locals_set_locals; apply (rel_to_strong na1); exact Hrt).
  assert (Hsub1 : forall x, domain (union n1 n2) x -> domain ssa1 x) by exact Hdom1.
  destruct h as [[hn [hp [l1' l2']]]|].
  - (* with an exception handler *)
    cbn [every_var] in Hevh. apply andb_prop in Hevh as [Hevhn Hevhp]. apply ltb_var in Hevhn.
    destruct (ssa_cc_trans hp (insert hn na4 ssa2) (na4 + 4) lt) as [hp' [ssa5 na5]] eqn:Ehp.
    destruct (fix_inconsistencies _ ssa4 ssa5 na5) as [cL [cR [naf ssaf]]] eqn:Ef.
    cbn beta iota zeta. rewrite (eval_Seq_none _ _ _ _ Es1), (eval_Seq_none _ _ _ _ Em).
    assert (Han1 : is_alloc_var (na1 + 2)) by (apply is_stack_var_flip, Hst1).
    assert (Hokc : ssa_map_ok (na1 + 2) (inter ssa1 all))
      by (apply ssa_map_ok_inter, (ssa_map_ok_more na1); split; [exact Hok1|lia]).
    destruct (lnvrm_Inv _ _ _ _ _ _ Erm (conj Hokc Han1)) as (Hle2 & Hok2 & Ha2).
    destruct (lnvr_Inv _ _ _ _ _ _ Erv (conj Hok2 Ha2)) as (Hle3 & Hok3 & Ha3).
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Erh (conj Hok3 Ha3)) as (Hle4 & Ha4 & Hok4).
    assert (Hok4' : ssa_map_ok (na4 + 4) (insert hn na4 ssa2)).
    { apply ssa_map_ok_extend. split; [apply (ssa_map_ok_more na2); split; [exact Hok2|lia]|].
      rewrite is_alloc_var_not_phy by exact Ha4. discriminate. }
    destruct (ssa_cc_trans_props _ _ _ _ _ _ _ Ehp (conj Hok4' (is_alloc_var_add _ Ha4))) as (Hle5 & Ha5 & Hok5).
    destruct (ssa_gcall rv n1 n2 rh l1 l2 dest args (Some (hn, (hp, (l1', l2')))) regs
                (Seq (Seq rmov (Seq (Move 1 (ZIP (ret', regs))) rh')) cL) conv
                (Some (2, (Seq (Seq rmov (Seq (Move 1 [(na4, 2)]) hp')) cR, (l1', l2'))))
                st tcs (option_lookup ssa1) lt naf ssaf xs Hwt Eg Hgt Hbd Hdr Hlr Hinj Hst
                ltac:(cbn; split; reflexivity)) as [perm Hp].
    + intros s1p cs1p ys Hw1 Hsr1 Hd1 Hly Hrvd.
      destruct (ret_cont rh rv n1 n2 ssa1 na1 rmov ssa2 na2 ret' ssa3 na3 rh' ssa4 na4 lt na s1p cs1p ys
                  IHr Hlt Hok1 Hst1 ltac:(lia) Hevrv Hevrh Hsub1 Hnl Erm Erv Erh Hw1 Hsr1 Hd1 Hly Hrvd) as [prh Hrh].
      exists prh. destruct (evaluate (rh, set_permute prh (set_vars rv ys s1p))) as [res rst].
      destruct Hrh as [Hrh|Hrh]; [left; exact Hrh|right].
      exact (seq_fixL _ _ ssa4 ssa5 na4 na5 cL cR naf ssaf lt _ rst res Ef Ha5 Hok4 ltac:(lia) Hrh).
    + intros s2 cs2 y Hw2 Hsr2 Hd2.
      destruct (exc_cont hp hn n1 n2 ssa1 na1 rmov ssa2 na2 na4 hp' ssa5 na5 lt na s2 cs2 y
                  IHh Hlt Hok1 Hst1 ltac:(lia) ltac:(lia) Ha4 Hevhn Hevhp Hsub1 Hnl Erm Ehp Hw2 Hsr2 Hd2) as [php Hhp].
      exists php. destruct (evaluate (hp, set_permute php (set_var hn y s2))) as [res rst].
      destruct Hhp as [Hhp|Hhp]; [left; exact Hhp|right].
      exact (seq_fixR _ _ ssa4 ssa5 na5 cL cR naf ssaf lt _ rst res Ef Ha5 Hok5 Hhp).
    + exists perm. exact Hp.
  - (* no handler *)
    cbn beta iota zeta. rewrite (eval_Seq_none _ _ _ _ Es1), (eval_Seq_none _ _ _ _ Em).
    destruct (ssa_gcall rv n1 n2 rh l1 l2 dest args None regs
                (Seq rmov (Seq (Move 1 (ZIP (ret', regs))) rh')) conv None
                st tcs (option_lookup ssa1) lt na4 ssa4 xs Hwt Eg Hgt Hbd Hdr Hlr Hinj Hst eq_refl) as [perm Hp].
    + intros s1p cs1p ys Hw1 Hsr1 Hd1 Hly Hrvd.
      exact (ret_cont rh rv n1 n2 ssa1 na1 rmov ssa2 na2 ret' ssa3 na3 rh' ssa4 na4 lt na s1p cs1p ys
                  IHr Hlt Hok1 Hst1 ltac:(lia) Hevrv Hevrh Hsub1 Hnl Erm Erv Erh Hw1 Hsr1 Hd1 Hly Hrvd).
    + exact Logic.I.
    + exists perm. exact Hp.
Qed.

Lemma ssa_all : forall p : prog a, @ssa_IH a c ffi_t p.
Proof.
  induction p as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                  |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros st cst ssa na lt.
  - apply ssa_Skip.
  - apply ssa_Move.
  - apply ssa_Inst.
  - apply ssa_Assign.
  - apply ssa_Get.
  - apply ssa_Set.
  - apply ssa_Store.
  - apply ssa_MustTerminate, IH.
  - destruct ret as [[rv [names [rh [l1 l2]]]]|].
    + apply ssa_Call_Some; assumption.
    + apply ssa_Call_None.
  - apply ssa_Seq; assumption.
  - apply ssa_If; assumption.
  - apply ssa_Loop, IH.
  - apply ssa_Alloc.
  - apply ssa_StoreConsts.
  - apply ssa_Raise.
  - apply ssa_Return.
  - apply ssa_Break.
  - apply ssa_Continue.
  - apply ssa_Tick.
  - apply ssa_OpCurrHeap.
  - apply ssa_LocValue.
  - apply ssa_Install.
  - apply ssa_CodeBufferWrite.
  - apply ssa_DataBufferWrite.
  - apply ssa_FFI.
  - apply ssa_ShareInst.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct" *)
Theorem ssa_cc_trans_correct : forall prog (st cst : state) ssa na lt,
  word_state_eq_rel st cst /\
  ssa_locals_rel na ssa (locals st) (locals cst) /\
  is_alloc_var na /\
  every_var (fun x => x <? na) prog /\
  ssa_map_ok na ssa /\
  lt_ok lt ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(prog', (ssa', na')) := ssa_cc_trans prog ssa na lt in
    let '(res', rcst) := evaluate (prog', cst) in
    res = res' /\
    word_state_eq_rel rst rcst /\
    match res with
    | NONE => ssa_locals_rel na' ssa' (locals rst) (locals rcst)
    | SOME (Break n) =>
        match oEL n lt with
        | SOME (tgt_ssa, (_, exit_names)) =>
            strong_locals_rel (option_lookup tgt_ssa) (domain exit_names) (locals rst) (locals rcst)
        | NONE => True
        end
    | SOME (Continue n) =>
        match oEL n lt with
        | SOME (tgt_ssa, (names, _)) =>
            strong_locals_rel (option_lookup tgt_ssa) (domain names) (locals rst) (locals rcst)
        | NONE => True
        end
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros prog st cst ssa na lt H. destruct (ssa_all prog st cst ssa na lt H) as [perm Hp].
  exists perm. destruct (evaluate (prog, set_permute perm st)) as [res rst].
  destruct (decide (res = SOME Error)) as [E|E].
  - rewrite bd_true' by exact E. exact Logic.I.
  - rewrite bd_false' by exact E. destruct Hp as [Hp|Hp]; [contradiction|].
    destruct (ssa_cc_trans prog ssa na lt) as [p' [s' n']]. destruct (evaluate (p', cst)) as [res' rcst].
    destruct Hp as (Hr & Hw & Hpost). split; [exact Hr|split; [exact Hw|]].
    destruct res as [[]|]; cbn [ssa_post] in Hpost; try exact Hpost;
      destruct (oEL _ lt) as [[? [? ?]]|]; exact Hpost.
Qed.

End SSA4.




