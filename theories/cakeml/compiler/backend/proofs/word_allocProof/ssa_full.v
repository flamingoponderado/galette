(** * CakeML [word_allocProof]: full SSA correctness

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    10139-10377): [setup_ssa_props], the [max_var] lemmas,
    [limit_var_props] and [full_ssa_cc_trans_correct].

    Notes: HOL's [every_var (λx. x ≤ m)] is [every_var (fun x => x <=? m)]. *)

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
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang word_alloc.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock locals_rel permute_swap stack_swap code.
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring ssa_props ssa_loop ssa ssa_call.
Open Scope N_scope.

Lemma MAX_LIST_ge x l : In x l -> x <= MAX_LIST l.
Proof.
  induction l as [|y l IH]; intros H; [destruct H|]. cbn [MAX_LIST]. unfold MAX.
  destruct H as [->|H]; [destruct (x <? MAX_LIST l) eqn:E; [apply N.ltb_lt in E|]; lia|].
  specialize (IH H). destruct (y <? MAX_LIST l) eqn:E; [lia|apply N.ltb_ge in E; lia].
Qed.

Lemma MAX_ge_l m n : m <= MAX m n.
Proof. unfold MAX. destruct (m <? n) eqn:E; [apply N.ltb_lt in E|]; lia. Qed.
Lemma MAX_ge_r m n : n <= MAX m n.
Proof. unfold MAX. destruct (m <? n) eqn:E; [|apply N.ltb_ge in E]; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "max3_eq" *)
Theorem max3_eq : forall x y z, max3 x y z = MAX x (MAX y z).
Proof.
  intros x y z. unfold max3, MAX.
  destruct (N.ltb_spec y x); destruct (N.ltb_spec x z); destruct (N.ltb_spec y z); cbn beta iota;
  repeat match goal with |- context [?u <? ?v] => destruct (N.ltb_spec u v); cbn beta iota end; lia.
Qed.

Section Full.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma EVERY_le_MAX_LIST l m : MAX_LIST l <= m -> is_true (EVERY (fun x => x <=? m) l).
Proof.
  intros H. unfold is_true. rewrite EVERY_Forall, Forall_forall. intros x Hx.
  apply N.leb_le. pose proof (MAX_LIST_ge x l Hx). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "max_var_exp_max" *)
Theorem max_var_exp_max : forall (exp : exp a), every_var_exp (fun x => x <=? max_var_exp exp) exp.
Proof.
  enough (G : forall (exp : wordLang.exp a) m, max_var_exp exp <= m -> is_true (every_var_exp (fun x => x <=? m) exp))
    by (intros exp; apply G; lia).
  intros exp; induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros m Hm; cbn [every_var_exp max_var_exp] in *; try reflexivity.
  - apply N.leb_le; exact Hm.
  - apply IH, Hm.
  - unfold is_true. rewrite EVERY_Forall, Forall_forall. rewrite Forall_forall in IH. intros e He.
    apply IH; [exact He|]. pose proof (MAX_LIST_ge (max_var_exp e) (MAP max_var_exp es) (in_map _ _ _ He)). lia.
  - apply andb_true_intro; split; [apply IH1|apply IH2]; pose proof (MAX_ge_l (max_var_exp e1) (max_var_exp e2));
      pose proof (MAX_ge_r (max_var_exp e1) (max_var_exp e2)); lia.
Qed.

Lemma every_var_exp_le (e : exp a) m : max_var_exp e <= m -> is_true (every_var_exp (fun x => x <=? m) e).
Proof.
  intros H. apply (every_var_exp_mono (fun x => x <=? max_var_exp e)). split; [|apply max_var_exp_max].
  intros x Hx. unfold is_true in *. apply N.leb_le in Hx. apply N.leb_le. lia.
Qed.

Ltac mx_le := first [ apply N.le_refl
                    | (eapply N.le_trans; [|apply MAX_ge_l]; mx_le)
                    | (eapply N.le_trans; [|apply MAX_ge_r]; mx_le) ].
Ltac mx := apply N.leb_le; mx_le.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "max_var_inst_max" *)
Theorem max_var_inst_max : forall (inst : asm.inst a), every_var_inst (fun x => x <=? max_var_inst inst) inst.
Proof.
  intros i. destruct_inst i; cbn [every_var_inst max_var_inst every_var_imm]; rewrite ?max3_eq;
    try (destruct (dimindex a =? 64)); unfold is_true; rewrite ?andb_true_iff; repeat split; try reflexivity; mx.
Qed.

Lemma EVERY_le_In l m : (forall x, In x l -> x <= m) -> is_true (EVERY (fun x => x <=? m) l).
Proof. intros H. unfold is_true. rewrite EVERY_Forall, Forall_forall. intros x Hx. apply N.leb_le, H, Hx. Qed.

Ltac sub_le :=
  first [ apply N.le_refl
        | (rewrite max3_eq; sub_le)
        | (eapply N.le_trans; [|apply MAX_ge_l]; sub_le)
        | (eapply N.le_trans; [|apply MAX_ge_r]; sub_le)
        | (apply MAX_LIST_ge; cbn [In]; tauto)
        | (eapply N.le_trans; [|apply MAX_LIST_ge; cbn [In]; left; reflexivity]; sub_le)
        | (eapply N.le_trans; [|apply MAX_LIST_ge; cbn [In]; right; left; reflexivity]; sub_le)
        | (eapply N.le_trans; [|apply MAX_LIST_ge; cbn [In]; right; right; left; reflexivity]; sub_le)
        | (eapply N.le_trans; [|apply MAX_LIST_ge; cbn [In]; right; right; right; left; reflexivity]; sub_le)
        | (eapply N.le_trans; [|apply MAX_LIST_ge; cbn [In]; right; right; right; right; left; reflexivity]; sub_le) ].

Lemma every_name_le (n1 n2 : num_set) m :
  cutsets_max (n1, n2) <= m -> is_true (every_name (fun x => x <=? m) (n1, n2)).
Proof.
  unfold cutsets_max, every_name. cbn [FST SND fst snd]. intros H. apply andb_true_intro. split;
    apply EVERY_le_In; intros x Hx; (eapply N.le_trans; [apply MAX_LIST_ge, Hx|]); (eapply N.le_trans; [|exact H]); sub_le.
Qed.

Lemma max_var_le : forall (p : prog a) m, max_var p <= m -> is_true (every_var (fun x => x <=? m) p).
Proof.
  intros p; induction p as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                  |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros m Hm; cbn [every_var max_var] in *; unfold is_true; rewrite ?andb_true_iff;
    repeat match goal with |- _ /\ _ => split end;
    try reflexivity;
    try (apply N.leb_le; eapply N.le_trans; [|exact Hm]; sub_le; fail);
    try (apply every_var_exp_le; eapply N.le_trans; [|exact Hm]; sub_le; fail);
    try (apply EVERY_le_In; intros x Hx; eapply N.le_trans; [|exact Hm];
         eapply N.le_trans; [apply MAX_LIST_ge|]; [cbn [In]; first [apply in_or_app; tauto|tauto]|sub_le]; fail);
    try (apply IH; eapply N.le_trans; [|exact Hm]; sub_le; fail);
    try (apply IH1; eapply N.le_trans; [|exact Hm]; sub_le; fail);
    try (apply IH2; eapply N.le_trans; [|exact Hm]; sub_le; fail).
  - apply EVERY_le_In; intros x Hx. eapply N.le_trans; [|exact Hm]. apply MAX_LIST_ge, in_or_app; left; exact Hx.
  - apply EVERY_le_In; intros x Hx. eapply N.le_trans; [|exact Hm]. apply MAX_LIST_ge, in_or_app; right; exact Hx.
  - apply (every_var_inst_mono (fun x => x <=? max_var_inst i)). split; [|apply max_var_inst_max].
    intros x Hx. unfold is_true in *. apply N.leb_le in Hx. apply N.leb_le. lia.
  - apply EVERY_le_In; intros x Hx. eapply N.le_trans; [apply MAX_LIST_ge, Hx|]. eapply N.le_trans; [|exact Hm].
    destruct ret as [[v [[c1 c2] [rh [l1 l2]]]]|]; [destruct h as [[hv [hp [l1' l2']]]|]|]; cbv zeta; sub_le.
  - destruct ret as [[v [[c1 c2] [rh [l1 l2]]]]|]; [|reflexivity]. cbv zeta in Hm.
    rewrite !andb_true_iff. repeat match goal with |- _ /\ _ => split end.
    + apply EVERY_le_In; intros x Hx. eapply N.le_trans; [apply MAX_LIST_ge, Hx|]. eapply N.le_trans; [|exact Hm].
      destruct h as [[hv [hp [l1' l2']]]|]; sub_le.
    + apply every_name_le. eapply N.le_trans; [|exact Hm]. destruct h as [[hv [hp [l1' l2']]]|]; sub_le.
    + apply IHr. eapply N.le_trans; [|exact Hm]. destruct h as [[hv [hp [l1' l2']]]|]; sub_le.
    + destruct h as [[hv [hp [l1' l2']]]|]; [|reflexivity]. rewrite andb_true_iff. split.
      * apply N.leb_le. eapply N.le_trans; [|exact Hm]. sub_le.
      * apply IHh. eapply N.le_trans; [|exact Hm]. sub_le.
  - apply N.leb_le. eapply N.le_trans; [|exact Hm]. destruct ri; sub_le.
  - destruct ri as [r2|w]; [|reflexivity]. cbn [every_var_imm]. apply N.leb_le. eapply N.le_trans; [|exact Hm]. sub_le.
  - apply EVERY_le_In; intros x Hx. eapply N.le_trans; [apply MAX_LIST_ge, Hx|]. eapply N.le_trans; [|exact Hm]. sub_le.
  - apply EVERY_le_In; intros x Hx. eapply N.le_trans; [apply MAX_LIST_ge, Hx|]. eapply N.le_trans; [|exact Hm]. sub_le.
  - destruct names as [c1 c2]. apply every_name_le. eapply N.le_trans; [|exact Hm]. sub_le.
  - apply EVERY_le_In; intros x Hx. eapply N.le_trans; [|exact Hm]. apply MAX_LIST_ge. right; exact Hx.
  - destruct names as [c1 c2]. apply every_name_le. eapply N.le_trans; [|exact Hm]. sub_le.
  - destruct names as [c1 c2]. apply every_name_le. eapply N.le_trans; [|exact Hm]. sub_le.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "max_var_max" *)
Theorem max_var_max : forall (prog : prog a), every_var (fun x => x <=? max_var prog) prog.
Proof. intros prog; apply max_var_le; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "limit_var_props" *)
Theorem limit_var_props : forall (prog : prog a) lim,
  limit_var prog = lim -> is_alloc_var lim /\ every_var (fun x => x <? lim) prog.
Proof.
  intros prog lim <-. unfold limit_var. cbv zeta. set (x := max_var prog). split.
  - unfold is_alloc_var. apply N.eqb_eq. pose proof (N.div_mod x 4 ltac:(lia)) as E.
    pose proof (N.mod_lt x 4 ltac:(lia)) as Hlt.
    replace (x + (4 - x mod 4) + 1) with (1 + (x / 4 + 1) * 4) by lia.
    rewrite N.Div0.mod_add. reflexivity.
  - apply (every_var_mono (fun y => y <=? x)). split; [|apply max_var_max].
    intros y Hy. unfold is_true in *. apply N.leb_le in Hy. apply N.ltb_lt. lia.
Qed.

Lemma even_list_props n :
  NoDup (even_list n) /\ forall x, In x (even_list n) -> is_phy_var x = true.
Proof.
  unfold even_list. split.
  - apply ALL_DISTINCT_iff', ALL_DISTINCT_GENLIST. intros; lia.
  - intros y Hy. apply In_GENLIST_iff in Hy as (i & _ & ->). unfold is_phy_var. apply N.eqb_eq.
    replace (2 * i) with (0 + i * 2) by lia. rewrite N.Div0.mod_add. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "setup_ssa_props" *)
Theorem setup_ssa_props : forall lim (st : state) n (prog : prog a),
  is_alloc_var lim /\ domain (locals st) = set (even_list n) ->
  let '(mov, (ssa, na)) := setup_ssa n lim prog in
  let '(res, cst) := evaluate (mov, st) in
  res = NONE /\
  word_state_eq_rel st cst /\
  ssa_map_ok na ssa /\
  ssa_locals_rel na ssa (locals st) (locals cst) /\
  is_alloc_var na /\
  lim <= na.
Proof.
  intros lim st n prog [Ha Hd]. unfold setup_ssa. set (args := even_list n).
  destruct (even_list_props n) as [Hnd Hph]. fold args in Hnd, Hph.
  assert (Hda : ALL_DISTINCT args) by (apply ALL_DISTINCT_iff', Hnd).
  destruct (list_next_var_rename args LN lim) as [nl [ssa' na']] eqn:E.
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E) as (Hdn & _ & _).
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E Hda) as (Hm & Hdom & _ & Hex).
  assert (Hin : forall x, In x args <-> domain (locals st) x).
  { intros x. rewrite Hd. symmetry. apply (IN_set x args). }
  destruct (get_vars_exists' args st) as [vs Hvs].
  { intros x Hx. apply domain_lookup, Hin, Hx. }
  assert (Hlen : LENGTH nl = LENGTH args) by (rewrite Hm, LENGTH_MAP'; reflexivity).
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlen.
  rewrite Hdn, Hvs.
  assert (Hok0 : ssa_map_ok lim (LN : num_map N)) by (intros x y Hx; cbn in Hx; discriminate Hx).
  destruct (lnvr_Inv _ _ _ _ _ _ E (conj Hok0 Ha)) as (Hle & Hok & Ha').
  set (f := fun x => THE (lookup x ssa')) in Hm.
  assert (Hndf : NoDup (List.map f args)) by (apply ALL_DISTINCT_iff'; rewrite <- Hm; exact Hdn).
  assert (Hvs' : get_vars (MAP (fun x => x) args) st = Some vs) by (rewrite map_id; exact Hvs).
  assert (K : forall x, In x args -> lookup (f x) (alist_insert nl vs (locals st)) = lookup x (locals st)).
  { intros x Hx. rewrite Hm. apply (alist_insert_map_lookup f (fun x => x) args vs st); assumption. }
  split; [reflexivity|split; [unfold set_vars; apply wser_sl|split; [exact Hok|split; [|split; [exact Ha'|exact Hle]]]]].
  unfold set_vars. rewrite locals_set_locals. split.
  - intros x y Hxy. assert (Hx : In x args).
    { assert (Hd' : domain ssa' x) by (apply domain_lookup; eauto). rewrite Hdom in Hd'.
      destruct Hd' as [Hd'|Hd']; [cbn [domain] in Hd'; contradiction|]. apply IN_set, Hd'. }
    assert (Ef : f x = y) by (unfold f; rewrite Hxy; reflexivity).
    apply domain_lookup. rewrite <- Ef, K by exact Hx. apply domain_lookup, Hin, Hx.
  - intros x v Hxv. assert (Hx : In x args) by (apply Hin, domain_lookup; eauto).
    split; [rewrite Hdom; right; apply IN_set, Hx|split].
    + change (THE (lookup x ssa')) with (f x). rewrite K by exact Hx. exact Hxv.
    + intros Hal. exfalso. specialize (Hph x Hx). rewrite is_alloc_var_not_phy in Hph by exact Hal. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "full_ssa_cc_trans_correct" *)
Theorem full_ssa_cc_trans_correct : forall (prog : prog a) (st : state) n,
  domain (locals st) = set (even_list n) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res', rcst) := evaluate (full_ssa_cc_trans n prog, st) in
    res = res' /\
    word_state_eq_rel rst rcst /\
    match res with
    | NONE => True
    | SOME (Break _) => True
    | SOME (Continue _) => True
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros prog st n Hd. unfold full_ssa_cc_trans. cbv zeta.
  destruct (limit_var_props prog (limit_var prog) eq_refl) as [Ha Hev].
  pose proof (setup_ssa_props (limit_var prog) st n prog (conj Ha Hd)) as S.
  destruct (setup_ssa n (limit_var prog) prog) as [mov [ssa na]].
  destruct (evaluate (mov, st)) as [r cst] eqn:Em.
  destruct S as (-> & Hw & Hok & Hr & Ha' & Hle).
  destruct (ssa_cc_trans_correct prog st cst ssa na [])
    as [perm Hp].
  { split; [exact Hw|split; [exact Hr|split; [exact Ha'|split; [|split; [exact Hok|reflexivity]]]]].
    apply (every_var_mono (fun x => x <? limit_var prog)). split; [|exact Hev].
    intros x Hx. unfold is_true in *. apply N.ltb_lt in Hx. apply N.ltb_lt. lia. }
  exists perm. destruct (evaluate (prog, set_permute perm st)) as [res rst].
  destruct (bool_decide _); [exact Logic.I|].
  destruct (ssa_cc_trans prog ssa na []) as [p' [s' n']].
  rewrite (eval_Seq_none _ _ _ _ Em). destruct (evaluate (p', cst)) as [res' rcst].
  destruct Hp as (Hres & Hw' & Hpost). split; [exact Hres|split; [exact Hw'|]].
  destruct res as [[]|]; auto.
Qed.

End Full.
