(** * CakeML [word_allocProof]: SSA invariants and auxiliary lemmas

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    4506-6212): [ssa_locals_rel], [ssa_map_ok], the lemmas on
    [list_next_var_rename], [merge_moves], [fake_moves],
    [fix_inconsistencies], [list_next_var_rename_move] and
    [ssa_cc_trans_props].

    Notes:
    - HOL's [let (a,b,c) = f x in P] is [let '(a, (b, c)) := f x in P]
      (HOL tuples nest to the right); HOL [s with locals := l] is
      [set_locals l s].
    - HOL's free variables (e.g. [prio], [st], [cst]) are quantified
      explicitly.
    - [is_phy_var], [is_alloc_var], [is_stack_var] are booleans. *)

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
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring.
Open Scope N_scope.

(** ** Galette-only arithmetic facts on the variable conventions *)

Lemma is_alloc_var_add4 n : is_alloc_var n = true -> is_alloc_var (n + 4) = true.
Proof.
  unfold is_alloc_var; rewrite !N.eqb_eq; intros H.
  rewrite N.Div0.add_mod, H; reflexivity.
Qed.

Lemma is_alloc_var_not_phy n : is_alloc_var n = true -> is_phy_var n = false.
Proof.
  unfold is_alloc_var, is_phy_var; rewrite N.eqb_eq; intros H.
  apply N.eqb_neq; intros H2.
  pose proof (N.div_mod n 4 ltac:(lia)) as E. rewrite H in E.
  pose proof (N.div_mod n 2 ltac:(lia)) as E2. rewrite H2 in E2. lia.
Qed.

Lemma lookup_insert' {A} k2 (v : A) t k1 :
  lookup k1 (insert k2 v t) = if decide (k1 = k2) then Some v else lookup k1 t.
Proof. apply lookup_insert. Qed.

Ltac dec_eq := repeat match goal with
  | |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst
  | H : context [decide (?x = ?y)] |- _ => destruct (decide (x = y)); subst
  end.

Section SSA1.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma sl_sl l l' (s : state) : set_locals l (set_locals l' s) = set_locals l s.
Proof. destruct s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_def" *)
Definition ssa_locals_rel {A} (na : N) (ssa : num_map N) (st_locs cst_locs : num_map A) : Prop :=
  (forall x y, lookup x ssa = SOME y -> y IN domain cst_locs) /\
  (forall x y, lookup x st_locs = SOME y ->
     x IN domain ssa /\ lookup (THE (lookup x ssa)) cst_locs = SOME y /\
     (is_alloc_var x -> x < na)).

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_def" *)
Definition ssa_map_ok (na : N) (ssa : num_map N) : Prop :=
  forall x y, lookup x ssa = SOME y -> ~ is_phy_var y /\ y < na.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_lemma_1" *)
Theorem list_next_var_rename_lemma_1 : forall ls ssa na ls' ssa' na',
  list_next_var_rename ls ssa na = (ls', (ssa', na')) ->
  let len := LENGTH ls in
  ALL_DISTINCT ls' /\
  ls' = MAP (fun x => 4 * x + na) (COUNT_LIST len) /\
  na' = na + 4 * len.
Proof.
  induction ls as [|h ls IH]; intros ssa na ls' ssa' na' H; cbn [list_next_var_rename next_var_rename] in H.
  - injection H as <- <- <-. cbn. split; [reflexivity|split; [reflexivity|lia]].
  - destruct (list_next_var_rename ls (insert h na ssa) (na + 4)) as [ys [s2 n2]] eqn:E.
    injection H as <- <- <-. destruct (IH _ _ _ _ _ E) as (Hd & -> & ->).
    cbv zeta. cbn [LENGTH]. rewrite (proj2 (COUNT_LIST_def _)).
    assert (Hm : MAP (fun x => 4 * x + na) (0 :: MAP N.succ (COUNT_LIST (LENGTH ls))) =
                 na :: MAP (fun x => 4 * x + (na + 4)) (COUNT_LIST (LENGTH ls))).
    { cbn [MAP List.map]. replace (4 * 0 + na) with na by lia. f_equal. rewrite List.map_map. apply List.map_ext; intros; lia. }
    rewrite Hm. split; [|split; [reflexivity|lia]].
    cbn [ALL_DISTINCT]. rewrite Hd, Bool.andb_true_r. apply Bool.negb_true_iff.
    destruct (MEM na _) eqn:Em; [|reflexivity]. apply MEM_iff' in Em.
    apply in_map_iff in Em as [x [Ex _]]. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_lemma_2" *)
Theorem list_next_var_rename_lemma_2 : forall ls ssa na,
  ALL_DISTINCT ls ->
  let '(ls', (ssa', na')) := list_next_var_rename ls ssa na in
  ls' = MAP (fun x => THE (lookup x ssa')) ls /\
  domain ssa' = domain ssa UNION set ls /\
  (forall x, ~ MEM x ls -> lookup x ssa' = lookup x ssa) /\
  (forall x, MEM x ls -> exists y, lookup x ssa' = SOME y).
Proof.
  induction ls as [|h ls IH]; intros ssa na Hd; cbn [list_next_var_rename next_var_rename].
  - split; [reflexivity|split; [|split; [reflexivity|intros x Hx; discriminate Hx]]].
    apply set_ext; intros x; set_simp; tauto.
  - cbn [ALL_DISTINCT] in Hd. apply andb_prop in Hd as [Hh Hd].
    specialize (IH (insert h na ssa) (na + 4) Hd).
    destruct (list_next_var_rename ls (insert h na ssa) (na + 4)) as [ys [s2 n2]] eqn:E.
    destruct IH as (-> & Hdom & Hn & Hm).
    assert (Hh' : ~ In h ls) by (rewrite <- MEM_iff'; destruct (MEM h ls); [discriminate|discriminate]).
    split; [|split; [|split]].
    + cbn [MAP List.map]. f_equal. rewrite Hn by (rewrite MEM_iff'; exact Hh').
      rewrite lookup_insert1. reflexivity.
    + rewrite Hdom, domain_insert. apply set_ext; intros x; set_simp; tauto.
    + intros x Hx. rewrite MEM_iff' in Hx. cbn [In] in Hx.
      rewrite Hn by (rewrite MEM_iff'; tauto). rewrite lookup_insert'. dec_eq; [tauto|reflexivity].
    + intros x Hx. rewrite MEM_iff' in Hx. destruct Hx as [<-|Hx].
      * rewrite Hn by (rewrite MEM_iff'; exact Hh'). rewrite lookup_insert1. eauto.
      * apply Hm, MEM_iff', Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_lemma_2'" *)
Theorem list_next_var_rename_lemma_2' : forall ls ssa na ls' ssa' na',
  list_next_var_rename ls ssa na = (ls', (ssa', na')) ->
  ALL_DISTINCT ls ->
  ls' = MAP (fun x => THE (lookup x ssa')) ls /\
  domain ssa' = domain ssa UNION set ls /\
  (forall x, ~ MEM x ls -> lookup x ssa' = lookup x ssa) /\
  (forall x, MEM x ls -> exists y, lookup x ssa' = SOME y).
Proof.
  intros ls ssa na ls' ssa' na' E Hd. pose proof (list_next_var_rename_lemma_2 ls ssa na Hd) as H.
  rewrite E in H. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_get_var" *)
Theorem ssa_locals_rel_get_var : forall na ssa (st cst : state) n x,
  ssa_locals_rel na ssa (locals st) (locals cst) /\ get_var n st = SOME x ->
  get_var (option_lookup ssa n) cst = SOME x.
Proof.
  intros na ssa st cst n x [[_ H] Hg]. unfold get_var in *.
  destruct (H _ _ Hg) as (Hd & Hl & _). unfold option_lookup.
  apply domain_lookup in Hd as [v Hv]. rewrite Hv in Hl |- *. exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_get_vars" *)
Theorem ssa_locals_rel_get_vars : forall ls y na ssa (st cst : state),
  ssa_locals_rel na ssa (locals st) (locals cst) /\ get_vars ls st = SOME y ->
  get_vars (MAP (option_lookup ssa) ls) cst = SOME y.
Proof.
  induction ls as [|h ls IH]; intros y na ssa st cst [Hr Hg]; cbn [get_vars MAP List.map] in *; [exact Hg|].
  destruct (get_var h st) as [v|] eqn:Ev; [|discriminate].
  destruct (get_vars ls st) as [vs|] eqn:Evs; [|discriminate]. injection Hg as <-.
  rewrite (ssa_locals_rel_get_var na ssa st cst h v (conj Hr Ev)).
  change (List.map (option_lookup ssa) ls) with (MAP (option_lookup ssa) ls).
  rewrite (IH vs na ssa st cst (conj Hr Evs)). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_extend" *)
Theorem ssa_map_ok_extend : forall na ssa h,
  ssa_map_ok na ssa /\ ~ is_phy_var na -> ssa_map_ok (na + 4) (insert h na ssa).
Proof.
  intros na ssa h [H Hp] x y Hl. rewrite lookup_insert' in Hl. dec_eq.
  - injection Hl as <-. split; [exact Hp|lia].
  - destruct (H _ _ Hl) as [H1 H2]. split; [exact H1|lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_more" *)
Theorem ssa_map_ok_more : forall na ssa na',
  ssa_map_ok na ssa /\ na <= na' -> ssa_map_ok na' ssa.
Proof. intros na ssa na' [H Hle] x y Hl. destruct (H _ _ Hl). split; [assumption|lia]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_more" *)
Theorem ssa_locals_rel_more : forall {A} na ssa (stlocs cstlocs : num_map A) na',
  ssa_locals_rel na ssa stlocs cstlocs /\ na <= na' ->
  ssa_locals_rel na' ssa stlocs cstlocs.
Proof.
  intros A na ssa stlocs cstlocs na' [[H1 H2] Hle]. split; [exact H1|].
  intros x y Hl. destruct (H2 _ _ Hl) as (? & ? & H3). split; [assumption|split; [assumption|]].
  intros Ha; specialize (H3 Ha); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_eq_rel_swap" *)
Theorem ssa_eq_rel_swap : forall {A} na ssaL ssaR (st cst : num_map A),
  ssa_locals_rel na ssaR st cst /\ domain ssaL = domain ssaR /\
  (forall x, lookup x ssaL = lookup x ssaR) ->
  ssa_locals_rel na ssaL st cst.
Proof.
  intros A na ssaL ssaR st cst ([H1 H2] & Hd & Hl). split.
  - intros x y Hx. rewrite Hl in Hx. eapply H1; exact Hx.
  - intros x y Hx. rewrite Hd, Hl. apply H2, Hx.
Qed.

(** Swapping the two sides (Galette-only). *)
Definition swap_prio (p : option (unit + unit)) : option (unit + unit) :=
  match p with None => None | Some (inl tt) => Some (inr tt) | Some (inr tt) => Some (inl tt) end.

Lemma priority_swap p b : priority (swap_prio p) b = priority p (negb b).
Proof. destruct p as [[[]|[]]|]; destruct b; reflexivity. Qed.

Lemma merge_moves_swap : forall ls ssaL ssaR na,
  merge_moves ls ssaR ssaL na =
  let '(mL, (mR, (n', (sL, sR)))) := merge_moves ls ssaL ssaR na in (mR, (mL, (n', (sR, sL)))).
Proof.
  induction ls as [|h ls IH]; intros ssaL ssaR na; [reflexivity|]. cbn [merge_moves].
  rewrite IH. destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  destruct (lookup h sL) as [x|], (lookup h sR) as [y|]; try reflexivity.
  destruct (x =? y) eqn:Exy; rewrite N.eqb_sym, Exy; reflexivity.
Qed.

Lemma fake_moves_swap : forall prio ls ssaL ssaR na,
  @fake_moves a (swap_prio prio) ls ssaR ssaL na =
  let '(mL, (mR, (n', (sL, sR)))) := @fake_moves a prio ls ssaL ssaR na in (mR, (mL, (n', (sR, sL)))).
Proof.
  intros prio; induction ls as [|h ls IH]; intros ssaL ssaR na; [reflexivity|]. cbn [fake_moves].
  rewrite IH. destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  rewrite !priority_swap. cbn [negb].
  destruct (lookup h sL) as [x|], (lookup h sR) as [y|]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_frame" *)
Theorem merge_moves_frame : forall ls na ssaL ssaR,
  is_alloc_var na ->
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := merge_moves ls ssaL ssaR na in
  is_alloc_var na' /\ na <= na' /\
  (ssa_map_ok na ssaL -> ssa_map_ok na' ssaL') /\
  (ssa_map_ok na ssaR -> ssa_map_ok na' ssaR').
Proof.
  induction ls as [|h ls IH]; intros na ssaL ssaR Ha; cbn [merge_moves].
  - split; [exact Ha|split; [lia|split; auto]].
  - specialize (IH na ssaL ssaR Ha).
    destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct IH as (Ha' & Hle & HL & HR).
    destruct (lookup h sL) as [x|], (lookup h sR) as [y|]; try (split; [exact Ha'|split; [lia|split; auto]]).
    destruct (x =? y); [split; [exact Ha'|split; [lia|split; auto]]|].
    pose proof (is_alloc_var_not_phy _ Ha') as Hp.
    split; [apply is_alloc_var_add4, Ha'|split; [lia|split]];
      intros H; apply ssa_map_ok_extend; split; auto; rewrite Hp; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_fst" *)
Theorem merge_moves_fst : forall ls na ssaL ssaR,
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := merge_moves ls ssaL ssaR na in
  na <= na' /\
  EVERY (fun x => bool_decide (x < na' /\ x >= na)) (MAP FST moveL) /\
  EVERY (fun x => bool_decide (x < na' /\ x >= na)) (MAP FST moveR).
Proof.
  induction ls as [|h ls IH]; intros na ssaL ssaR; cbn [merge_moves].
  - split; [lia|split; reflexivity].
  - specialize (IH na ssaL ssaR).
    destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct IH as (Hle & HL & HR).
    destruct (lookup h sL) as [x|], (lookup h sR) as [y|]; try (split; [lia|split; assumption]).
    destruct (x =? y); [split; [lia|split; assumption]|].
    unfold is_true in *. rewrite !EVERY_Forall, !Forall_forall in *.
    split; [lia|split]; cbn [MAP List.map In FST fst]; intros z Hz; apply bool_decide_spec;
      (destruct Hz as [<-|Hz]; [lia|]).
    + specialize (HL z Hz); apply bool_decide_spec in HL; lia.
    + specialize (HR z Hz); apply bool_decide_spec in HR; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_frame2" *)
Theorem merge_moves_frame2 : forall ls na ssaL ssaR,
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := merge_moves ls ssaL ssaR na in
  domain ssaL' = domain ssaL /\ domain ssaR' = domain ssaR /\
  forall x, MEM x ls /\ x IN domain (inter ssaL ssaR) -> lookup x ssaL' = lookup x ssaR'.
Proof.
  induction ls as [|h ls IH]; intros na ssaL ssaR; cbn [merge_moves].
  - split; [reflexivity|split; [reflexivity|intros x [Hx _]; discriminate Hx]].
  - specialize (IH na ssaL ssaR).
    destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct IH as (HdL & HdR & Hl).
    assert (Hin : forall x, x IN domain (inter ssaL ssaR) -> x IN domain sL /\ x IN domain sR)
      by (intros x Hx; rewrite HdL, HdR; rewrite domain_inter in Hx; exact Hx).
    destruct (lookup h sL) as [x|] eqn:EL, (lookup h sR) as [y|] eqn:ER;
      try (split; [assumption|split; [assumption|]]; intros z [Hz Hz2]; rewrite MEM_iff' in Hz; cbn [In] in Hz;
           destruct Hz as [<-|Hz]; [destruct (Hin _ Hz2) as [H1 H2]; apply domain_lookup in H1 as [? ?];
             apply domain_lookup in H2 as [? ?]; congruence|apply Hl; rewrite MEM_iff'; auto]).
    destruct (x =? y) eqn:Exy.
    + apply N.eqb_eq in Exy; subst y.
      split; [assumption|split; [assumption|]]. intros z [Hz Hz2]. rewrite MEM_iff' in Hz; cbn [In] in Hz.
      destruct Hz as [<-|Hz]; [congruence|apply Hl; rewrite MEM_iff'; auto].
    + split; [|split].
      * rewrite domain_insert, HdL. apply set_ext; intros z; split; [intros [->|Hz]; [|exact Hz]|intros; right; assumption].
        rewrite <- HdL. apply domain_lookup; eauto.
      * rewrite domain_insert, HdR. apply set_ext; intros z; split; [intros [->|Hz]; [|exact Hz]|intros; right; assumption].
        rewrite <- HdR. apply domain_lookup; eauto.
      * intros z [Hz Hz2]. rewrite !lookup_insert'. dec_eq; [reflexivity|].
        rewrite MEM_iff' in Hz; cbn [In] in Hz. destruct Hz as [Hz|Hz]; [congruence|].
        apply Hl; rewrite MEM_iff'; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_frame3" *)
Theorem merge_moves_frame3 : forall ls na ssaL ssaR,
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := merge_moves ls ssaL ssaR na in
  forall x, ~ MEM x ls \/ ~ x IN domain (inter ssaL ssaR) ->
    lookup x ssaL' = lookup x ssaL /\ lookup x ssaR' = lookup x ssaR.
Proof.
  induction ls as [|h ls IH]; intros na ssaL ssaR; cbn [merge_moves].
  - intros; split; reflexivity.
  - pose proof (merge_moves_frame2 ls na ssaL ssaR) as F2. specialize (IH na ssaL ssaR).
    destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct F2 as (HdL & HdR & _).
    assert (IH' : forall x, ~ MEM x (h :: ls) \/ ~ x IN domain (inter ssaL ssaR) ->
              lookup x sL = lookup x ssaL /\ lookup x sR = lookup x ssaR).
    { intros x Hx; apply IH. destruct Hx as [Hx|Hx]; [left|right; exact Hx].
      rewrite MEM_iff' in *; cbn [In] in Hx; tauto. }
    destruct (lookup h sL) as [x|] eqn:EL, (lookup h sR) as [y|] eqn:ER; try exact IH'.
    destruct (x =? y); [exact IH'|].
    intros z Hz. rewrite !lookup_insert'. dec_eq; [|apply IH', Hz].
    exfalso. destruct Hz as [Hz|Hz].
    + apply Hz; rewrite MEM_iff'; left; reflexivity.
    + apply Hz. rewrite domain_inter. split; [rewrite <- HdL|rewrite <- HdR]; apply domain_lookup; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "mov_eval_head" *)
Theorem mov_eval_head : forall p moves (st rst : state) x y,
  evaluate (Move p moves, st) = (NONE, rst) /\
  y IN domain (locals st) /\
  ~ MEM y (MAP FST moves) /\
  ~ MEM x (MAP FST moves) ->
  evaluate (Move p ((x, y) :: moves), st) =
    (NONE, set_locals (insert x (THE (lookup y (locals st))) (locals rst)) rst).
Proof.
  intros p moves st rst x y (Hev & Hy & _ & Hx).
  rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
  cbn [MAP List.map ALL_DISTINCT FST SND get_vars].
  destruct (ALL_DISTINCT (MAP FST moves)) eqn:Ed; [|discriminate].
  destruct (get_vars (MAP SND moves) st) as [vs|] eqn:Eg; [|discriminate].
  injection Hev as <-. apply domain_lookup in Hy as [v Hv].
  change (List.map FST moves) with (MAP FST moves).
  destruct (MEM x (MAP FST moves)); [exfalso; apply Hx; reflexivity|]. cbn [negb andb].
  rewrite ?Ed. unfold get_var; rewrite Hv. change (List.map SND moves) with (MAP SND moves). rewrite ?Eg.
  unfold set_vars. cbn [alist_insert]. rewrite locals_set_locals, sl_sl. cbn [THE]. reflexivity.
Qed.
Lemma not_MEM_cons {A} `{EqDecision A} (x h : A) l : ~ is_true (MEM x (h :: l)) <-> x <> h /\ ~ is_true (MEM x l).
Proof.
  rewrite !MEM_iff'. cbn [In]. split; [intros Hn; split; [intros E; apply Hn; left; auto|auto]|].
  intros [H1 H2] [E|E]; auto.
Qed.

Lemma ALL_DISTINCT_cons' {A} `{EqDecision A} (h : A) l :
  is_true (ALL_DISTINCT (h :: l)) <-> ~ is_true (MEM h l) /\ is_true (ALL_DISTINCT l).
Proof.
  unfold is_true; cbn [ALL_DISTINCT]. rewrite Bool.andb_true_iff, Bool.negb_true_iff.
  destruct (MEM h l); intuition congruence.
Qed.

Lemma EVERY_bd_MEM (P : N -> Prop) `{forall x, Decision (P x)} l x :
  is_true (EVERY (fun x => bool_decide (P x)) l) -> is_true (MEM x l) -> P x.
Proof.
  unfold is_true; rewrite EVERY_Forall, Forall_forall. intros He Hm. apply MEM_iff' in Hm.
  apply (bool_decide_spec (P x)), He, Hm.
Qed.

Lemma move_nil_eval pri (s : state) : evaluate (Move pri [], s) = (NONE, s).
Proof.
  rewrite evaluate_eqn; cbn [evaluate_body MAP List.map ALL_DISTINCT get_vars].
  unfold set_vars; cbn [alist_insert]. rewrite set_locals_eta. reflexivity.
Qed.

(** The step of [merge_moves_correctL] (Galette-only). *)
Lemma merge_moves_step (stL cstL rc : state) pri mL na n' ssaL sL h x :
  ssa_locals_rel na ssaL (locals stL) (locals cstL) -> ssa_map_ok na ssaL -> ssa_map_ok n' sL ->
  na <= n' -> is_true (EVERY (fun x => bool_decide (x < n' /\ x >= na)) (MAP FST mL)) ->
  evaluate (Move pri mL, cstL) = (NONE, rc) ->
  lookup h ssaL = Some x -> lookup h sL = Some x ->
  (forall x y, x < na /\ lookup x (locals cstL) = SOME y -> lookup x (locals rc) = SOME y) ->
  ssa_locals_rel n' sL (locals stL) (locals rc) ->
  word_state_eq_rel cstL rc ->
  let '(resL, rcstL) := evaluate (Move pri ((n', x) :: mL), cstL) in
  resL = NONE /\
  (forall x y, x < na /\ lookup x (locals cstL) = SOME y -> lookup x (locals rcstL) = SOME y) /\
  ssa_locals_rel (n' + 4) (insert h n' sL) (locals stL) (locals rcstL) /\
  word_state_eq_rel cstL rcstL.
Proof.
  intros Hr Hok HokL Hle FL Ev EhL EL Hlt Hrel Hw.
  destruct (Hok h x EhL) as [_ Hxna].
  assert (Hxd : x IN domain (locals cstL)) by (destruct Hr as [Hr1 _]; exact (Hr1 h x EhL)).
  rewrite (mov_eval_head pri mL cstL rc n' x).
  2: { split; [exact Ev|split; [exact Hxd|split]]; intros Hm; apply (EVERY_bd_MEM _ _ _ FL) in Hm; lia. }
  rewrite locals_set_locals.
  split; [reflexivity|split; [|split]].
  - intros z w [Hz Hzw]. rewrite lookup_insert'. destruct (decide (z = n')); [lia|apply Hlt; auto].
  - destruct Hrel as [R1 R2]. destruct Hr as [Q1 Q2]. split.
    + intros z w Hz. rewrite lookup_insert' in Hz. rewrite domain_insert.
      destruct (decide (z = h)); [injection Hz as <-; left; reflexivity|right; eapply R1; exact Hz].
    + intros z w Hz. destruct (R2 _ _ Hz) as (Hzd & Hzl & Hza). rewrite domain_insert, !lookup_insert'.
      split; [right; exact Hzd|split; [|intros Ha; specialize (Hza Ha); lia]].
      destruct (decide (z = h)) as [->|Hne].
      * cbn [THE]. rewrite decide_True' by reflexivity. f_equal.
        destruct (Q2 _ _ Hz) as (_ & Hq & _). rewrite EhL in Hq. cbn [THE] in Hq. rewrite Hq. reflexivity.
      * apply domain_lookup in Hzd as [zz Hzz]. rewrite Hzz in Hzl |- *. cbn [THE] in *.
        destruct (HokL _ _ Hzz) as [_ Hzn]. rewrite decide_False' by lia. exact Hzl.
  - eapply word_state_eq_rel_trans; [exact Hw|apply wser_sl].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_correctL" *)
Theorem merge_moves_correctL : forall ls na ssaL ssaR (stL cstL : state) pri,
  is_alloc_var na /\ ALL_DISTINCT ls /\ ssa_map_ok na ssaL ->
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL (locals stL) (locals cstL) ->
   let '(resL, rcstL) := evaluate (Move pri moveL, cstL) in
   resL = NONE /\
   (forall x, ~ MEM x ls -> lookup x ssaL' = lookup x ssaL) /\
   (forall x y, x < na /\ lookup x (locals cstL) = SOME y -> lookup x (locals rcstL) = SOME y) /\
   ssa_locals_rel na' ssaL' (locals stL) (locals rcstL) /\
   word_state_eq_rel cstL rcstL).
Proof.
  induction ls as [|h ls IH]; intros na ssaL ssaR stL cstL pri (Ha & Hd & Hok); cbn [merge_moves].
  - intros Hr. rewrite move_nil_eval.
    split; [reflexivity|split; [auto|split; [intros x y [_ H]; exact H|split; [exact Hr|apply word_state_eq_rel_refl]]]].
  - apply ALL_DISTINCT_cons' in Hd as [Hh Hd].
    pose proof (merge_moves_frame ls na ssaL ssaR Ha) as Fr.
    pose proof (merge_moves_fst ls na ssaL ssaR) as Ff.
    specialize (IH na ssaL ssaR stL cstL pri (conj Ha (conj Hd Hok))).
    destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
    destruct Fr as (Ha' & Hle & HokL & _). specialize (HokL Hok).
    destruct Ff as (_ & FL & _).
    destruct (lookup h sL) as [x|] eqn:EL; [destruct (lookup h sR) as [y|] eqn:ER; [destruct (x =? y)|]|];
      intros Hr; specialize (IH Hr);
      destruct (evaluate (Move pri mL, cstL)) as [r rc] eqn:Ev;
      destruct IH as (-> & Hfr & Hlt & Hrel & Hw);
      (assert (Hfr' : forall x, ~ MEM x (h :: ls) -> lookup x sL = lookup x ssaL)
        by (intros z Hz; apply not_MEM_cons in Hz; apply Hfr, Hz));
      try (split; [reflexivity|split; [exact Hfr'|split; [exact Hlt|split; [exact Hrel|exact Hw]]]]).
    assert (EhL : lookup h ssaL = Some x) by (rewrite <- (Hfr h Hh); exact EL).
    pose proof (merge_moves_step stL cstL rc pri mL na n' ssaL sL h x Hr Hok HokL Hle FL Ev EhL EL Hlt Hrel Hw) as S.
    destruct (evaluate (Move pri ((n', x) :: mL), cstL)) as [r2 rc2].
    destruct S as (-> & S1 & S2 & S3). split; [reflexivity|split; [|split; [exact S1|split; [exact S2|exact S3]]]].
    intros z Hz. apply not_MEM_cons in Hz as [Hz1 Hz2]. rewrite lookup_insert', decide_False' by exact Hz1.
    apply Hfr, Hz2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "merge_moves_correctR" *)
Theorem merge_moves_correctR : forall ls na ssaL ssaR (stR cstR : state) pri,
  is_alloc_var na /\ ALL_DISTINCT ls /\ ssa_map_ok na ssaR ->
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaR (locals stR) (locals cstR) ->
   let '(resR, rcstR) := evaluate (Move pri moveR, cstR) in
   resR = NONE /\
   (forall x, ~ MEM x ls -> lookup x ssaR' = lookup x ssaR) /\
   (forall x y, x < na /\ lookup x (locals cstR) = SOME y -> lookup x (locals rcstR) = SOME y) /\
   ssa_locals_rel na' ssaR' (locals stR) (locals rcstR) /\
   word_state_eq_rel cstR rcstR).
Proof.
  intros ls na ssaL ssaR stR cstR pri H.
  pose proof (merge_moves_correctL ls na ssaR ssaL stR cstR pri H) as C.
  rewrite merge_moves_swap in C. destruct (merge_moves ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. exact C.
Qed.
Lemma eval_fake_move r (s : state) : evaluate (fake_move r, s) = (NONE, set_var r (Word (n2w 0)) s).
Proof. unfold fake_move. rewrite evaluate_eqn; cbn [evaluate_body]. unfold inst, assign. cbn [word_exp]. reflexivity. Qed.

Lemma eval_Seq_none (p1 p2 : prog a) (s s1 : state) :
  evaluate (p1, s) = (NONE, s1) -> evaluate (Seq p1 p2, s) = evaluate (p2, s1).
Proof. intros E. rewrite evaluate_Seq_eq', E. reflexivity. Qed.

Lemma eval_move1 pri r1 r2 (s : state) v :
  lookup r2 (locals s) = Some v ->
  evaluate (Move pri [(r1, r2)], s) = (NONE, set_locals (insert r1 v (locals s)) s).
Proof.
  intros E. rewrite evaluate_eqn; cbn [evaluate_body MAP List.map FST SND ALL_DISTINCT MEM negb andb get_vars].
  unfold get_var; rewrite E. reflexivity.
Qed.

(** Redirecting [h] to a fresh name (Galette-only). *)
Lemma ssa_locals_rel_redirect {A} n' sL h (stl cl : num_map A) v :
  ssa_locals_rel n' sL stl cl -> ssa_map_ok n' sL ->
  (forall w, lookup h stl = Some w -> v = w) ->
  ssa_locals_rel (n' + 4) (insert h n' sL) stl (insert n' v cl).
Proof.
  intros [R1 R2] Hok Hv. split.
  - intros z w Hz. rewrite lookup_insert' in Hz. rewrite domain_insert.
    destruct (decide (z = h)); [injection Hz as <-; left; reflexivity|right; eapply R1; exact Hz].
  - intros z w Hz. destruct (R2 _ _ Hz) as (Hzd & Hzl & Hza). rewrite domain_insert, !lookup_insert'.
    split; [right; exact Hzd|split; [|intros Ha; specialize (Hza Ha); lia]].
    destruct (decide (z = h)) as [->|Hne].
    + cbn [THE]. rewrite decide_True' by reflexivity. f_equal. apply Hv, Hz.
    + apply domain_lookup in Hzd as [zz Hzz]. rewrite Hzz in Hzl |- *. cbn [THE] in *.
      destruct (Hok _ _ Hzz) as [_ Hzn]. rewrite decide_False' by lia. exact Hzl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_frame" *)
Theorem fake_moves_frame : forall prio ls na ssaL ssaR,
  is_alloc_var na ->
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := @fake_moves a prio ls ssaL ssaR na in
  is_alloc_var na' /\ na <= na' /\
  (ssa_map_ok na ssaL -> ssa_map_ok na' ssaL') /\
  (ssa_map_ok na ssaR -> ssa_map_ok na' ssaR').
Proof.
  intros prio; induction ls as [|h ls IH]; intros na ssaL ssaR Ha; cbn [fake_moves].
  - split; [exact Ha|split; [lia|split; auto]].
  - specialize (IH na ssaL ssaR Ha).
    destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct IH as (Ha' & Hle & HL & HR).
    pose proof (is_alloc_var_not_phy _ Ha') as Hp.
    destruct (lookup h sL) as [x|], (lookup h sR) as [y|]; try (split; [exact Ha'|split; [lia|split; auto]]);
    (split; [apply is_alloc_var_add4, Ha'|split; [lia|split]];
      intros H; apply ssa_map_ok_extend; split; auto; rewrite Hp; discriminate).
Qed.

Lemma LTS_In {A} (l : list A) z : LIST_TO_SET l z <-> In z l.
Proof. apply IN_set. Qed.

Lemma lookup_dom_some {A} (t : num_map A) k v : lookup k t = Some v -> domain t k.
Proof. intros E; apply domain_lookup; eauto. Qed.

Lemma lookup_dom_none {A} (t : num_map A) k : lookup k t = None -> ~ domain t k.
Proof. apply lookup_NONE_domain. Qed.

Ltac fm2_dom DL DR E1 E2 :=
  apply set_ext; let z := fresh "z" in intros z; rewrite ?domain_insert; cbn beta;
  rewrite ?DL, ?DR; unfold pred_set.UNION, pred_set.INTER, pred_set.IN; cbn [LIST_TO_SET];
  rewrite ?LTS_In; clear - E1 E2; intuition (subst; tauto).

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_frame2" *)
Theorem fake_moves_frame2 : forall prio ls na ssaL ssaR,
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := @fake_moves a prio ls ssaL ssaR na in
  domain ssaL' = domain ssaL UNION (set ls INTER (domain ssaR UNION domain ssaL)) /\
  domain ssaR' = domain ssaR UNION (set ls INTER (domain ssaR UNION domain ssaL)) /\
  forall x, MEM x ls /\ ~ x IN domain (inter ssaL ssaR) -> lookup x ssaL' = lookup x ssaR'.
Proof.
  intros prio; induction ls as [|h ls IH]; intros na ssaL ssaR; cbn [fake_moves].
  - split; [|split; [|intros x [Hx _]; discriminate Hx]]; apply set_ext; intros x; set_simp; tauto.
  - specialize (IH na ssaL ssaR).
    destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct IH as (HdL & HdR & Hl).
    assert (DL : forall z, domain sL z <-> domain ssaL z \/ (In z ls /\ (domain ssaR z \/ domain ssaL z)))
      by (intros z; rewrite HdL, <- LTS_In; reflexivity).
    assert (DR : forall z, domain sR z <-> domain ssaR z \/ (In z ls /\ (domain ssaR z \/ domain ssaL z)))
      by (intros z; rewrite HdR, <- LTS_In; reflexivity).
    assert (Hi : forall z, z IN domain (inter ssaL ssaR) <-> domain ssaL z /\ domain ssaR z)
      by (intros z; rewrite domain_inter; reflexivity).
    assert (Hl' : forall z, In z ls -> ~ (domain ssaL z /\ domain ssaR z) -> lookup z sL = lookup z sR)
      by (intros z Hz Hz2; apply Hl; rewrite MEM_iff', Hi; auto).
    destruct (lookup h sL) as [x|] eqn:EL, (lookup h sR) as [y|] eqn:ER;
      pose proof EL as EL'; pose proof ER as ER';
      first [apply lookup_dom_some in EL'|apply lookup_dom_none in EL'];
      first [apply lookup_dom_some in ER'|apply lookup_dom_none in ER'];
      rewrite DL in EL'; rewrite DR in ER';
      (split; [fm2_dom DL DR EL' ER'|split; [fm2_dom DL DR EL' ER'|]]);
      intros z [Hz Hz2]; rewrite MEM_iff' in Hz; rewrite Hi in Hz2; rewrite ?lookup_insert';
      (destruct (decide (z = h)) as [->|Hne]; [|destruct Hz as [<-|Hz]; [congruence|apply Hl'; auto]]);
      try reflexivity;
      (destruct (decide (In h ls)) as [Hin|Hin]; [rewrite (Hl' h Hin Hz2) in *; congruence|first [congruence|tauto]]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_frame3" *)
Theorem fake_moves_frame3 : forall prio ls na ssaL ssaR,
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := @fake_moves a prio ls ssaL ssaR na in
  forall x, ~ MEM x ls \/ x IN domain (inter ssaL ssaR) ->
    lookup x ssaL' = lookup x ssaL /\ lookup x ssaR' = lookup x ssaR.
Proof.
  intros prio; induction ls as [|h ls IH]; intros na ssaL ssaR; cbn [fake_moves].
  - intros; split; reflexivity.
  - pose proof (fake_moves_frame2 prio ls na ssaL ssaR) as F2. specialize (IH na ssaL ssaR).
    destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. destruct F2 as (HdL & HdR & _).
    assert (IH' : forall x, ~ MEM x (h :: ls) \/ x IN domain (inter ssaL ssaR) ->
              lookup x sL = lookup x ssaL /\ lookup x sR = lookup x ssaR).
    { intros x Hx; apply IH. destruct Hx as [Hx|Hx]; [left|right; exact Hx].
      apply not_MEM_cons in Hx; tauto. }
    assert (Hin : forall x, x IN domain (inter ssaL ssaR) -> domain sL x /\ domain sR x).
    { intros x Hx. rewrite domain_inter in Hx. destruct Hx as [H1 H2]. rewrite HdL, HdR.
      split; left; assumption. }
    destruct (lookup h sL) as [x|] eqn:EL, (lookup h sR) as [y|] eqn:ER; try exact IH';
      intros z Hz; rewrite !lookup_insert'; (destruct (decide (z = h)) as [->|Hne]; [|apply IH', Hz]);
      exfalso; (destruct Hz as [Hz|Hz]; [apply Hz; rewrite MEM_iff'; left; reflexivity|]);
      destruct (Hin h Hz) as [H1 H2]; apply lookup_NONE_domain in EL || apply lookup_NONE_domain in ER; tauto.
Qed.

Lemma fm_finish (stL cstL rc : state) na n' ssaL sL h ls v :
  na <= n' -> ssa_map_ok n' sL ->
  (forall x, ~ MEM x ls -> lookup x sL = lookup x ssaL) ->
  (forall x y, x < na /\ lookup x (locals cstL) = Some y -> lookup x (locals rc) = Some y) ->
  ssa_locals_rel n' sL (locals stL) (locals rc) -> word_state_eq_rel cstL rc ->
  (forall w, lookup h (locals stL) = Some w -> v = w) ->
  let rc' := set_locals (insert n' v (locals rc)) rc in
  (forall x, ~ MEM x (h :: ls) -> lookup x (insert h n' sL) = lookup x ssaL) /\
  (forall x y, x < na /\ lookup x (locals cstL) = Some y -> lookup x (locals rc') = Some y) /\
  ssa_locals_rel (n' + 4) (insert h n' sL) (locals stL) (locals rc') /\ word_state_eq_rel cstL rc'.
Proof.
  intros Hle Hok Hfr Hlt Hrel Hw Hv rc'. subst rc'. rewrite locals_set_locals.
  split; [|split; [|split]].
  - intros z Hz. apply not_MEM_cons in Hz as [Hz1 Hz2]. rewrite lookup_insert', decide_False' by exact Hz1.
    apply Hfr, Hz2.
  - intros z w [Hz Hzw]. rewrite lookup_insert'. destruct (decide (z = n')); [lia|apply Hlt; auto].
  - apply ssa_locals_rel_redirect; assumption.
  - eapply word_state_eq_rel_trans; [exact Hw|apply wser_sl].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_correctL" *)
Theorem fake_moves_correctL : forall prio ls na ssaL ssaR (stL cstL : state),
  is_alloc_var na /\ ALL_DISTINCT ls /\ ssa_map_ok na ssaL ->
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaL (locals stL) (locals cstL) ->
   let '(resL, rcstL) := evaluate (moveL, cstL) in
   resL = NONE /\
   (forall x, ~ MEM x ls -> lookup x ssaL' = lookup x ssaL) /\
   (forall x y, x < na /\ lookup x (locals cstL) = SOME y -> lookup x (locals rcstL) = SOME y) /\
   ssa_locals_rel na' ssaL' (locals stL) (locals rcstL) /\
   word_state_eq_rel cstL rcstL).
Proof.
  intros prio; induction ls as [|h ls IH]; intros na ssaL ssaR stL cstL (Ha & Hd & Hok); cbn [fake_moves].
  - intros Hr. rewrite evaluate_eqn; cbn [evaluate_body].
    split; [reflexivity|split; [auto|split; [intros x y [_ H]; exact H|split; [exact Hr|apply word_state_eq_rel_refl]]]].
  - apply ALL_DISTINCT_cons' in Hd as [Hh Hd].
    pose proof (fake_moves_frame prio ls na ssaL ssaR Ha) as Fr.
    specialize (IH na ssaL ssaR stL cstL (conj Ha (conj Hd Hok))).
    destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
    destruct Fr as (Ha' & Hle & HokL & _). specialize (HokL Hok).
    destruct (lookup h sL) as [x|] eqn:EL; [destruct (lookup h sR) as [y|] eqn:ER|destruct (lookup h sR) as [y|] eqn:ER];
      intros Hr; specialize (IH Hr);
      destruct (evaluate (mL, cstL)) as [r rc] eqn:Ev;
      destruct IH as (-> & Hfr & Hlt & Hrel & Hw);
      (assert (Hfr' : forall x, ~ MEM x (h :: ls) -> lookup x sL = lookup x ssaL)
        by (intros z Hz; apply not_MEM_cons in Hz; apply Hfr, Hz));
      try (split; [reflexivity|split; [exact Hfr'|split; [exact Hlt|split; [exact Hrel|exact Hw]]]]).
    + rewrite (eval_Seq_none _ _ _ _ Ev).
      destruct Hrel as [R1 R2] eqn:HR. pose proof (R1 h x EL) as Hx. apply domain_lookup in Hx as [v Hv].
      rewrite (eval_move1 _ _ _ _ v Hv). split; [reflexivity|].
      apply (fm_finish stL cstL rc na n' ssaL sL h ls v); try assumption.
      intros w Hw'. destruct (R2 _ _ Hw') as (_ & Hl & _). rewrite EL in Hl. cbn [THE] in Hl. congruence.
    + rewrite (eval_Seq_none _ _ _ _ Ev), eval_fake_move. unfold set_var. split; [reflexivity|].
      apply (fm_finish stL cstL rc na n' ssaL sL h ls); try assumption.
      intros w Hw'. destruct Hrel as [_ R2]. destruct (R2 _ _ Hw') as (Hd' & _). apply lookup_NONE_domain in EL. contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_correctR" *)
Theorem fake_moves_correctR : forall prio ls na ssaL ssaR (stR cstR : state),
  is_alloc_var na /\ ALL_DISTINCT ls /\ ssa_map_ok na ssaR ->
  let '(moveL, (moveR, (na', (ssaL', ssaR')))) := fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaR (locals stR) (locals cstR) ->
   let '(resR, rcstR) := evaluate (moveR, cstR) in
   resR = NONE /\
   (forall x, ~ MEM x ls -> lookup x ssaR' = lookup x ssaR) /\
   (forall x y, x < na /\ lookup x (locals cstR) = SOME y -> lookup x (locals rcstR) = SOME y) /\
   ssa_locals_rel na' ssaR' (locals stR) (locals rcstR) /\
   word_state_eq_rel cstR rcstR).
Proof.
  intros prio ls na ssaL ssaR stR cstR H.
  pose proof (fake_moves_correctL (swap_prio prio) ls na ssaR ssaL stR cstR H) as C.
  rewrite fake_moves_swap in C. destruct (fake_moves prio ls ssaL ssaR na) as [mL [mR [n' [sL sR]]]]. exact C.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_var_ignore" *)
Theorem get_var_ignore : forall ls (a0 : list (word_loc a)) x (cst : state) y,
  get_var x cst = SOME y /\ ~ MEM x ls /\ LENGTH ls = LENGTH a0 ->
  get_var x (set_vars ls a0 cst) = SOME y.
Proof.
  induction ls as [|h ls IH]; intros a0 x cst y (Hg & Hm & Hl); unfold set_vars, get_var in *;
    rewrite locals_set_locals; [exact Hg|].
  destruct a0 as [|v a0]; [cbn [LENGTH] in Hl; lia|]. cbn [alist_insert]. apply not_MEM_cons in Hm as [Hm1 Hm2].
  rewrite lookup_insert', decide_False' by exact Hm1.
  specialize (IH a0 x cst y). rewrite locals_set_locals in IH. apply IH.
  split; [exact Hg|split; [exact Hm2|]]. cbn [LENGTH] in Hl. lia.
Qed.
Lemma MEM_toAList_dom {A} (t : num_map A) x : is_true (MEM x (MAP FST (toAList t))) <-> domain t x.
Proof.
  pose proof (f_equal (fun P => P x) (set_MAP_FST_toAList_domain t)) as H; cbv beta in H.
  rewrite <- H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fix_inconsistencies_correctL" *)
Theorem fix_inconsistencies_correctL : forall prio na ssaL ssaR,
  is_alloc_var na /\ ssa_map_ok na ssaL ->
  let '(moveL, (moveR, (na', ssaU))) := @fix_inconsistencies a prio ssaL ssaR na in
  (forall (stL cstL : state),
   ssa_locals_rel na ssaL (locals stL) (locals cstL) ->
   let '(resL, rcstL) := evaluate (moveL, cstL) in
   resL = NONE /\
   ssa_locals_rel na' ssaU (locals stL) (locals rcstL) /\
   word_state_eq_rel cstL rcstL).
Proof.
  intros prio na ssaL ssaR [Ha Hok]. unfold fix_inconsistencies.
  set (vu := MAP FST (toAList (union ssaL ssaR))).
  assert (Hd : ALL_DISTINCT vu) by apply ALL_DISTINCT_MAP_FST_toAList.
  pose proof (merge_moves_frame vu na ssaL ssaR Ha) as Fr.
  pose proof (fun stL cstL => merge_moves_correctL vu na ssaL ssaR stL cstL (priority prio true) (conj Ha (conj Hd Hok))) as M.
  destruct (merge_moves vu ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  destruct Fr as (Ha' & _ & HokL & _). specialize (HokL Hok).
  pose proof (fun stL cstL => fake_moves_correctL prio vu n' sL sR stL cstL (conj Ha' (conj Hd HokL))) as Fk.
  destruct (fake_moves prio vu sL sR n') as [fL [fR [n'' [sL' sR']]]].
  intros stL cstL Hr. specialize (M stL cstL Hr).
  destruct (evaluate (Move (priority prio true) mL, cstL)) as [r1 c1] eqn:E1.
  destruct M as (-> & _ & _ & Hr1 & Hw1).
  specialize (Fk stL c1 Hr1). destruct (evaluate (fL, c1)) as [r2 c2] eqn:E2.
  destruct Fk as (-> & _ & _ & Hr2 & Hw2).
  rewrite (eval_Seq_none _ _ _ _ E1), E2.
  split; [reflexivity|split; [exact Hr2|eapply word_state_eq_rel_trans; eassumption]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fix_inconsistencies_correctR" *)
Theorem fix_inconsistencies_correctR : forall na ssaL ssaR prio,
  is_alloc_var na /\ ssa_map_ok na ssaR ->
  let '(moveL, (moveR, (na', ssaU))) := @fix_inconsistencies a prio ssaL ssaR na in
  (forall (stR cstR : state),
   ssa_locals_rel na ssaR (locals stR) (locals cstR) ->
   let '(resR, rcstR) := evaluate (moveR, cstR) in
   resR = NONE /\
   ssa_locals_rel na' ssaU (locals stR) (locals rcstR) /\
   word_state_eq_rel cstR rcstR).
Proof.
  intros na ssaL ssaR prio [Ha Hok]. unfold fix_inconsistencies.
  set (vu := MAP FST (toAList (union ssaL ssaR))).
  assert (Hd : ALL_DISTINCT vu) by apply ALL_DISTINCT_MAP_FST_toAList.
  assert (Hvu : forall x, is_true (MEM x vu) <-> domain ssaL x \/ domain ssaR x)
    by (intros x; unfold vu; rewrite MEM_toAList_dom, domain_union; reflexivity).
  pose proof (merge_moves_frame vu na ssaL ssaR Ha) as Fr.
  pose proof (merge_moves_frame2 vu na ssaL ssaR) as Fr2.
  pose proof (merge_moves_frame3 vu na ssaL ssaR) as Fr3.
  pose proof (fun stR cstR => merge_moves_correctR vu na ssaL ssaR stR cstR (priority prio false) (conj Ha (conj Hd Hok))) as M.
  destruct (merge_moves vu ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  destruct Fr as (Ha' & _ & _ & HokR). specialize (HokR Hok).
  destruct Fr2 as (D2L & D2R & E2).
  pose proof (fun stR cstR => fake_moves_correctR prio vu n' sL sR stR cstR (conj Ha' (conj Hd HokR))) as Fk.
  pose proof (fake_moves_frame2 prio vu n' sL sR) as G2.
  pose proof (fake_moves_frame3 prio vu n' sL sR) as G3.
  destruct (fake_moves prio vu sL sR n') as [fL [fR [n'' [sL' sR']]]].
  destruct G2 as (G2L & G2R & G2E).
  intros stR cstR Hr. specialize (M stR cstR Hr).
  destruct (evaluate (Move (priority prio false) mR, cstR)) as [r1 c1] eqn:E1.
  destruct M as (-> & _ & _ & Hr1 & Hw1).
  specialize (Fk stR c1 Hr1). destruct (evaluate (fR, c1)) as [r2 c2] eqn:E2'.
  destruct Fk as (-> & _ & _ & Hr2 & Hw2).
  rewrite (eval_Seq_none _ _ _ _ E1), E2'.
  split; [reflexivity|split; [|eapply word_state_eq_rel_trans; eassumption]].
  assert (DL : forall x, domain sL' x <-> domain ssaL x \/ domain ssaR x).
  { intros x. rewrite G2L, D2L, D2R. unfold pred_set.UNION, pred_set.INTER, pred_set.IN.
    change (LIST_TO_SET vu x) with (x IN set vu). rewrite IN_set, <- MEM_iff', Hvu. tauto. }
  assert (DR : forall x, domain sR' x <-> domain ssaL x \/ domain ssaR x).
  { intros x. rewrite G2R, D2L, D2R. unfold pred_set.UNION, pred_set.INTER, pred_set.IN.
    change (LIST_TO_SET vu x) with (x IN set vu). rewrite IN_set, <- MEM_iff', Hvu. tauto. }
  apply (ssa_eq_rel_swap _ _ sR'). split; [exact Hr2|split].
  - apply set_ext; intros x; rewrite DL, DR; reflexivity.
  - intros x. destruct (decide (domain ssaL x \/ domain ssaR x)) as [Hx|Hx].
    + assert (Hm : is_true (MEM x vu)) by (apply Hvu, Hx).
      destruct (decide (x IN domain (inter sL sR))) as [Hi|Hi].
      * destruct (G3 x (or_intror Hi)) as [-> ->]. apply E2. split; [exact Hm|].
        rewrite domain_inter in Hi |- *. rewrite <- D2L, <- D2R. exact Hi.
      * apply G2E. split; assumption.
    + assert (N1 : ~ domain sL' x) by (rewrite DL; exact Hx).
      assert (N2 : ~ domain sR' x) by (rewrite DR; exact Hx).
      apply lookup_NONE_domain in N1, N2. congruence.
Qed.
Lemma alist_insert_notin {A} k (ns : list N) (vs : list A) l :
  ~ In k ns -> lookup k (alist_insert ns vs l) = lookup k l.
Proof.
  revert vs; induction ns as [|n ns IH]; intros [|v vs] Hk; cbn [alist_insert]; try reflexivity.
  rewrite lookup_insert', decide_False' by (intros ->; apply Hk; left; reflexivity).
  apply IH. intros H; apply Hk; right; exact H.
Qed.

Lemma alist_insert_map_lookup (f g : N -> N) ls vs (cst : state) l x :
  NoDup (List.map f ls) -> In x ls -> get_vars (MAP g ls) cst = Some vs ->
  lookup (f x) (alist_insert (MAP f ls) vs l) = lookup (g x) (locals cst).
Proof.
  revert vs; induction ls as [|h ls IH]; intros vs Hd Hx Hg; [destruct Hx|].
  cbn [MAP List.map get_vars] in Hg |- *. inversion Hd as [|? ? Hn Hd']; subst.
  destruct (get_var (g h) cst) as [v|] eqn:Ev; [|discriminate].
  destruct (get_vars (MAP g ls) cst) as [vs'|] eqn:Evs; [|discriminate]. injection Hg as <-.
  cbn [alist_insert]. rewrite lookup_insert'. destruct Hx as [->|Hx].
  - rewrite decide_True' by reflexivity. symmetry; exact Ev.
  - rewrite decide_False'; [apply IH; auto|].
    intros E; apply Hn. rewrite <- E. apply in_map, Hx.
Qed.

Lemma get_vars_exists' (l : list N) (s : state) :
  (forall x, In x l -> exists v, lookup x (locals s) = Some v) ->
  exists vs, get_vars l s = Some vs.
Proof.
  induction l as [|h l IH]; intros H; [exists []; reflexivity|].
  destruct (H h (or_introl eq_refl)) as [v Hv].
  destruct IH as [vs Hvs]; [intros x Hx; apply H; right; exact Hx|].
  exists (v :: vs). cbn [get_vars]. unfold get_var; rewrite Hv, Hvs. reflexivity.
Qed.

Lemma is_phy_var_4 i n : is_phy_var (4 * i + n) = is_phy_var n.
Proof.
  unfold is_phy_var. replace (4 * i + n) with (n + (2 * i) * 2) by lia.
  rewrite N.Div0.mod_add. reflexivity.
Qed.

Lemma In_map_4 y na l : In y (List.map (fun x => 4 * x + na) l) -> exists i, y = 4 * i + na.
Proof. intros H. apply in_map_iff in H as [i [<- _]]. eauto. Qed.

Lemma lookup_some_THE (ssa : num_map N) x z :
  lookup x ssa = Some z -> option_lookup ssa x = z /\ THE (lookup x ssa) = z.
Proof. intros E. unfold option_lookup. rewrite E. split; reflexivity. Qed.

Lemma lnvrm_core (st cst : state) ssa na ls :
  ssa_locals_rel na ssa (locals st) (locals cst) -> (forall x, In x ls -> domain ssa x) ->
  ALL_DISTINCT ls -> ssa_map_ok na ssa -> word_state_eq_rel st cst ->
  let '(mov, (ssa', na')) := @list_next_var_rename_move a ssa na ls in
  let '(res, rcst) := evaluate (mov, cst) in
  res = NONE /\ ssa_locals_rel na' ssa' (locals st) (locals rcst) /\ word_state_eq_rel st rcst /\
  (~ is_phy_var na -> forall w, is_phy_var w -> lookup w (locals rcst) = lookup w (locals cst)) /\
  (forall x y, lookup x (locals st) = Some y -> lookup (THE (lookup x ssa)) (locals rcst) = Some y).
Proof.
  intros [R1 R2] Hls Hdist Hok Hw. unfold list_next_var_rename_move.
  destruct (list_next_var_rename ls ssa na) as [ls' [ssa' na']] eqn:E.
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E) as (Hd' & Hls' & Hna').
  destruct (list_next_var_rename_lemma_2' _ _ _ _ _ _ E Hdist) as (Hmap & Hdom & Hfr & Hex).
  set (f := fun x => THE (lookup x ssa')) in Hmap.
  assert (Hv : forall x, In x ls -> exists v, lookup (option_lookup ssa x) (locals cst) = Some v).
  { intros x Hx. destruct (proj1 (domain_lookup _ _) (Hls x Hx)) as [z Hz].
    destruct (lookup_some_THE _ _ _ Hz) as [-> _]. apply domain_lookup, (R1 x z Hz). }
  destruct (get_vars_exists' (MAP (option_lookup ssa) ls) cst) as [vs Hvs].
  { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. apply Hv, Hx. }
  assert (Hlen : LENGTH ls' = LENGTH (MAP (option_lookup ssa) ls))
    by (rewrite Hmap, !LENGTH_MAP'; reflexivity).
  rewrite evaluate_eqn; cbn [evaluate_body].
  rewrite MAP_FST_ZIP', MAP_SND_ZIP' by exact Hlen. rewrite Hd', Hvs.
  unfold set_vars. rewrite locals_set_locals.
  assert (Hnd : NoDup (List.map f ls)) by (apply ALL_DISTINCT_iff'; rewrite <- Hmap; exact Hd').
  assert (K1 : forall x, In x ls -> lookup (f x) (alist_insert ls' vs (locals cst)) =
                                    lookup (option_lookup ssa x) (locals cst))
    by (intros x Hx; rewrite Hmap; apply (alist_insert_map_lookup f _ _ _ cst); assumption).
  assert (Hge : forall y, In y ls' -> exists i, y = 4 * i + na)
    by (intros y Hy; rewrite Hls' in Hy; apply In_map_4 in Hy; exact Hy).
  assert (K2 : forall k, ~ In k ls' -> lookup k (alist_insert ls' vs (locals cst)) = lookup k (locals cst))
    by (intros k Hk; apply alist_insert_notin, Hk).
  assert (Hlt : forall k, k < na -> ~ In k ls') by (intros k Hk Hin; destruct (Hge k Hin); lia).
  split; [reflexivity|split; [split|split; [eapply word_state_eq_rel_trans; [exact Hw|apply wser_sl]|split]]].
  - intros x y Hxy. destruct (decide (In x ls)) as [Hx|Hx].
    + assert (Ef : f x = y) by (unfold f; rewrite Hxy; reflexivity).
      apply domain_lookup. rewrite <- Ef, K1 by exact Hx. apply Hv, Hx.
    + rewrite Hfr in Hxy by (rewrite MEM_iff'; exact Hx).
      destruct (Hok _ _ Hxy) as [_ Hy]. apply domain_lookup. rewrite K2 by (apply Hlt, Hy).
      apply domain_lookup, (R1 _ _ Hxy).
  - intros x y Hxy. destruct (R2 _ _ Hxy) as (Hxd & Hxl & Hxa).
    split; [rewrite Hdom; left; exact Hxd|split; [|intros Ha; specialize (Hxa Ha); lia]].
    apply domain_lookup in Hxd as [z Hz]. destruct (lookup_some_THE _ _ _ Hz) as [Ho Ht].
    destruct (decide (In x ls)) as [Hx|Hx].
    + change (THE (lookup x ssa')) with (f x). rewrite K1, Ho by exact Hx. rewrite Ht in Hxl. exact Hxl.
    + rewrite Hfr by (rewrite MEM_iff'; exact Hx). rewrite Ht in Hxl |- *.
      destruct (Hok _ _ Hz) as [_ Hzn]. rewrite K2 by (apply Hlt, Hzn). exact Hxl.
  - intros Hp w Hw'. apply K2. intros Hin. destruct (Hge w Hin) as [i ->].
    rewrite is_phy_var_4 in Hw'. contradiction.
  - intros x y Hxy. destruct (R2 _ _ Hxy) as (Hxd & Hxl & _).
    apply domain_lookup in Hxd as [z Hz]. destruct (lookup_some_THE _ _ _ Hz) as [_ Ht].
    rewrite Ht in Hxl |- *. destruct (Hok _ _ Hz) as [_ Hzn]. rewrite K2 by (apply Hlt, Hzn). exact Hxl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_preserve" *)
Theorem list_next_var_rename_move_preserve : forall (st : state) ssa na ls (cst : state),
  ssa_locals_rel na ssa (locals st) (locals cst) /\
  set ls SUBSET domain (locals st) /\
  ALL_DISTINCT ls /\
  ssa_map_ok na ssa /\
  word_state_eq_rel st cst ->
  let '(mov, (ssa', na')) := list_next_var_rename_move ssa na ls in
  let '(res, rcst) := evaluate (mov, cst) in
  res = NONE /\
  ssa_locals_rel na' ssa' (locals st) (locals rcst) /\
  word_state_eq_rel st rcst /\
  (~ is_phy_var na -> forall w, is_phy_var w -> lookup w (locals rcst) = lookup w (locals cst)) /\
  (forall x y, lookup x (locals st) = SOME y -> lookup (THE (lookup x ssa)) (locals rcst) = SOME y).
Proof.
  intros st ssa na ls cst (Hr & Hs & Hd & Hok & Hw). apply lnvrm_core; try assumption.
  intros x Hx. assert (Hx' : domain (locals st) x) by (apply Hs, IN_set, Hx).
  apply domain_lookup in Hx' as [v Hv]. destruct Hr as [_ R2]. apply (R2 _ _ Hv).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "option_lookup_subset_helper" *)
Theorem option_lookup_subset_helper : forall {A} ssa (cst_locs : num_map A) ls,
  (forall x y, lookup x ssa = SOME y -> y IN domain cst_locs) /\
  set ls SUBSET domain ssa ->
  set (MAP (option_lookup ssa) ls) SUBSET domain cst_locs.
Proof.
  intros A ssa cst_locs ls [H1 H2] y Hy. apply IN_set in Hy. apply in_map_iff in Hy as [x [<- Hx]].
  assert (Hx' : domain ssa x) by (apply H2, IN_set, Hx).
  apply domain_lookup in Hx' as [z Hz]. destruct (lookup_some_THE _ _ _ Hz) as [-> _]. apply (H1 _ _ Hz).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_preserve_weak" *)
Theorem list_next_var_rename_move_preserve_weak : forall (st : state) ssa na ls (cst : state),
  ssa_locals_rel na ssa (locals st) (locals cst) /\
  set ls SUBSET domain ssa /\
  ALL_DISTINCT ls /\
  ssa_map_ok na ssa /\
  word_state_eq_rel st cst ->
  let '(mov, (ssa', na')) := list_next_var_rename_move ssa na ls in
  let '(res, rcst) := evaluate (mov, cst) in
  res = NONE /\
  ssa_locals_rel na' ssa' (locals st) (locals rcst) /\
  word_state_eq_rel st rcst.
Proof.
  intros st ssa na ls cst (Hr & Hs & Hd & Hok & Hw).
  pose proof (lnvrm_core st cst ssa na ls Hr ltac:(intros x Hx; apply Hs, IN_set, Hx) Hd Hok Hw) as C.
  destruct (list_next_var_rename_move ssa na ls) as [mov [ssa' na']].
  destruct (evaluate (mov, cst)) as [res rcst]. destruct C as (? & ? & ? & _). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_list_insert_eq_gen" *)
Theorem get_vars_list_insert_eq_gen : forall ls x locs (a0 : list N) b (st : state),
  LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\ LENGTH a0 = LENGTH b /\
  (forall e, MEM e ls -> ~ MEM e a0) ->
  get_vars ls (set_locals (alist_insert (a0 ++ ls) (b ++ x) locs) st) = SOME x.
Proof.
  induction ls as [|h ls IH]; intros x locs a0 b st (Hl & Hd & Hab & He).
  - destruct x; [reflexivity|cbn [LENGTH] in Hl; lia].
  - destruct x as [|v x]; [cbn [LENGTH] in Hl; lia|]. apply ALL_DISTINCT_cons' in Hd as [Hh Hd].
    replace (a0 ++ h :: ls) with ((a0 ++ [h]) ++ ls) by (rewrite <- app_assoc; reflexivity).
    replace (b ++ v :: x) with ((b ++ [v]) ++ x) by (rewrite <- app_assoc; reflexivity).
    cbn [get_vars]. rewrite IH.
    2: { split; [cbn [LENGTH] in Hl; lia|split; [exact Hd|split]].
         - rewrite !LENGTH_length, !length_app. rewrite !LENGTH_length in Hab. cbn [length]. lia.
         - intros e Hm Hm'. rewrite MEM_iff' in Hm, Hm'. apply in_app_or in Hm' as [Hm'|[<-|[]]].
           + apply (He e); rewrite MEM_iff'; [right; exact Hm|exact Hm'].
           + apply Hh. rewrite MEM_iff'; exact Hm. }
    unfold get_var. rewrite locals_set_locals.
    rewrite alist_insert_append by (rewrite !LENGTH_length, !length_app; rewrite !LENGTH_length in Hab; cbn [length]; lia).
    rewrite alist_insert_append by exact Hab. rewrite alist_insert_notin.
    2: { rewrite <- MEM_iff'. apply He. rewrite MEM_iff'; left; reflexivity. }
    cbn [alist_insert]. rewrite lookup_insert1. reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_set_vars_eq" *)
Theorem get_vars_set_vars_eq : forall ls x (cst : state),
  ALL_DISTINCT ls /\ LENGTH x = LENGTH ls ->
  get_vars ls (set_vars ls x cst) = SOME x.
Proof.
  intros ls x cst [Hd Hl]. unfold set_vars.
  apply (get_vars_list_insert_eq_gen ls x (locals cst) [] [] cst).
  split; [lia|split; [exact Hd|split; [reflexivity|intros e _ H; discriminate H]]].
Qed.
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_ignore_insert" *)
Theorem ssa_locals_rel_ignore_insert : forall {A} na ssa (stloc cstloc : num_map A) v (w0 : A),
  ssa_map_ok na ssa /\ ssa_locals_rel na ssa stloc cstloc /\ is_phy_var v ->
  ssa_locals_rel na ssa stloc (insert v w0 cstloc).
Proof.
  intros A na ssa stloc cstloc v w0 (Hok & [R1 R2] & Hp). split.
  - intros x y Hx. rewrite domain_insert. right. eapply R1; exact Hx.
  - intros x y Hx. destruct (R2 _ _ Hx) as (Hd & Hl & Ha). split; [exact Hd|split; [|exact Ha]].
    apply domain_lookup in Hd as [z Hz]. rewrite Hz in Hl |- *. cbn [THE] in *.
    destruct (Hok _ _ Hz) as [Hz' _]. rewrite lookup_insert', decide_False' by (intros ->; contradiction). exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_ignore_set_var" *)
Theorem ssa_locals_rel_ignore_set_var : forall na ssa (st cst : state) v w0,
  ssa_map_ok na ssa /\ ssa_locals_rel na ssa (locals st) (locals cst) /\ is_phy_var v ->
  ssa_locals_rel na ssa (locals st) (locals (set_var v w0 cst)).
Proof. intros. unfold set_var; rewrite locals_set_locals. apply ssa_locals_rel_ignore_insert; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_ignore_list_insert" *)
Theorem ssa_locals_rel_ignore_list_insert : forall na ssa (st cst : state) ls x,
  ssa_map_ok na ssa /\ ssa_locals_rel na ssa (locals st) (locals cst) /\
  EVERY is_phy_var ls /\ LENGTH ls = LENGTH x ->
  ssa_locals_rel na ssa (locals st) (alist_insert ls x (locals cst)).
Proof.
  intros na ssa st cst ls; induction ls as [|h ls IH]; intros x (Hok & Hr & He & Hl); [exact Hr|].
  destruct x as [|v x]; [cbn [LENGTH] in Hl; lia|]. cbn [alist_insert]. cbn [EVERY] in He.
  apply andb_prop in He as [Hh He]. apply ssa_locals_rel_ignore_insert. split; [exact Hok|split; [|exact Hh]].
  apply IH. split; [exact Hok|split; [exact Hr|split; [exact He|cbn [LENGTH] in Hl; lia]]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_insert" *)
Theorem ssa_locals_rel_insert : forall {A} na ssa (stloc cstloc : num_map A) n (w : A),
  ssa_locals_rel na ssa stloc cstloc /\ ssa_map_ok na ssa /\ n < na ->
  ssa_locals_rel (na + 4) (insert n na ssa) (insert n w stloc) (insert na w cstloc).
Proof.
  intros A na ssa stloc cstloc n w ([R1 R2] & Hok & Hn). split.
  - intros x y Hx. rewrite lookup_insert' in Hx. rewrite domain_insert.
    destruct (decide (x = n)); [injection Hx as <-; left; reflexivity|right; eapply R1; exact Hx].
  - intros x y Hx. rewrite lookup_insert' in Hx. rewrite domain_insert, !lookup_insert'.
    destruct (decide (x = n)) as [->|Hne].
    + injection Hx as <-. split; [left; reflexivity|split; [cbn [THE]; rewrite decide_True' by reflexivity; reflexivity|lia]].
    + destruct (R2 _ _ Hx) as (Hd & Hl & Ha). split; [right; exact Hd|split; [|intros Ha'; specialize (Ha Ha'); lia]].
      apply domain_lookup in Hd as [z Hz]. rewrite Hz in Hl |- *. cbn [THE] in *.
      destruct (Hok _ _ Hz) as [_ Hzn]. rewrite decide_False' by lia. exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_set_var" *)
Theorem ssa_locals_rel_set_var : forall {A} na ssa (stl cstl : num_map A) n (w : A),
  ssa_locals_rel na ssa stl cstl /\ ssa_map_ok na ssa /\ n < na ->
  ssa_locals_rel (na + 4) (insert n na ssa) (insert n w stl) (insert na w cstl).
Proof. intros; apply ssa_locals_rel_insert; assumption. Qed.

Lemma alist_insert_insert_comm {A} k (v : A) ns vs l :
  ~ In k ns -> alist_insert ns vs (insert k v l) = insert k v (alist_insert ns vs l).
Proof.
  revert vs; induction ns as [|n ns IH]; intros [|w vs] Hk; cbn [alist_insert]; try reflexivity.
  rewrite IH by (intros H; apply Hk; right; exact H). apply insert_swap. intros ->; apply Hk; left; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_list_next_var_rename" *)
Theorem ssa_locals_rel_list_next_var_rename : forall {A} xs ssa na (stloc cstloc : num_map A) ys ssa' na' ls,
  list_next_var_rename xs ssa na = (ys, (ssa', na')) /\
  ssa_locals_rel na ssa stloc cstloc /\
  ssa_map_ok na ssa /\
  LENGTH xs = LENGTH ls /\
  EVERY (fun x => x <? na) xs /\
  ALL_DISTINCT xs /\
  ~ is_phy_var na ->
  ssa_locals_rel na' ssa' (alist_insert xs ls stloc) (alist_insert ys ls cstloc).
Proof.
  intros A xs; induction xs as [|h xs IH]; intros ssa na stloc cstloc ys ssa' na' ls (E & Hr & Hok & Hl & He & Hd & Hp).
  - cbn [list_next_var_rename] in E. injection E as <- <- <-. exact Hr.
  - destruct ls as [|v ls]; [cbn [LENGTH] in Hl; lia|].
    cbn [list_next_var_rename next_var_rename] in E.
    destruct (list_next_var_rename xs (insert h na ssa) (na + 4)) as [ys' [s2 n2]] eqn:E2.
    injection E as <- <- <-. cbn [EVERY] in He. apply andb_prop in He as [Hh He]. apply N.ltb_lt in Hh.
    apply ALL_DISTINCT_cons' in Hd as [Hhd Hd].
    destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E2) as (_ & Hys & _).
    cbn [alist_insert].
    rewrite <- alist_insert_insert_comm by (rewrite <- MEM_iff'; exact Hhd).
    rewrite <- alist_insert_insert_comm.
    2: { rewrite Hys. intros Hin. apply In_map_4 in Hin as [i Hi]. lia. }
    apply (IH (insert h na ssa) (na + 4)). split; [exact E2|split; [|split; [|split; [|split; [|split]]]]].
    + apply ssa_locals_rel_insert. auto.
    + apply ssa_map_ok_extend. auto.
    + cbn [LENGTH] in Hl; lia.
    + unfold is_true in *. rewrite EVERY_Forall, Forall_forall in *. intros x Hx. specialize (He x Hx).
      apply N.ltb_lt in He. apply N.ltb_lt. lia.
    + exact Hd.
    + replace (na + 4) with (4 * 1 + na) by lia. rewrite is_phy_var_4. exact Hp.
Qed.

Lemma mod4_add n k : (n + 4 * k) mod 4 = n mod 4.
Proof. replace (n + 4 * k) with (n + k * 4) by lia. apply N.Div0.mod_add. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_alloc_var_add" *)
Theorem is_alloc_var_add : forall na, is_alloc_var na -> is_alloc_var (na + 4).
Proof. intros na; apply is_alloc_var_add4. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_stack_var_add" *)
Theorem is_stack_var_add : forall na, is_stack_var na -> is_stack_var (na + 4).
Proof.
  intros na; unfold is_true, is_stack_var; rewrite !N.eqb_eq. replace (na + 4) with (na + 4 * 1) by lia.
  rewrite mod4_add. auto.
Qed.

Lemma mod4_add2 n : (n + 2) mod 4 = (n mod 4 + 2) mod 4.
Proof. rewrite N.Div0.add_mod. reflexivity. Qed.

Lemma mod4_cases n : n mod 4 = 0 \/ n mod 4 = 1 \/ n mod 4 = 2 \/ n mod 4 = 3.
Proof. pose proof (N.mod_lt n 4 ltac:(lia)). lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "flip_rw" *)
Theorem flip_rw : forall na,
  is_stack_var (na + 2) = is_alloc_var na /\ is_alloc_var (na + 2) = is_stack_var na.
Proof.
  intros na; unfold is_stack_var, is_alloc_var. rewrite mod4_add2.
  destruct (mod4_cases na) as [E|[E|[E|E]]]; rewrite E; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_alloc_var_flip" *)
Theorem is_alloc_var_flip : forall na, is_alloc_var na -> is_stack_var (na + 2).
Proof. intros na; rewrite (proj1 (flip_rw na)); auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "is_stack_var_flip" *)
Theorem is_stack_var_flip : forall na, is_stack_var na -> is_alloc_var (na + 2).
Proof. intros na; rewrite (proj2 (flip_rw na)); auto. Qed.

Lemma alloc_or_stack_not_phy na : is_alloc_var na \/ is_stack_var na -> ~ is_phy_var na.
Proof.
  unfold is_true, is_alloc_var, is_stack_var, is_phy_var; rewrite !N.eqb_eq. intros H Hp.
  pose proof (N.div_mod na 4 ltac:(lia)) as E1. pose proof (N.div_mod na 2 ltac:(lia)) as E2. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_props" *)
Theorem list_next_var_rename_props : forall ls ssa na ls' ssa' na',
  list_next_var_rename ls ssa na = (ls', (ssa', na')) ->
  (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa ->
  na <= na' /\
  (is_alloc_var na -> is_alloc_var na') /\
  (is_stack_var na -> is_stack_var na') /\
  ssa_map_ok na' ssa'.
Proof.
  induction ls as [|h ls IH]; intros ssa na ls' ssa' na' E (Hv & Hok); cbn [list_next_var_rename next_var_rename] in E.
  - injection E as <- <- <-. split; [lia|auto].
  - destruct (list_next_var_rename ls (insert h na ssa) (na + 4)) as [ys [s2 n2]] eqn:E2.
    injection E as <- <- <-.
    destruct (IH _ _ _ _ _ E2) as (H1 & H2 & H3 & H4).
    + split; [destruct Hv; [left; apply is_alloc_var_add|right; apply is_stack_var_add]; assumption|].
      apply ssa_map_ok_extend. split; [exact Hok|apply alloc_or_stack_not_phy, Hv].
    + split; [lia|split; [intros Ha; apply H2, is_alloc_var_add, Ha|split; [intros Hs; apply H3, is_stack_var_add, Hs|exact H4]]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_props" *)
Theorem list_next_var_rename_move_props : forall ls ssa na ls' ssa' na',
  @list_next_var_rename_move a ssa na ls = (ls', (ssa', na')) ->
  (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa ->
  na <= na' /\
  (is_alloc_var na -> is_alloc_var na') /\
  (is_stack_var na -> is_stack_var na') /\
  ssa_map_ok na' ssa'.
Proof.
  intros ls ssa na ls' ssa' na' E H. unfold list_next_var_rename_move in E.
  destruct (list_next_var_rename ls ssa na) as [l1 [s1 n1]] eqn:E1. injection E as <- <- <-.
  exact (list_next_var_rename_props _ _ _ _ _ _ E1 H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "next_var_rename_props" *)
Theorem next_var_rename_props : forall ls ssa na ls' ssa' na',
  next_var_rename ls ssa na = (ls', (ssa', na')) ->
  (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa ->
  na <= na' /\
  (is_alloc_var na -> is_alloc_var na') /\
  (is_stack_var na -> is_stack_var na') /\
  ssa_map_ok na' ssa'.
Proof.
  intros ls ssa na ls' ssa' na' E H. apply (list_next_var_rename_props [ls] ssa na [ls']).
  cbn [list_next_var_rename]. rewrite E. reflexivity. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_lem" *)
Theorem ssa_map_ok_lem : forall na ssa, ssa_map_ok na ssa -> ssa_map_ok (na + 2) ssa.
Proof. intros na ssa H; apply (ssa_map_ok_more na); split; [exact H|lia]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_next_var_rename_move_props_2" *)
Theorem list_next_var_rename_move_props_2 : forall ls ssa na ls' ssa' na',
  @list_next_var_rename_move a ssa (na + 2) ls = (ls', (ssa', na')) ->
  (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa ->
  (na + 2) <= na' /\
  (is_alloc_var na -> is_stack_var na') /\
  (is_stack_var na -> is_alloc_var na') /\
  ssa_map_ok na' ssa'.
Proof.
  intros ls ssa na ls' ssa' na' E (Hv & Hok).
  destruct (list_next_var_rename_move_props _ _ _ _ _ _ E) as (H1 & H2 & H3 & H4).
  - split; [destruct Hv; [right; apply is_alloc_var_flip|left; apply is_stack_var_flip]; assumption|].
    apply ssa_map_ok_lem, Hok.
  - split; [exact H1|split; [intros Ha; apply H3, is_alloc_var_flip, Ha|split; [intros Hs; apply H2, is_stack_var_flip, Hs|exact H4]]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_inter" *)
Theorem ssa_map_ok_inter : forall {B} na ssa (ssa' : num_map B),
  ssa_map_ok na ssa -> ssa_map_ok na (inter ssa ssa').
Proof.
  intros B na ssa ssa' H x y Hx. rewrite lookup_inter in Hx.
  destruct (lookup x ssa) eqn:E, (lookup x ssa'); try discriminate. injection Hx as <-. eapply H; exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_insert" *)
Theorem ssa_map_ok_insert : forall na ssa x y,
  ssa_map_ok na ssa /\ y < na /\ ~ is_phy_var y -> ssa_map_ok na (insert x y ssa).
Proof.
  intros na ssa x y (H & Hy & Hp) z w Hz. rewrite lookup_insert' in Hz.
  destruct (decide (z = x)); [injection Hz as <-; auto|eapply H; exact Hz].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_force_rename" *)
Theorem ssa_map_ok_force_rename : forall na ls ssa,
  ssa_map_ok na ssa /\
  EVERY (fun x => bool_decide (SND x < na /\ ~ is_phy_var (SND x))) ls ->
  ssa_map_ok na (force_rename ls ssa).
Proof.
  intros na ls; induction ls as [|[x y] ls IH]; intros ssa [Hok He]; [exact Hok|].
  cbn [force_rename]. cbn [EVERY] in He. apply andb_prop in He as [Hh He]. apply bool_decide_spec in Hh.
  cbn [SND] in Hh. apply IH. split; [|exact He]. apply ssa_map_ok_insert. tauto.
Qed.
Ltac destr_lets E :=
  repeat match type of E with
  | context [match ?X with (_, _) => _ end] =>
      lazymatch X with
      | (_, _) => fail
      | _ => tryif is_var X then destruct X else (let Ex := fresh "Ex" in destruct X eqn:Ex)
      end; cbn beta iota zeta in E
  end.

Definition Inv (na : N) (ssa : num_map N) : Prop := ssa_map_ok na ssa /\ is_alloc_var na.

Lemma Inv_step na ssa h : Inv na ssa -> Inv (na + 4) (insert h na ssa).
Proof.
  intros [Hok Ha]. split; [|apply is_alloc_var_add, Ha].
  apply ssa_map_ok_extend. split; [exact Hok|]. rewrite is_alloc_var_not_phy by exact Ha. discriminate.
Qed.

Lemma Inv_more na ssa na' : Inv na ssa -> na <= na' -> ssa_map_ok na' ssa.
Proof. intros [H _] Hle. apply (ssa_map_ok_more na); auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_inst_props" *)
Theorem ssa_cc_trans_inst_props : forall i ssa na i' ssa' na',
  @ssa_cc_trans_inst a i ssa na = (i', (ssa', na')) ->
  ssa_map_ok na ssa /\ is_alloc_var na ->
  na <= na' /\ is_alloc_var na' /\ ssa_map_ok na' ssa'.
Proof.
  intros i ssa na i' ssa' na' E HI. change (Inv na ssa) in HI.
  cut (na <= na' /\ Inv na' ssa'); [intros [H1 [H2 H3]]; auto|].
  destruct_inst i; cbn [ssa_cc_trans_inst next_var_rename] in E;
    repeat match type of E with
           | context [if ?b then _ else _] => destruct b
           | context [match ?r with Reg _ => _ | Imm _ => _ end] => destruct r
           end;
    injection E as <- <- <-;
    first [split; [lia|exact HI]
          |split; [lia|apply Inv_step, HI]
          |split; [lia|replace (na + 4 + 4) with (na + 4 + 4) by reflexivity; apply Inv_step, Inv_step, HI]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fix_inconsistencies_props" *)
Theorem fix_inconsistencies_props : forall prio ssaL ssaR na a0 b na' ssaU,
  @fix_inconsistencies a prio ssaL ssaR na = (a0, (b, (na', ssaU))) ->
  is_alloc_var na /\ ssa_map_ok na ssaL /\ ssa_map_ok na ssaR ->
  na <= na' /\ is_alloc_var na' /\ ssa_map_ok na' ssaU.
Proof.
  intros prio ssaL ssaR na a0 b na' ssaU E (Ha & HL & HR). unfold fix_inconsistencies in E.
  set (vu := MAP FST (toAList (union ssaL ssaR))) in E.
  pose proof (merge_moves_frame vu na ssaL ssaR Ha) as Fr.
  destruct (merge_moves vu ssaL ssaR na) as [mL [mR [n' [sL sR]]]].
  destruct Fr as (Ha' & Hle & HL' & HR'). specialize (HL' HL).
  pose proof (fake_moves_frame prio vu n' sL sR Ha') as Fk.
  destruct (fake_moves prio vu sL sR n') as [fL [fR [n'' [sL' sR']]]].
  destruct Fk as (Ha'' & Hle' & HL'' & _). injection E as <- <- <- <-.
  split; [lia|split; [exact Ha''|apply HL'', HL']].
Qed.
Lemma lnvr_Inv ls ssa na l s n :
  list_next_var_rename ls ssa na = (l, (s, n)) -> Inv na ssa -> na <= n /\ Inv n s.
Proof.
  intros E [Hok Ha]. destruct (list_next_var_rename_props _ _ _ _ _ _ E (conj (or_introl Ha) Hok)) as (H1 & H2 & _ & H4).
  split; [exact H1|split; [exact H4|apply H2, Ha]].
Qed.

Lemma lnvrm_Inv ls ssa na (l : prog a) s n :
  list_next_var_rename_move ssa na ls = (l, (s, n)) -> Inv na ssa -> na <= n /\ Inv n s.
Proof.
  intros E [Hok Ha]. destruct (list_next_var_rename_move_props _ _ _ _ _ _ E (conj (or_introl Ha) Hok)) as (H1 & H2 & _ & H4).
  split; [exact H1|split; [exact H4|apply H2, Ha]].
Qed.

Lemma lnvrm2_Inv ls ssa na (l : prog a) s n :
  list_next_var_rename_move ssa (na + 2) ls = (l, (s, n)) -> Inv na ssa ->
  na + 2 <= n /\ ssa_map_ok n s /\ is_stack_var n.
Proof.
  intros E [Hok Ha]. destruct (list_next_var_rename_move_props_2 _ _ _ _ _ _ E (conj (or_introl Ha) Hok)) as (H1 & H2 & _ & H4).
  split; [exact H1|split; [exact H4|apply H2, Ha]].
Qed.

Lemma lnvrm_stack_Inv ls ssa na (l : prog a) s n :
  list_next_var_rename_move ssa (na + 2) ls = (l, (s, n)) -> is_stack_var na -> ssa_map_ok na ssa ->
  na + 2 <= n /\ Inv n s.
Proof.
  intros E Hs Hok. destruct (list_next_var_rename_move_props_2 _ _ _ _ _ _ E (conj (or_intror Hs) Hok)) as (H1 & _ & H3 & H4).
  split; [exact H1|split; [exact H4|apply H3, Hs]].
Qed.

Lemma loop_setup_Inv names exit_names ssa na (p : prog a) s n :
  loop_setup names exit_names ssa na = (p, (s, n)) -> Inv na ssa -> na <= n /\ Inv n s.
Proof.
  intros E HI. unfold loop_setup in E.
  destruct (list_next_var_rename _ ssa na) as [l1 [s1 n1]] eqn:E1.
  destruct (list_next_var_rename_move s1 n1 _) as [l2 [s2 n2]] eqn:E2. injection E as <- <- <-.
  destruct (lnvr_Inv _ _ _ _ _ _ E1 HI) as [H1 HI1]. destruct (lnvrm_Inv _ _ _ _ _ _ E2 HI1) as [H2 HI2].
  split; [lia|exact HI2].
Qed.

Lemma In_COUNT_LIST i n : In i (COUNT_LIST n) -> i < n.
Proof.
  revert i; induction n as [|n IH] using N.peano_ind; intros i Hi; [destruct Hi|].
  rewrite (proj2 (COUNT_LIST_def n)) in Hi. destruct Hi as [<-|Hi]; [lia|].
  apply in_map_iff in Hi as [j [<- Hj]]. specialize (IH _ Hj). lia.
Qed.

Lemma ssa_map_ok_force_rename_move ls ssa na ren ssa' na' :
  list_next_var_rename (MAP FST ls) ssa na = (ren, (ssa', na')) -> Inv na ssa ->
  ssa_map_ok na' (force_rename (FILTER (fun '(x, y) => negb (MEM x (MAP FST ls))) (ZIP (MAP SND ls, ren))) ssa').
Proof.
  intros E HI. destruct (lnvr_Inv _ _ _ _ _ _ E HI) as [_ [Hok _]].
  destruct (list_next_var_rename_lemma_1 _ _ _ _ _ _ E) as (_ & Hren & Hna).
  apply ssa_map_ok_force_rename. split; [exact Hok|].
  unfold is_true; rewrite EVERY_Forall, Forall_forall. intros [x y] Hxy.
  apply filter_In in Hxy as [Hxy _]. rewrite ZIP_combine' in Hxy. apply in_combine_r in Hxy.
  rewrite Hren in Hxy. apply in_map_iff in Hxy as [i [<- Hi]]. apply In_COUNT_LIST in Hi.
  apply bool_decide_spec. cbn [SND]. split; [lia|].
  rewrite is_phy_var_4, is_alloc_var_not_phy by (destruct HI; assumption). discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_props" *)
Theorem ssa_cc_trans_props : forall prog ssa na lt prog' ssa' na',
  @ssa_cc_trans a prog ssa na lt = (prog', (ssa', na')) ->
  ssa_map_ok na ssa /\ is_alloc_var na ->
  na <= na' /\ is_alloc_var na' /\ ssa_map_ok na' ssa'.
Proof.
  intros prog.
  cut (forall ssa na lt prog' ssa' na', @ssa_cc_trans a prog ssa na lt = (prog', (ssa', na')) ->
         Inv na ssa -> na <= na' /\ Inv na' ssa').
  { intros H ssa na lt prog' ssa' na' E HI. destruct (H _ _ _ _ _ _ E HI) as [? [? ?]]. auto. }
  induction prog as [| | | | | | |p IH|ret dest args h IHr IHh|p1 p2 IH1 IH2|cmp r ri p1 p2 IH1 IH2
                     |n1 p n2 IH| | | | | | | | | | | | | |] using prog_nested_ind;
    intros ssa na lt prog' ssa' na' E HI; cbn [ssa_cc_trans next_var_rename] in E; destr_lets E.
  (* Skip *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* Move *)
  - injection E as <- <- <-. destruct (lnvr_Inv _ _ _ _ _ _ Ex HI) as [H1 [_ Ha]].
    split; [exact H1|split; [|exact Ha]]. eapply ssa_map_ok_force_rename_move; eassumption.
  (* Inst *)
  - injection E as <- <- <-. destruct HI as [H1 H2].
    destruct (ssa_cc_trans_inst_props _ _ _ _ _ _ Ex (conj H1 H2)) as (? & ? & ?). split; [lia|split; assumption].
  (* Assign *)
  - injection E as <- <- <-. split; [lia|apply Inv_step, HI].
  (* Get *)
  - injection E as <- <- <-. split; [lia|apply Inv_step, HI].
  (* Set *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* Store *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* MustTerminate *)
  - injection E as <- <- <-. eapply IH; eassumption.
  (* Call *)
  - destruct ret as [[rv [numset [rh [l1 l2]]]]|]; cbn beta iota zeta in E; destr_lets E;
      [|injection E as <- <- <-; split; [lia|exact HI]].
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    destruct (lnvrm_stack_Inv _ _ _ _ _ _ Ex0 H3 (ssa_map_ok_inter _ _ _ H2)) as (H4 & HI4).
    destruct (lnvr_Inv _ _ _ _ _ _ Ex1 HI4) as (H5 & HI5).
    destruct (IHr _ _ _ _ _ _ Ex2 HI5) as (H6 & HI6).
    destruct h as [[hn [hp [l1' l2']]]|]; cbn beta iota zeta in E; destr_lets E;
      [|injection E as <- <- <-; split; [lia|exact HI6]].
    assert (HI7 : Inv (n2 + 4) (insert hn n2 s0)).
    { apply Inv_step. split; [apply (Inv_more _ _ _ HI4); lia|apply HI6]. }
    destruct (IHh _ _ _ _ _ _ Ex3 HI7) as (H8 & HI8).
    injection E as <- <- <-.
    destruct (fix_inconsistencies_props _ _ _ _ _ _ _ _ Ex4) as (H9 & H10 & H11).
    + split; [apply HI8|split; [apply (Inv_more _ _ _ HI6); lia|apply HI8]].
    + split; [lia|split; assumption].
  (* Seq *)
  - injection E as <- <- <-.
    destruct (IH1 _ _ _ _ _ _ Ex HI) as [H1 HI1]. destruct (IH2 _ _ _ _ _ _ Ex0 HI1) as [H2 HI2].
    split; [lia|exact HI2].
  (* If *)
  - injection E as <- <- <-.
    destruct (IH1 _ _ _ _ _ _ Ex HI) as [H1 HI1].
    destruct (IH2 _ _ _ _ _ _ Ex0 (conj (Inv_more _ _ _ HI H1) (proj2 HI1))) as [H2 HI2].
    destruct (fix_inconsistencies_props _ _ _ _ _ _ _ _ Ex1) as (H3 & H4 & H5).
    + split; [apply HI2|split; [apply (Inv_more _ _ _ HI1); lia|apply HI2]].
    + split; [lia|split; assumption].
  (* Loop *)
  - injection E as <- <- <-.
    destruct (loop_setup_Inv _ _ _ _ _ _ _ Ex HI) as [H1 HI1].
    destruct (IH _ _ _ _ _ _ Ex0 (conj (ssa_map_ok_inter _ _ _ (proj1 HI1)) (proj2 HI1))) as [H2 HI2].
    split; [lia|split; [|apply HI2]]. apply ssa_map_ok_inter. apply (Inv_more _ _ _ HI1); lia.
  (* Alloc *)
  - injection E as <- <- <-.
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    destruct (lnvrm_stack_Inv _ _ _ _ _ _ Ex0 H3 (ssa_map_ok_inter _ _ _ H2)) as (H4 & HI4).
    split; [lia|exact HI4].
  (* StoreConsts *)
  - injection E as <- <- <-. split; [lia|apply Inv_step, Inv_step, HI].
  (* Raise *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* Return *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* Break *)
  - destruct (oEL _ lt) as [[? [? ?]]|]; injection E as <- <- <-; split; [lia|exact HI|lia|exact HI].
  (* Continue *)
  - destruct (oEL _ lt) as [[? [? ?]]|]; injection E as <- <- <-; split; [lia|exact HI|lia|exact HI].
  (* Tick *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* OpCurrHeap *)
  - injection E as <- <- <-. split; [lia|apply Inv_step, HI].
  (* LocValue *)
  - injection E as <- <- <-. split; [lia|apply Inv_step, HI].
  (* Install *)
  - injection E as <- <- <-.
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    match type of Ex0 with list_next_var_rename_move ?S0 ?N0 _ = _ => assert (HI2 : Inv N0 S0) end.
    { apply Inv_step. split; [apply ssa_map_ok_inter, ssa_map_ok_lem, H2|apply is_stack_var_flip, H3]. }
    destruct (lnvrm_Inv _ _ _ _ _ _ Ex0 HI2) as (H4 & HI4). split; [lia|exact HI4].
  (* CodeBufferWrite *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* DataBufferWrite *)
  - injection E as <- <- <-. split; [lia|exact HI].
  (* FFI *)
  - injection E as <- <- <-.
    destruct (lnvrm2_Inv _ _ _ _ _ _ Ex HI) as (H1 & H2 & H3).
    destruct (lnvrm_stack_Inv _ _ _ _ _ _ Ex0 H3 (ssa_map_ok_inter _ _ _ H2)) as (H4 & HI4).
    split; [lia|exact HI4].
  (* ShareInst *)
  - destruct (bool_decide _); destr_lets E; injection E as <- <- <-; split; [lia|exact HI|lia|apply Inv_step, HI].
Qed.
End SSA1.
