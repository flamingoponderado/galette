(** * CakeML [word_allocProof]: dead code removal

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    3479-4506): [live_store_rel], [nlive_store], [evaluate_remove_dead] and
    [evaluate_remove_dead_prog].

    Notes:
    - HOL [st with <| locals := t; store := tstore |>] is
      [set_store_field tstore (set_locals t st)]; HOL's [I] is [combin.I].
    - [nlive_store] is boolean (HOL's [s ∉ set nlive] is [negb (MEM s nlive)]).
    - HOL's [simp] rewrites [st_eq], [with_same_store], [with_same_locals]
      are stated as equations on [set_store_field]/[set_locals].
    - [evaluate_remove_dead] is proved by structural induction on the
      program (HOL: [remove_dead_ind]); the [Loop] case is
      [evaluate_remove_dead_Loop_helper] (induction on the clock).  The
      Galette-only lemmas and tactics have no tag. *)

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
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring clash.
Open Scope N_scope.

Section RD.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "apply_colour_exp_I" *)
Theorem apply_colour_exp_I : forall (exp : exp a), apply_colour_exp I exp = exp.
Proof.
  intros exp; induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [apply_colour_exp]; try reflexivity.
  - rewrite IH; reflexivity.
  - f_equal. rewrite Forall_forall in IH. induction es as [|e es IHes]; [reflexivity|].
    cbn [MAP List.map]. rewrite IH by (left; reflexivity). f_equal. apply IHes. intros x Hx; apply IH; right; exact Hx.
  - rewrite IH1, IH2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_def" *)
Definition live_store_rel (nlive : list store_name) (sstore tstore : fmap store_name (word_loc a)) : Prop :=
  forall n, ~ n IN set nlive -> FLOOKUP sstore n = FLOOKUP tstore n.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_less" *)
Theorem live_store_rel_less : forall ls ls' st tt,
  live_store_rel ls st tt /\ set ls SUBSET set ls' -> live_store_rel ls' st tt.
Proof. intros ls ls' st tt [H Hs] n Hn. apply H. intros Hn'. apply Hn, Hs, Hn'. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_FLOOKUP_store" *)
Theorem live_store_rel_FLOOKUP_store : forall ls sstore tstore s,
  live_store_rel ls sstore tstore /\ ~ s IN set ls -> FLOOKUP tstore s = FLOOKUP sstore s.
Proof. intros ls sstore tstore s [H Hs]. symmetry; apply H, Hs. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "nlive_store_def" *)
Fixpoint nlive_store (nlive : list store_name) (e : exp a) : bool :=
  match e with
  | Op _ ls => EVERY (nlive_store nlive) ls
  | Lookup s => negb (MEM s nlive)
  | Load e => nlive_store nlive e
  | Shift _ e1 e2 => nlive_store nlive e1 && nlive_store nlive e2
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_get_var" *)
Theorem strong_locals_rel_I_get_var : forall x (st : state) v live t tstore,
  get_var x st = SOME v /\ strong_locals_rel I (x INSERT live) (locals st) t ->
  get_var x (set_store_field tstore (set_locals t st)) = SOME v.
Proof. intros x st v live t tstore [Hg Hs]. apply Hs. split; [left; reflexivity|exact Hg]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_get_var'" *)
Theorem strong_locals_rel_I_get_var' : forall x (st : state) v live t,
  get_var x st = SOME v /\ strong_locals_rel I (x INSERT live) (locals st) t ->
  get_var x (set_locals t st) = SOME v.
Proof. intros x st v live t [Hg Hs]. apply Hs. split; [left; reflexivity|exact Hg]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_word_exp" *)
Theorem strong_locals_rel_I_word_exp : forall (st : state) (exp : exp a) res live t nlive tstore,
  word_exp st exp = SOME res /\
  strong_locals_rel I (domain (union (get_live_exp exp) live)) (locals st) t /\
  live_store_rel nlive (store st) tstore /\
  nlive_store nlive exp ->
  word_exp (set_store_field tstore (set_locals t st)) exp = SOME res.
Proof.
  intros st exp; induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros res live t nlive tstore (H & Hs & Hst & Hn); cbn [word_exp nlive_store get_live_exp] in *.
  - exact H.
  - apply Hs. split; [|exact H]. rewrite domain_union, domain_insert. left; left; reflexivity.
  - unfold get_store in *. cbn [store set_store_field]. rewrite <- (Hst n); [exact H|].
    rewrite IN_set. intros Hm; apply MEM_iff' in Hm. rewrite Hm in Hn; discriminate.
  - destruct (word_exp st e) as [[w|]|] eqn:E; try discriminate.
    rewrite (IH (Word w) live t nlive tstore); [exact H|]. repeat split; assumption.
  - destruct (the_words (MAP (word_exp st) es)) as [ws|] eqn:Ews; [|discriminate].
    assert (Hmap : MAP (word_exp (set_store_field tstore (set_locals t st))) es = MAP (word_exp st) es).
    { apply map_ext_in. intros e He.
      pose proof (the_words_EVERY_IS_SOME _ _ Ews) as Hev. unfold is_true in Hev.
      rewrite EVERY_Forall, Forall_map, Forall_forall in Hev. specialize (Hev e He).
      destruct (word_exp st e) as [r|] eqn:Ee; [|discriminate].
      rewrite Forall_forall in IH. apply (IH e He r live t nlive tstore). split; [exact Ee|split; [|split; [exact Hst|]]].
      - eapply strong_locals_rel_subset; split; [|exact Hs]. rewrite !domain_union.
        intros x [Hx|Hx]; [left; apply (domain_big_union_subset es e); [apply MEM_iff', He|exact Hx]|right; exact Hx].
      - unfold is_true in Hn. rewrite EVERY_Forall, Forall_forall in Hn. apply Hn, He. }
    rewrite Hmap, Ews. exact H.
  - unfold is_true in Hn. apply andb_prop in Hn as [Hn1 Hn2].
    destruct (word_exp st e1) as [[w1|]|] eqn:E1; try discriminate.
    destruct (word_exp st e2) as [[w2|]|] eqn:E2; try discriminate.
    rewrite (IH1 (Word w1) live t nlive tstore), (IH2 (Word w2) live t nlive tstore); [exact H| |].
    + split; [reflexivity|split; [|split; assumption]]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
    + split; [reflexivity|split; [|split; assumption]]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_insert_notin" *)
Theorem strong_locals_rel_insert_notin : forall {A} f live (s t : num_map A) n v,
  strong_locals_rel f live s t /\ ~ n IN live -> strong_locals_rel f live (insert n v s) t.
Proof.
  intros A f live s t n v [Hs Hn] m w [Hm Hl]. rewrite lookup_insert in Hl.
  destruct (decide (m = n)) as [->|]; [contradiction|]. apply Hs; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_get_vars'" *)
Theorem strong_locals_rel_I_get_vars' : forall ls live (st : state) t vs,
  (forall x, MEM x ls -> x IN live) /\
  strong_locals_rel I live (locals st) t /\
  get_vars ls st = SOME vs ->
  get_vars ls (set_locals t st) = SOME vs.
Proof.
  intros ls live st t vs (Hm & Hs & H).
  pose proof (strong_locals_rel_get_vars ls vs I live st (set_locals t st) (conj Hs (conj Hm H))) as G.
  replace (MAP I ls) with ls in G by (clear; induction ls as [|x ls IH]; [reflexivity|cbn; unfold I; f_equal; exact IH]). exact G.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_cut_envs" *)
Theorem strong_locals_rel_I_cut_envs : forall (cutset : cutsets) (st : state) t x,
  strong_locals_rel I (domain (FST cutset) UNION domain (SND cutset)) (locals st) t /\
  cut_envs cutset (locals st) = SOME x ->
  cut_envs cutset t = SOME x.
Proof.
  intros [c1 c2] st t x [Hs H]. unfold cut_envs, cut_names in *. cbn [FST SND fst snd] in *.
  assert (Hc : forall (c : num_set), domain c SUBSET domain (locals st) ->
            (forall n, n IN domain c -> forall v, lookup n (locals st) = Some v -> lookup n t = Some v) ->
            domain c SUBSET domain t /\ inter t c = inter (locals st) c).
  { intros cc Hsub Hrel. split.
    - intros n Hn. pose proof (Hsub n Hn) as Hn'. apply IN_domain_iff in Hn' as [v Hv].
      apply IN_domain_iff. exists v. apply (Hrel n Hn v Hv).
    - apply spt_eq_thm; [split; apply wf_inter|]. intros n. rewrite !lookup_inter.
      destruct (lookup n cc) as [u|] eqn:Ec; [|destruct (lookup n t), (lookup n (locals st)); reflexivity].
      assert (Hn : n IN domain cc) by (apply IN_domain_iff; eauto).
      pose proof (Hsub n Hn) as Hn'. apply IN_domain_iff in Hn' as [v Hv].
      rewrite Hv, (Hrel n Hn v Hv). reflexivity. }
  destruct (classical_dec (domain c1 SUBSET domain (locals st))) as [S1|]; [|discriminate].
  destruct (classical_dec (domain c2 SUBSET domain (locals st))) as [S2|]; [|discriminate].
  injection H as <-.
  destruct (Hc c1 S1) as [T1 E1]; [intros n Hn v Hv; apply (Hs n v); split; [left; exact Hn|exact Hv]|].
  destruct (Hc c2 S2) as [T2 E2]; [intros n Hn v Hv; apply (Hs n v); split; [right; exact Hn|exact Hv]|].
  destruct (classical_dec (domain c1 SUBSET domain t)); [|contradiction].
  destruct (classical_dec (domain c2 SUBSET domain t)); [|contradiction].
  rewrite E1, E2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_cut_env" *)
Theorem strong_locals_rel_I_cut_env : forall (cutset : cutsets) (st : state) t x,
  strong_locals_rel I (domain (FST cutset) UNION domain (SND cutset)) (locals st) t /\
  cut_env cutset (locals st) = SOME x ->
  cut_env cutset t = SOME x.
Proof.
  intros cutset st t x [Hs H]. unfold cut_env in *.
  destruct (cut_envs cutset (locals st)) as [envs|] eqn:E; [|discriminate].
  rewrite (strong_locals_rel_I_cut_envs cutset st t envs (conj Hs E)). exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_eq" *)
Theorem get_vars_eq : forall ls (st : state),
  set ls SUBSET domain (locals st) ->
  exists z, get_vars ls st = SOME z /\ z = MAP (fun x => THE (lookup x (locals st))) ls.
Proof.
  induction ls as [|x ls IH]; intros st H; [exists []; split; reflexivity|].
  destruct (IH st) as [z [Ez ->]]; [intros y Hy; apply H; right; exact Hy|].
  assert (Hx : x IN domain (locals st)) by (apply H; left; reflexivity).
  apply IN_domain_iff in Hx as [v Hv].
  exists (v :: MAP (fun x => THE (lookup x (locals st))) ls). cbn [get_vars MAP List.map]. unfold get_var.
  rewrite Hv, Ez. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_vars_exists" *)
Theorem get_vars_exists : forall ls (st : state),
  (exists z, get_vars ls st = SOME z) <-> set ls SUBSET domain (locals st).
Proof.
  induction ls as [|x ls IH]; intros st; [split; [intros _ y []|intros _; exists []; reflexivity]|].
  cbn [get_vars]. unfold get_var. split.
  - intros [z Hz]. destruct (lookup x (locals st)) as [v|] eqn:Ev; [|discriminate].
    destruct (get_vars ls st) as [zs|] eqn:Ezs; [|discriminate].
    intros y [->|Hy]; [apply IN_domain_iff; eauto|]. apply (proj1 (IH st) (ex_intro _ zs Ezs)), Hy.
  - intros H. assert (Hx : x IN domain (locals st)) by (apply H; left; reflexivity).
    apply IN_domain_iff in Hx as [v Hv]. rewrite Hv.
    destruct (proj2 (IH st) (fun y Hy => H y (or_intror Hy))) as [zs Ezs]. rewrite Ezs. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_I_insert_insert" *)
Theorem strong_locals_rel_I_insert_insert : forall {A} live p (A0 B : num_map A) v v',
  strong_locals_rel I (live DELETE p) A0 B /\ v = v' ->
  strong_locals_rel I live (insert p v A0) (insert p v' B).
Proof.
  intros A live p A0 B v v' [Hs <-] n w [Hn Hl]. unfold I. rewrite lookup_insert in Hl |- *.
  destruct (decide (n = p)) as [->|Hne]; [exact Hl|].
  apply (Hs n w). split; [split; [exact Hn|intros [E|[]]; contradiction]|exact Hl].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "st_eq" *)
Theorem st_eq : forall (rst : state) t tstore t' tstore',
  set_store_field tstore (set_locals t rst) = set_store_field tstore' (set_locals t' rst) <->
  t = t' /\ tstore = tstore'.
Proof.
  intros rst t tstore t' tstore'. split; [|intros [-> ->]; reflexivity].
  intros H. split; [apply (f_equal locals) in H|apply (f_equal store) in H]; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_NIL" *)
Theorem live_store_rel_NIL : forall (sstore tstore : fmap store_name (word_loc a)),
  live_store_rel [] sstore tstore <-> sstore = tstore.
Proof.
  intros sstore tstore. split; [|intros ->; intros n _; reflexivity].
  intros H. apply fmap_eq_flookup. intros x. apply H. intros [].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_refl" *)
Theorem live_store_rel_refl : forall ls (sstore : fmap store_name (word_loc a)), live_store_rel ls sstore sstore.
Proof. intros ls sstore n _; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "with_same_store" *)
Theorem with_same_store : forall (st : state), set_store_field (store st) st = st.
Proof. intros st; destruct st; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "with_same_locals" *)
Theorem with_same_locals : forall (st : state), set_locals (locals st) st = st.
Proof. intros st; destruct st; reflexivity. Qed.

(** ** Galette-only: states differing in their locals and store *)

Definition RS (t : num_map (word_loc a)) (ts : fmap store_name (word_loc a)) (s : state) : state :=
  set_store_field ts (set_locals t s).

Lemma RS_set_locals t ts l s : RS t ts (set_locals l s) = RS t ts s.
Proof. destruct s; reflexivity. Qed.
Lemma RS_set_store_field t ts ts' s : RS t ts (set_store_field ts' s) = RS t ts s.
Proof. destruct s; reflexivity. Qed.
Lemma RS_set_var t ts v x s : RS t ts (set_var v x s) = RS t ts s.
Proof. destruct s; reflexivity. Qed.
Lemma set_var_RS t ts v x s : set_var v x (RS t ts s) = RS (insert v x t) ts s.
Proof. destruct s; reflexivity. Qed.
Lemma set_memory_RS t ts m s : set_memory m (RS t ts s) = RS t ts (set_memory m s).
Proof. destruct s; reflexivity. Qed.
Lemma set_fp_var_RS t ts d x s : set_fp_var d x (RS t ts s) = RS t ts (set_fp_var d x s).
Proof. destruct s; reflexivity. Qed.
Lemma RS_same s : RS (locals s) (store s) s = s.
Proof. destruct s; reflexivity. Qed.
Lemma locals_RS t ts s : locals (RS t ts s) = t.
Proof. reflexivity. Qed.
Lemma store_RS t ts s : store (RS t ts s) = ts.
Proof. reflexivity. Qed.

Ltac slrI Hs :=
  repeat (apply strong_locals_rel_I_insert_insert; split; [|reflexivity]);
  eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve.

Lemma inst_rd (i : asm.inst a) (st s1 : state) live t ts :
  remove_dead_inst i live = false ->
  strong_locals_rel I (domain (get_live_inst i live)) (locals st) t ->
  inst i st = SOME s1 ->
  exists t', inst i (RS t ts st) = SOME (RS t' ts s1) /\ strong_locals_rel I (domain live) (locals s1) t'.
Proof.
  intros Hd Hs H.
  assert (Hg : forall r v, r IN domain (get_live_inst i live) -> get_var r st = Some v ->
                 get_var r (RS t ts st) = Some v)
    by (intros r v Hr Hv; apply Hs; split; assumption).
  destruct_inst i;
    cbv beta iota zeta delta [inst wordSem.assign get_live_inst remove_dead_inst get_vars] in *;
    cbn [word_exp the_words MAP List.map] in *;
    unfold mem_load, mem_store, get_fp_var, set_fp_var in *;
    split_in H; try discriminate H; try (injection H as <-); subst;
    repeat match goal with
           | E : get_var ?r st = Some ?v |- context [get_var ?r (RS t ts st)] =>
               rewrite (Hg r v ltac:(in_solve) E)
           end;
    cbn [RS memory mdomain be fp_regs set_store_field set_locals] in *;
    rw_eqs; try discriminate Hd;
    (eexists; split;
    [ f_equal; rewrite ?set_var_RS, ?set_memory_RS, ?set_fp_var_RS, ?RS_set_var; reflexivity
    | cbn_ws; slrI Hs ]).
Qed.

Lemma inst_dead (i : asm.inst a) (st s1 : state) live :
  remove_dead_inst i live = true -> inst i st = SOME s1 ->
  s1 = set_locals (locals s1) st /\
  (forall n, n IN domain live -> lookup n (locals s1) = lookup n (locals st)).
Proof.
  intros Hd H.
  destruct_inst i;
    cbv beta iota zeta delta [inst wordSem.assign remove_dead_inst get_vars] in *;
    cbn [word_exp the_words MAP List.map] in *;
    unfold mem_load, mem_store, get_fp_var, set_fp_var in *;
    split_in H; try discriminate H; try discriminate Hd; try (injection H as <-); subst;
    repeat match goal with
           | E : (if ?b then _ else _) = true |- _ => destruct b eqn:?
           | E : _ && _ = true |- _ => apply andb_prop in E as [? ?]
           | E : bool_decide _ = true |- _ => apply bool_decide_spec in E
           end; try discriminate;
    (split; [destruct st; reflexivity|]);
    intros nn Hn; cbn_ws; rewrite ?lookup_insert;
    repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); [subst|] end;
    try reflexivity;
    exfalso; apply IN_domain_iff in Hn as [v Hv]; congruence.
Qed.

(** ** Galette-only: [Move] helpers *)

Lemma lookup_alist_insert_get_vars (ls : list (N * N)) (s : state) vs n :
  get_vars (MAP SND ls) s = SOME vs ->
  lookup n (alist_insert (MAP FST ls) vs (locals s)) =
  match ALOOKUP ls n with Some y => lookup y (locals s) | None => lookup n (locals s) end.
Proof.
  revert vs; induction ls as [|[x y] ls IH]; intros vs H; cbn [MAP List.map get_vars FST SND fst snd] in *.
  - injection H as <-. reflexivity.
  - unfold get_var in H. destruct (lookup y (locals s)) as [v|] eqn:Ey; [|discriminate].
    destruct (get_vars (MAP SND ls) s) as [vs'|] eqn:Es; [|discriminate]. injection H as <-.
    cbn [alist_insert ALOOKUP fst snd]. rewrite lookup_insert, (IH vs' eq_refl).
    destruct (decide (n = x)) as [->|Hne].
    + destruct (decide (x = x)); [rewrite Ey; reflexivity|congruence].
    + destruct (decide (x = n)); [congruence|reflexivity].
Qed.

Lemma ALOOKUP_FILTER_key (ls : list (N * N)) (P : N -> bool) n :
  P n = true -> ALOOKUP (FILTER (fun '(x, y) => P x) ls) n = ALOOKUP ls n.
Proof.
  intros Hn; induction ls as [|[x y] ls IH]; [reflexivity|]. cbn [FILTER List.filter ALOOKUP].
  destruct (P x) eqn:Ex; cbn [ALOOKUP]; destruct (decide (x = n)) as [->|]; try rewrite IH; try reflexivity.
  congruence.
Qed.

Lemma NoDup_map_filter {A B} (f : A -> B) (P : A -> bool) l :
  NoDup (List.map f l) -> NoDup (List.map f (List.filter P l)).
Proof.
  induction l as [|x l IH]; intros H; cbn; [constructor|]. inversion H as [|? ? Hx Hl]; subst.
  destruct (P x); [|apply IH, Hl]. constructor; [|apply IH, Hl].
  intros Hin. apply Hx. apply in_map_iff in Hin as [y [<- Hy]]. apply filter_In in Hy as [Hy _].
  apply in_map, Hy.
Qed.

Lemma get_vars_sub (xs ys : list N) (s : state) vs :
  get_vars xs s = SOME vs -> (forall y, In y ys -> In y xs) -> exists vs', get_vars ys s = SOME vs'.
Proof.
  intros H Hsub. apply get_vars_exists. pose proof (proj1 (get_vars_exists xs s) (ex_intro _ vs H)) as Hx.
  intros y Hy. apply Hx. rewrite IN_set in *. apply Hsub, Hy.
Qed.

Definition rd_post (live : num_set) (nlive : list store_name) (lt : list (num_set * num_set))
    (res : option (result a)) (rst : state) t' tstore' : Prop :=
  match res with
  | NONE => strong_locals_rel I (domain live) (locals rst) t' /\ live_store_rel nlive (store rst) tstore'
  | SOME (Break n) =>
      store rst = tstore' /\
      match oEL n lt with
      | Some (_, exit_names) => strong_locals_rel I (domain exit_names) (locals rst) t'
      | None => True
      end
  | SOME (Continue n) =>
      store rst = tstore' /\
      match oEL n lt with
      | Some (names, _) => strong_locals_rel I (domain names) (locals rst) t'
      | None => True
      end
  | SOME _ => locals rst = t' /\ store rst = tstore'
  end.

Definition rd_IH (p : prog a) : Prop :=
  forall live nlive lt prog' livein nlivein (st : state) t tstore res rst,
  strong_locals_rel I (domain livein) (locals st) t ->
  live_store_rel nlivein (store st) tstore ->
  evaluate (p, st) = (res, rst) ->
  flat_exp_conventions p ->
  remove_dead p live nlive lt = (prog', (livein, nlivein)) ->
  res <> SOME Error ->
  exists t' tstore',
    evaluate (prog', RS t tstore st) = (res, RS t' tstore' rst) /\
    rd_post live nlive lt res rst t' tstore'.

Ltac rd_start :=
  let live := fresh "live" in let nlive := fresh "nlive" in let lt := fresh "lt" in
  let prog' := fresh "prog'" in let livein := fresh "livein" in let nlivein := fresh "nlivein" in
  let st := fresh "st" in let t := fresh "t" in let tstore := fresh "tstore" in
  let res := fresh "res" in let rst := fresh "rst" in
  intros live nlive lt prog' livein nlivein st t tstore res rst Hs Hst Hev Hf Hrd Hr;
  cbn [flat_exp_conventions] in Hf; cbn [remove_dead] in Hrd.

Lemma rd_Move pri ls : rd_IH (Move pri ls).
Proof.
  rd_start. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (ALL_DISTINCT (MAP FST ls)) eqn:Ed; [|err_case Hev Hr].
  destruct (get_vars (MAP SND ls) st) as [vs|] eqn:Eg; [|err_case Hev Hr]. injection Hev as <- <-.
  set (P := fun x => bool_decide (lookup x live = Some tt)).
  replace (FILTER (fun '(x, y) => bool_decide (lookup x live = Some tt)) ls)
    with (FILTER (fun '(x, y) => P x) ls) in Hrd by reflexivity.
  set (ls' := FILTER (fun '(x, y) => P x) ls) in *.
  assert (Hk : forall n, n IN domain live -> ALOOKUP ls' n = ALOOKUP ls n).
  { intros n Hn. apply ALOOKUP_FILTER_key. subst P; cbn beta. apply bd_true'.
    apply IN_domain_iff in Hn as [[] Hn]; exact Hn. }
  destruct ls' as [|p0 ls0] eqn:El.
  - injection Hrd as <- <- <-. exists t, tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. unfold set_vars, RS. f_equal; destruct st; reflexivity.
    + cbn [rd_post]. split; [|unfold set_vars; cbn_ws; exact Hst].
      intros n v [Hn Hl]. unfold set_vars in Hl; cbn_ws.
      change (alist_insert (MAP FST ls) vs (locals st)) with (alist_insert (MAP FST ls) vs (locals st)) in Hl.
      rewrite (lookup_alist_insert_get_vars ls st vs n Eg) in Hl. rewrite <- (Hk n Hn) in Hl. cbn [ALOOKUP] in Hl.
      apply Hs. split; [exact Hn|exact Hl].
  - rewrite <- El in Hrd. injection Hrd as <- <- <-. assert (Hk' : forall n, n IN domain live -> ALOOKUP ls' n = ALOOKUP ls n) by (intros n Hn; rewrite El; apply Hk, Hn). clear Hk El.
    assert (Hsub : forall y, In y (MAP SND ls') -> In y (MAP SND ls)).
    { intros y Hy. apply in_map_iff in Hy as [[x' y'] [<- Hy]]. unfold ls' in Hy.
      apply filter_In in Hy as [Hy _]. apply (in_map snd) in Hy; exact Hy. }
    assert (Hd' : ALL_DISTINCT (MAP FST ls') = true).
    { apply ALL_DISTINCT_iff' in Ed. apply ALL_DISTINCT_iff'. unfold ls'. apply NoDup_map_filter, Ed. }
    destruct (get_vars_sub (MAP SND ls) (MAP SND ls') st vs Eg Hsub) as [vs' Eg'].
    assert (Eg2 : forall ts', get_vars (MAP SND ls') (set_store_field ts' (set_locals t st)) = SOME vs').
    { intros ts'. pose proof (strong_locals_rel_get_vars (MAP SND ls') vs' I
        (domain (numset_list_insert (MAP SND ls') (FOLDR delete live (MAP FST ls')))) st
        (set_store_field ts' (set_locals t st))) as G.
      replace (MAP I (MAP SND ls')) with (MAP SND ls') in G by
        (clear; induction (MAP SND ls') as [|x l IH]; [reflexivity|cbn; unfold I; f_equal; exact IH]).
      apply G. split; [exact Hs|split; [|exact Eg']]. intros x Hx. rewrite domain_numset_list_insert.
      right; apply IN_set, MEM_iff', Hx. }
    exists (alist_insert (MAP FST ls') vs' t), tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. unfold RS. rewrite Hd', Eg2. f_equal; unfold set_vars; destruct st; reflexivity.
    + cbn [rd_post]. split; [|unfold set_vars; cbn_ws; exact Hst].
      intros n v [Hn Hl]. unfold set_vars in Hl; cbn_ws.
      rewrite (lookup_alist_insert_get_vars ls st vs n Eg) in Hl.
      unfold I. change t with (locals (set_store_field tstore (set_locals t st))).
      rewrite (lookup_alist_insert_get_vars ls' _ vs' n (Eg2 tstore)). rewrite (Hk' n Hn).
      cbn_ws. destruct (ALOOKUP ls n) as [y|] eqn:Ea.
      * apply Hs. split; [|exact Hl]. rewrite domain_numset_list_insert. right. apply IN_set.
        rewrite <- (Hk' n Hn) in Ea. apply ALOOKUP_In, (in_map snd) in Ea. exact Ea.
      * apply Hs. split; [|exact Hl]. rewrite domain_numset_list_insert, domain_FOLDR_delete. left.
        split; [exact Hn|]. rewrite <- (Hk' n Hn) in Ea. intros Hm. apply ALOOKUP_NONE in Ea. contradiction.
Qed.

Lemma inst_store (i : asm.inst a) (st s1 : state) : inst i st = SOME s1 -> store s1 = store st.
Proof.
  intros H. destruct_inst i;
    cbv beta iota zeta delta [inst wordSem.assign get_vars] in *;
    cbn [word_exp the_words MAP List.map] in *;
    unfold mem_load, mem_store, get_fp_var, set_fp_var in *;
    split_in H; try discriminate H; try (injection H as <-); subst; reflexivity.
Qed.

Lemma rd_Inst i : rd_IH (Inst i).
Proof.
  rd_start. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (inst i st) as [s1|] eqn:Ei; [|err_case Hev Hr]. injection Hev as <- <-.
  destruct (remove_dead_inst i live) eqn:Ed; injection Hrd as <- <- <-.
  - destruct (inst_dead i st s1 live Ed Ei) as [Es Hl]. exists t, tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Es, RS_set_locals. reflexivity.
    + cbn [rd_post]. split.
      * intros n v [Hn Hlk]. rewrite (Hl n Hn) in Hlk. apply Hs; split; assumption.
      * rewrite (inst_store i st s1 Ei). exact Hst.
  - destruct (inst_rd i st s1 live t tstore Ed Hs Ei) as [t' [E' Hl]]. exists t', tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite E'. reflexivity.
    + cbn [rd_post]. split; [exact Hl|]. rewrite (inst_store i st s1 Ei). exact Hst.
Qed.

Lemma rd_Skip : rd_IH (@Skip a).
Proof.
  rd_start. injection Hrd as <- <- <-. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  injection Hev as <- <-. exists t, tstore. split; [rewrite evaluate_eqn; reflexivity|].
  cbn [rd_post get_live] in *. split; assumption.
Qed.

Lemma rd_Get v n : rd_IH (Get v n).
Proof.
  rd_start. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_store n st) as [x|] eqn:Eg; [|err_case Hev Hr]. injection Hev as <- <-.
  destruct (bool_decide (lookup v live = None)) eqn:Ed; injection Hrd as <- <- <-.
  - apply bool_decide_spec in Ed. exists t, tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite RS_set_var. reflexivity.
    + cbn [rd_post]. split; [|exact Hst]. unfold set_var; cbn_ws.
      apply strong_locals_rel_insert_notin. split; [exact Hs|]. intros Hn; apply IN_domain_iff in Hn as [? ?]; congruence.
  - exists (insert v x t), tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. unfold get_store in *. cbn [RS store set_store_field].
      assert (Hn : ~ n IN set (FILTER (fun s => negb (bool_decide (n = s))) nlive)).
      { rewrite IN_set. intros Hin. apply filter_In in Hin as [_ Hin].
        rewrite bd_true' in Hin by reflexivity. discriminate. }
      rewrite (live_store_rel_FLOOKUP_store _ _ _ n (conj Hst Hn)).
      rewrite Eg, set_var_RS, RS_set_var. reflexivity.
    + cbn [rd_post]. unfold set_var; cbn_ws. split.
      * apply strong_locals_rel_I_insert_insert. split; [|reflexivity]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
      * apply (live_store_rel_less (FILTER (fun s => negb (bool_decide (n = s))) nlive) nlive _ _). split; [exact Hst|]. intros z Hz. rewrite IN_set in *. apply filter_In in Hz as [Hz _]; exact Hz.
Qed.

Lemma RS_store t s : RS t (store s) s = set_locals t s.
Proof. destruct s; reflexivity. Qed.
Lemma dec_clock_RS t ts s : dec_clock (RS t ts s) = RS t ts (dec_clock s).
Proof. reflexivity. Qed.
Lemma flush_true_RS t ts s : flush_state true (RS t ts s) = flush_state true s.
Proof. reflexivity. Qed.
Lemma RS_flush_true s : RS LN FEMPTY (flush_state true s) = flush_state true s.
Proof. destruct s; reflexivity. Qed.
Lemma set_ffi_RS t ts f s : set_ffi f (RS t ts s) = RS t ts (set_ffi f s).
Proof. reflexivity. Qed.
Lemma set_code_buffer_RS t ts f s : set_code_buffer f (RS t ts s) = RS t ts (set_code_buffer f s).
Proof. reflexivity. Qed.
Lemma set_data_buffer_RS t ts f s : set_data_buffer f (RS t ts s) = RS t ts (set_data_buffer f s).
Proof. reflexivity. Qed.
Lemma set_store_RS t ts v x s : set_store v x (RS t ts s) = RS t (ts |+ (v, x)) s.
Proof. reflexivity. Qed.
Lemma RS_set_store t ts v x s : RS t ts (set_store v x s) = RS t ts s.
Proof. destruct s; reflexivity. Qed.
Lemma unset_var_RS t ts v s : unset_var v (RS t ts s) = RS (delete v t) ts s.
Proof. reflexivity. Qed.
Lemma RS_unset_var t ts v s : RS t ts (unset_var v s) = RS t ts s.
Proof. destruct s; reflexivity. Qed.
Lemma get_var_RS x t ts s : get_var x (RS t ts s) = lookup x t.
Proof. reflexivity. Qed.

Lemma strong_locals_rel_I_delete_delete {A} live p (A0 B : num_map A) :
  strong_locals_rel I (live DELETE p) A0 B -> strong_locals_rel I live (delete p A0) (delete p B).
Proof.
  intros Hs n w [Hn Hl]. unfold I. rewrite lookup_delete in Hl |- *.
  destruct (decide (n = p)) as [->|Hne]; [discriminate|].
  apply (Hs n w). split; [split; [exact Hn|intros [E|[]]; contradiction]|exact Hl].
Qed.

Ltac slrI2 Hs :=
  repeat first [ apply strong_locals_rel_I_insert_insert; split; [|reflexivity]
               | apply strong_locals_rel_I_delete_delete ];
  eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve.

Ltac rd_get Hs :=
  repeat match goal with
         | E : get_var ?r ?st = Some ?v |- context [get_var ?r (RS ?t ?ts ?st)] =>
             let H := fresh "Hlk" in
             assert (H : lookup r t = Some v) by (apply (Hs r v); split; [in_solve|exact E]);
             rewrite (get_var_RS r t ts st), H; clear H
         end.

Lemma slr_refl {A} f (S : N -> Prop) (l : num_map A) : f = I -> strong_locals_rel f S l l.
Proof. intros -> n v [_ H]; exact H. Qed.

Lemma rd_OpCurrHeap b dst src : rd_IH (OpCurrHeap b dst src).
Proof.
  rd_start. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (word_exp st (Op b [Var src; Lookup CurrHeap])) as [w|] eqn:Ew; [|err_case Hev Hr].
  injection Hev as <- <-.
  destruct (bool_decide (lookup dst live = None)) eqn:Ed; injection Hrd as <- <- <-.
  - apply bool_decide_spec in Ed. exists t, tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite RS_set_var. reflexivity.
    + cbn [rd_post]. split; [|exact Hst]. unfold set_var; cbn_ws.
      apply strong_locals_rel_insert_notin. split; [exact Hs|]. intros Hn; apply IN_domain_iff in Hn as [? ?]; congruence.
  - exists (insert dst w t), tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body].
      rewrite (strong_locals_rel_I_word_exp st _ w (delete dst live) t (FILTER (fun s => negb (bool_decide (CurrHeap = s))) nlive) tstore).
      * rewrite set_var_RS, RS_set_var. reflexivity.
      * split; [exact Ew|split; [|split; [exact Hst|]]].
        -- eapply strong_locals_rel_subset; split; [|exact Hs]. cbn [get_live_exp big_union MAP List.map FOLDR]. set_solve.
        -- cbn [nlive_store EVERY]. rewrite andb_true_r. apply Bool.negb_true_iff.
           destruct (MEM CurrHeap _) eqn:Em; [|reflexivity]. apply MEM_iff', filter_In in Em as [_ Em].
           rewrite bd_true' in Em by reflexivity. discriminate.
    + cbn [rd_post]. unfold set_var; cbn_ws. split.
      * slrI2 Hs.
      * apply (live_store_rel_less (FILTER (fun s => negb (bool_decide (CurrHeap = s))) nlive) nlive _ _).
        split; [exact Hst|]. intros z Hz. rewrite IN_set in *. apply filter_In in Hz as [Hz _]; exact Hz.
Qed.

Lemma rd_LocValue r l1 : rd_IH (LocValue r l1).
Proof.
  rd_start. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (classical_dec _) as [Hc|]; [|err_case Hev Hr]. injection Hev as <- <-.
  destruct (bool_decide (lookup r live = None)) eqn:Ed; injection Hrd as <- <- <-.
  - apply bool_decide_spec in Ed. exists t, tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite RS_set_var. reflexivity.
    + cbn [rd_post]. split; [|exact Hst]. unfold set_var; cbn_ws.
      apply strong_locals_rel_insert_notin. split; [exact Hs|]. intros Hn; apply IN_domain_iff in Hn as [? ?]; congruence.
  - exists (insert r (Loc l1 0) t), tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. cbn [RS code set_store_field set_locals].
      destruct (classical_dec _); [|contradiction]. rewrite set_var_RS, RS_set_var. reflexivity.
    + cbn [rd_post]. unfold set_var; cbn_ws. split; [slrI2 Hs|exact Hst].
Qed.

Lemma rd_Set v e : rd_IH (Set_ v e).
Proof.
  rd_start. destruct e as [w|r|n|e|op es|sh e1 e2]; try discriminate Hf; cbn [remove_dead] in Hrd.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body word_exp] in Hev.
  destruct (_ || _) eqn:Eb; [err_case Hev Hr|].
  destruct (get_var r st) as [w|] eqn:Eg; [|err_case Hev Hr]. injection Hev as <- <-.
  destruct (MEM v nlive) eqn:Em; injection Hrd as <- <- <-.
  - exists t, tstore. split.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite RS_set_store. reflexivity.
    + cbn [rd_post]. split; [exact Hs|]. intros n Hn. unfold set_store; cbn_ws. rewrite FLOOKUP_UPDATE.
      destruct (decide (v = n)) as [->|]; [exfalso; apply Hn, IN_set, MEM_iff', Em|apply Hst, Hn].
  - exists t, (tstore |+ (v, w)). split.
    + rewrite evaluate_eqn; cbn [evaluate_body word_exp]. rewrite Eb.
      assert (Hrw : lookup r t = Some w) by (apply (Hs r w); split; [in_solve|exact Eg]).
      rewrite get_var_RS, Hrw. rewrite set_store_RS, RS_set_store. reflexivity.
    + cbn [rd_post]. split.
      * eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
      * intros n Hn. unfold set_store; cbn_ws. rewrite !FLOOKUP_UPDATE. destruct (decide (v = n)); [reflexivity|].
        apply Hst. rewrite IN_set in *. cbn [In]. intros [E|E]; [congruence|contradiction].
Qed.

Lemma rd_Tick : rd_IH (@Tick a).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (clock st =? 0) eqn:Ec; injection Hev as <- <-.
  - exists LN, FEMPTY. split; [rewrite evaluate_eqn; cbn [evaluate_body]; change (clock (RS t tstore st)) with (clock st); rewrite Ec; destruct st; reflexivity|].
    cbn [rd_post]. split; reflexivity.
  - exists t, tstore. split; [rewrite evaluate_eqn; cbn [evaluate_body]; change (clock (RS t tstore st)) with (clock st); rewrite Ec; reflexivity|].
    cbn [rd_post]. split; [exact Hs|exact Hst].
Qed.

Lemma rd_Raise n : rd_IH (Raise n).
Proof.
  rd_start. injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var n st) as [w|] eqn:Eg; [|err_case Hev Hr].
  destruct (jump_exc st) as [[s1 [l1 l2]]|] eqn:Ej; [|err_case Hev Hr]. injection Hev as <- <-.
  exists (locals s1), (store s1). rewrite RS_same, RS_store. split; [|cbn [rd_post]; split; reflexivity].
  rewrite evaluate_eqn; cbn [evaluate_body]. rewrite (strong_locals_rel_I_get_var' n st w (domain live) t)
    by (split; [exact Eg|rewrite domain_insert in Hs; exact Hs]). rewrite jump_exc_set_locals, Ej. reflexivity.
Qed.

Lemma rd_Return n ns : rd_IH (Return n ns).
Proof.
  rd_start. injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var n st) as [[w|l1 l2]|] eqn:Eg; try err_case Hev Hr.
  destruct (get_vars ns st) as [ys|] eqn:Egs; [|err_case Hev Hr]. injection Hev as <- <-.
  exists (locals (flush_state false st)), (store (flush_state false st)). rewrite RS_same, RS_store.
  split; [|cbn [rd_post]; split; reflexivity].
  rewrite evaluate_eqn; cbn [evaluate_body].
  rewrite (strong_locals_rel_I_get_var' n st (Loc l1 l2) (domain (numset_list_insert ns live)) t)
    by (split; [exact Eg|eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve]).
  rewrite (strong_locals_rel_I_get_vars' ns (domain (insert n tt (numset_list_insert ns live))) st t ys).
  - rewrite flush_state_set_locals. reflexivity.
  - split; [|split; [exact Hs|exact Egs]]. intros x Hx. rewrite domain_insert, domain_numset_list_insert.
    right; right; apply IN_set, MEM_iff', Hx.
Qed.

Lemma rd_Break k : rd_IH (wordLang.Break k).
Proof.
  rd_start. injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev. injection Hev as <- <-.
  exists t, (store st). rewrite RS_store. split; [rewrite evaluate_eqn; reflexivity|].
  cbn [rd_post get_live] in *. split; [reflexivity|]. destruct (oEL k lt) as [[? ?]|]; [exact Hs|exact Logic.I].
Qed.

Lemma rd_Continue k : rd_IH (wordLang.Continue k).
Proof.
  rd_start. injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev. injection Hev as <- <-.
  exists t, (store st). rewrite RS_store. split; [rewrite evaluate_eqn; reflexivity|].
  cbn [rd_post get_live] in *. split; [reflexivity|]. destruct (oEL k lt) as [[? ?]|]; [exact Hs|exact Logic.I].
Qed.

Lemma rd_Assign v e : rd_IH (Assign v e).
Proof. rd_start. discriminate Hf. Qed.

Lemma rd_Store e v : rd_IH (Store e v).
Proof. rd_start. discriminate Hf. Qed.

Lemma rd_CodeBufferWrite r1 r2 : rd_IH (CodeBufferWrite r1 r2).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var r1 st) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (get_var r2 st) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (buffer_write _ _ _) as [cb|] eqn:Eb; [|err_case Hev Hr]. injection Hev as <- <-.
  exists t, tstore. split.
  - rewrite evaluate_eqn; cbn [evaluate_body]. rd_get Hs.
    change (code_buffer (RS t tstore st)) with (code_buffer st). rewrite Eb, set_code_buffer_RS. reflexivity.
  - cbn [rd_post]. cbn_ws. split; [|exact Hst]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
Qed.

Lemma rd_DataBufferWrite r1 r2 : rd_IH (DataBufferWrite r1 r2).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var r1 st) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (get_var r2 st) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (buffer_write _ _ _) as [cb|] eqn:Eb; [|err_case Hev Hr]. injection Hev as <- <-.
  exists t, tstore. split.
  - rewrite evaluate_eqn; cbn [evaluate_body]. rd_get Hs.
    change (data_buffer (RS t tstore st)) with (data_buffer st). rewrite Eb, set_data_buffer_RS. reflexivity.
  - cbn [rd_post]. cbn_ws. split; [|exact Hst]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
Qed.

Lemma rd_StoreConsts t1 t2 ad off ws : rd_IH (StoreConsts t1 t2 ad off ws).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var ad st) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (get_var off st) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (negb _) eqn:En; [err_case Hev Hr|]. injection Hev as <- <-.
  eexists _, tstore. split.
  - rewrite evaluate_eqn; cbn [evaluate_body]. rd_get Hs.
    change (mdomain (RS t tstore st)) with (mdomain st). change (memory (RS t tstore st)) with (memory st).
    rewrite En. f_equal.
    rewrite set_memory_RS, !unset_var_RS, !set_var_RS, !RS_set_var, !RS_unset_var. reflexivity.
  - cbn [rd_post]. unfold set_var, unset_var; cbn_ws. split; [slrI2 Hs|exact Hst].
Qed.

Lemma rd_ShareInst op v e : rd_IH (ShareInst op v e).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (word_exp st e) as [[ad|]|] eqn:Ee; try err_case Hev Hr.
  assert (Hne : nlive_store nlive e = true).
  { destruct e as [| | | |op' es|]; try discriminate Hf; try reflexivity.
    destruct op', es as [|[] [|[] []]]; try discriminate Hf; reflexivity. }
  assert (Ew : word_exp (RS t tstore st) e = SOME (Word ad)).
  { apply (strong_locals_rel_I_word_exp st e (Word ad) (if is_store_op op then insert v tt live else delete v live) t nlive tstore).
    split; [exact Ee|split; [|split; [exact Hst|exact Hne]]].
    destruct (is_store_op op); exact Hs. }
  assert (Hsl : strong_locals_rel I (domain live DELETE v) (locals st) t).
  { eapply strong_locals_rel_subset; split; [|exact Hs]. destruct (is_store_op op); set_solve. }
  destruct op; cbn [share_inst] in *;
    match type of Hs with context [is_store_op ?o] =>
      let E := fresh "Eso" in
      assert (E : is_store_op o = ltac:(let b := eval vm_compute in (is_store_op o) in exact b))
        by reflexivity; rewrite E in Hs end;
    unfold sh_mem_set_var, sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32,
      sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32 in *;
    split_in Hev; try err_case Hev Hr; injection Hev as <- <-;
    (eexists _, _; split;
     [ rewrite evaluate_eqn; cbn [evaluate_body]; rewrite Ew; cbn [share_inst];
       unfold sh_mem_set_var, sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32,
         sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32;
       rd_get Hs; cbn [RS sh_mdomain ffi set_store_field set_locals]; rw_eqs;
       first [rewrite flush_true_RS, <- RS_flush_true; reflexivity
             | rewrite ?set_ffi_RS, ?set_var_RS, ?RS_set_var; reflexivity]
     | cbn [rd_post]; first [split; reflexivity
                           | unfold set_var; cbn_ws; split; [slrI2 Hs|exact Hst]
                           | cbn_ws; split; [eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve|exact Hst]] ]).
Qed.

Lemma rd_FFI fi p1 l1 p2 l2 names : rd_IH (FFI fi p1 l1 p2 l2 names).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var l1 st) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (get_var p1 st) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (get_var l2 st) as [[w3|]|] eqn:E3; try err_case Hev Hr.
  destruct (get_var p2 st) as [[w4|]|] eqn:E4; try err_case Hev Hr.
  destruct (cut_env names (locals st)) as [env|] eqn:Ec; [|err_case Hev Hr].
  assert (Ec' : cut_env names t = SOME env).
  { apply (strong_locals_rel_I_cut_env names st t env). split; [|exact Ec].
    eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  split_in Hev; try err_case Hev Hr; injection Hev as <- <-.
  all: first
    [ exists LN, FEMPTY; split; [|cbn [rd_post]; split; reflexivity];
      rewrite evaluate_eqn; cbn [evaluate_body]; rd_get Hs; change (locals (RS t tstore st)) with t; rewrite Ec';
      cbn [RS memory mdomain be ffi set_store_field set_locals]; rw_eqs; destruct st; reflexivity
    | exists env, tstore; split;
      [ rewrite evaluate_eqn; cbn [evaluate_body]; rd_get Hs; change (locals (RS t tstore st)) with t; rewrite Ec';
        cbn [RS memory mdomain be ffi set_store_field set_locals]; rw_eqs; destruct st; reflexivity
      | cbn [rd_post]; cbn_ws; split; [apply slr_refl; reflexivity|exact Hst] ] ].
Qed.

Lemma rd_Install r1 r2 r3 r4 names : rd_IH (Install r1 r2 r3 r4 names).
Proof.
  rd_start. injection Hrd as <- <- <-. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (cut_env names (locals st)) as [env|] eqn:Ec; [|err_case Hev Hr].
  assert (Ec' : cut_env names t = SOME env).
  { apply (strong_locals_rel_I_cut_env names st t env). split; [|exact Ec].
    eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  destruct (get_var r1 st) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (get_var r2 st) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (get_var r3 st) as [[w3|]|] eqn:E3; try err_case Hev Hr.
  destruct (get_var r4 st) as [[w4|]|] eqn:E4; try err_case Hev Hr.
  split_in Hev; try err_case Hev Hr; injection Hev as <- <-.
  eexists _, tstore. split.
  - rewrite evaluate_eqn; cbn [evaluate_body]. change (locals (RS t tstore st)) with t. rewrite Ec'. rd_get Hs.
    cbn [RS compile_oracle code_buffer data_buffer compile code set_store_field set_locals]. rw_eqs.
    destruct st; reflexivity.
  - cbn [rd_post]. cbn_ws. split; [apply slr_refl; reflexivity|exact Hst].
Qed.

Lemma rd_Alloc n names : rd_IH (Alloc n names).
Proof.
  rd_start. injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore. cbn [get_live] in Hs.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var n st) as [[w|]|] eqn:Eg; try err_case Hev Hr.
  destruct (cut_envs names (locals st)) as [envs|] eqn:Ec.
  2:{ unfold alloc in Hev. rewrite Ec in Hev. err_case Hev Hr. }
  assert (Ec' : cut_envs names t = SOME envs).
  { apply (strong_locals_rel_I_cut_envs names st t envs). split; [|exact Ec].
    eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  exists (locals rst), (store rst). rewrite RS_same, RS_store. split.
  - rewrite evaluate_eqn; cbn [evaluate_body].
    rewrite (strong_locals_rel_I_get_var' n st (Word w) (domain (union (FST names) (SND names))) t)
      by (split; [exact Eg|rewrite domain_insert in Hs; exact Hs]).
    rewrite (alloc_set_locals w names t st envs Ec' Ec). exact Hev.
  - destruct res as [[]|]; cbn [rd_post]; try (split; reflexivity);
      try (split; [apply slr_refl; reflexivity|apply live_store_rel_refl]);
      (split; [reflexivity|]; destruct (oEL _ _) as [[? ?]|]; [apply slr_refl; reflexivity|exact Logic.I]).
Qed.

Lemma rd_Call_None dest args h : rd_IH (Call None dest args h).
Proof.
  rd_start. injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore. cbn [get_live] in Hs.
  exists (locals rst), (store rst). rewrite RS_same, RS_store. split.
  - rewrite evaluate_eqn in Hev |- *; cbn [evaluate_body] in Hev |- *.
    destruct (get_vars args st) as [xs|] eqn:Eg; [|err_case Hev Hr].
    rewrite (strong_locals_rel_I_get_vars' args (domain (numset_list_insert args LN)) st t xs).
    2:{ split; [|split; [exact Hs|exact Eg]]. intros x Hx. rewrite domain_numset_list_insert. right; apply IN_set, MEM_iff', Hx. }
    destruct (bad_dest_args dest args); [err_case Hev Hr|].
    rewrite code_set_locals, state_stack_size_set_locals.
    destruct (find_code _ _ _ _) as [[args1 [prog ss]]|]; [|err_case Hev Hr].
    destruct (bool_decide (h = NONE)); [|err_case Hev Hr].
    rewrite clock_set_locals, dec_clock_set_locals, call_env_set_locals, flush_state_set_locals. exact Hev.
  - cbn [rd_post]. rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
    split_in Hev; injection Hev as <- <-; try (exfalso; apply Hr; reflexivity); try (split; reflexivity).
    all: match goal with E : bad_fun_return ?r = false |- _ =>
           destruct r as [[]|]; cbn [bad_fun_return] in E; try discriminate E end; split; reflexivity.
Qed.

Lemma evaluate_smart_seq (p1 p2 : prog a) (s : state) :
  evaluate (if is_Skip p1 then p2 else if is_Skip p2 then p1 else Seq p1 p2, s) = evaluate (Seq p1 p2, s).
Proof.
  destruct (is_Skip p1) eqn:E1.
  - destruct p1; try discriminate E1. rewrite evaluate_Seq_eq'. rewrite (evaluate_eqn Skip). cbn [evaluate_body].
    rewrite bd_true' by reflexivity. reflexivity.
  - destruct (is_Skip p2) eqn:E2; [|reflexivity]. destruct p2; try discriminate E2.
    rewrite evaluate_Seq_eq'. destruct (evaluate (p1, s)) as [r s1]. destruct (bool_decide (r = NONE)) eqn:E; [|reflexivity].
    apply bool_decide_spec in E; subst r. rewrite evaluate_eqn. reflexivity.
Qed.

Lemma rd_post_not_none live live' nlive nlive' lt res rst t' ts' :
  res <> NONE -> rd_post live nlive lt res rst t' ts' -> rd_post live' nlive' lt res rst t' ts'.
Proof. intros H; destruct res as [[]|]; cbn [rd_post]; auto; contradiction. Qed.

Lemma rd_Seq p1 p2 : rd_IH p1 -> rd_IH p2 -> rd_IH (Seq p1 p2).
Proof.
  intros IH1 IH2. rd_start. unfold is_true in Hf. apply andb_prop in Hf as [Hf1 Hf2].
  destruct (remove_dead p2 live nlive lt) as [p2' [l2 n2]] eqn:E2.
  destruct (remove_dead p1 l2 n2 lt) as [p1' [l1 n1]] eqn:E1.
  injection Hrd as <- <- <-.
  rewrite evaluate_Seq_eq' in Hev. destruct (evaluate (p1, st)) as [r1 m] eqn:Ev1.
  assert (Hr1 : r1 <> SOME Error) by (intros ->; rewrite bd_false' in Hev by discriminate; injection Hev as <- _; apply Hr; reflexivity).
  destruct (IH1 l2 n2 lt p1' l1 n1 st t tstore r1 m Hs Hst Ev1 Hf1 E1 Hr1) as (t1 & ts1 & Et1 & Hp1).
  rewrite evaluate_smart_seq, evaluate_Seq_eq', Et1.
  destruct (bool_decide (r1 = NONE)) eqn:En.
  - apply bool_decide_spec in En; subst r1. cbn [rd_post] in Hp1. destruct Hp1 as [Hs1 Hst1].
    exact (IH2 live nlive lt p2' l2 n2 m t1 ts1 res rst Hs1 Hst1 Hev Hf2 E2 Hr).
  - injection Hev as <- <-. exists t1, ts1. split; [reflexivity|].
    apply (rd_post_not_none l2 live n2 nlive); [intros ->; rewrite bd_true' in En by reflexivity; discriminate|exact Hp1].
Qed.

Lemma rd_MustTerminate p : rd_IH p -> rd_IH (MustTerminate p).
Proof.
  intros IH. rd_start. destruct (remove_dead p live nlive lt) as [p' [l1 n1]] eqn:E1. injection Hrd as <- <- <-.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (termdep st =? 0) eqn:Et; [err_case Hev Hr|].
  destruct (evaluate (p, set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st))) as [r1 s1] eqn:Ev1.
  destruct (bool_decide (r1 = SOME TimeOut)) eqn:Eto; [err_case Hev Hr|]. injection Hev as <- <-.
  destruct (IH live nlive lt p' l1 n1 (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)) t tstore r1 s1 Hs Hst Ev1 Hf E1 Hr) as (t1 & ts1 & Et1 & Hp1).
  exists t1, ts1. split.
  - rewrite evaluate_eqn; cbn [evaluate_body]. change (termdep (RS t tstore st)) with (termdep st). rewrite Et.
    change (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) (RS t tstore st)))
      with (RS t tstore (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st))).
    rewrite Et1, Eto. reflexivity.
  - destruct r1 as [[]|]; cbn [rd_post] in *; cbn_ws; exact Hp1.
Qed.

Lemma rd_If cmp r ri p1 p2 : rd_IH p1 -> rd_IH p2 -> rd_IH (If cmp r ri p1 p2).
Proof.
  intros IH1 IH2. rd_start. unfold is_true in Hf. apply andb_prop in Hf as [Hf1 Hf2].
  destruct (remove_dead p1 live nlive lt) as [p1' [l1 n1]] eqn:E1.
  destruct (remove_dead p2 live nlive lt) as [p2' [l2 n2]] eqn:E2.
  injection Hrd as <- <- <-.
  assert (Hs1 : strong_locals_rel I (domain l1) (locals st) t)
    by (eapply strong_locals_rel_subset; split; [|exact Hs]; destruct ri; set_solve).
  assert (Hs2 : strong_locals_rel I (domain l2) (locals st) t)
    by (eapply strong_locals_rel_subset; split; [|exact Hs]; destruct ri; set_solve).
  assert (Hst1 : live_store_rel n1 (store st) tstore).
  { apply (live_store_rel_less (FILTER (fun s => MEM s n2) n1)); split; [exact Hst|].
    intros z Hz. rewrite IN_set in *. apply filter_In in Hz as [Hz _]; exact Hz. }
  assert (Hst2 : live_store_rel n2 (store st) tstore).
  { apply (live_store_rel_less (FILTER (fun s => MEM s n2) n1)); split; [exact Hst|].
    intros z Hz. rewrite IN_set in *. apply filter_In in Hz as [_ Hz]. apply MEM_iff', Hz. }
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev.
  destruct (get_var r st) as [x|] eqn:Ex; [|err_case Hev Hr].
  destruct (get_var_imm ri st) as [y|] eqn:Ey; [|err_case Hev Hr].
  assert (Ex' : get_var r (RS t tstore st) = Some x).
  { rewrite get_var_RS. apply (Hs r x); split; [destruct ri; in_solve|exact Ex]. }
  assert (Ey' : get_var_imm ri (RS t tstore st) = Some y).
  { destruct ri as [r2|w]; cbn [get_var_imm] in *; [|exact Ey].
    rewrite get_var_RS. apply (Hs r2 y); split; [in_solve|exact Ey]. }
  destruct (word_cmp cmp x y) as [[]|] eqn:Ec; [| |err_case Hev Hr].
  - destruct (IH1 live nlive lt p1' l1 n1 st t tstore res rst Hs1 Hst1 Hev Hf1 E1 Hr) as (t1 & ts1 & Et1 & Hp1).
    exists t1, ts1. split; [|exact Hp1].
    destruct (is_Skip p1' && is_Skip p2') eqn:Esk.
    + apply andb_prop in Esk as [Sk _]. destruct p1'; try discriminate Sk. exact Et1.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Ex', Ey', Ec. exact Et1.
  - destruct (IH2 live nlive lt p2' l2 n2 st t tstore res rst Hs2 Hst2 Hev Hf2 E2 Hr) as (t1 & ts1 & Et1 & Hp1).
    exists t1, ts1. split; [|exact Hp1].
    destruct (is_Skip p1' && is_Skip p2') eqn:Esk.
    + apply andb_prop in Esk as [_ Sk]. destruct p2'; try discriminate Sk. exact Et1.
    + rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Ex', Ey', Ec. exact Et1.
Qed.

Lemma rd_Call_Some n names rh l1 l2 dest args h :
  rd_IH rh -> (match h with Some (_, (p, _)) => rd_IH p | None => True end) ->
  rd_IH (Call (Some (n, (names, (rh, (l1, l2))))) dest args h).
Proof.
  intros IHr IHh. rd_start. cbv zeta in Hrd.
  destruct (remove_dead rh live nlive lt) as [rh' [lr nr]] eqn:Er.
  injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore. rewrite RS_store.
  unfold is_true in Hf. apply andb_prop in Hf as [Hfr Hfh].
  set (h' := match h with
             | None => None
             | Some (v', (prog, (l1, l2))) => Some (v', (FST (remove_dead prog live nlive lt), (l1, l2)))
             end).
  assert (Hph : forall envs (s : state), push_env envs h' s = push_env envs h s)
    by (intros; subst h'; destruct h as [[? [? [? ?]]]|]; reflexivity).
  pose proof Hev as Hev0.
  rewrite evaluate_eqn in Hev; cbn [evaluate_body add_ret_loc] in Hev.
  destruct (get_vars args st) as [xs|] eqn:Eg; [|err_case Hev Hr].
  destruct (bad_dest_args dest args) eqn:Ebd; [err_case Hev Hr|].
  destruct (find_code dest (Loc l1 l2 :: xs) (code st) (state_stack_size st)) as [[args1 [prog ss]]|] eqn:Ef;
    [|err_case Hev Hr].
  destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ecd; [err_case Hev Hr|].
  destruct (cut_envs names (locals st)) as [envs|] eqn:Ec; [|err_case Hev Hr].
  assert (Eg' : get_vars args (set_locals t st) = SOME xs).
  { apply (strong_locals_rel_I_get_vars' args (domain (union (union (FST names) (SND names)) (numset_list_insert args LN))) st t xs).
    split; [|split; [exact Hs|exact Eg]]. intros x Hx. rewrite domain_union, domain_numset_list_insert.
    right; right; apply IN_set, MEM_iff', Hx. }
  assert (Ec' : cut_envs names t = SOME envs).
  { apply (strong_locals_rel_I_cut_envs names st t envs). split; [|exact Ec].
    eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  destruct (clock st =? 0) eqn:Eck.
  - injection Hev as <- Erst. exists (locals rst), (store rst). rewrite RS_same.
    split; [|cbn [rd_post]; split; reflexivity].
    rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc]. rewrite Eg', Ebd.
    cbn [code state_stack_size locals clock set_locals]. rewrite Ef, Ecd, Ec', Eck.
    rewrite Hph, push_env_set_locals, call_env_set_locals, <- Erst. f_equal; destruct st; reflexivity.
  - clear Hev. rename Hev0 into Hev.
    rewrite (evaluate_Call_Some_eq n names rh l1 l2 dest args h st xs args1 prog ss envs) in Hev by assumption.
    rewrite (evaluate_Call_Some_eq n names rh' l1 l2 dest args h' (set_locals t st) xs args1 prog ss envs);
      cbn [code state_stack_size locals clock set_locals]; try assumption.
    rewrite dec_clock_set_locals, push_env_set_locals, call_env_set_locals, Hph.
    destruct (evaluate (prog, call_env args1 ss (push_env envs h (dec_clock st)))) as [r1 s2] eqn:Eb.
    unfold call_cont in Hev |- *. destruct r1 as [[x ys|x y| | | | | |]|]; try err_case Hev Hr.
    + destruct (negb _ || negb _) eqn:Echk; [err_case Hev Hr|].
      destruct (pop_env s2) as [s1|] eqn:Ep; [|err_case Hev Hr].
      destruct (⌜domain (locals s1) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edc; [|err_case Hev Hr].
      destruct (IHr live nlive lt rh' lr nr (set_vars n ys s1) (locals (set_vars n ys s1)) (store (set_vars n ys s1)) res rst)
        as (t' & ts' & Et & Hp); try assumption.
      * apply slr_refl; reflexivity.
      * apply live_store_rel_refl.
      * exists t', ts'. rewrite RS_same in Et. split; [exact Et|exact Hp].
    + destruct h as [[hv [hp [hl1 hl2]]]|].
      * subst h'. cbn beta iota in *.
        destruct (negb ⌜x = Loc hl1 hl2⌝) eqn:Ex; [err_case Hev Hr|].
        destruct (⌜domain (locals s2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Edc; [|err_case Hev Hr].
        destruct (remove_dead hp live nlive lt) as [hp' [lh nh]] eqn:Eh. cbn [FST fst].
        destruct (IHh live nlive lt hp' lh nh (set_var hv y s2) (locals (set_var hv y s2)) (store (set_var hv y s2)) res rst)
          as (t' & ts' & Et & Hp); try assumption.
        -- apply slr_refl; reflexivity.
        -- apply live_store_rel_refl.
        -- exists t', ts'. rewrite RS_same in Et. split; [exact Et|exact Hp].
      * subst h'. cbn beta iota in *. injection Hev as <- <-. exists (locals s2), (store s2). rewrite RS_same.
        split; [reflexivity|cbn [rd_post]; split; reflexivity].
    + injection Hev as <- <-. exists (locals s2), (store s2). rewrite RS_same. split; [reflexivity|cbn [rd_post]; split; reflexivity].
    + injection Hev as <- <-. exists (locals s2), (store s2). rewrite RS_same. split; [reflexivity|cbn [rd_post]; split; reflexivity].
    + injection Hev as <- <-. exists (locals s2), (store s2). rewrite RS_same. split; [reflexivity|cbn [rd_post]; split; reflexivity].
Qed.

Lemma set_locals_set_locals' l l' (s : state) : set_locals l (set_locals l' s) = set_locals l s.
Proof. destruct s; reflexivity. Qed.

Definition rd_loop_IH names (body : prog a) exit_names lt : Prop :=
  forall (st' : state) t' tstore' prog'' livein' nlivein' res' rst',
    strong_locals_rel I (domain livein') (locals st') t' ->
    live_store_rel nlivein' (store st') tstore' ->
    evaluate (body, st') = (res', rst') ->
    remove_dead body names [] ((names, exit_names) :: lt) = (prog'', (livein', nlivein')) ->
    res' <> SOME Error ->
    exists t'' tstore'',
      evaluate (prog'', RS t' tstore' st') = (res', RS t'' tstore'' rst') /\
      rd_post names [] ((names, exit_names) :: lt) res' rst' t'' tstore''.

Lemma rd_Loop_gen names body exit_names live nlive lt :
  rd_loop_IH names body exit_names lt ->
  forall prog' livein nlivein (st : state) t tstore res rst,
  strong_locals_rel I (domain livein) (locals st) t ->
  live_store_rel nlivein (store st) tstore ->
  evaluate (Loop names body exit_names, st) = (res, rst) ->
  flat_exp_conventions (Loop names body exit_names) ->
  remove_dead (Loop names body exit_names) live nlive lt = (prog', (livein, nlivein)) ->
  res <> SOME Error ->
  exists t' tstore',
    evaluate (prog', RS t tstore st) = (res, RS t' tstore' rst) /\
    rd_post live nlive lt res rst t' tstore'.
Proof.
  intros IHb prog' livein nlivein st. remember (N.to_nat (clock st)) as k eqn:Hk. revert st Hk.
  induction k as [k IHk] using (well_founded_induction lt_wf).
  intros st Hk t tstore res rst Hs Hst Hev Hf Hrd Hr. cbn [flat_exp_conventions remove_dead] in Hf, Hrd.
  destruct (remove_dead body names [] ((names, exit_names) :: lt)) as [body' [lb nb]] eqn:Eb.
  injection Hrd as <- <- <-. apply live_store_rel_NIL in Hst. subst tstore. rewrite RS_store.
  rewrite evaluate_Loop_eq in Hev. unfold cut_state in Hev.
  destruct (cut_env (names, LN) (locals st)) as [env|] eqn:Ec; [|err_case Hev Hr].
  assert (Ec' : cut_env (names, LN) t = SOME env).
  { apply (strong_locals_rel_I_cut_env (names, LN) st t env). split; [|exact Ec].
    eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  destruct (evaluate (body, set_locals env st)) as [r1 s1] eqn:E1.
  assert (Hr1 : r1 <> SOME Error).
  { intros ->. cbn [cont_loop exit_loop] in Hev. rewrite bd_false' in Hev by discriminate. err_case Hev Hr. }
  destruct (IHb (set_locals env st) (locals (set_locals env st)) (store (set_locals env st)) body' lb nb r1 s1)
    as (t1 & ts1 & Et1 & Hp1); try assumption.
  { apply slr_refl; reflexivity. }
  { apply live_store_rel_refl. }
  rewrite RS_same in Et1.
  assert (Hcol : evaluate (Loop names body' exit_names, set_locals t st) =
    let '(res, s1) := (r1, RS t1 ts1 s1) in
    if cont_loop res then
      (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
       else evaluate (Loop names body' exit_names, dec_clock s1))
    else if bool_decide (res = SOME (Break 0)) then
      match cut_state (exit_names, LN) s1 with
      | NONE => (SOME Error, s1)
      | SOME s2 => (NONE, s2)
      end
    else (exit_loop res, s1)).
  { rewrite evaluate_Loop_eq. unfold cut_state. rewrite locals_set_locals, Ec', set_locals_set_locals'. rewrite Et1. reflexivity. }
  rewrite Hcol. cbn beta iota. clear Hcol.
  assert (Hck : (clock s1 <= clock st)%N).
  { apply evaluate_clock in E1 as [E1 _]. exact E1. }
  assert (Hrd' : remove_dead (Loop names body exit_names) live nlive lt =
                 (Loop names body' exit_names, (names, []))) by (cbn [remove_dead]; rewrite Eb; reflexivity).
  assert (Hloop :
    strong_locals_rel I (domain names) (locals s1) t1 ->
    (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
     else evaluate (Loop names body exit_names, dec_clock s1)) = (res, rst) ->
    exists t' tstore',
      (if clock (RS t1 (store s1) s1) =? 0 then (SOME TimeOut, flush_state true (RS t1 (store s1) s1))
       else evaluate (Loop names body' exit_names, dec_clock (RS t1 (store s1) s1))) = (res, RS t' tstore' rst) /\
      rd_post live nlive lt res rst t' tstore').
  { intros Hs1 Hev1. change (clock (RS t1 (store s1) s1)) with (clock s1).
    destruct (clock s1 =? 0) eqn:Ez.
    - injection Hev1 as <- <-. exists (locals (flush_state true s1)), (store (flush_state true s1)).
      rewrite RS_same, flush_true_RS. split; [reflexivity|cbn [rd_post]; split; reflexivity].
    - rewrite dec_clock_RS.
      refine (IHk _ _ (dec_clock s1) eq_refl t1 (store s1) res rst Hs1 (live_store_rel_refl _ _) Hev1 Hf Hrd' Hr).
      apply N.eqb_neq in Ez. unfold dec_clock; cbn_ws. lia. }
  destruct r1 as [[x ys|x y|n|n| | |ou|]|]; cbn [cont_loop exit_loop rd_post] in *.
  - rewrite bd_false' in Hev |- * by discriminate. injection Hev as <- <-. exists t1, ts1. split; [reflexivity|exact Hp1].
  - rewrite bd_false' in Hev |- * by discriminate. injection Hev as <- <-. exists t1, ts1. split; [reflexivity|exact Hp1].
  - destruct Hp1 as [<- Hp1]. destruct (n =? 0) eqn:En.
    + apply N.eqb_eq in En. subst n. rewrite bd_true' in Hev |- * by reflexivity. cbn [oEL N.eqb] in Hp1.
      unfold cut_state in Hev |- *. destruct (cut_env (exit_names, LN) (locals s1)) as [env2|] eqn:Ec2; [|err_case Hev Hr].
      injection Hev as <- <-.
      assert (Ec2' : cut_env (exit_names, LN) t1 = SOME env2).
      { apply (strong_locals_rel_I_cut_env (exit_names, LN) s1 t1 env2). split; [|exact Ec2].
        eapply strong_locals_rel_subset; split; [|exact Hp1]. set_solve. }
      cbn_ws. change (locals (RS t1 (store s1) s1)) with t1. rewrite Ec2'.
      exists env2, (store s1). split; [f_equal; destruct s1; reflexivity|].
      cbn [rd_post]. cbn_ws. split; [apply slr_refl; reflexivity|apply live_store_rel_refl].
    + rewrite bd_false' in Hev |- * by (intros E; injection E as ->; discriminate).
      injection Hev as <- <-. exists t1, (store s1). split; [reflexivity|].
      cbn [rd_post]. split; [reflexivity|]. cbn [oEL] in Hp1. rewrite En in Hp1. exact Hp1.
  - destruct Hp1 as [<- Hp1]. destruct (n =? 0) eqn:En.
    + apply N.eqb_eq in En. subst n. cbn [oEL N.eqb] in Hp1. cbn [N.eqb] in Hev |- *.
      exact (Hloop Hp1 Hev).
    + rewrite bd_false' in Hev |- * by discriminate.
      injection Hev as <- <-. exists t1, (store s1). split; [reflexivity|].
      cbn [rd_post]. split; [reflexivity|]. cbn [oEL] in Hp1. rewrite En in Hp1. exact Hp1.
  - rewrite bd_false' in Hev |- * by discriminate. injection Hev as <- <-. exists t1, ts1. split; [reflexivity|exact Hp1].
  - rewrite bd_false' in Hev |- * by discriminate. injection Hev as <- <-. exists t1, ts1. split; [reflexivity|exact Hp1].
  - rewrite bd_false' in Hev |- * by discriminate. injection Hev as <- <-. exists t1, ts1. split; [reflexivity|exact Hp1].
  - contradiction.
  - destruct Hp1 as [Hp1 Hst1]. apply live_store_rel_NIL in Hst1. subst ts1.
    exact (Hloop Hp1 Hev).
Qed.

Lemma rd_Loop names body exit_names : rd_IH body -> rd_IH (Loop names body exit_names).
Proof.
  intros IHb live nlive lt prog' livein nlivein st t tstore res rst Hs Hst Hev Hf Hrd Hr.
  apply (rd_Loop_gen names body exit_names live nlive lt) with (livein := livein) (nlivein := nlivein); try assumption.
  intros st' t' tstore' prog'' livein' nlivein' res' rst' H1 H2 H3 H4 H5.
  exact (IHb names [] ((names, exit_names) :: lt) prog'' livein' nlivein' st' t' tstore' res' rst' H1 H2 H3 Hf H4 H5).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead_Loop_helper" *)
Theorem evaluate_remove_dead_Loop_helper : forall (st : state) t tstore names body exit_names
    live nlive lt prog' livein nlivein res rst,
  strong_locals_rel I (domain livein) (locals st) t /\
  live_store_rel nlivein (store st) tstore /\
  evaluate (Loop names body exit_names, st) = (res, rst) /\
  flat_exp_conventions body /\
  remove_dead (Loop names body exit_names) live nlive lt = (prog', (livein, nlivein)) /\
  nlivein = [] /\
  res <> SOME Error /\
  (forall (st' : state) t' tstore' prog'' livein' nlivein' res' rst',
     strong_locals_rel I (domain livein') (locals st') t' /\
     live_store_rel nlivein' (store st') tstore' /\
     evaluate (body, st') = (res', rst') /\
     remove_dead body names [] ((names, exit_names) :: lt) = (prog'', (livein', nlivein')) /\
     res' <> SOME Error ->
     exists t'' tstore'',
       evaluate (prog'', set_store_field tstore' (set_locals t' st')) =
         (res', set_store_field tstore'' (set_locals t'' rst')) /\
       match res' with
       | NONE => strong_locals_rel I (domain names) (locals rst') t'' /\ live_store_rel [] (store rst') tstore''
       | SOME (Break n) =>
           store rst' = tstore'' /\
           match oEL n ((names, exit_names) :: lt) with
           | Some (_, exit_names) => strong_locals_rel I (domain exit_names) (locals rst') t''
           | None => True
           end
       | SOME (Continue n) =>
           store rst' = tstore'' /\
           match oEL n ((names, exit_names) :: lt) with
           | Some (names, _) => strong_locals_rel I (domain names) (locals rst') t''
           | None => True
           end
       | SOME _ => locals rst' = t'' /\ store rst' = tstore''
       end) ->
  exists t' tstore',
    evaluate (prog', set_store_field tstore (set_locals t st)) = (res, set_store_field tstore' (set_locals t' rst)) /\
    match res with
    | NONE => strong_locals_rel I (domain live) (locals rst) t' /\ live_store_rel nlive (store rst) tstore'
    | SOME (Break n) =>
        store rst = tstore' /\
        match oEL n lt with
        | Some (_, exit_names) => strong_locals_rel I (domain exit_names) (locals rst) t'
        | None => True
        end
    | SOME (Continue n) =>
        store rst = tstore' /\
        match oEL n lt with
        | Some (names, _) => strong_locals_rel I (domain names) (locals rst) t'
        | None => True
        end
    | SOME _ => locals rst = t' /\ store rst = tstore'
    end.
Proof.
  intros st t tstore names body exit_names live nlive lt prog' livein nlivein res rst
    (Hs & Hst & Hev & Hf & Hrd & _ & Hr & IH).
  apply (rd_Loop_gen names body exit_names live nlive lt) with (livein := livein) (nlivein := nlivein); try assumption.
  intros st' t' tstore' prog'' livein' nlivein' res' rst' H1 H2 H3 H4 H5.
  exact (IH st' t' tstore' prog'' livein' nlivein' res' rst' (conj H1 (conj H2 (conj H3 (conj H4 H5))))).
Qed.

Lemma rd_all : forall p : prog a, rd_IH p.
Proof.
  intros p; induction p as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind.
  - apply rd_Skip.
  - apply rd_Move.
  - apply rd_Inst.
  - apply rd_Assign.
  - apply rd_Get.
  - apply rd_Set.
  - apply rd_Store.
  - apply rd_MustTerminate, IHq.
  - destruct ret as [[n [names [rh [l1 l2]]]]|]; [apply rd_Call_Some; assumption|apply rd_Call_None].
  - apply rd_Seq; assumption.
  - apply rd_If; assumption.
  - apply rd_Loop, IHq.
  - apply rd_Alloc.
  - apply rd_StoreConsts.
  - apply rd_Raise.
  - apply rd_Return.
  - apply rd_Break.
  - apply rd_Continue.
  - apply rd_Tick.
  - apply rd_OpCurrHeap.
  - apply rd_LocValue.
  - apply rd_Install.
  - apply rd_CodeBufferWrite.
  - apply rd_DataBufferWrite.
  - apply rd_FFI.
  - apply rd_ShareInst.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead" *)
Theorem evaluate_remove_dead : forall (prog : prog a) live nlive lt prog' livein nlivein (st : state) t tstore res rst,
  strong_locals_rel I (domain livein) (locals st) t /\
  live_store_rel nlivein (store st) tstore /\
  evaluate (prog, st) = (res, rst) /\
  flat_exp_conventions prog /\
  remove_dead prog live nlive lt = (prog', (livein, nlivein)) /\
  res <> SOME Error ->
  exists t' tstore',
    evaluate (prog', set_store_field tstore (set_locals t st)) =
      (res, set_store_field tstore' (set_locals t' rst)) /\
    match res with
    | NONE => strong_locals_rel I (domain live) (locals rst) t' /\ live_store_rel nlive (store rst) tstore'
    | SOME (Break n) =>
        store rst = tstore' /\
        match oEL n lt with
        | Some (_, exit_names) => strong_locals_rel I (domain exit_names) (locals rst) t'
        | None => True
        end
    | SOME (Continue n) =>
        store rst = tstore' /\
        match oEL n lt with
        | Some (names, _) => strong_locals_rel I (domain names) (locals rst) t'
        | None => True
        end
    | SOME _ => locals rst = t' /\ store rst = tstore'
    end.
Proof.
  intros prog live nlive lt prog' livein nlivein st t tstore res rst (H1 & H2 & H3 & H4 & H5 & H6).
  exact (rd_all prog live nlive lt prog' livein nlivein st t tstore res rst H1 H2 H3 H4 H5 H6).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead_prog" *)
Theorem evaluate_remove_dead_prog : forall (prog : prog a) (st rst : state) res,
  flat_exp_conventions prog /\
  evaluate (prog, st) = (res, rst) /\
  res <> SOME Error ->
  exists t',
    evaluate (remove_dead_prog prog, st) = (res, set_locals t' rst) /\
    match res with
    | NONE => True
    | SOME (Break _) => True
    | SOME (Continue _) => True
    | SOME _ => locals rst = t'
    end.
Proof.
  intros prog st rst res (Hf & Hev & Hr). unfold remove_dead_prog.
  destruct (remove_dead prog LN [] []) as [prog' [livein nlivein]] eqn:E.
  destruct (rd_all prog LN [] [] prog' livein nlivein st (locals st) (store st) res rst
              (slr_refl _ _ _ eq_refl) (live_store_rel_refl _ _) Hev Hf E Hr) as (t' & ts' & Et & Hp).
  rewrite RS_same in Et. exists t'. cbn [FST fst].
  assert (Hts : ts' = store rst).
  { destruct res as [[]|]; cbn [rd_post] in Hp; destr_conj; try congruence.
    symmetry; apply live_store_rel_NIL; assumption. }
  subst ts'. rewrite Et. split; [f_equal; unfold RS; destruct rst; reflexivity|].
  destruct res as [[]|]; cbn [rd_post] in Hp; destr_conj; auto.
Qed.

End RD.
