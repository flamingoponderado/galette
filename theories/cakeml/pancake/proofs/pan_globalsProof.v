(** * CakeML Pancake [pan_globalsProof]: correctness of [pan_globals]

    Port of [cakeml/pancake/proofs/pan_globalsProofScript.sml].

    Carrier and statement notes:
    - [pan_globals]'s [context] has a field [globals], as does [panSem]'s
      [state]; the context field is written qualified
      ([pan_globals.globals ctxt]).  HOL's [stack_removeProof$addresses]
      is [stack_removeProof.addresses] (that module is not imported, its
      names clash with [panSem]'s).
    - [state_rel]'s flag [ls] is a [bool], as in HOL ([ls ⇒ ...] is
      [is_true ls -> ...]).
    - HOL proves [compile_correct] by [evaluate_ind] with one [Resume]
      block per program constructor; here it is one well-founded induction
      on [eval_lt] whose cases are the Galette-only lemmas [gc_<case>].
    - HOL's [eval_upd_code_eta] is a rewriting form of
      [panProps.eval_upd_code_eq] (function equality); ported with that
      statement.
    - [compile_correct] is stated with HOL's quantifiers in one block:
      [state_rel true ctxt s t /\ evaluate (p, s) = (res, s') /\
      res <> SOME Error -> exists t', ...].  HOL's [evaluate_fresh_local],
      [evaluate_two_fresh_locals] and [evaluate_unchanged_local] are
      corollaries of the Galette-only [ev_fresh], which runs a program in a
      state whose locals differ at one variable the program does not
      mention ([res_var] of that variable).
    - HOL record updates are setter compositions ([s with code := c] is
      [set_code c s]; [s with <|code := c; clock := k|>] is
      [set_clock k (set_code c s)]).  HOL's [s with top_addr := x] has no
      [panSem] setter; [set_top_addr] below is Galette-only.
    - HOL's [EVERY] over a [prop]-valued predicate (e.g.
      [EVERY (\d. !fi. d = Function fi ==> ...) ds]) is [EVERY] over the
      [bool_decide] of the predicate ([⌜...⌝]); HOL's [P ==> Q] inside a
      boolean predicate is [implb].
    - HOL's [fperm_decs_decls] has a vacuous quantifier [ys] (of an
      arbitrary type), kept.
    - [semantics_init_call], [state_rel_imp_semantics],
      [semantics_fperm] and [semantics_empty_locals] are proved by
      relating the clocked runs of the two semantics directly (Galette-only
      [sem_of], [sem_of_corr]); no least-upper-bound reasoning is needed
      ([LUB_IMAGE_SUC] is still ported).
    - The [localised_*] statements are [is_true] of the boolean
      [localised_prog]/[localised_exp]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.proofs Require stack_removeProof.
From Galette.cakeml.pancake Require Import panLang pan_globals.
From Galette.cakeml.pancake.semantics Require Import panSem pan_commonProps panProps.
Open Scope N_scope.
Local Open Scope fmap_scope.
Open Scope hol_string_scope.

#[local] Instance eq_dec_cl {A} : EqDecision A | 1000 := fun x y => classical_dec (x = y).

Abbreviation addresses := stack_removeProof.addresses.

(** ** The state relation *)

Section Rel.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "disjoint_globals_def" *)
Definition disjoint_globals (top_addr : word a) (cglobals : fmap varname (shape * word a))
    (globals : fmap varname (v a)) : Prop :=
  forall v0 v' sh addr sh' addr',
    v0 <> v' /\ is_true (IS_SOME (FLOOKUP globals v0)) /\ is_true (IS_SOME (FLOOKUP globals v')) /\
    FLOOKUP cglobals v0 = SOME (sh, addr) /\
    FLOOKUP cglobals v' = SOME (sh', addr') ->
    DISJOINT (addresses (top_addr - addr) (size_of_shape sh))
             (addresses (top_addr - addr') (size_of_shape sh')).

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_def" *)
Definition state_rel (ls : bool) (ctxt : context a) (s t : state a ffi_t) : Prop :=
  top_addr s = top_addr t - max_globals_size ctxt /\
  (is_true ls -> locals s = locals t) /\
  base_addr s = base_addr t /\
  be s = be t /\
  eshapes s = eshapes t /\
  clock s = clock t /\
  structs s = [] /\ structs t = [] /\
  (forall v0 val, FLOOKUP (globals s) v0 = SOME val ->
     exists addr, FLOOKUP (pan_globals.globals ctxt) v0 = SOME (shape_of val, addr) /\
       is_true (is_wf_shape_nil (shape_of val)) /\
       mem_load (shape_of val) (top_addr t - addr) (memaddrs t) (memory t) [] = SOME val /\
       DISJOINT (memaddrs s) (addresses (top_addr t - addr) (size_of_shape (shape_of val))) /\
       is_true (byte_aligned addr)) /\
  FEVERY (fun '(nm, (sh, addr)) => is_true (is_wf_shape_nil sh)) (pan_globals.globals ctxt) /\
  memaddrs s SUBSET memaddrs t /\
  sh_memaddrs s = sh_memaddrs t /\
  (forall addr, addr IN memaddrs s -> memory s addr = memory t addr) /\
  ffi s = ffi t /\
  (forall fname vshapes prog rshape,
     FLOOKUP (code s) fname = SOME (vshapes, (prog, rshape)) ->
     FLOOKUP (code t) fname = SOME (vshapes, (compile ctxt prog, rshape))) /\
  disjoint_globals (top_addr t) (pan_globals.globals ctxt) (globals s) /\
  top_addr t NOTIN memaddrs t /\
  is_true (byte_aligned (top_addr t)) /\
  good_dimindex a.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_structs" *)
Theorem state_rel_structs : forall ls ctxt s t,
  state_rel ls ctxt s t -> structs s = [] /\ structs t = [].
Proof. intros ls ctxt s t (_ & _ & _ & _ & _ & _ & H1 & H2 & _); split; assumption. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_globals_wf" *)
Theorem state_rel_globals_wf : forall ls ctxt s t nm x,
  FLOOKUP (pan_globals.globals ctxt) nm = SOME x /\ state_rel ls ctxt s t ->
  is_true (is_wf_shape_nil (FST x)).
Proof.
  intros ls ctxt s t nm [sh addr] [H Hr]. destruct Hr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _).
  exact (Hf _ _ H).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_mem_load" *)
Theorem state_rel_mem_load : forall ls ctxt s t shape w v0,
  state_rel ls ctxt s t /\ mem_load shape w (memaddrs s) (memory s) [] = SOME v0 ->
  mem_load shape w (memaddrs t) (memory t) [] = SOME v0.
Proof.
  intros ls ctxt s t shape w v0 [Hr H].
  destruct Hr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsub & _ & Hmem & _).
  unfold mem_load in *. eapply mem_load_f_mono; [|exact H].
  intros x Hx; split; [apply Hsub, Hx|apply Hmem, Hx].
Qed.

End Rel.

Section Exp.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Local Open Scope word_scope.

Lemma eval_top_sub t (addr : word a) :
  eval t (Op asm.Sub [TopAddr; Const addr]) = SOME (ValWord (top_addr t - addr)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct" *)
Theorem compile_exp_correct : forall s e v0 ctxt t,
  state_rel true ctxt s t /\ eval s e = SOME v0 ->
  eval t (compile_exp ctxt e) = SOME v0.
Proof.
  intros s e v0 ctxt t [Hr H]. pose proof Hr as Hr'.
  destruct Hr as (Htop & Hloc & Hbase & Hbe & _ & _ & Hss & Hts & Hglob & _ & Hsub & _ & Hmem & _).
  specialize (Hloc eq_refl).
  assert (Hd : forall x, x IN memaddrs s -> x IN memaddrs t /\ memory s x = memory t x)
    by (intros x Hx; split; [apply Hsub, Hx|apply Hmem, Hx]).
  revert v0 H.
  induction e as [w|vk vn|es IH|i e IH|nm eflds IH|fld e IH|sh e IH|e IH|e IH|bop es IH|pop es IH
                  |c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| | | ] using exp_nested_ind; intros v0 H;
    cbn [eval compile_exp] in H |- *.
  - exact H.
  - destruct vk; cbn [eval compile_exp] in H |- *.
    + rewrite <- Hloc. exact H.
    + destruct (Hglob _ _ H) as (addr & Ha & Hw & Hm & _). rewrite Ha. cbn [eval].
      rewrite Hts. rewrite Hw. exact Hm.
  - destruct (OPT_MMAP (eval s) es) as [vs|] eqn:E; [|discriminate].
    rewrite OPT_MMAP_MAP. replace (OPT_MMAP (fun x => eval t (compile_exp ctxt x)) es) with (SOME vs);
      [exact H|].
    symmetry. clear H. revert vs E. induction IH as [|x xs Hx Hxs IHl]; intros vs E; [exact E|].
    cbn [OPT_MMAP] in E |- *. destruct (eval s x) as [y|] eqn:Ey; [|discriminate]. cbn in E.
    destruct (OPT_MMAP (eval s) xs) as [ys|] eqn:Eys; [|discriminate]. cbn in E. injection E as <-.
    rewrite (Hx _ eq_refl), (IHl _ eq_refl). reflexivity.
  - destruct (eval s e) as [x|] eqn:E; [|discriminate]. rewrite (IH _ eq_refl). exact H.
  - rewrite Hss in H. cbn [ALOOKUP] in H. discriminate.
  - destruct (eval s e) as [[| |nm vf]|] eqn:E; try discriminate.
    rewrite Hss in H. cbn [ALOOKUP] in H. rewrite bool_decide_eq_true_2 in H by reflexivity. discriminate.
  - destruct (is_wf_shape (structs s) sh) eqn:Ew; [|discriminate].
    destruct (eval s e) as [[[w]| |]|] eqn:E; try discriminate.
    rewrite Hts, <- Hss, Ew, (IH _ eq_refl). rewrite Hss in H |- *.
    unfold mem_load in *. eapply mem_load_f_mono; [exact Hd|exact H].
  - destruct (eval s e) as [[[w]| |]|] eqn:E; try discriminate. rewrite (IH _ eq_refl).
    destruct (mem_load_32 (memory s) (memaddrs s) (be s) w) as [b|] eqn:Em; [|discriminate].
    rewrite <- Hbe, (mem_load_32_mono _ _ _ _ _ _ _ Hd Em). exact H.
  - destruct (eval s e) as [[[w]| |]|] eqn:E; try discriminate. rewrite (IH _ eq_refl).
    destruct (mem_load_byte (memory s) (memaddrs s) (be s) w) as [b|] eqn:Em; [|discriminate].
    rewrite <- Hbe, (mem_load_byte_mono _ _ _ _ _ _ _ Hd Em). exact H.
  - destruct (OPT_MMAP (eval s) es) as [vs|] eqn:E; [|discriminate].
    rewrite OPT_MMAP_MAP. replace (OPT_MMAP (fun x => eval t (compile_exp ctxt x)) es) with (SOME vs);
      [exact H|].
    symmetry. clear H. revert vs E. induction IH as [|x xs Hx Hxs IHl]; intros vs E; [exact E|].
    cbn [OPT_MMAP] in E |- *. destruct (eval s x) as [y|] eqn:Ey; [|discriminate]. cbn in E.
    destruct (OPT_MMAP (eval s) xs) as [ys|] eqn:Eys; [|discriminate]. cbn in E. injection E as <-.
    rewrite (Hx _ eq_refl), (IHl _ eq_refl). reflexivity.
  - destruct (OPT_MMAP (eval s) es) as [vs|] eqn:E; [|discriminate].
    rewrite OPT_MMAP_MAP. replace (OPT_MMAP (fun x => eval t (compile_exp ctxt x)) es) with (SOME vs);
      [exact H|].
    symmetry. clear H. revert vs E. induction IH as [|x xs Hx Hxs IHl]; intros vs E; [exact E|].
    cbn [OPT_MMAP] in E |- *. destruct (eval s x) as [y|] eqn:Ey; [|discriminate]. cbn in E.
    destruct (OPT_MMAP (eval s) xs) as [ys|] eqn:Eys; [|discriminate]. cbn in E. injection E as <-.
    rewrite (Hx _ eq_refl), (IHl _ eq_refl). reflexivity.
  - destruct (eval s e1) as [x1|] eqn:E1; [|discriminate].
    destruct (eval s e2) as [x2|] eqn:E2; [|destruct x1 as [[]| |]; discriminate].
    rewrite (IH1 _ eq_refl), (IH2 _ eq_refl). exact H.
  - destruct (eval s e1) as [x1|] eqn:E1; [|discriminate].
    destruct (eval s e2) as [x2|] eqn:E2; [|destruct x1 as [[]| |]; discriminate].
    rewrite (IH1 _ eq_refl), (IH2 _ eq_refl). exact H.
  - rewrite <- Hbase. exact H.
  - injection H as <-. rewrite Htop. reflexivity.
  - exact H.
Qed.

End Exp.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "good_res_def" *)
Definition good_res {a} (res : option (result a)) : bool :=
  match res with
  | SOME TimeOut => false
  | SOME (Return v0) => false
  | SOME (Exception l v0) => false
  | SOME (FinalFFI ev) => false
  | _ => true
  end.

(** ** Galette-only word and address helpers *)

Section WordHelpers.
Context {a : N}.

Lemma gd_cases : good_dimindex a ->
  (dimindex a = 32 /\ dimword a = 4294967296) \/ (dimindex a = 64 /\ dimword a = 18446744073709551616).
Proof. unfold good_dimindex, dimword; intros [H|H]; [left|right]; rewrite H; split; reflexivity. Qed.

Lemma w2n_bw : good_dimindex a -> w2n (bytes_in_word : word a) = dimindex a / 8.
Proof.
  intros Hg. unfold bytes_in_word. rewrite w2n_n2w. apply N.mod_small.
  destruct (gd_cases Hg) as [[-> ->]|[-> ->]]; reflexivity.
Qed.

Lemma bw_props : good_dimindex a ->
  let k := dimindex a / 8 in (k = 4 \/ k = 8) /\ dimword a mod k = 0 /\ 2 * k <= dimword a /\
  N.pow 2 (LOG2 k) = k.
Proof.
  intros Hg; destruct (gd_cases Hg) as [[-> ->]|[-> ->]]; cbn; repeat split; try lia.
Qed.

Lemma n2w_mul_bw i : ((n2w i : word a) * bytes_in_word)%w = n2w (i * (dimindex a / 8)).
Proof. unfold bytes_in_word. apply word_mul_n2w. Qed.

Lemma bw_mul_n2w i : (bytes_in_word * (n2w i : word a))%w = n2w ((dimindex a / 8) * i).
Proof. unfold bytes_in_word. apply word_mul_n2w. Qed.

Lemma w2n_n2w_small n : n < dimword a -> w2n (n2w n : word a) = n.
Proof. intros H; rewrite w2n_n2w; apply N.mod_small, H. Qed.

Lemma byte_aligned_iff (w : word a) : good_dimindex a ->
  is_true (byte_aligned w) <-> w2n w mod (dimindex a / 8) = 0.
Proof.
  intros Hg. unfold byte_aligned. rewrite aligned_w2n.
  destruct (bw_props Hg) as (_ & _ & _ & Hk). unfold LOG2 in Hk |- *. rewrite Hk. reflexivity.
Qed.

Lemma in_addresses (ad x : word a) n :
  x IN addresses ad n <-> exists i, x = (ad + n2w i * bytes_in_word)%w /\ i < n.
Proof. rewrite stack_removeProof.addresses_thm. reflexivity. Qed.

Lemma addresses_split (ad : word a) n m :
  addresses ad (n + m) = addresses ad n UNION addresses (ad + bytes_in_word * n2w n)%w m.
Proof.
  apply set_ext; intros x.
  change (x IN addresses ad (n + m) <-> x IN (addresses ad n UNION addresses (ad + bytes_in_word * n2w n)%w m)).
  rewrite IN_UNION, !in_addresses. split.
  - intros (i & -> & Hi). destruct (N.lt_ge_cases i n) as [Hl|Hl].
    + left; exists i; split; [reflexivity|exact Hl].
    + right; exists (i - n); split; [|lia].
      replace i with (n + (i - n)) at 1 by lia. rewrite <- word_add_n2w. word_ring.
  - intros [(i & -> & Hi)|(i & -> & Hi)].
    + exists i; split; [reflexivity|lia].
    + exists (n + i); split; [|lia]. rewrite <- word_add_n2w. word_ring.
Qed.

Lemma addresses_0 (ad : word a) : addresses ad 0 = EMPTY.
Proof. apply (proj1 (stack_removeProof.addresses_def ad 0)). Qed.

Lemma addresses_1 (ad x : word a) : x IN addresses ad 1 <-> x = ad.
Proof.
  rewrite in_addresses. split.
  - intros (i & -> & Hi). replace i with 0 by lia. word_ring.
  - intros ->. exists 0. split; [word_ring|lia].
Qed.

Lemma n2w_mul_bw_inj i j : good_dimindex a ->
  i * (dimindex a / 8) < dimword a -> j * (dimindex a / 8) < dimword a ->
  ((n2w i : word a) * bytes_in_word)%w = (n2w j * bytes_in_word)%w -> i = j.
Proof.
  intros Hg Hi Hj H. rewrite !n2w_mul_bw in H. apply (f_equal w2n) in H.
  rewrite !w2n_n2w_small in H by assumption. destruct (bw_props Hg) as ([Hk|Hk] & _); nia.
Qed.

(** HOL's [DISJOINT_addresses_lemma], in its general form. *)
Lemma addresses_disjoint_off (ad : word a) n m : good_dimindex a ->
  (n + m) * (dimindex a / 8) < dimword a ->
  DISJOINT (addresses ad n) (addresses (ad + bytes_in_word * n2w n)%w m).
Proof.
  intros Hg Hb. apply DISJOINT_ALT. intros x Hx1 Hx2. rewrite in_addresses in Hx1, Hx2.
  destruct Hx1 as (i & -> & Hi). destruct Hx2 as (j & Hj & Hjm).
  assert (E : ((n2w i : word a) * bytes_in_word)%w = (n2w (n + j) * bytes_in_word)%w).
  { apply (proj1 (WORD_EQ_ADD_LCANCEL ad _ _)). rewrite Hj, <- word_add_n2w. word_ring. }
  apply n2w_mul_bw_inj in E; [lia|exact Hg| |]; destruct (bw_props Hg) as ([Hk|Hk] & _); nia.
Qed.

End WordHelpers.

(** ** Memory *)

Section Memory.
Context {a : N}.

Lemma size_nil (stcs : list (stcname * struct_info)) sh :
  is_true (is_wf_shape_nil sh) -> size_of_sh_with_ctxt stcs sh = size_of_shape sh.
Proof. intros H; apply size_of_sh_with_ctxt_eq, H. Qed.

Lemma wf_nil_Comb shs : is_true (is_wf_shape_nil (Comb shs)) <-> Forall (fun sh => is_true (is_wf_shape_nil sh)) shs.
Proof. cbn [is_wf_shape]. unfold is_true; rewrite EVERY_Forall. reflexivity. Qed.

(** [mem_load] at a well-formed shape reads only the addresses of the
    shape. *)
Lemma mem_load_frame : forall sh stcs (addr : word a) dm (m1 m2 : word a -> word_lab a),
  is_true (is_wf_shape_nil sh) ->
  (forall x, x IN addresses addr (size_of_shape sh) -> m1 x = m2 x) ->
  mem_load sh addr dm m1 stcs = mem_load sh addr dm m2 stcs.
Proof.
  intros sh stcs; induction sh as [| l Hl | nm] using shape_nested_ind; intros addr dm m1 m2 Hw Hm.
  - rewrite !(proj1 mem_load_def). rewrite Hm; [reflexivity|]. apply addresses_1; reflexivity.
  - rewrite !(proj1 mem_load_def). apply wf_nil_Comb in Hw. cbn [size_of_shape] in Hm.
    enough (E : mem_loads l addr dm m1 stcs = mem_loads l addr dm m2 stcs) by (rewrite E; reflexivity).
    revert addr Hm. induction Hl as [|x xs Hx Hxs IHl]; intros addr Hm;
      [rewrite !(proj1 (proj2 mem_load_def)); reflexivity|].
    inversion Hw as [|? ? Hw1 Hw2]; subst.
    rewrite !(proj1 (proj2 (proj2 mem_load_def))). cbn [MAP List.map SUM] in Hm.
    rewrite addresses_split in Hm. rewrite (size_nil _ _ Hw1).
    rewrite (Hx addr dm m1 m2 Hw1), (IHl Hw2 _).
    + reflexivity.
    + intros y Hy; apply Hm, IN_UNION; right; exact Hy.
    + intros y Hy; apply Hm, IN_UNION; left; exact Hy.
  - discriminate.
Qed.

Lemma mem_loads_frame : forall shs stcs (addr : word a) dm (m1 m2 : word a -> word_lab a),
  Forall (fun sh => is_true (is_wf_shape_nil sh)) shs ->
  (forall x, x IN addresses addr (SUM (MAP size_of_shape shs)) -> m1 x = m2 x) ->
  mem_loads shs addr dm m1 stcs = mem_loads shs addr dm m2 stcs.
Proof.
  intros shs stcs addr dm m1 m2 Hw Hm.
  pose proof (mem_load_frame (Comb shs) stcs addr dm m1 m2 (proj2 (wf_nil_Comb shs) Hw) Hm) as E.
  rewrite !(proj1 mem_load_def) in E.
  destruct (mem_loads shs addr dm m1 stcs), (mem_loads shs addr dm m2 stcs); congruence.
Qed.

Lemma mem_load_addresses : forall sh (addr : word a) dm m v0,
  is_true (is_wf_shape_nil sh) -> mem_load sh addr dm m [] = SOME v0 ->
  addresses addr (size_of_shape sh) SUBSET dm.
Proof.
  intros sh; induction sh as [| l Hl | nm] using shape_nested_ind; intros addr dm m v0 Hw H.
  - rewrite (proj1 mem_load_def) in H. destruct (classical_dec _) as [Hi|]; [|discriminate].
    intros x Hx. apply addresses_1 in Hx. subst. exact Hi.
  - rewrite (proj1 mem_load_def) in H. apply wf_nil_Comb in Hw. cbn [size_of_shape].
    destruct (mem_loads l addr dm m []) as [vs|] eqn:E; [|discriminate]. clear H.
    revert addr vs E. induction Hl as [|x xs Hx Hxs IHl]; intros addr vs E.
    + intros y Hy. cbn [MAP List.map SUM] in Hy. rewrite addresses_0 in Hy. destruct Hy.
    + inversion Hw as [|? ? Hw1 Hw2]; subst.
      rewrite (proj1 (proj2 (proj2 mem_load_def))) in E.
      destruct (mem_load x addr dm m []) as [y|] eqn:Ey; [|discriminate].
      destruct (mem_loads xs _ dm m []) as [ys|] eqn:Eys; [|discriminate].
      cbn [MAP List.map SUM]. rewrite addresses_split. intros z Hz. apply IN_UNION in Hz as [Hz|Hz].
      * exact (Hx addr dm m y Hw1 Ey z Hz).
      * rewrite (size_nil _ _ Hw1) in Eys. exact (IHl Hw2 _ _ Eys z Hz).
  - discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_append" *)
Theorem mem_stores_append : forall (addr : word a) vs addrs memory vs',
  mem_stores addr (vs ++ vs') addrs memory =
  match mem_stores addr vs addrs memory with
  | NONE => NONE
  | SOME memory' => mem_stores (addr + bytes_in_word * n2w (LENGTH vs))%w vs' addrs memory'
  end.
Proof.
  intros addr vs; revert addr; induction vs as [|v0 vs IH]; intros addr addrs memory vs'.
  - cbn [mem_stores List.app LENGTH]. f_equal. word_ring.
  - cbn [List.app mem_stores]. destruct (mem_store addr v0 addrs memory) as [m'|]; [|reflexivity].
    rewrite IH. destruct (mem_stores _ vs addrs m'); [|reflexivity]. f_equal.
    rewrite LENGTH_cons, <- word_add_n2w. word_ring.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_memory_swap" *)
Theorem mem_stores_memory_swap : forall (addr : word a) vs addrs memory memory' m,
  mem_stores addr vs addrs memory = SOME m -> exists m', mem_stores addr vs addrs memory' = SOME m'.
Proof.
  intros addr vs; revert addr; induction vs as [|v0 vs IH]; intros addr addrs memory memory' m H.
  - eexists; reflexivity.
  - cbn [mem_stores] in H |- *. unfold mem_store in *.
    destruct (classical_dec (addr IN addrs)); [|discriminate].
    exact (IH _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_addrs_IS_SOME" *)
Theorem mem_stores_addrs_IS_SOME : forall (addr' : word a) ws memaddrs memory,
  addresses addr' (LENGTH ws) SUBSET memaddrs ->
  exists m, mem_stores addr' ws memaddrs memory = SOME m.
Proof.
  intros addr' ws; revert addr'; induction ws as [|w ws IH]; intros addr' dm memory H.
  - eexists; reflexivity.
  - cbn [mem_stores LENGTH] in *. rewrite (proj2 (stack_removeProof.addresses_def addr' _)) in H.
    unfold mem_store. destruct (classical_dec (addr' IN dm)) as [|Hn].
    + apply IH. intros x Hx. apply H, IN_INSERT. right; exact Hx.
    + exfalso; apply Hn, H, IN_INSERT. left; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_load_mem_store" *)
Theorem mem_load_mem_store :
  (forall s (addr : word a) addrs memory sctxt v0 w,
     mem_load s addr addrs memory sctxt = SOME v0 /\
     sctxt = [] /\ is_true (is_wf_shape sctxt s) /\ shape_of w = s ->
     exists m, mem_stores addr (flatten w) addrs memory = SOME m) /\
  (forall ss (addr : word a) addrs memory sctxt vs ws,
     mem_loads ss addr addrs memory sctxt = SOME vs /\
     sctxt = [] /\ is_true (EVERY (is_wf_shape sctxt) ss) /\ ss = MAP shape_of ws ->
     exists m, mem_stores addr (FLAT (MAP (fun a0 => flatten a0) ws)) addrs memory = SOME m) /\
  (forall (fs : list (fldname * shape)) (addr : word a) addrs memory (sctxt : list (stcname * struct_info)) vfs,
     mem_load_flds fs addr addrs memory sctxt = SOME vfs /\ sctxt = [] /\ True -> True).
Proof.
  split; [|split; [|intros; exact Logic.I]].
  - intros s addr addrs memory sctxt v0 w (H & -> & Hw & <-).
    apply mem_stores_addrs_IS_SOME. rewrite length_flatten_eq_size_of_shape by exact Hw.
    exact (mem_load_addresses _ _ _ _ _ Hw H).
  - intros ss addr addrs memory sctxt vs ws (H & -> & Hw & ->).
    apply mem_stores_addrs_IS_SOME.
    assert (Hc : is_true (is_wf_shape_nil (Comb (MAP shape_of ws)))) by exact Hw.
    pose proof (mem_load_addresses (Comb (MAP shape_of ws)) addr addrs memory (RStruct vs) Hc) as Ha.
    rewrite (proj1 mem_load_def), H in Ha. specialize (Ha eq_refl).
    replace (LENGTH (FLAT (MAP (fun a0 => flatten a0) ws))) with (size_of_shape (Comb (MAP shape_of ws)));
      [exact Ha|].
    exact (eq_sym (length_flatten_eq_size_of_shape (RStruct ws) Hc)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_lookup" *)
Theorem mem_stores_lookup : forall (addr : word a) vs addrs memory m addr',
  mem_stores addr vs addrs memory = SOME m /\ addr' NOTIN addresses addr (LENGTH vs) ->
  m addr' = memory addr'.
Proof.
  intros addr vs; revert addr; induction vs as [|v0 vs IH]; intros addr addrs memory m addr' [H Hn].
  - injection H as <-; reflexivity.
  - cbn [mem_stores LENGTH] in H, Hn. rewrite (proj2 (stack_removeProof.addresses_def addr _)) in Hn.
    unfold mem_store in H. destruct (classical_dec (addr IN addrs)); [|discriminate].
    rewrite (IH _ _ _ _ _ (conj H (fun Hx => Hn (proj2 (IN_INSERT _ _ _) (or_intror Hx))))).
    rewrite APPLY_UPDATE_THM. destruct (decide (addr = addr')) as [->|]; [|reflexivity].
    exfalso; apply Hn, IN_INSERT; left; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_load_disjoint" *)
Theorem mem_stores_load_disjoint :
  (forall sh (addr : word a) vs addrs memory m stcs addr',
     mem_stores addr vs addrs memory = SOME m /\
     stcs = [] /\ is_true (is_wf_shape stcs sh) /\
     DISJOINT (addresses addr' (size_of_shape sh)) (addresses addr (LENGTH vs)) ->
     mem_load sh addr' addrs m stcs = mem_load sh addr' addrs memory []) /\
  (forall shs (addr : word a) vs addrs memory m stcs addr',
     mem_stores addr vs addrs memory = SOME m /\
     stcs = [] /\ is_true (EVERY (is_wf_shape stcs) shs) /\
     DISJOINT (addresses addr' (SUM (MAP size_of_shape shs))) (addresses addr (LENGTH vs)) ->
     mem_loads shs addr' addrs m stcs = mem_loads shs addr' addrs memory []).
Proof.
  split.
  - intros sh addr vs addrs memory m stcs addr' (H & -> & Hw & Hd). apply mem_load_frame; [exact Hw|].
    intros x Hx. apply (mem_stores_lookup _ _ _ _ _ _ (conj H (proj1 (DISJOINT_ALT _ _) Hd x Hx))).
  - intros shs addr vs addrs memory m stcs addr' (H & -> & Hw & Hd). apply mem_loads_frame.
    + apply EVERY_Forall in Hw. exact Hw.
    + intros x Hx. apply (mem_stores_lookup _ _ _ _ _ _ (conj H (proj1 (DISJOINT_ALT _ _) Hd x Hx))).
Qed.

Lemma LENGTH_app_ {A} (l1 l2 : list A) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. rewrite !LENGTH_length, length_app. lia. Qed.

Lemma mem_stores_back_list (vals : list (v a)) :
  Forall (fun val => forall (addr : word a) addrs memory m,
     mem_stores addr (flatten val) addrs memory = SOME m ->
     LENGTH (flatten val) * w2n (bytes_in_word : word a) < dimword a ->
     is_true (is_wf_shape_nil (shape_of val)) -> good_dimindex a ->
     mem_load (shape_of val) addr addrs m [] = SOME val) vals ->
  forall (addr : word a) addrs memory m,
    mem_stores addr (FLAT (MAP (fun a0 => flatten a0) vals)) addrs memory = SOME m ->
    LENGTH (FLAT (MAP (fun a0 => flatten a0) vals)) * w2n (bytes_in_word : word a) < dimword a ->
    is_true (EVERY is_wf_shape_nil (MAP shape_of vals)) -> good_dimindex a ->
    mem_loads (MAP shape_of vals) addr addrs m [] = SOME vals.
Proof.
  induction 1 as [|x xs Hx Hxs IH]; intros addr addrs memory m H Hl Hw Hg.
  - apply (proj1 (proj2 mem_load_def)).
  - cbn [MAP List.map FLAT List.concat] in H, Hl, Hw. unfold is_true in Hw.
    apply Bool.andb_true_iff in Hw as [Hw1 Hw2].
    rewrite mem_stores_append in H.
    destruct (mem_stores addr (flatten x) addrs memory) as [m1|] eqn:E1; [|discriminate].
    rewrite LENGTH_app_ in Hl.
    cbn [MAP List.map]. rewrite (proj1 (proj2 (proj2 mem_load_def))).
    rewrite (size_nil _ _ Hw1), <- (length_flatten_eq_size_of_shape x Hw1).
    rewrite (IH _ _ _ _ H ltac:(lia) Hw2 Hg).
    rewrite (mem_load_frame (shape_of x) [] addr addrs m m1 Hw1).
    + rewrite (Hx addr addrs memory m1 E1 ltac:(lia) Hw1 Hg). reflexivity.
    + intros y Hy. rewrite w2n_bw in Hl by exact Hg.
      pose proof (addresses_disjoint_off addr (LENGTH (flatten x))
                    (LENGTH (FLAT (MAP (fun a0 => flatten a0) xs))) Hg ltac:(lia)) as Hd.
      rewrite <- (length_flatten_eq_size_of_shape x Hw1) in Hy.
      exact (mem_stores_lookup _ _ _ _ _ _ (conj H (proj1 (DISJOINT_ALT _ _) Hd y Hy))).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_mem_load_back" *)
Theorem mem_stores_mem_load_back :
  (forall val (addr : word a) addrs memory m sctxt,
     mem_stores addr (flatten val) addrs memory = SOME m /\
     LENGTH (flatten val) * w2n (bytes_in_word : word a) < dimword a /\
     is_true (is_wf_shape sctxt (shape_of val)) /\ sctxt = [] /\
     good_dimindex a ->
     mem_load (shape_of val) addr addrs m sctxt = SOME val) /\
  (forall vals (addr : word a) addrs memory m sctxt,
     mem_stores addr (FLAT (MAP (fun a0 => flatten a0) vals)) addrs memory = SOME m /\
     LENGTH (FLAT (MAP (fun a0 => flatten a0) vals)) * w2n (bytes_in_word : word a) < dimword a /\
     is_true (EVERY (is_wf_shape sctxt) (MAP shape_of vals)) /\ sctxt = [] /\
     good_dimindex a ->
     mem_loads (MAP shape_of vals) addr addrs m sctxt = SOME vals).
Proof.
  assert (G : forall val (addr : word a) addrs memory m,
     mem_stores addr (flatten val) addrs memory = SOME m ->
     LENGTH (flatten val) * w2n (bytes_in_word : word a) < dimword a ->
     is_true (is_wf_shape_nil (shape_of val)) -> good_dimindex a ->
     mem_load (shape_of val) addr addrs m [] = SOME val).
  { intros val; induction val as [w|vs IH|nm vs IH] using v_nested_ind; intros addr addrs memory m H Hl Hw Hg.
    - cbn [flatten mem_stores] in H. unfold mem_store in H.
      destruct (classical_dec (addr IN addrs)) as [Hi|]; [|discriminate]. injection H as <-.
      cbn [shape_of]. rewrite (proj1 mem_load_def). destruct (classical_dec _); [|contradiction].
      rewrite APPLY_UPDATE_THM. destruct (decide (addr = addr)) as [_|C]; [reflexivity|exfalso; apply C; reflexivity].
    - cbn [shape_of]. rewrite (proj1 mem_load_def).
      rewrite (mem_stores_back_list vs IH addr addrs memory m H Hl Hw Hg). reflexivity.
    - discriminate. }
  split.
  - intros val addr addrs memory m sctxt (H & Hl & Hw & -> & Hg). exact (G _ _ _ _ _ H Hl Hw Hg).
  - intros vals addr addrs memory m sctxt (H & Hl & Hw & -> & Hg).
    apply (mem_stores_back_list vals) with (memory := memory); try assumption.
    apply Forall_forall. intros x _. exact (G x).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "LESS_MULT_MONO'" *)
Theorem LESS_MULT_MONO' : forall a0 m n : N, 0 < a0 -> (a0 * m < a0 * n <-> m < n).
Proof. intros a0 m n H; split; intros; nia. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "byte_aligned_mul_bytes_in_word" *)
Theorem byte_aligned_mul_bytes_in_word : forall a0 : word a,
  good_dimindex a /\ is_true (byte_aligned a0) ->
  exists b, a0 = (b * bytes_in_word)%w /\ w2n b * w2n (bytes_in_word : word a) < dimword a.
Proof.
  intros a0 [Hg Ha]. apply (byte_aligned_iff a0 Hg) in Ha.
  rewrite w2n_bw by exact Hg. destruct (bw_props Hg) as (Hk & Hd & _).
  set (k := dimindex a / 8) in *. assert (Hk0 : k <> 0) by (destruct Hk; lia).
  pose proof (w2n_lt a0) as Hl. pose proof (N.Div0.div_mod (w2n a0) k) as Hdm. rewrite Ha in Hdm.
  set (q := w2n a0 / k) in *.
  assert (Hq : q < dimword a) by nia.
  exists (n2w q). rewrite n2w_mul_bw. fold k. rewrite w2n_n2w_small by exact Hq.
  split; [|nia]. apply word_eq_w2n. rewrite w2n_n2w_small by nia. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "w2n_add_alt" *)
Theorem w2n_add_alt : forall a0 b : word a,
  w2n a0 + w2n b < dimword a -> w2n a0 + w2n b = w2n (a0 + b)%w.
Proof. intros a0 b H. unfold word_add. rewrite w2n_n2w, N.mod_small by exact H. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "good_dimindex_w2n_add" *)
Theorem good_dimindex_w2n_add : forall a0 : word a,
  good_dimindex a /\ is_true (byte_aligned a0) /\ a0 <> (- n2w 1 * bytes_in_word)%w ->
  w2n a0 + w2n (bytes_in_word : word a) = w2n (a0 + bytes_in_word)%w.
Proof.
  intros a0 (Hg & Ha & Hn). apply w2n_add_alt. apply (byte_aligned_iff a0 Hg) in Ha.
  rewrite w2n_bw by exact Hg. pose proof (w2n_lt a0) as Hl.
  destruct (N.lt_ge_cases (w2n a0 + dimindex a / 8) (dimword a)) as [|Hge]; [assumption|exfalso].
  assert (E : w2n a0 = dimword a - dimindex a / 8).
  { pose proof (N.Div0.div_mod (w2n a0) (dimindex a / 8)) as Hdm. rewrite Ha in Hdm.
    destruct (gd_cases Hg) as [[Hd HD]|[Hd HD]];
      [assert (Hk : dimindex a / 8 = 4) by (rewrite Hd; reflexivity)
      |assert (Hk : dimindex a / 8 = 8) by (rewrite Hd; reflexivity)];
      rewrite Hk, HD in *; lia. }
  apply Hn. apply word_eq_w2n. rewrite E.
  replace (- n2w 1 * bytes_in_word)%w with (- (bytes_in_word : word a))%w by word_ring.
  unfold word_2comp. rewrite w2n_bw by exact Hg.
  destruct (gd_cases Hg) as [[Hd HD]|[Hd HD]];
    [assert (Hk : dimindex a / 8 = 4) by (rewrite Hd; reflexivity)
    |assert (Hk : dimindex a / 8 = 8) by (rewrite Hd; reflexivity)];
    rewrite Hk, HD; rewrite w2n_n2w_small; rewrite ?HD; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_bounded_length" *)
Theorem mem_stores_bounded_length : forall (addr : word a) ws addrs memory m addr',
  mem_stores addr ws addrs memory = SOME m /\
  addr' NOTIN addrs /\
  is_true (byte_aligned addr) /\ is_true (byte_aligned addr') /\
  good_dimindex a ->
  w2n (bytes_in_word : word a) * LENGTH ws <= w2n (addr' - addr)%w.
Proof.
  intros addr ws addrs memory m addr' (H & Hn & Ha & Ha' & Hg).
  assert (Hin : forall i, i < LENGTH ws -> (addr + n2w i * bytes_in_word)%w IN addrs).
  { clear Hn Ha Ha'. revert addr memory H. induction ws as [|w ws IH]; intros addr memory H i Hi;
      [cbn in Hi; lia|].
    cbn [mem_stores] in H. unfold mem_store in H.
    destruct (classical_dec (addr IN addrs)) as [Hi'|]; [|discriminate].
    destruct (N.eq_dec i 0) as [->|Hi0].
    - replace (addr + n2w 0 * bytes_in_word)%w with addr by word_ring. exact Hi'.
    - replace (addr + n2w i * bytes_in_word)%w with (addr + bytes_in_word + n2w (i - 1) * bytes_in_word)%w.
      + apply (IH _ _ H). rewrite LENGTH_cons in Hi; lia.
      + replace i with (i - 1 + 1) at 2 by lia. rewrite <- word_add_n2w. word_ring. }
  apply (byte_aligned_iff _ Hg) in Ha, Ha'. rewrite w2n_bw by exact Hg.
  destruct (bw_props Hg) as (Hk & Hd & H2 & _).
  set (k := dimindex a / 8) in *. set (d := w2n (addr' - addr)%w).
  assert (Hdm : d mod k = 0).
  { apply (byte_aligned_iff (addr' - addr)%w Hg).
    apply (aligned_add_sub_cor _ addr' addr). split; apply (byte_aligned_iff _ Hg); assumption. }
  destruct (N.le_gt_cases (k * LENGTH ws) d) as [|Hlt]; [assumption|exfalso].
  apply Hn. assert (Hk0 : k <> 0) by (destruct Hk; lia).
  replace addr' with (addr + n2w (d / k) * bytes_in_word)%w.
  - apply Hin. apply N.Div0.div_lt_upper_bound; lia.
  - rewrite n2w_mul_bw. fold k.
    replace (d / k * k) with d by (rewrite N.mul_comm; apply (proj2 (N.Div0.div_exact d k) Hdm)).
    unfold d. rewrite n2w_w2n. word_ring.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_load_disjoint" *)
Theorem mem_load_disjoint :
  (forall val (addr'' : word a) memory stcs v0 addr' addrs,
     mem_load (shape_of val) addr' addrs memory stcs = SOME val /\
     addr'' NOTIN addresses addr' (size_of_shape (shape_of val)) /\
     is_true (is_wf_shape_nil (shape_of val)) ->
     mem_load (shape_of val) addr' addrs ((addr'' =+ v0) memory) stcs = SOME val) /\
  (forall vals (addr'' : word a) memory stcs v0 addr' addrs,
     mem_loads (MAP shape_of vals) addr' addrs memory stcs = SOME vals /\
     addr'' NOTIN addresses addr' (SUM (MAP (size_of_shape ∘ shape_of) vals)) /\
     is_true (EVERY is_wf_shape_nil (MAP shape_of vals)) ->
     mem_loads (MAP shape_of vals) addr' addrs ((addr'' =+ v0) memory) stcs = SOME vals).
Proof.
  split.
  - intros val addr'' memory stcs v0 addr' addrs (H & Hn & Hw).
    rewrite <- H. apply mem_load_frame; [exact Hw|]. intros x Hx. rewrite APPLY_UPDATE_THM.
    destruct (decide (addr'' = x)) as [->|]; [contradiction|reflexivity].
  - intros vals addr'' memory stcs v0 addr' addrs (H & Hn & Hw).
    rewrite <- H. apply mem_loads_frame; [apply EVERY_Forall in Hw; exact Hw|]. intros x Hx.
    rewrite APPLY_UPDATE_THM. rewrite map_map in Hx.
    destruct (decide (addr'' = x)) as [->|]; [contradiction|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "byte_aligned_bytes_in_word_mul" *)
Theorem byte_aligned_bytes_in_word_mul : forall x : word a,
  good_dimindex a -> is_true (byte_aligned (bytes_in_word * x)%w).
Proof.
  intros x Hg. apply (byte_aligned_iff _ Hg). rewrite <- (n2w_w2n x), bw_mul_n2w, w2n_n2w.
  destruct (gd_cases Hg) as [[Hd HD]|[Hd HD]]; rewrite Hd, HD; cbn [N.div];
    [replace 4294967296 with (4 * 1073741824) by reflexivity|replace 18446744073709551616 with (8 * 2305843009213693952) by reflexivity];
    rewrite N.Div0.mul_mod_distr_l; rewrite N.mul_comm; apply N.Div0.mod_mul.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "DISJOINT_addresses_lemma" *)
Theorem DISJOINT_addresses_lemma : forall (addr1 addr2 : word a) offs offs',
  (addr1 + bytes_in_word * n2w offs)%w = addr2 /\ good_dimindex a /\
  w2n (bytes_in_word : word a) * (offs + offs') < dimword a ->
  DISJOINT (addresses addr1 offs) (addresses addr2 offs').
Proof.
  intros addr1 addr2 offs offs' (<- & Hg & Hb). rewrite w2n_bw in Hb by exact Hg.
  apply addresses_disjoint_off; [exact Hg|lia].
Qed.

End Memory.

(** ** Properties of the state relation *)

Section RelProps.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** Galette-only: the state relation for states whose relevant fields
    are those of related states. *)
Lemma state_rel_frame ls ls' ctxt s t s2 t2 :
  state_rel ls ctxt s t ->
  top_addr s2 = top_addr s -> top_addr t2 = top_addr t ->
  (is_true ls' -> locals s2 = locals t2) ->
  base_addr s2 = base_addr s -> base_addr t2 = base_addr t ->
  be s2 = be s -> be t2 = be t -> eshapes s2 = eshapes s -> eshapes t2 = eshapes t ->
  clock s2 = clock t2 -> structs s2 = structs s -> structs t2 = structs t ->
  globals s2 = globals s -> memaddrs s2 = memaddrs s -> memaddrs t2 = memaddrs t ->
  memory s2 = memory s -> memory t2 = memory t ->
  sh_memaddrs s2 = sh_memaddrs s -> sh_memaddrs t2 = sh_memaddrs t ->
  ffi s2 = ffi t2 -> code s2 = code s -> code t2 = code t ->
  state_rel ls' ctxt s2 t2.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19)
    E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 E22.
  unfold state_rel. rewrite E1, E2, E4, E5, E6, E7, E8, E9, E11, E12, E13, E14, E15, E16, E17, E18, E19, E21, E22.
  repeat split; assumption.
Qed.

Ltac sframe H := eapply (state_rel_frame _ _ _ _ _ _ _ H); try reflexivity.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_res_var" *)
Theorem state_rel_res_var : forall l ctxt s t s' t' v0 v',
  state_rel l ctxt s t /\ state_rel true ctxt s' t' ->
  state_rel l ctxt (set_locals (res_var (locals s) (v0, FLOOKUP (locals s') v')) s)
                   (set_locals (res_var (locals t) (v0, FLOOKUP (locals t') v')) t).
Proof.
  intros l ctxt s t s' t' v0 v' [H H']. pose proof H as Hc. destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _).
  destruct H' as (_ & Hl' & _).
  sframe H; cbn; [|exact Hck|exact Hf]. intros Hls. rewrite (Hl Hls), (Hl' eq_refl). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_dec_clock" *)
Theorem state_rel_dec_clock : forall ls ctxt s t,
  state_rel ls ctxt s t -> state_rel ls ctxt (dec_clock s) (dec_clock t).
Proof.
  intros ls ctxt s t H. pose proof H as Hc. destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _).
  sframe H; cbn; [exact Hl| |exact Hf]. rewrite Hck. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_empty_locals" *)
Theorem state_rel_empty_locals : forall ls' ctxt s t,
  (state_rel true ctxt s t -> state_rel ls' ctxt (empty_locals s) (empty_locals t)) /\
  (state_rel false ctxt s t -> state_rel ls' ctxt (empty_locals s) (empty_locals t)).
Proof.
  intros ls' ctxt s t; split; intros H; pose proof H as Hc;
    destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _);
    sframe H; cbn; try assumption; intros _; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_change_locals" *)
Theorem state_rel_change_locals : forall ls' ctxt s t x,
  (state_rel true ctxt s t -> state_rel ls' ctxt (set_locals x s) (set_locals x t)) /\
  (state_rel false ctxt s t -> state_rel ls' ctxt (set_locals x s) (set_locals x t)).
Proof.
  intros ls' ctxt s t x; split; intros H; pose proof H as Hc;
    destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _);
    sframe H; cbn; try assumption; intros _; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_set_var" *)
Theorem state_rel_set_var : forall ls' ctxt s t rt retv,
  state_rel true ctxt s t -> state_rel ls' ctxt (set_var rt retv s) (set_var rt retv t).
Proof.
  intros ls' ctxt s t rt retv H; pose proof H as Hc;
    destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _).
  unfold set_var. sframe H; cbn; try assumption. intros _; rewrite (Hl eq_refl); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_change_ffi" *)
Theorem state_rel_change_ffi : forall ls' ctxt s t x,
  state_rel ls' ctxt s t -> state_rel ls' ctxt (set_ffi x s) (set_ffi x t).
Proof.
  intros ls' ctxt s t x H; pose proof H as Hc;
    destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _).
  sframe H; cbn; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_memory_update" *)
Theorem state_rel_memory_update : forall ctxt s t addr' h,
  state_rel true ctxt s t /\ addr' IN memaddrs s ->
  state_rel true ctxt (set_memory ((addr' =+ h) (memory s)) s) (set_memory ((addr' =+ h) (memory t)) t).
Proof.
  intros ctxt s t addr' h [H Hin].
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  unfold state_rel; state_cbn. repeat split; try assumption.
  - intros v0 val Hv. destruct (H9 v0 val Hv) as (addr & A1 & A2 & A3 & A4 & A5).
    exists addr. split; [exact A1|split; [exact A2|split; [|split; assumption]]].
    apply (proj1 mem_load_disjoint). split; [exact A3|split; [|exact A2]].
    intros Hx. exact (proj1 (DISJOINT_ALT _ _) A4 addr' Hin Hx).
  - intros x Hx. rewrite !APPLY_UPDATE_THM. destruct (decide (addr' = x)); [reflexivity|apply H13, Hx].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FLOOKUP_globals_val_state_rel" *)
Theorem FLOOKUP_globals_val_state_rel : forall s nm v0 b ctxt t,
  FLOOKUP (globals s) nm = SOME (Val v0) /\ state_rel b ctxt s t ->
  exists addr_diff, FLOOKUP (pan_globals.globals ctxt) nm = SOME (shape_of (Val v0), addr_diff) /\
    mem_load (shape_of (Val v0)) (top_addr t - addr_diff)%w (memaddrs t) (memory t) [] = SOME (Val v0) /\
    DISJOINT (memaddrs s) (addresses (top_addr t - addr_diff)%w (size_of_shape (shape_of (Val v0)))) /\
    is_true (byte_aligned addr_diff).
Proof.
  intros s nm v0 b ctxt t [H Hr]. destruct Hr as (_ & _ & _ & _ & _ & _ & _ & _ & H9 & _).
  destruct (H9 _ _ H) as (addr & A1 & _ & A3 & A4 & A5). exists addr. repeat split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "OPT_MMAP_eval_correct" *)
Theorem OPT_MMAP_eval_correct : forall ctxt s t argexps args,
  state_rel true ctxt s t /\ OPT_MMAP (eval s) argexps = SOME args ->
  OPT_MMAP (eval t) (MAP (compile_exp ctxt) argexps) = SOME args.
Proof.
  intros ctxt s t argexps args [Hr H]. rewrite OPT_MMAP_MAP. revert args H.
  induction argexps as [|e es IH]; intros args H; [exact H|].
  cbn [OPT_MMAP] in H |- *. destruct (eval s e) as [x|] eqn:E; [|discriminate]. cbn in H.
  destruct (OPT_MMAP (eval s) es) as [xs|] eqn:Es; [|discriminate]. cbn in H. injection H as <-.
  rewrite (compile_exp_correct s e x ctxt t (conj Hr E)), (IH xs eq_refl). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_lookup_code" *)
Theorem state_rel_lookup_code : forall ls ctxt s t fname (args : list (v a)) prog newlocals,
  state_rel ls ctxt s t /\ lookup_code (code s) fname args = SOME (prog, newlocals) ->
  lookup_code (code t) fname args = SOME (compile ctxt prog, newlocals).
Proof.
  intros ls ctxt s t fname args prog newlocals [Hr H].
  destruct Hr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & _).
  unfold lookup_code in *. destruct (FLOOKUP (code s) fname) as [[vs [p rs]]|] eqn:E; [|discriminate].
  rewrite (Hc _ _ _ _ E). destruct (_ && _); [|discriminate]. injection H as <- <-. reflexivity.
Qed.

Lemma read_bytearray_mono {B} (f g : word a -> option B) sz n bytes :
  (forall x y, f x = SOME y -> g x = SOME y) ->
  read_bytearray sz n f = SOME bytes -> read_bytearray sz n g = SOME bytes.
Proof.
  intros Hfg. revert sz bytes. induction n as [|n IH] using N.peano_ind; intros sz bytes H; [exact H|].
  rewrite (proj2 (read_bytearray_def sz f n)) in H. rewrite (proj2 (read_bytearray_def sz g n)).
  destruct (f sz) as [b|] eqn:Ef; [|discriminate]. rewrite (Hfg _ _ Ef).
  destruct (read_bytearray (sz + n2w 1)%w n f) as [bs|] eqn:Er; [|discriminate].
  rewrite (IH _ _ Er). exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_read_bytearray" *)
Theorem state_rel_read_bytearray : forall ls ctxt s t bytes sz ad,
  state_rel ls ctxt s t /\
  read_bytearray sz ad (mem_load_byte (memory s) (memaddrs s) (be s)) = SOME bytes ->
  read_bytearray sz ad (mem_load_byte (memory t) (memaddrs t) (be t)) = SOME bytes.
Proof.
  intros ls ctxt s t bytes sz ad [Hr H].
  destruct Hr as (_ & _ & _ & Hbe & _ & _ & _ & _ & _ & _ & Hsub & _ & Hmem & _).
  assert (Hd : forall x, x IN memaddrs s -> x IN memaddrs t /\ memory s x = memory t x)
    by (intros x Hx; split; [apply Hsub, Hx|apply Hmem, Hx]).
  rewrite <- Hbe. eapply read_bytearray_mono; [|exact H].
  intros x y Hx. exact (mem_load_byte_mono _ _ _ _ _ _ _ Hd Hx).
Qed.

Lemma sr_memory_update ls ctxt s t addr' h :
  state_rel ls ctxt s t -> addr' IN memaddrs s ->
  state_rel ls ctxt (set_memory ((addr' =+ h) (memory s)) s) (set_memory ((addr' =+ h) (memory t)) t).
Proof.
  intros H Hin.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  unfold state_rel; state_cbn. repeat split; try assumption.
  - intros v0 val Hv. destruct (H9 v0 val Hv) as (addr & A1 & A2 & A3 & A4 & A5).
    exists addr. split; [exact A1|split; [exact A2|split; [|split; assumption]]].
    apply (proj1 mem_load_disjoint). split; [exact A3|split; [|exact A2]].
    intros Hx. exact (proj1 (DISJOINT_ALT _ _) A4 addr' Hin Hx).
  - intros x Hx. rewrite !APPLY_UPDATE_THM. destruct (decide (addr' = x)); [reflexivity|apply H13, Hx].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_mem_store_byte" *)
Theorem state_rel_mem_store_byte : forall ls ctxt s t addr' b m',
  state_rel ls ctxt s t /\ mem_store_byte (memory s) (memaddrs s) (be s) addr' b = SOME m' ->
  exists m'', mem_store_byte (memory t) (memaddrs t) (be t) addr' b = SOME m'' /\
    state_rel ls ctxt (set_memory m' s) (set_memory m'' t).
Proof.
  intros ls ctxt s t addr' b m' [Hr H]. pose proof Hr as Hc.
  destruct Hc as (_ & _ & _ & Hbe & _ & _ & _ & _ & _ & _ & Hsub & _ & Hmem & _).
  unfold mem_store_byte in *. destruct (memory s (byte_align addr')) as [w] eqn:Em.
  destruct (classical_dec (byte_align addr' IN memaddrs s)) as [Hi|]; [|discriminate].
  injection H as <-. rewrite <- (Hmem _ Hi), Em, <- Hbe.
  destruct (classical_dec (byte_align addr' IN memaddrs t)) as [|Hn]; [|exfalso; apply Hn, Hsub, Hi].
  eexists; split; [reflexivity|]. exact (sr_memory_update _ _ _ _ _ _ Hr Hi).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_write_bytearray" *)
Theorem state_rel_write_bytearray : forall {A} (a0 : A) ls ctxt s t sz nbw bs,
  state_rel ls ctxt s t /\
  read_bytearray sz (LENGTH nbw) (mem_load_byte (memory s) (memaddrs s) (be s)) = SOME bs ->
  state_rel ls ctxt (set_memory (write_bytearray sz nbw (memory s) (memaddrs s) (be s)) s)
                    (set_memory (write_bytearray sz nbw (memory t) (memaddrs t) (be t)) t).
Proof.
  intros A a0 ls ctxt s t sz nbw; revert sz. induction nbw as [|b nbw IH]; intros sz bs [Hr H].
  - cbn [write_bytearray]. pose proof Hr as Hc.
    destruct Hc as (_ & Hl & _ & _ & _ & Hck & _ & _ & _ & _ & _ & _ & _ & Hf & _).
    sframe Hr; cbn; try assumption; destruct s; destruct t; reflexivity.
  - rewrite LENGTH_cons, N.add_1_r in H. rewrite (proj2 (read_bytearray_def sz _ _)) in H.
    destruct (mem_load_byte (memory s) (memaddrs s) (be s) sz) as [b0|] eqn:Eb; [|discriminate].
    destruct (read_bytearray (sz + n2w 1)%w (LENGTH nbw) _) as [bs'|] eqn:Er; [|discriminate].
    pose proof (IH _ _ (conj Hr Er)) as Hr'.
    assert (Hi : byte_align sz IN memaddrs s).
    { unfold mem_load_byte in Eb. destruct (memory s (byte_align sz)).
      destruct (classical_dec _); [assumption|discriminate]. }
    cbn [write_bytearray].
    destruct (mem_store_byte (write_bytearray (sz + n2w 1)%w nbw (memory s) (memaddrs s) (be s))
                (memaddrs s) (be s) sz b) as [ms|] eqn:Es.
    + destruct (state_rel_mem_store_byte ls ctxt _ _ sz b ms (conj Hr' Es)) as (mt & Et & Hrt).
      cbn [memory memaddrs be set_memory] in Et. rewrite Et.
      replace (set_memory ms s) with (set_memory ms (set_memory (write_bytearray (sz + n2w 1)%w nbw (memory s) (memaddrs s) (be s)) s))
        by (destruct s; reflexivity).
      replace (set_memory mt t) with (set_memory mt (set_memory (write_bytearray (sz + n2w 1)%w nbw (memory t) (memaddrs t) (be t)) t))
        by (destruct t; reflexivity).
      exact Hrt.
    + exfalso. unfold mem_store_byte in Es. destruct (write_bytearray _ _ _ _ _ (byte_align sz)).
      destruct (classical_dec _); [discriminate|contradiction].
Qed.

End RelProps.

(** ** Fresh variables *)

Section Fresh.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma eval_locals_agree s (e : exp a) L :
  (forall x, In x (var_exp e) -> FLOOKUP L x = FLOOKUP (locals s) x) ->
  eval (set_locals L s) e = eval s e.
Proof.
  induction e using exp_nested_ind; cbn [eval var_exp]; intros Hn;
    repeat match goal with IH : (forall x, In x (var_exp ?e) -> _) -> eval _ ?e = eval s ?e |- _ =>
             rewrite IH by (intros x Hx; apply Hn; rewrite ?in_app_iff; tauto); clear IH end;
    try reflexivity.
  all: try (destruct vk; [|reflexivity]; state_cbn; apply Hn; cbn; left; reflexivity).
  all: match goal with IH : Forall _ ?l |- context [OPT_MMAP ?f ?l] =>
      erewrite (OPT_MMAP_ext_In f _ l); [reflexivity|]
    end.
  all: intros x Hx; rewrite Forall_forall in *.
  all: match goal with IH : forall x, In x _ -> _ |- _ => apply IH end; [exact Hx|];
    intros y Hy; apply Hn, In_FLAT_MAP; eauto.
Qed.

Lemma OPT_MMAP_eval_locals_agree s (es : list (exp a)) L :
  (forall x, In x (FLAT (MAP var_exp es)) -> FLOOKUP L x = FLOOKUP (locals s) x) ->
  OPT_MMAP (eval (set_locals L s)) es = OPT_MMAP (eval s) es.
Proof.
  intros H. apply OPT_MMAP_ext_In. intros e He. apply eval_locals_agree.
  intros x Hx. apply H, In_FLAT_MAP. eauto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_shape_val_NONE" *)
Theorem eval_shape_val_NONE : forall (t : state a ffi_t),
  (forall sh, eval t (shape_val sh) = NONE <-> False) /\
  (forall shs, OPT_MMAP (eval t) (shape_vals shs) = NONE <-> False).
Proof.
  intros t. assert (G : forall sh, exists x, eval t (shape_val sh) = SOME x).
  { intros sh; induction sh as [| l Hl | nm] using shape_nested_ind.
    - eexists; reflexivity.
    - rewrite shape_val_Comb. cbn [eval].
      assert (E : exists xs, OPT_MMAP (eval t) (shape_vals l) = SOME xs).
      { induction Hl as [|x xs [y Hy] _ [ys Hys]]; [eexists; reflexivity|].
        cbn [shape_vals OPT_MMAP]. rewrite Hy, Hys. eexists; reflexivity. }
      destruct E as [xs ->]. eexists; reflexivity.
    - eexists; reflexivity. }
  split.
  - intros sh. destruct (G sh) as [x ->]. split; [discriminate|intros []].
  - intros shs. induction shs as [|sh shs IH]; cbn [shape_vals OPT_MMAP]; [split; [discriminate|intros []]|].
    destruct (G sh) as [x ->]. cbn. destruct (OPT_MMAP (eval t) (shape_vals shs)); cbn;
      [split; [discriminate|intros []]|exact IH].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_shape_val_thm" *)
Theorem eval_shape_val_thm : forall (t : state a ffi_t),
  (forall sh v0, eval t (shape_val sh) = SOME v0 /\ is_true (is_wf_shape_nil sh) -> sh = shape_of v0) /\
  (forall shs vs, OPT_MMAP (eval t) (shape_vals shs) = SOME vs /\
     is_true (EVERY is_wf_shape_nil shs) -> shs = MAP shape_of vs).
Proof.
  intros t. assert (G : forall sh v0, eval t (shape_val sh) = SOME v0 -> is_true (is_wf_shape_nil sh) ->
                          sh = shape_of v0).
  { intros sh; induction sh as [| l Hl | nm] using shape_nested_ind; intros v0 H Hw.
    - injection H as <-; reflexivity.
    - rewrite shape_val_Comb in H. cbn [eval] in H.
      destruct (OPT_MMAP (eval t) (shape_vals l)) as [xs|] eqn:E; [|discriminate]. injection H as <-.
      cbn [shape_of]. f_equal. apply wf_nil_Comb in Hw. clear -Hl Hw E. revert xs E.
      induction Hl as [|x xs Hx Hxs IH]; intros ys E; cbn [shape_vals OPT_MMAP] in E.
      + injection E as <-; reflexivity.
      + destruct (eval t (shape_val x)) as [y|] eqn:Ey; [|discriminate]. cbn in E.
        destruct (OPT_MMAP (eval t) (shape_vals xs)) as [zs|] eqn:Ez; [|discriminate]. cbn in E.
        injection E as <-. inversion Hw as [|? ? Hw1 Hw2]; subst. cbn [MAP List.map].
        rewrite <- (Hx y eq_refl Hw1), <- (IH Hw2 zs eq_refl). reflexivity.
    - discriminate. }
  split.
  - intros sh v0 [H Hw]; exact (G sh v0 H Hw).
  - intros shs vs [H Hw]. pose proof (G (Comb shs) (RStruct vs)) as Gc.
    rewrite shape_val_Comb in Gc. cbn [eval] in Gc. rewrite H in Gc.
    specialize (Gc eq_refl Hw). injection Gc as Gc. exact Gc.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct" *)
Theorem fresh_name_correct : forall name names, is_true (MEM (fresh_name name names) names) -> False.
Proof.
  intros name names.
  remember (N.to_nat (1 + max_strlen names - strlen name)) as m eqn:Hm. revert name Hm.
  induction m as [m IH] using (well_founded_induction lt_wf). intros name Hm.
  rewrite fresh_name_def. destruct (MEM name names) eqn:E.
  - apply MEM_strlen_le in E. apply (IH (N.to_nat (1 + max_strlen names - strlen (strcat name (strlit "'")))));
      [|reflexivity]. rewrite strlen_strcat. cbn [strlen LENGTH]. lia.
  - rewrite E. discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct'" *)
Theorem fresh_name_correct' : forall name names names',
  is_true (MEM (fresh_name name names) names') -> set names' SUBSET set names -> False.
Proof.
  intros name names names' H Hs. apply (fresh_name_correct name names).
  apply MEM_set. apply Hs. apply MEM_set, H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "res_var_FEMPTY" *)
Theorem res_var_FEMPTY : forall n, res_var (FEMPTY : fmap varname (v a)) (n, NONE) = FEMPTY.
Proof. intros n; apply fmap_ext; intros k. rewrite FLOOKUP_pan_res_var_thm. destruct (decide _); reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "OPT_MMAP_eval_fresh_var" *)
Theorem OPT_MMAP_eval_fresh_var : forall s (es : list (exp a)) n w,
  ~ is_true (MEM n (FLAT (MAP var_exp es))) ->
  OPT_MMAP (eval (set_locals (locals s |+ (n, w)) s)) es = OPT_MMAP (eval s) es.
Proof.
  intros s es n w H. apply OPT_MMAP_eval_locals_agree. intros x Hx. rewrite FLOOKUP_UPDATE.
  destruct (decide (n = x)) as [->|]; [|reflexivity]. exfalso; apply H, MEM_In, Hx.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "OPT_MMAP_eval_two_fresh_vars" *)
Theorem OPT_MMAP_eval_two_fresh_vars : forall s (es : list (exp a)) n1 w1 n2 w2,
  ~ is_true (MEM n1 (FLAT (MAP var_exp es))) /\ ~ is_true (MEM n2 (FLAT (MAP var_exp es))) ->
  OPT_MMAP (eval (set_locals (locals s |+ (n1, w1) |+ (n2, w2)) s)) es = OPT_MMAP (eval s) es.
Proof.
  intros s es n1 w1 n2 w2 [H1 H2].
  transitivity (OPT_MMAP (eval (set_locals (locals s |+ (n1, w1)) s)) es).
  - exact (OPT_MMAP_eval_fresh_var (set_locals (locals s |+ (n1, w1)) s) es n2 w2 H2).
  - exact (OPT_MMAP_eval_fresh_var s es n1 w1 H1).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "v_neq_v'" *)
Theorem v_neq_v' : forall v0 : mlstring, v0 <> strcat v0 (strlit "'").
Proof.
  intros v0 H. apply (f_equal strlen) in H. rewrite strlen_strcat in H. cbn [strlen LENGTH] in H. lia.
Qed.

End Fresh.

Section FreshEval.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma sim_locals (X Y : state a ffi_t) :
  globals X = globals Y -> structs X = structs Y -> code X = code Y -> eshapes X = eshapes Y ->
  memory X = memory Y -> memaddrs X = memaddrs Y -> sh_memaddrs X = sh_memaddrs Y ->
  clock X = clock Y -> be X = be Y -> ffi X = ffi Y -> base_addr X = base_addr Y ->
  top_addr X = top_addr Y -> X = set_locals (locals X) Y.
Proof. destruct X, Y; cbn; intros; subst; reflexivity. Qed.


Lemma FLOOKUP_res_var_other (m : fmap varname (v a)) z o x : x <> z -> FLOOKUP (res_var m (z, o)) x = FLOOKUP m x.
Proof. intros H. rewrite FLOOKUP_pan_res_var_thm. destruct (decide (x = z)); [contradiction|reflexivity]. Qed.

Lemma FLOOKUP_res_var_same (m : fmap varname (v a)) z o : FLOOKUP (res_var m (z, o)) z = o.
Proof. rewrite FLOOKUP_pan_res_var_thm. destruct (decide (z = z)) as [|C]; [reflexivity|exfalso; apply C; reflexivity]. Qed.

Lemma res_var_upd_comm (m : fmap varname (v a)) z o x w :
  x <> z -> res_var (m |+ (x, w)) (z, o) = res_var m (z, o) |+ (x, w).
Proof.
  intros H. apply fmap_ext; intros k. rewrite FLOOKUP_UPDATE, !FLOOKUP_pan_res_var_thm, FLOOKUP_UPDATE.
  destruct (decide (k = z)), (decide (x = k)); subst; try reflexivity. contradiction.
Qed.

Lemma res_var_res_var_comm (m : fmap varname (v a)) z o x o' :
  x <> z -> res_var (res_var m (x, o')) (z, o) = res_var (res_var m (z, o)) (x, o').
Proof.
  intros H. apply fmap_ext; intros k. rewrite !FLOOKUP_pan_res_var_thm.
  destruct (decide (k = z)), (decide (k = x)); subst; try reflexivity. contradiction.
Qed.

Lemma res_var_upd_same (m : fmap varname (v a)) z o w : res_var m (z, o) |+ (z, w) = m |+ (z, w).
Proof.
  apply fmap_ext; intros k. rewrite !FLOOKUP_UPDATE, FLOOKUP_pan_res_var_thm.
  destruct (decide (z = k)), (decide (k = z)); subst; try reflexivity. contradiction.
Qed.

Lemma res_var_res_var_same (m : fmap varname (v a)) z o1 o2 : res_var (res_var m (z, o1)) (z, o2) = res_var m (z, o2).
Proof. apply fmap_ext; intros k. rewrite !FLOOKUP_pan_res_var_thm. destruct (decide (k = z)); reflexivity. Qed.

Lemma res_var_self (m : fmap varname (v a)) z : res_var m (z, FLOOKUP m z) = m.
Proof. apply fmap_ext; intros k. rewrite FLOOKUP_pan_res_var_thm. destruct (decide (k = z)); subst; reflexivity. Qed.

Lemma not_in_app_iff {A} (x : A) l1 l2 : ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof. rewrite in_app_iff. tauto. Qed.

Ltac ex_loc := match goal with |- exists L, (_, ?X) = (_, set_locals L ?Y) /\ _ =>
  exists (locals X); split; [f_equal; apply sim_locals; reflexivity|] end.
Ltac errc' := ex_loc; intros _ C; exfalso; apply C; reflexivity.
Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.
Ltac errc := match goal with H : (_, _) = (_, _) |- _ => injp H end; errc'.

Lemma not_or' {P Q : Prop} : ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof. tauto. Qed.

Ltac nin_split :=
  repeat match goal with
  | H : ~ (_ \/ _) |- _ => apply not_or' in H as [? ?]
  | H : ~ In _ (_ ++ _) |- _ => apply not_in_app_iff in H as [? ?]
  | H : ~ In _ (_ :: _) |- _ => apply not_in_cons in H as [? ?]
  end.

Lemma In_FILTER_ne (z vn : varname) l :
  z <> vn -> ~ In z (FILTER (fun x => bool_decide (vn <> x)) l) -> ~ In z l.
Proof.
  intros Hne H Hin. apply H, filter_In. split; [exact Hin|]. apply bool_decide_spec. intros ->; apply Hne; reflexivity.
Qed.

Lemma ivv_sz (s : state a ffi_t) z o vk x v0 :
  (vk = Local -> x <> z) ->
  is_valid_value (set_locals (res_var (locals s) (z, o)) s) vk x v0 = is_valid_value s vk x v0.
Proof.
  intros H. unfold is_valid_value. destruct vk; [|reflexivity]. cbn [lookup_kvar locals set_locals].
  rewrite FLOOKUP_res_var_other by (intros ->; apply (H eq_refl); reflexivity). reflexivity.
Qed.

Lemma lookup_kvar_sz (s : state a ffi_t) z o vk x :
  (vk = Local -> x <> z) ->
  lookup_kvar vk x (set_locals (res_var (locals s) (z, o)) s) = lookup_kvar vk x s.
Proof.
  intros H. destruct vk; [|reflexivity]. cbn [lookup_kvar locals set_locals].
  apply FLOOKUP_res_var_other. intros ->; apply (H eq_refl); reflexivity.
Qed.

Lemma set_locals_set_locals X Y (s : state a ffi_t) : set_locals X (set_locals Y s) = set_locals X s.
Proof. reflexivity. Qed.


End FreshEval.

Section FreshEval2.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma not_or'' {P Q : Prop} : ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof. tauto. Qed.

Ltac nin_split :=
  repeat match goal with
  | H : ~ (_ \/ _) |- _ => apply not_or'' in H as [? ?]
  | H : ~ In _ (_ ++ _) |- _ => apply not_in_app_iff in H as [? ?]
  | H : ~ In _ (_ :: _) |- _ => apply not_in_cons in H as [? ?]
  end.

Lemma sl_dec_clock n L s : set_locals n (dec_clock (set_locals L s)) = set_locals n (dec_clock s).
Proof. reflexivity. Qed.
Lemma sl_dec_clock' L s : dec_clock (set_locals L s) = set_locals L (dec_clock s).
Proof. reflexivity. Qed.
Lemma locals_dec_clock s : locals (dec_clock s) = locals s.
Proof. reflexivity. Qed.
Lemma locals_sl L s : locals (set_locals L s) = L. Proof. reflexivity. Qed.
Lemma globals_sl L s : globals (set_locals L s) = globals s. Proof. reflexivity. Qed.
Lemma structs_sl L s : structs (set_locals L s) = structs s. Proof. reflexivity. Qed.
Lemma code_sl L s : code (set_locals L s) = code s. Proof. reflexivity. Qed.
Lemma eshapes_sl L s : eshapes (set_locals L s) = eshapes s. Proof. reflexivity. Qed.
Lemma memory_sl L s : memory (set_locals L s) = memory s. Proof. reflexivity. Qed.
Lemma memaddrs_sl L s : memaddrs (set_locals L s) = memaddrs s. Proof. reflexivity. Qed.
Lemma sh_memaddrs_sl L s : sh_memaddrs (set_locals L s) = sh_memaddrs s. Proof. reflexivity. Qed.
Lemma clock_sl L s : clock (set_locals L s) = clock s. Proof. reflexivity. Qed.
Lemma be_sl L s : be (set_locals L s) = be s. Proof. reflexivity. Qed.
Lemma ffi_sl L s : ffi (set_locals L s) = ffi s. Proof. reflexivity. Qed.
Lemma base_addr_sl L s : base_addr (set_locals L s) = base_addr s. Proof. reflexivity. Qed.
Lemma top_addr_sl L s : top_addr (set_locals L s) = top_addr s. Proof. reflexivity. Qed.

Ltac sl_proj := rewrite ?locals_sl, ?globals_sl, ?structs_sl, ?code_sl, ?eshapes_sl, ?memory_sl,
  ?memaddrs_sl, ?sh_memaddrs_sl, ?clock_sl, ?be_sl, ?ffi_sl, ?base_addr_sl, ?top_addr_sl.

Lemma sv_sz evar exn R0 (st : state a ffi_t) z o : evar <> z ->
  set_var evar exn (set_locals (res_var R0 (z, o)) st) =
  set_locals (res_var (locals (set_var evar exn (set_locals R0 st))) (z, o)) (set_var evar exn (set_locals R0 st)).
Proof. intros H. unfold set_var. rewrite !locals_sl, res_var_upd_comm by exact H. reflexivity. Qed.

Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.

Ltac sz_rw Hez Hesz :=
  repeat first
    [ match goal with |- context [eval (set_locals (res_var (locals ?s) (?z, ?o)) ?s) ?e] =>
        rewrite (Hez e) by assumption end
    | match goal with |- context [OPT_MMAP (eval (set_locals (res_var (locals ?s) (?z, ?o)) ?s)) ?es] =>
        rewrite (Hesz es) by assumption end ].

Ltac neqz := intros ?C ?Heq; first [discriminate C | congruence].

Ltac kv_rw :=
  repeat first
    [ rewrite ivv_sz by neqz
    | rewrite lookup_kvar_sz by neqz ].

Ltac leaf_ex :=
  first [ eexists; split; [reflexivity|]
        | match goal with |- exists L, (_, ?X) = (_, set_locals L ?Y) /\ _ =>
            exists (locals X); split; [f_equal; apply sim_locals; reflexivity|] end ].

Ltac leaf_fin :=
  leaf_ex;
  intros ?Hg ?Hne; cbn [good_res is_true] in *;
  first [ discriminate
        | exfalso; match goal with Hn : SOME Error <> SOME Error |- _ => apply Hn; reflexivity end
        | cbn [locals set_locals set_memory set_ffi set_globals set_global set_kvar set_var empty_locals dec_clock set_clock];
          first [ reflexivity
                | symmetry; apply res_var_upd_comm; congruence ] ].

Ltac dec_hz Hz :=
  repeat match type of Hz with context [decide ?P] =>
    destruct (decide P); [try discriminate | try congruence] end.

Ltac simple_case H Hz Hez Hesz :=
  cbn [evaluate_body free_var_ids] in H, Hz |- *; dec_hz Hz; nin_split;
  unfold sh_mem_load, sh_mem_store in H |- *;
  sz_rw Hez Hesz; sl_proj; kv_rw;
  split_all H; try injp H; repeat first [goal_scrut | progress kv_rw | progress sl_proj]; leaf_fin.

Ltac ih_apply IH H z o :=
  match type of H with evaluate (?p, ?s1) = (?r, ?t) =>
    let L := fresh "L" in let F := fresh "F" in let HL := fresh "HL" in
    destruct (IH (p, s1) ltac:(prove_lt) r t z o ltac:(assumption) H) as (L & F & HL);
    exists L; split; [exact F|exact HL] end.

Ltac split_nonrec2 H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | fix_clock _ _ => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H |- *
      end
  end.

Ltac goodres HL := intros ?Hg ?Hn; apply HL; [first [assumption | reflexivity] | first [assumption | discriminate]].

Lemma ev_fresh : forall (x : prog a * state a ffi_t) res s' z o,
  ~ In z (free_var_ids (fst x)) -> evaluate x = (res, s') ->
  exists L, evaluate (fst x, set_locals (res_var (locals (snd x)) (z, o)) (snd x)) = (res, set_locals L s') /\
    (is_true (good_res res) -> res <> SOME Error -> L = res_var (locals s') (z, o)).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res s' z o Hz H. cbn [fst snd] in *.
  assert (Hez : forall e, ~ In z (var_exp e) -> eval (set_locals (res_var (locals s) (z, o)) s) e = eval s e).
  { intros e He. apply eval_locals_agree. intros y Hy. apply FLOOKUP_res_var_other. intros ->; contradiction. }
  assert (Hesz : forall es, ~ In z (FLAT (MAP var_exp es)) ->
            OPT_MMAP (eval (set_locals (res_var (locals s) (z, o)) s)) es = OPT_MMAP (eval s) es).
  { intros es He. apply OPT_MMAP_eval_locals_agree. intros y Hy. apply FLOOKUP_res_var_other. intros ->; contradiction. }
  pose proof Hz as Hz0.
  rewrite evaluate_unfold in H |- *.
  destruct p as [|vn sh e p|vk vn e|vn pop es|e1 e2|e1 e2|e1 e2|p1 p2|e p1 p2|e p| | |ct f args
                 |vn sh f args p|f e1 e2 e3 e4|eid e|e|op vk vn e|op e1 e2| |m1 m2].
  - (* Skip *) simple_case H Hz Hez Hesz.
  - (* Dec *)
    cbn [evaluate_body free_var_ids] in H, Hz |- *. apply not_in_app_iff in Hz as [Hze Hzp].
    rewrite (Hez e Hze), locals_sl.
    destruct (eval s e) as [value|] eqn:Ee; cbn beta iota zeta in H |- *; [|injp H; leaf_fin].
    destruct (bool_decide (sh = shape_of value)) eqn:Eb; cbn beta iota zeta in H |- *; [|injp H; leaf_fin].
    rewrite set_locals_set_locals.
    destruct (decide (vn = z)) as [->|Hne].
    + rewrite res_var_upd_same, FLOOKUP_res_var_same.
      destruct (evaluate (p, set_locals (locals s |+ (z, value)) s)) as [r st] eqn:Ep.
      injp H. exists (res_var (locals st) (z, o)). split; [reflexivity|].
      intros _ _. rewrite locals_sl, res_var_res_var_same. reflexivity.
    + assert (Hzp' : ~ In z (free_var_ids p)) by (apply (In_FILTER_ne z vn); [congruence|exact Hzp]).
      rewrite <- res_var_upd_comm by exact Hne. rewrite FLOOKUP_res_var_other by exact Hne.
      change (set_locals (res_var (locals s |+ (vn, value)) (z, o)) s) with
        (set_locals (res_var (locals (set_locals (locals s |+ (vn, value)) s)) (z, o)) (set_locals (locals s |+ (vn, value)) s)).
      destruct (evaluate (p, set_locals (locals s |+ (vn, value)) s)) as [r st] eqn:Ep.
      destruct (IH (p, set_locals (locals s |+ (vn, value)) s) ltac:(prove_lt) r st z o Hzp' Ep) as (L1 & F1 & HL1).
      cbn [fst snd] in F1. rewrite F1. cbn beta iota zeta.
      injp H. exists (res_var L1 (vn, FLOOKUP (locals s) vn)). split; [reflexivity|].
      intros Hg Hn. rewrite (HL1 Hg Hn), locals_sl. symmetry; apply res_var_res_var_comm; exact Hne.
  - (* Assign *) destruct vk; simple_case H Hz Hez Hesz.
  - (* Primitive *) simple_case H Hz Hez Hesz.
  - (* Store *) simple_case H Hz Hez Hesz.
  - (* Store32 *) simple_case H Hz Hez Hesz.
  - (* StoreByte *) simple_case H Hz Hez Hesz.
  - (* Seq *)
    cbn [evaluate_body free_var_ids] in H, Hz |- *. apply not_in_app_iff in Hz as [Hz1 Hz2].
    rewrite fix_clock_evaluate in H |- *.
    destruct (evaluate (p1, s)) as [r1 s1] eqn:Ec1.
    destruct (IH (p1, s) ltac:(prove_lt) r1 s1 z o Hz1 Ec1) as (L1 & F1 & HL1). cbn [fst snd] in F1. rewrite F1.
    cbn beta iota zeta in H |- *.
    destruct r1 as [r1|]; cbn beta iota zeta in H |- *.
    + injp H. exists L1. split; [reflexivity|exact HL1].
    + rewrite (HL1 eq_refl ltac:(discriminate)). ih_apply IH H z o.
  - (* If *)
    cbn [evaluate_body free_var_ids] in H, Hz |- *. nin_split.
    sz_rw Hez Hesz. repeat split_nonrec H.
    all: first [injp H; leaf_fin | ih_apply IH H z o].
  - (* While *)
    cbn [evaluate_body free_var_ids] in H, Hz |- *. nin_split.
    sz_rw Hez Hesz. sl_proj. rewrite fix_clock_evaluate in H. rewrite sl_dec_clock', fix_clock_evaluate.
    repeat split_nonrec H.
    all: try (injp H; leaf_fin).
    destruct (evaluate (p, dec_clock s)) as [r1 s1] eqn:Ec1.
    destruct (IH (p, dec_clock s) ltac:(prove_lt) r1 s1 z o ltac:(assumption) Ec1) as (L1 & F1 & HL1).
    cbn [fst snd] in F1. rewrite locals_dec_clock in F1. rewrite F1.
    cbn beta iota zeta in H |- *.
    destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota zeta in H |- *.
    all: try (injp H; exists L1; split; [reflexivity|goodres HL1]).
    all: rewrite (HL1 eq_refl ltac:(discriminate)); ih_apply IH H z o.
  - (* Break *) simple_case H Hz Hez Hesz.
  - (* Continue *) simple_case H Hz Hez Hesz.
  - (* Call *)
    destruct ct as [[[[[|] rt]|] [[eid' [evar hp]]|]]|];
      cbn [evaluate_body free_var_ids] in H, Hz |- *; dec_hz Hz; cbn [app] in Hz; nin_split.
    all: sz_rw Hez Hesz; sl_proj.
    all: repeat split_nonrec2 H.
    all: try (injp H; leaf_fin).
    all: rewrite sl_dec_clock, fix_clock_evaluate; rewrite fix_clock_evaluate in H.
    all: destruct (evaluate (_, set_locals _ (dec_clock s))) as [r1 st] eqn:Ec1; cbn beta iota zeta in H |- *.
    all: destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota zeta in H |- *.
    all: kv_rw; sl_proj; repeat split_nonrec H.
    all: try (injp H; leaf_fin).
    all: rewrite sv_sz by congruence; ih_apply IH H z o.
  - (* DecCall *)
    cbn [evaluate_body free_var_ids] in H, Hz |- *; nin_split.
    sz_rw Hez Hesz; sl_proj.
    repeat split_nonrec2 H.
    all: try (injp H; leaf_fin).
    all: rewrite sl_dec_clock, fix_clock_evaluate; rewrite fix_clock_evaluate in H.
    all: destruct (evaluate (_, set_locals _ (dec_clock s))) as [r1 st] eqn:Ec1; cbn beta iota zeta in H |- *.
    all: destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota zeta in H |- *.
    all: try (injp H; leaf_fin).
    repeat split_nonrec2 H.
    all: try (injp H; leaf_fin).
    rewrite sv_sz by congruence. rewrite FLOOKUP_res_var_other by congruence.
    destruct (evaluate (p, set_var vn retv (set_locals (locals s) st))) as [r2 st2] eqn:Ec2.
    destruct (IH (p, set_var vn retv (set_locals (locals s) st)) ltac:(prove_lt) r2 st2 z o ltac:(assumption) Ec2)
      as (L2 & F2 & HL2).
    cbn [fst snd] in F2. rewrite F2. cbn beta iota zeta in H |- *.
    injp H. exists (res_var L2 (vn, FLOOKUP (locals s) vn)). split; [reflexivity|].
    intros Hg Hn. rewrite (HL2 Hg Hn), locals_sl. symmetry; apply res_var_res_var_comm; congruence.
  - (* ExtCall *) simple_case H Hz Hez Hesz.
  - (* Raise *) simple_case H Hz Hez Hesz.
  - (* Return *) simple_case H Hz Hez Hesz.
  - (* ShMemLoad *) destruct vk; simple_case H Hz Hez Hesz.
  - (* ShMemStore *) simple_case H Hz Hez Hesz.
  - (* Tick *) simple_case H Hz Hez Hesz.
  - (* Annot *) simple_case H Hz Hez Hesz.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fresh_local" *)
Theorem evaluate_fresh_local : forall z v0 (p : prog a) (s : state a ffi_t) res s',
  ~ is_true (MEM z (free_var_ids p)) /\ evaluate (p, s) = (res, s') ->
  exists locals0,
    evaluate (p, set_locals (locals s |+ (z, v0)) s) = (res, set_locals locals0 s') /\
    (is_true (good_res res) /\ res <> SOME Error -> locals0 = locals s' |+ (z, v0)).
Proof.
  intros z v0 p s res s' [Hz H]. rewrite MEM_is_true_In in Hz.
  destruct (ev_fresh (p, s) res s' z (SOME v0) Hz H) as (L & E & HL).
  exists L. split; [exact E|]. intros [Hg Hn]. exact (HL Hg Hn).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_two_fresh_locals" *)
Theorem evaluate_two_fresh_locals : forall z1 v1 z2 v2 (p : prog a) (s : state a ffi_t) res s',
  ~ is_true (MEM z1 (free_var_ids p)) /\ ~ is_true (MEM z2 (free_var_ids p)) /\ evaluate (p, s) = (res, s') ->
  exists locals0,
    evaluate (p, set_locals (locals s |+ (z1, v1) |+ (z2, v2)) s) = (res, set_locals locals0 s') /\
    (is_true (good_res res) /\ res <> SOME Error -> locals0 = locals s' |+ (z1, v1) |+ (z2, v2)).
Proof.
  intros z1 v1 z2 v2 p s res s' (H1 & H2 & H).
  destruct (evaluate_fresh_local z1 v1 p s res s' (conj H1 H)) as (L1 & E1 & HL1).
  destruct (evaluate_fresh_local z2 v2 p _ res _ (conj H2 E1)) as (L2 & E2 & HL2).
  exists L2. split; [exact E2|]. intros Hg. rewrite (HL2 Hg), (HL1 Hg). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_unchanged_local" *)
Theorem evaluate_unchanged_local : forall z (v0 : v a) (p : prog a) (s : state a ffi_t) res s',
  ~ is_true (MEM z (free_var_ids p)) /\ evaluate (p, s) = (res, s') /\ is_true (good_res res) /\
  res <> SOME Error ->
  FLOOKUP (locals s') z = FLOOKUP (locals s) z.
Proof.
  intros z v0 p s res s' (Hz & H & Hg & Hn). rewrite MEM_is_true_In in Hz.
  destruct (ev_fresh (p, s) res s' z (FLOOKUP (locals s) z) Hz H) as (L & E & HL).
  cbn [fst snd] in E. rewrite res_var_self in E.
  replace (set_locals (locals s) s) with s in E by (destruct s; reflexivity).
  rewrite H in E. injection E as E. rewrite (HL Hg Hn) in E.
  apply (f_equal locals) in E. cbn [locals set_locals] in E.
  rewrite E at 1. apply FLOOKUP_res_var_same.
Qed.

End FreshEval2.

Section CompileCorrect.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Local Open Scope word_scope.

Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.

Definition gc_P (p : prog a) s : Prop :=
  forall res ctxt t s', state_rel true ctxt s t -> evaluate (p, s) = (res, s') -> res <> SOME Error ->
  exists t', evaluate (compile ctxt p, t) = (res, t') /\ state_rel (good_res res) ctxt s' t'.

Ltac gc_intro := intros ?res ?ctxt ?t ?s' ?Hr ?H ?Hne.
Ltac sstep H := rewrite evaluate_unfold in H; cbn [evaluate_body] in H; rewrite ?fix_clock_evaluate in H.
Ltac tstep := rewrite evaluate_unfold; cbn [evaluate_body]; rewrite ?fix_clock_evaluate.
Ltac err H := injp H; exfalso; match goal with Hn : SOME Error <> SOME Error |- _ => apply Hn; reflexivity end.

Lemma sr_locals ctxt s t : state_rel true ctxt s t -> locals s = locals t.
Proof. intros (_ & H & _). exact (H eq_refl). Qed.
Lemma sr_clock ls ctxt s t : state_rel ls ctxt s t -> clock s = clock t.
Proof. intros (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma sr_eshapes ls ctxt s t : state_rel ls ctxt s t -> eshapes s = eshapes t.
Proof. intros (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma sr_be ls ctxt s t : state_rel ls ctxt s t -> be s = be t.
Proof. intros (_ & _ & _ & H & _). exact H. Qed.
Lemma sr_structs ls ctxt s t : state_rel ls ctxt s t -> structs s = [] /\ structs t = [].
Proof. intros (_ & _ & _ & _ & _ & _ & H1 & H2 & _). split; assumption. Qed.
Lemma sr_ffi ls ctxt s t : state_rel ls ctxt s t -> ffi s = ffi t.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma sr_sh_memaddrs ls ctxt s t : state_rel ls ctxt s t -> sh_memaddrs s = sh_memaddrs t.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ivv_local_rel ctxt s t vn x :
  state_rel true ctxt s t -> is_valid_value t Local vn x = is_valid_value s Local vn x.
Proof. intros Hr. unfold is_valid_value, lookup_kvar. rewrite (sr_locals _ _ _ Hr). reflexivity. Qed.

Lemma byte_aligned_sub (x y : word a) :
  is_true (byte_aligned x) -> is_true (byte_aligned y) -> is_true (byte_aligned (x - y)).
Proof. intros Hx Hy. unfold byte_aligned in *. apply (aligned_add_sub_cor _ x y). split; assumption. Qed.

Lemma sr_store_global ls ctxt s t vn w value addr :
  state_rel ls ctxt s t -> FLOOKUP (globals s) vn = SOME w -> shape_of value = shape_of w ->
  FLOOKUP (pan_globals.globals ctxt) vn = SOME (shape_of w, addr) ->
  exists m, mem_stores (top_addr t - addr) (flatten value) (memaddrs t) (memory t) = SOME m /\
    state_rel ls ctxt (set_global vn value s) (set_memory m t).
Proof.
  intros Hr Hw Hsh Hc. pose proof Hr as Hr0.
  destruct Hr as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  destruct (H9 vn w Hw) as (addr0 & A1 & A2 & A3 & A4 & A5).
  rewrite Hc in A1. injection A1 as <-.
  destruct (proj1 mem_load_mem_store (shape_of w) _ _ _ [] w value (conj A3 (conj eq_refl (conj A2 Hsh))))
    as [m Hm].
  assert (Hal : is_true (byte_aligned (top_addr t - addr))) by (apply byte_aligned_sub; assumption).
  pose proof (mem_stores_bounded_length _ _ _ _ _ (top_addr t) (conj Hm (conj H17 (conj Hal (conj H18 H19))))) as Hb.
  rewrite WORD_SUB_SUB2 in Hb. pose proof (w2n_lt addr) as Hlt.
  assert (Hwf : is_true (is_wf_shape_nil (shape_of value))) by (rewrite Hsh; exact A2).
  assert (Hlen : LENGTH (flatten value) = size_of_shape (shape_of w))
    by (rewrite <- Hsh; apply length_flatten_eq_size_of_shape, Hwf).
  exists m. split; [exact Hm|].
  unfold state_rel, set_global, set_globals, set_memory; cbn [locals globals structs code eshapes memory memaddrs
    sh_memaddrs clock be ffi base_addr top_addr].
  repeat split; try assumption.
  - intros v0 val Hv. rewrite FLOOKUP_UPDATE in Hv. destruct (decide (vn = v0)) as [<-|Hne].
    + injection Hv as <-. exists addr. rewrite Hsh. split; [exact Hc|split; [exact A2|split; [|split; assumption]]].
      rewrite <- Hsh. apply (proj1 mem_stores_mem_load_back _ _ _ (memory t) _ []).
      repeat split; try assumption. lia.
    + destruct (H9 v0 val Hv) as (addr' & B1 & B2 & B3 & B4 & B5).
      exists addr'. split; [exact B1|split; [exact B2|split; [|split; assumption]]].
      assert (Hd : DISJOINT (addresses (top_addr t - addr') (size_of_shape (shape_of val)))
                            (addresses (top_addr t - addr) (LENGTH (flatten value)))).
      { rewrite Hlen. apply (H16 v0 vn _ _ _ _).
        repeat split; [exact (fun E => Hne (eq_sym E))| | |exact B1|exact Hc]; rewrite ?Hv, ?Hw; reflexivity. }
      rewrite (proj1 mem_stores_load_disjoint _ _ _ _ _ m [] _ (conj Hm (conj eq_refl (conj B2 Hd)))). exact B3.
  - intros x Hx. rewrite (H13 x Hx). symmetry.
    assert (Hn : x NOTIN addresses (top_addr t - addr) (LENGTH (flatten value))).
    { intros Hin. rewrite Hlen in Hin. exact (proj1 (DISJOINT_ALT _ _) A4 x Hx Hin). }
    exact (mem_stores_lookup _ _ _ _ _ _ (conj Hm Hn)).
  - intros v1 v2 sh1 a1 sh2 a2 (Hn & Hs1 & Hs2 & C1 & C2). apply (H16 v1 v2 sh1 a1 sh2 a2).
    rewrite !FLOOKUP_UPDATE in Hs1, Hs2.
    repeat split; [exact Hn| | |exact C1|exact C2].
    + destruct (decide (vn = v1)) as [<-|]; [rewrite Hw; reflexivity|exact Hs1].
    + destruct (decide (vn = v2)) as [<-|]; [rewrite Hw; reflexivity|exact Hs2].
Qed.


Lemma sr_global_lookup ls ctxt s t vn w : state_rel ls ctxt s t -> FLOOKUP (globals s) vn = SOME w ->
  exists addr, FLOOKUP (pan_globals.globals ctxt) vn = SOME (shape_of w, addr).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & H9 & _) Hw. destruct (H9 _ _ Hw) as (addr & A1 & _). exists addr; exact A1.
Qed.

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.

Lemma sr_mem_stores ctxt : forall ws addr s t m, state_rel true ctxt s t ->
  mem_stores addr ws (memaddrs s) (memory s) = SOME m ->
  exists m', mem_stores addr ws (memaddrs t) (memory t) = SOME m' /\
    state_rel true ctxt (set_memory m s) (set_memory m' t).
Proof.
  induction ws as [|w ws IH]; intros addr s t m Hr H; cbn [mem_stores] in H |- *.
  - injection H as <-. exists (memory t). split; [reflexivity|].
    replace (set_memory (memory s) s) with s by (destruct s; reflexivity).
    replace (set_memory (memory t) t) with t by (destruct t; reflexivity). exact Hr.
  - unfold mem_store in H |- *. destruct (classical_dec (addr IN memaddrs s)) as [Hi|]; [|discriminate].
    pose proof Hr as Hc. destruct Hc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsub & _).
    destruct (classical_dec (addr IN memaddrs t)) as [Hi'|Hn]; [|exfalso; apply Hn, Hsub, Hi].
    pose proof (state_rel_memory_update ctxt s t addr w (conj Hr Hi)) as Hr'.
    destruct (IH (addr + bytes_in_word) _ _ m Hr' H) as (m' & Hm' & Hr2).
    exists m'. split; [exact Hm'|exact Hr2].
Qed.

Lemma sr_mem_store_32 ls ctxt s t adr hw m :
  state_rel ls ctxt s t -> mem_store_32 (memory s) (memaddrs s) (be s) adr hw = SOME m ->
  exists m', mem_store_32 (memory t) (memaddrs t) (be t) adr hw = SOME m' /\
    state_rel ls ctxt (set_memory m s) (set_memory m' t).
Proof.
  intros Hr H. pose proof Hr as Hc.
  destruct Hc as (_ & _ & _ & Hbe & _ & _ & _ & _ & _ & _ & Hsub & _ & Hmem & _).
  unfold mem_store_32 in *. destruct (aligned 2 adr); [|discriminate].
  destruct (memory s (byte_align adr)) as [w] eqn:Em.
  destruct (classical_dec (byte_align adr IN memaddrs s)) as [Hi|]; [|discriminate].
  injection H as <-. rewrite <- (Hmem _ Hi), Em, <- Hbe.
  destruct (classical_dec (byte_align adr IN memaddrs t)) as [|Hn]; [|exfalso; apply Hn, Hsub, Hi].
  eexists; split; [reflexivity|]. exact (sr_memory_update _ _ _ _ _ _ Hr Hi).
Qed.

Lemma sh_mem_load_rel vk vk' r r' addr nb s (T : state a ffi_t) :
  sh_memaddrs T = sh_memaddrs s -> ffi T = ffi s ->
  (exists f, sh_mem_load vk r addr nb s = (SOME (FinalFFI f), empty_locals s) /\
             sh_mem_load vk' r' addr nb T = (SOME (FinalFFI f), empty_locals T)) \/
  (exists nf w, sh_mem_load vk r addr nb s = (NONE, set_ffi nf (set_kvar vk r (ValWord w) s)) /\
                sh_mem_load vk' r' addr nb T = (NONE, set_ffi nf (set_kvar vk' r' (ValWord w) T))) \/
  (sh_mem_load vk r addr nb s = (SOME Error, s) /\ sh_mem_load vk' r' addr nb T = (SOME Error, T)).
Proof.
  intros E1 E2. unfold sh_mem_load. rewrite E1, E2.
  destruct (nb =? 0);
    match goal with |- context [classical_dec ?P] => destruct (classical_dec P) end;
    try (right; right; split; reflexivity);
    match goal with |- context [call_FFI ?a ?b ?c ?d] => destruct (call_FFI a b c d) end;
    [right; left; do 2 eexists; split; reflexivity|left; eexists; split; reflexivity
    |right; left; do 2 eexists; split; reflexivity|left; eexists; split; reflexivity].
Qed.

Lemma sh_mem_store_rel {b} (w : word b) addr nb s (T : state a ffi_t) :
  sh_memaddrs T = sh_memaddrs s -> ffi T = ffi s ->
  (exists f, sh_mem_store w addr nb s = (SOME (FinalFFI f), s) /\ sh_mem_store w addr nb T = (SOME (FinalFFI f), T)) \/
  (exists nf, sh_mem_store w addr nb s = (NONE, set_ffi nf s) /\ sh_mem_store w addr nb T = (NONE, set_ffi nf T)) \/
  (sh_mem_store w addr nb s = (SOME Error, s) /\ sh_mem_store w addr nb T = (SOME Error, T)).
Proof.
  intros E1 E2. unfold sh_mem_store. rewrite E1, E2.
  destruct (nb =? 0);
    match goal with |- context [classical_dec ?P] => destruct (classical_dec P) end;
    try (right; right; split; reflexivity);
    match goal with |- context [call_FFI ?a ?b ?c ?d] => destruct (call_FFI a b c d) end;
    [right; left; eexists; split; reflexivity|left; eexists; split; reflexivity
    |right; left; eexists; split; reflexivity|left; eexists; split; reflexivity].
Qed.

Lemma sr_empty ls ctxt s t : state_rel ls ctxt s t -> state_rel false ctxt (empty_locals s) (empty_locals t).
Proof. destruct ls; intros Hr; [apply (proj1 (state_rel_empty_locals _ _ _ _))|apply (proj2 (state_rel_empty_locals _ _ _ _))]; exact Hr. Qed.

Lemma gc_Skip s : gc_P Skip s.
Proof. gc_intro. sstep H. injp H. cbn [compile]. exists t. split; [tstep; reflexivity|exact Hr]. Qed.

Lemma gc_Break s : gc_P panLang.Break s.
Proof. gc_intro. sstep H. injp H. cbn [compile]. exists t. split; [tstep; reflexivity|exact Hr]. Qed.

Lemma gc_Continue s : gc_P panLang.Continue s.
Proof. gc_intro. sstep H. injp H. cbn [compile]. exists t. split; [tstep; reflexivity|exact Hr]. Qed.

Lemma gc_Annot s m1 m2 : gc_P (Annot m1 m2) s.
Proof. gc_intro. sstep H. injp H. cbn [compile]. exists t. split; [tstep; reflexivity|exact Hr]. Qed.

Lemma gc_Tick s : gc_P Tick s.
Proof.
  gc_intro. sstep H. cbn [compile]. tstep. rewrite <- (sr_clock _ _ _ _ Hr).
  destruct (clock s =? 0); injp H.
  - exists (empty_locals t). split; [reflexivity|]. exact (sr_empty _ _ _ _ Hr).
  - exists (dec_clock t). split; [reflexivity|]. exact (state_rel_dec_clock _ _ _ _ Hr).
Qed.

Lemma gc_Assign s vk vn e : gc_P (Assign vk vn e) s.
Proof.
  gc_intro. sstep H. destruct (eval s e) as [value|] eqn:Ee; [|err H].
  destruct (is_valid_value s vk vn value) eqn:Ev; [|err H]. injp H.
  pose proof (compile_exp_correct s e value ctxt t (conj Hr Ee)) as Ce.
  destruct vk; cbn [compile].
  - tstep. rewrite Ce, (ivv_local_rel _ _ _ _ _ Hr), Ev. exists (set_var vn value t). split; [reflexivity|].
    exact (state_rel_set_var true ctxt s t vn value Hr).
  - unfold is_valid_value, lookup_kvar in Ev. destruct (FLOOKUP (globals s) vn) as [w|] eqn:Ew; [|discriminate].
    apply bool_decide_spec in Ev.
    destruct (sr_global_lookup _ _ _ _ _ _ Hr Ew) as [addr Hc]. rewrite Hc.
    destruct (sr_store_global _ _ _ _ _ _ _ _ Hr Ew Ev Hc) as (m & Hm & Hr').
    tstep. rewrite eval_top_sub, Ce. unfold ValWord. cbn beta iota. rewrite Hm. exists (set_memory m t). split; [reflexivity|exact Hr'].
Qed.


Lemma sr_false ls ctxt s t : state_rel ls ctxt s t -> state_rel false ctxt s t.
Proof.
  intros (H1 & H2 & H3). split; [exact H1|split; [intros C; discriminate C|exact H3]].
Qed.

Ltac ce_rw Hr :=
  repeat match goal with
  | E : eval ?s ?e = SOME ?v |- context [eval ?t (compile_exp ?ctxt ?e)] =>
      rewrite (compile_exp_correct s e v ctxt t (conj Hr E))
  | E : OPT_MMAP (eval ?s) ?es = SOME ?vs |- context [OPT_MMAP (eval ?t) (MAP (compile_exp ?ctxt) ?es)] =>
      rewrite (OPT_MMAP_eval_correct ctxt s t es vs (conj Hr E))
  end.

Lemma gc_Primitive s vn pop es : gc_P (Primitive vn pop es) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H. injp H.
  cbn [compile]. tstep. ce_rw Hr. repeat goal_scrut. rewrite (ivv_local_rel _ _ _ _ _ Hr).
  repeat goal_scrut. eexists. split; [reflexivity|]. exact (state_rel_set_var true ctxt s t _ _ Hr).
Qed.

Lemma gc_Dec s vn sh e p :
  (forall p' s', eval_lt (p', s') (Dec vn sh e p, s) -> gc_P p' s') -> gc_P (Dec vn sh e p) s.
Proof.
  intros IH. gc_intro. sstep H. destruct (eval s e) as [value|] eqn:Ee; [|err H].
  destruct (bool_decide (sh = shape_of value)) eqn:Eb; [|err H].
  destruct (evaluate (p, set_locals (locals s |+ (vn, value)) s)) as [r st] eqn:Ep. injp H.
  cbn [compile]. tstep. ce_rw Hr. rewrite Eb. cbn beta iota.
  assert (Hr1 : state_rel true ctxt (set_locals (locals s |+ (vn, value)) s) (set_locals (locals t |+ (vn, value)) t)).
  { rewrite (sr_locals _ _ _ Hr). exact (proj1 (state_rel_change_locals _ _ _ _ _) Hr). }
  destruct (IH p (set_locals (locals s |+ (vn, value)) s) ltac:(prove_lt) r ctxt _ st Hr1 Ep Hne) as (t1 & Et1 & Hr2).
  rewrite Et1. eexists. split; [reflexivity|].
  exact (state_rel_res_var (good_res r) ctxt st t1 s t vn vn (conj Hr2 Hr)).
Qed.

Lemma gc_Store s e1 e2 : gc_P (Store e1 e2) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H. injp H.
  cbn [compile]. tstep. ce_rw Hr. cbn beta iota.
  match goal with E : mem_stores _ _ _ _ = SOME _ |- _ =>
    destruct (sr_mem_stores ctxt _ _ _ _ _ Hr E) as (m' & Hm' & Hr') end.
  rewrite Hm'. eexists; split; [reflexivity|exact Hr'].
Qed.

Lemma gc_Store32 s e1 e2 : gc_P (Store32 e1 e2) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H. injp H.
  cbn [compile]. tstep. ce_rw Hr. cbn beta iota.
  match goal with E : mem_store_32 _ _ _ _ _ = SOME _ |- _ =>
    destruct (sr_mem_store_32 _ ctxt _ _ _ _ _ Hr E) as (m' & Hm' & Hr') end.
  rewrite Hm'. eexists; split; [reflexivity|exact Hr'].
Qed.

Lemma gc_StoreByte s e1 e2 : gc_P (StoreByte e1 e2) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H. injp H.
  cbn [compile]. tstep. ce_rw Hr. cbn beta iota.
  match goal with E : mem_store_byte _ _ _ _ _ = SOME _ |- _ =>
    destruct (state_rel_mem_store_byte _ ctxt _ _ _ _ _ (conj Hr E)) as (m' & Hm' & Hr') end.
  rewrite Hm'. eexists; split; [reflexivity|exact Hr'].
Qed.

Lemma gc_ShMemStore s op e1 e2 : gc_P (ShMemStore op e1 e2) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H.
  cbn [compile]. tstep. ce_rw Hr. cbn beta iota.
  match goal with |- context [sh_mem_store ?w ?ad ?nb t] =>
    destruct (sh_mem_store_rel w ad nb s t (eq_sym (sr_sh_memaddrs _ _ _ _ Hr)) (eq_sym (sr_ffi _ _ _ _ Hr)))
      as [(f & Q1 & Q2)|[(nf & Q1 & Q2)|(Q1 & Q2)]]; rewrite Q1 in H; rewrite Q2; injp H end.
  - eexists; split; [reflexivity|exact (sr_false _ _ _ _ Hr)].
  - eexists; split; [reflexivity|exact (state_rel_change_ffi _ _ _ _ _ Hr)].
  - exfalso; apply Hne; reflexivity.
Qed.

Lemma gc_Return s e : gc_P (panLang.Return e) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H. injp H.
  cbn [compile]. tstep. ce_rw Hr. cbn beta iota.
  destruct (sr_structs _ _ _ _ Hr) as [S1 S2]. rewrite S1 in *. rewrite S2. repeat goal_scrut.
  eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)].
Qed.

Lemma gc_Raise s eid e : gc_P (Raise eid e) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H. injp H.
  cbn [compile]. tstep. ce_rw Hr. rewrite <- (sr_eshapes _ _ _ _ Hr).
  destruct (sr_structs _ _ _ _ Hr) as [S1 S2]. rewrite S1 in *. rewrite S2. repeat goal_scrut.
  eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)].
Qed.

Lemma gc_ExtCall s f e1 e2 e3 e4 : gc_P (ExtCall f e1 e2 e3 e4) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H.
  all: cbn [compile]; tstep; ce_rw Hr; cbn beta iota.
  all: repeat match goal with E : read_bytearray ?x ?y (mem_load_byte (memory ?s0) (memaddrs ?s0) (be ?s0)) = SOME _
              |- context [read_bytearray ?x ?y (mem_load_byte (memory ?t0) (memaddrs ?t0) (be ?t0))] =>
    rewrite (state_rel_read_bytearray _ _ s0 t0 _ _ _ (conj Hr E)) end; cbn beta iota.
  all: rewrite <- (sr_ffi _ _ _ _ Hr); repeat goal_scrut; injp H.
  - eexists; split; [reflexivity|]. apply state_rel_change_ffi.
    match goal with E : call_FFI _ _ _ _ = FFI_return _ _ |- _ => pose proof (stack_removeProof.call_FFI_LENGTH _ _ _ _ _ _ E) as HL end.
    match goal with E : read_bytearray ?sz _ _ = SOME ?bs |- context [write_bytearray ?sz _ _ _ _] =>
      pose proof (read_bytearray_LENGTH _ _ _ _ E) as HL2;
      eapply state_rel_write_bytearray; [exact tt|]; split; [exact Hr|]; rewrite HL, HL2; exact E end.
  - eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)].
Qed.


Lemma gc_Seq s p1 p2 :
  (forall p' s', eval_lt (p', s') (Seq p1 p2, s) -> gc_P p' s') -> gc_P (Seq p1 p2) s.
Proof.
  intros IH. gc_intro. sstep H.
  destruct (evaluate (p1, s)) as [r1 s1] eqn:Ep1. cbn [compile]. tstep.
  destruct r1 as [r1|]; cbn beta iota in H.
  - injp H. destruct (IH p1 s ltac:(prove_lt) _ ctxt t s1 Hr Ep1 Hne) as (t1 & Et1 & Hr1).
    rewrite Et1. exists t1. split; [reflexivity|exact Hr1].
  - destruct (IH p1 s ltac:(prove_lt) NONE ctxt t s1 Hr Ep1 ltac:(discriminate)) as (t1 & Et1 & Hr1).
    rewrite Et1. cbn beta iota.
    exact (IH p2 s1 ltac:(prove_lt) res ctxt t1 s' Hr1 H Hne).
Qed.

Lemma gc_If s e p1 p2 :
  (forall p' s', eval_lt (p', s') (If e p1 p2, s) -> gc_P p' s') -> gc_P (If e p1 p2) s.
Proof.
  intros IH. gc_intro. sstep H. repeat split_nonrec H; try err H.
  all: cbn [compile]; tstep; ce_rw Hr; cbn beta iota; repeat goal_scrut.
  all: match type of H with evaluate (?p, ?s0) = _ => exact (IH p s0 ltac:(prove_lt) res ctxt t s' Hr H Hne) end.
Qed.

Lemma gc_While s e c :
  (forall p' s', eval_lt (p', s') (While e c, s) -> gc_P p' s') -> gc_P (While e c) s.
Proof.
  intros IH. gc_intro. sstep H. repeat split_nonrec H; try err H.
  all: cbn [compile]; tstep; ce_rw Hr; cbn beta iota; repeat goal_scrut.
  all: try (injp H; eexists; split; [reflexivity|exact Hr]).
  all: rewrite <- (sr_clock _ _ _ _ Hr); repeat goal_scrut.
  all: try (injp H; eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)]).
  destruct (evaluate (c, dec_clock s)) as [r1 s1] eqn:Ec.
  assert (Hne1 : r1 <> SOME Error) by (intros ->; cbn beta iota in H; injp H; apply Hne; reflexivity).
  destruct (IH c (dec_clock s) ltac:(prove_lt) r1 ctxt (dec_clock t) s1 (state_rel_dec_clock _ _ _ _ Hr) Ec Hne1)
    as (t1 & Et1 & Hr1).
  rewrite Et1. cbn beta iota in H |- *.
  destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota in H |- *.
  all: try (injp H; eexists; split; [reflexivity|exact Hr1]).
  all: exact (IH (While e c) s1 ltac:(prove_lt) res ctxt t1 s' Hr1 H Hne).
Qed.


Ltac split_nonrec2 H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | fix_clock _ _ => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H |- *
      end
  end.

Ltac lc_rw Hr :=
  match goal with E : lookup_code (code ?s0) ?f ?vs = SOME (?p0, ?nl) |- _ =>
    rewrite (state_rel_lookup_code _ _ s0 _ f vs p0 nl (conj Hr E)) end.

Lemma sr_call ctxt s t (nl : fmap varname (v a)) : state_rel true ctxt s t ->
  state_rel true ctxt (set_locals nl (dec_clock s)) (set_locals nl (dec_clock t)).
Proof. intros Hr. exact (proj1 (state_rel_change_locals _ _ _ _ _) (state_rel_dec_clock _ _ _ _ Hr)). Qed.

Lemma sr_ret ctxt s t (st st1 : state a ffi_t) : state_rel true ctxt s t -> state_rel false ctxt st st1 ->
  state_rel true ctxt (set_locals (locals s) st) (set_locals (locals t) st1).
Proof. intros Hr H. rewrite (sr_locals _ _ _ Hr). exact (proj2 (state_rel_change_locals _ _ _ _ _) H). Qed.

Lemma gc_DecCall s rt sh f args p :
  (forall p' s', eval_lt (p', s') (DecCall rt sh f args p, s) -> gc_P p' s') -> gc_P (DecCall rt sh f args p) s.
Proof.
  intros IH. gc_intro. sstep H. repeat split_nonrec2 H; try err H.
  all: cbn [compile]; tstep; ce_rw Hr; cbn beta iota; lc_rw Hr; cbn beta iota.
  all: rewrite <- (sr_clock _ _ _ _ Hr); repeat goal_scrut.
  all: try (injp H; eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)]).
  rewrite fix_clock_evaluate in H |- *.
  match type of H with context [evaluate (?p0, ?s0)] =>
    destruct (evaluate (p0, s0)) as [r1 st] eqn:Ecall end.
  assert (Hne1 : r1 <> SOME Error) by (intros ->; cbn beta iota in H; injp H; apply Hne; reflexivity).
  match type of Ecall with evaluate (?p0, set_locals ?nl (dec_clock s)) = _ =>
    destruct (IH p0 (set_locals nl (dec_clock s)) ltac:(prove_lt) r1 ctxt (set_locals nl (dec_clock t)) st (sr_call _ _ _ nl Hr) Ecall Hne1)
      as (st1 & Et & Hrr) end.
  rewrite Et. destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota in H |- *.
  all: try err H.
  all: try (injp H; eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hrr)]).
  repeat split_nonrec H; try err H. repeat goal_scrut.
  pose proof (state_rel_set_var true ctxt _ _ rt retv (sr_ret _ _ _ _ _ Hr Hrr)) as Hr2.
  destruct (evaluate (p, set_var rt retv (set_locals (locals s) st))) as [r2 st2] eqn:Ep. injp H.
  destruct (IH p (set_var rt retv (set_locals (locals s) st)) ltac:(prove_lt) r2 ctxt _ st2 Hr2 Ep Hne) as (t2 & Et2 & Hr3).
  rewrite Et2. eexists; split; [reflexivity|].
  exact (state_rel_res_var (good_res r2) ctxt st2 t2 s t rt rt (conj Hr3 Hr)).
Qed.


Lemma locals_sf f s : locals (set_ffi f s) = locals s. Proof. reflexivity. Qed.
Lemma locals_sv k x s : locals (set_var k x s) = locals s |+ (k, x). Proof. reflexivity. Qed.
Lemma locals_sm m s : locals (set_memory m s) = locals s. Proof. reflexivity. Qed.
Lemma locals_el s : locals (empty_locals s) = FEMPTY. Proof. reflexivity. Qed.

Ltac loc_rw := rewrite ?locals_sf, ?locals_sv, ?locals_sm, ?locals_sl, ?locals_el.

Ltac dec_solve :=
  repeat match goal with |- context [decide ?P] =>
    destruct (decide P) as [?C|?C]; try (exfalso; congruence) end.

Ltac fm_solve :=
  apply fmap_ext; intros ?k; rewrite ?FLOOKUP_pan_res_var_thm, ?FLOOKUP_UPDATE;
  repeat match goal with |- context [decide ?P] => destruct (decide P); subst end;
  try reflexivity; try congruence.

Ltac sframe H := eapply (state_rel_frame _ _ _ _ _ _ _ H); try reflexivity.

Lemma gc_ShMemLoad s op vk vn e : gc_P (ShMemLoad op vk vn e) s.
Proof.
  gc_intro. sstep H. repeat split_nonrec H; try err H.
  match type of H with context [sh_mem_load _ _ ?ad _ _] => rename ad into A end.
  destruct vk.
  - cbn [compile]. tstep. ce_rw Hr. cbn beta iota. unfold lookup_kvar in *. rewrite <- (sr_locals _ _ _ Hr).
    repeat goal_scrut.
    destruct (sh_mem_load_rel Local Local vn vn A (nb_op op) s t (eq_sym (sr_sh_memaddrs _ _ _ _ Hr)) (eq_sym (sr_ffi _ _ _ _ Hr)))
      as [(f & Q1 & Q2)|[(nf & wv & Q1 & Q2)|(Q1 & Q2)]]; rewrite Q1 in H; rewrite Q2; injp H.
    + eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)].
    + eexists; split; [reflexivity|]. apply state_rel_change_ffi. exact (state_rel_set_var _ _ _ _ _ _ Hr).
    + exfalso; apply Hne; reflexivity.
  - cbn [lookup_kvar] in *.
    match goal with E : FLOOKUP (globals s) vn = SOME ?w |- _ => rename E into Ew end.
    destruct (sr_global_lookup _ _ _ _ _ _ Hr Ew) as [ad Hc]. cbn [shape_of] in Hc.
    pose proof (v_neq_v' vn) as Hvr.
    cbn [compile]. rewrite Hc. cbn beta iota zeta.
    tstep. ce_rw Hr. rewrite bd_true by reflexivity. cbn beta iota zeta.
    rewrite evaluate_unfold. cbn [evaluate_body eval]. rewrite bd_true by reflexivity. cbn beta iota zeta.
    rewrite evaluate_unfold. cbn [evaluate_body]. rewrite fix_clock_evaluate.
    rewrite evaluate_unfold. cbn [evaluate_body eval lookup_kvar]. loc_rw.
    rewrite !FLOOKUP_UPDATE. dec_solve. unfold ValWord. cbn beta iota.
    match goal with |- context [sh_mem_load Local ?r' A ?nb ?T2] =>
      destruct (sh_mem_load_rel Global Local vn r' A nb s T2 (eq_sym (sr_sh_memaddrs _ _ _ _ Hr)) (eq_sym (sr_ffi _ _ _ _ Hr)))
        as [(f & Q1 & Q2)|[(nf & wv & Q1 & Q2)|(Q1 & Q2)]]; rewrite Q1 in H; rewrite Q2; injp H end.
    + cbn beta iota zeta. eexists; split; [reflexivity|].
      sframe (sr_empty _ _ _ _ Hr); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hr)|exact (sr_ffi _ _ _ _ Hr)].
    + cbn beta iota zeta. rewrite evaluate_unfold. cbn [evaluate_body]. rewrite eval_top_sub.
      cbn [eval set_kvar]. loc_rw. rewrite FLOOKUP_UPDATE. dec_solve. unfold ValWord. cbn beta iota.
      destruct (sr_store_global _ _ _ _ _ _ (ValWord wv) _ Hr Ew eq_refl Hc) as (m & Hm & Hsr).
      match goal with |- context [mem_stores ?x ?l ?d ?mm] =>
        replace (mem_stores x l d mm) with (SOME m) by (symmetry; exact Hm) end.
      cbn beta iota zeta. eexists; split; [reflexivity|].
      sframe Hsr; [|exact (sr_clock _ _ _ _ Hr)].
      intros _. cbn [set_kvar]. unfold set_global, set_globals, set_ffi, set_memory, set_var. cbn [locals].
      rewrite (sr_locals _ _ _ Hr). loc_rw. fm_solve.
    + exfalso; apply Hne; reflexivity.
Qed.


Lemma n2w_1_neq_0 : good_dimindex a -> (n2w 1 : word a) <> n2w 0.
Proof.
  intros Hg E. apply (f_equal w2n) in E. rewrite !w2n_n2w in E.
  destruct (gd_cases Hg) as [[_ Hd]|[_ Hd]]; rewrite Hd in E; cbn in E; discriminate.
Qed.

Lemma sr_gd ls ctxt s t : state_rel ls ctxt s t -> good_dimindex a.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(** The global-return facts of a [Call] whose result goes to global [rt]. *)
Lemma glob_ret ctxt s t rt sh addr prog0 nl r1 st st1 retv :
  state_rel true ctxt s t -> state_rel false ctxt st st1 ->
  FLOOKUP (pan_globals.globals ctxt) rt = SOME (sh, addr) ->
  is_valid_value s Global rt retv = true ->
  evaluate (prog0, set_locals nl (dec_clock s)) = (r1, st) ->
  shape_of retv = sh /\
  exists m, mem_stores (top_addr st1 - addr) (flatten retv) (memaddrs st1) (memory st1) = SOME m /\
    state_rel false ctxt (set_global rt retv st) (set_memory m st1).
Proof.
  intros Hr Hrr Eg Eiv Ecall. unfold is_valid_value, lookup_kvar in Eiv.
  destruct (FLOOKUP (globals s) rt) as [w|] eqn:Ew; [|discriminate]. apply bool_decide_spec in Eiv.
  destruct (sr_global_lookup _ _ _ _ _ _ Hr Ew) as [addr0 Hc]. rewrite Eg in Hc. injection Hc as Hsh0 Ha0.
  subst sh addr0.
  split; [exact Eiv|].
  destruct (evaluate_global_shape_invariant prog0 (set_locals nl (dec_clock s)) r1 st rt w (conj Ecall Ew))
    as (w' & Ew' & Hsh').
  rewrite <- Hsh' in Eg, Eiv.
  exact (sr_store_global _ _ _ _ _ _ _ _ Hrr Ew' Eiv Eg).
Qed.

Lemma tgtC_prefix t vn' flag sh x0 (BODY : prog a) :
  eval t (shape_val sh) = SOME x0 -> shape_of x0 = sh ->
  evaluate (Dec vn' sh (shape_val sh) (Dec flag One (Const (n2w 0)) BODY), t) =
  let '(r, st) := evaluate (BODY, set_locals (locals t |+ (vn', x0) |+ (flag, ValWord (n2w 0))) t) in
  (r, set_locals (res_var (res_var (locals st) (flag, FLOOKUP (locals t |+ (vn', x0)) flag))
                          (vn', FLOOKUP (locals t) vn')) st).
Proof.
  intros Ex Hsh. tstep. rewrite Ex. rewrite bd_true by (symmetry; exact Hsh). cbn beta iota zeta.
  rewrite evaluate_unfold. cbn [evaluate_body eval]. rewrite bd_true by reflexivity. cbn beta iota zeta.
  destruct (evaluate (BODY, _)). reflexivity.
Qed.

Ltac nin_split :=
  repeat match goal with
  | H : ~ (_ \/ _) |- _ => apply not_or'' in H as [? ?]
  | H : ~ In _ (_ ++ _) |- _ => apply not_in_app_iff in H as [? ?]
  | H : ~ In _ (_ :: _) |- _ => apply not_in_cons in H as [? ?]
  end.

Ltac good_HL HL :=
  match type of HL with is_true (good_res ?r) /\ ?r <> SOME Error -> ?L = _ =>
    let Hg := fresh "Hg" in let Hn := fresh "Hn" in
    assert (Hg : is_true (good_res r)) by reflexivity; assert (Hn : r <> SOME Error) by discriminate;
    specialize (HL (conj Hg Hn)); subst L end.

Ltac glob_contra Hr Eg :=
  match goal with E : is_valid_value ?s0 Global ?rt _ = true |- _ =>
    unfold is_valid_value, lookup_kvar in E;
    let w := fresh "w" in let Ew := fresh "Ew" in let Hc := fresh "Hc" in
    destruct (FLOOKUP (globals s0) rt) as [w|] eqn:Ew; [|discriminate];
    destruct (sr_global_lookup _ _ _ _ _ _ Hr Ew) as [? Hc]; rewrite Hc in Eg; discriminate end.

Ltac tgtA Eargs' Elc' Hck Ec :=
  tstep; rewrite Eargs'; cbn beta iota; rewrite Elc'; cbn beta iota; rewrite <- Hck, Ec; cbn beta iota.

Ltac leafA IH Hr Hrr H Hne :=
  first
    [ err H
    | injp H; eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hrr)]
    | injp H; eexists; split; [reflexivity|exact (sr_ret _ _ _ _ _ Hr Hrr)]
    | injp H; eexists; split; [reflexivity|exact (state_rel_set_var _ _ _ _ _ _ (sr_ret _ _ _ _ _ Hr Hrr))]
    | match type of H with evaluate (?p, ?s0) = _ =>
        match goal with |- context [evaluate (compile ?ctxt p, ?t0)] =>
          exact (IH p s0 ltac:(prove_lt) _ ctxt t0 _
                   (state_rel_set_var _ _ _ _ _ _ (sr_ret _ _ _ _ _ Hr Hrr)) H Hne) end end ].

Ltac blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et :=
  tgtA Eargs' Elc' Hck Ec; rewrite fix_clock_evaluate, Et;
  match type of Et with _ = (?r1, _) =>
   destruct r1 as [[| | | |?retv|?eid1 ?exn|?ff]|]; cbn beta iota in H |- *;
   try leafA IH Hr Hrr H Hne;
   repeat split_nonrec H; try leafA IH Hr Hrr H Hne;
   try (rewrite <- (sr_eshapes _ _ _ _ Hr)); repeat goal_scrut; try (rewrite (ivv_local_rel _ _ _ _ _ Hr));
   repeat goal_scrut; try leafA IH Hr Hrr H Hne
  end.

Lemma gc_Call s ct f args :
  (forall p' s', eval_lt (p', s') (Call ct f args, s) -> gc_P p' s') -> gc_P (Call ct f args) s.
Proof.
  intros IH. gc_intro. sstep H.
  destruct (OPT_MMAP (eval s) args) as [vs|] eqn:Eargs; cbn beta iota in H; [|err H].
  destruct (lookup_code (code s) f vs) as [[prog0 [nl rsh]]|] eqn:Elc; cbn beta iota in H; [|err H].
  pose proof (OPT_MMAP_eval_correct ctxt s t args vs (conj Hr Eargs)) as Eargs'.
  pose proof (state_rel_lookup_code _ _ s t f vs prog0 (nl, rsh) (conj Hr Elc)) as Elc'.
  pose proof (sr_clock _ _ _ _ Hr) as Hck.
  destruct (clock s =? 0) eqn:Ec; cbn beta iota in H.
  { injp H. destruct ct as [[[[[|] rt]|] [[eid' [evar hp]]|]]|]; cbn [compile]; cbn zeta.
    all: try (tgtA Eargs' Elc' Hck Ec; eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)]).
    all: destruct (FLOOKUP (pan_globals.globals ctxt) rt) as [[sh addr]|] eqn:Eg; cbn beta iota.
    all: try (tgtA Eargs' Elc' Hck Ec; eexists; split; [reflexivity|exact (sr_empty _ _ _ _ Hr)]).
    set (names := evar :: free_var_ids (compile ctxt hp) ++ FLAT (MAP var_exp (MAP (compile_exp ctxt) args))).
    set (vn' := fresh_name (strlit "") names).
    set (flag := fresh_name (strlit "vn'") (vn' :: names)).
    assert (Hv : ~ In vn' names) by (intros Hin; apply (fresh_name_correct (strlit "") names), MEM_In, Hin).
    assert (Hf : ~ In flag (vn' :: names))
      by (intros Hin; apply (fresh_name_correct (strlit "vn'") (vn' :: names)), MEM_In, Hin).
    clearbody flag vn'. subst names. nin_split.
    pose proof (state_rel_globals_wf true ctxt s t rt (sh, addr) (conj Eg Hr)) as Hwf. cbn [FST] in Hwf.
    destruct (eval t (shape_val sh)) as [x0|] eqn:Ex0;
      [|exfalso; exact (proj1 (proj1 (eval_shape_val_NONE t) sh) Ex0)].
    pose proof (proj1 (eval_shape_val_thm t) sh x0 (conj Ex0 Hwf)) as Hx0.
    rewrite (tgtC_prefix t vn' flag sh x0 _ Ex0 (eq_sym Hx0)).
    rewrite evaluate_unfold. cbn [evaluate_body]. rewrite fix_clock_evaluate.
    rewrite evaluate_unfold. cbn [evaluate_body].
    rewrite OPT_MMAP_eval_two_fresh_vars by (split; rewrite MEM_is_true_In; assumption).
    rewrite Eargs'. cbn beta iota. rewrite code_sl, Elc'. cbn beta iota.
    rewrite clock_sl, <- Hck, Ec. cbn beta iota.
    eexists; split; [reflexivity|].
    sframe (sr_empty _ _ _ _ Hr); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hr)|exact (sr_ffi _ _ _ _ Hr)]. }
  rewrite fix_clock_evaluate in H.
  destruct (evaluate (prog0, set_locals nl (dec_clock s))) as [r1 st] eqn:Ecall.
  assert (Hne1 : r1 <> SOME Error) by (intros ->; cbn beta iota in H; injp H; apply Hne; reflexivity).
  destruct (IH prog0 (set_locals nl (dec_clock s)) ltac:(prove_lt) r1 ctxt (set_locals nl (dec_clock t)) st
              (sr_call _ _ _ nl Hr) Ecall Hne1) as (st1 & Et & Hrr).
  destruct ct as [[[[[|] rt]|] [[eid' [evar hp]]|]]|]; cbn [compile]; cbn zeta.
  (* Local, handler *)
  - blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
  - blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
  - destruct (FLOOKUP (pan_globals.globals ctxt) rt) as [[sh addr]|] eqn:Eg; cbn beta iota.
    + set (names := evar :: free_var_ids (compile ctxt hp) ++ FLAT (MAP var_exp (MAP (compile_exp ctxt) args))).
      set (vn' := fresh_name (strlit "") names).
      set (flag := fresh_name (strlit "vn'") (vn' :: names)).
      assert (Hv : ~ In vn' names) by (intros Hin; apply (fresh_name_correct (strlit "") names), MEM_In, Hin).
      assert (Hf : ~ In flag (vn' :: names))
        by (intros Hin; apply (fresh_name_correct (strlit "vn'") (vn' :: names)), MEM_In, Hin).
      clearbody flag vn'. subst names. nin_split.
      pose proof (state_rel_globals_wf true ctxt s t rt (sh, addr) (conj Eg Hr)) as Hwf. cbn [FST] in Hwf.
      destruct (eval t (shape_val sh)) as [x0|] eqn:Ex0;
        [|exfalso; exact (proj1 (proj1 (eval_shape_val_NONE t) sh) Ex0)].
      pose proof (proj1 (eval_shape_val_thm t) sh x0 (conj Ex0 Hwf)) as Hx0.
      rewrite (tgtC_prefix t vn' flag sh x0 _ Ex0 (eq_sym Hx0)).
      rewrite evaluate_unfold. cbn [evaluate_body]. rewrite fix_clock_evaluate.
      rewrite evaluate_unfold. cbn [evaluate_body].
      rewrite OPT_MMAP_eval_two_fresh_vars by (split; rewrite MEM_is_true_In; assumption).
      rewrite Eargs'. cbn beta iota. rewrite code_sl, Elc'. cbn beta iota.
      rewrite clock_sl, <- Hck, Ec. cbn beta iota. rewrite !sl_dec_clock, fix_clock_evaluate, Et.
      destruct r1 as [[| | | |retv|eid1 exn|ff]|]; cbn beta iota in H |- *; try err H.
      * injp H. eexists; split; [reflexivity|].
        sframe (sr_empty _ _ _ _ Hrr); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hrr)|exact (sr_ffi _ _ _ _ Hrr)].
      * (* Return *)
        repeat split_nonrec H; try err H. injp H.
        match goal with E : negb (bool_decide _) = false |- _ =>
          apply Bool.negb_false_iff, bool_decide_spec in E; rename E into Ersh end.
        match goal with E : is_valid_value s Global rt _ = true |- _ =>
          destruct (glob_ret _ _ _ _ _ _ _ _ _ _ _ _ Hr Hrr Eg E Ecall) as (Hsh & m & Hm & Hsr) end.
        cbn beta iota.
        assert (Hiv1 : is_valid_value (set_locals (locals t |+ (vn', x0) |+ (flag, ValWord (n2w 0))) t)
                         Local vn' retv = true)
          by (unfold is_valid_value, lookup_kvar; rewrite locals_sl, !FLOOKUP_UPDATE; dec_solve; apply bd_true; congruence).
        rewrite Hiv1. cbn beta iota.
        rewrite evaluate_unfold. cbn [evaluate_body eval set_kvar]. loc_rw. rewrite !FLOOKUP_UPDATE. dec_solve.
        unfold ValWord. cbn beta iota. rewrite bd_true by reflexivity. cbn [negb].
        rewrite evaluate_unfold. cbn [evaluate_body]. rewrite eval_top_sub. cbn [eval]. loc_rw.
        rewrite FLOOKUP_UPDATE. dec_solve. unfold ValWord. cbn beta iota.
        match goal with |- context [mem_stores ?x ?l ?d ?mm] =>
          replace (mem_stores x l d mm) with (SOME m) by (symmetry; exact Hm) end.
        cbn beta iota zeta. eexists; split; [reflexivity|].
        sframe Hsr; [|exact (sr_clock _ _ _ _ Hrr)|exact (sr_ffi _ _ _ _ Hrr)].
        intros _. cbn [set_kvar]. unfold set_global, set_globals, set_ffi, set_memory, set_var. cbn [locals].
        rewrite (sr_locals _ _ _ Hr). loc_rw. fm_solve.
      * (* Exception *)
        repeat split_nonrec H; try err H.
        all: try (injp H; eexists; split; [reflexivity|];
           sframe (sr_empty _ _ _ _ Hrr); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hrr)|exact (sr_ffi _ _ _ _ Hrr)]).
        -- rewrite eshapes_sl, <- (sr_eshapes _ _ _ _ Hr). repeat goal_scrut.
           assert (Hiv2 : is_valid_value (set_locals (locals t |+ (vn', x0) |+ (flag, ValWord (n2w 0))) t)
                            Local evar exn = is_valid_value s Local evar exn)
             by (unfold is_valid_value, lookup_kvar; rewrite locals_sl, !FLOOKUP_UPDATE; dec_solve;
                 rewrite (sr_locals _ _ _ Hr); reflexivity).
           rewrite Hiv2. repeat goal_scrut.
           rewrite evaluate_unfold. cbn [evaluate_body]. rewrite fix_clock_evaluate.
           pose proof (state_rel_set_var true ctxt _ _ evar exn (sr_ret _ _ _ _ _ Hr Hrr)) as Hr0.
           destruct (IH hp (set_var evar exn (set_locals (locals s) st)) ltac:(prove_lt) res ctxt _ s' Hr0 H Hne)
             as (t3 & Et3 & Hr3).
           assert (Hvn : ~ is_true (MEM vn' (free_var_ids (compile ctxt hp)))) by (rewrite MEM_is_true_In; assumption).
           assert (Hfl : ~ is_true (MEM flag (free_var_ids (compile ctxt hp)))) by (rewrite MEM_is_true_In; assumption).
           destruct (evaluate_two_fresh_locals vn' x0 flag (ValWord (n2w 0)) _ _ res t3 (conj Hvn (conj Hfl Et3)))
             as (L & EL & HL).
           match goal with |- context [evaluate (compile ctxt hp, ?S)] =>
             replace S with (set_locals (locals (set_var evar exn (set_locals (locals t) st1)) |+ (vn', x0)
                                        |+ (flag, ValWord (n2w 0))) (set_var evar exn (set_locals (locals t) st1)))
           end.
           2: { unfold set_var. rewrite !locals_sl, !set_locals_set_locals. f_equal. fm_solve. }
           rewrite EL.
           assert (U : forall z, ~ In z (free_var_ids (compile ctxt hp)) -> z <> evar -> is_true (good_res res) ->
                         FLOOKUP (locals t3) z = FLOOKUP (locals t) z).
           { intros z Hz1 Hz2 Hg.
             assert (Hz1' : ~ is_true (MEM z (free_var_ids (compile ctxt hp)))) by (rewrite MEM_is_true_In; exact Hz1).
             rewrite (evaluate_unchanged_local z x0 (compile ctxt hp) _ res t3 (conj Hz1' (conj Et3 (conj Hg Hne)))).
             rewrite locals_sv, locals_sl, FLOOKUP_UPDATE. dec_solve. reflexivity. }
           destruct res as [[| | | |rv|eidx ex|fx]|]; cbn beta iota.
           ++ exfalso; apply Hne; reflexivity.
           ++ eexists; split; [reflexivity|].
              sframe (sr_false _ _ _ _ Hr3); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
           ++ good_HL HL. eexists; split; [reflexivity|].
              sframe Hr3; [|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
              intros _. pose proof (U vn' ltac:(assumption) ltac:(congruence) eq_refl).
              pose proof (U flag ltac:(assumption) ltac:(congruence) eq_refl).
              loc_rw. rewrite (sr_locals _ _ _ Hr3). fm_solve.
           ++ good_HL HL. eexists; split; [reflexivity|].
              sframe Hr3; [|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
              intros _. pose proof (U vn' ltac:(assumption) ltac:(congruence) eq_refl).
              pose proof (U flag ltac:(assumption) ltac:(congruence) eq_refl).
              loc_rw. rewrite (sr_locals _ _ _ Hr3). fm_solve.
           ++ eexists; split; [reflexivity|].
              sframe (sr_false _ _ _ _ Hr3); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
           ++ eexists; split; [reflexivity|].
              sframe (sr_false _ _ _ _ Hr3); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
           ++ eexists; split; [reflexivity|].
              sframe (sr_false _ _ _ _ Hr3); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
           ++ good_HL HL.
              rewrite evaluate_unfold. cbn [evaluate_body eval].
              unfold is_valid_value, lookup_kvar. loc_rw. rewrite !FLOOKUP_UPDATE. dec_solve.
              rewrite bd_true by reflexivity. cbn beta iota.
              rewrite evaluate_unfold. cbn [evaluate_body eval set_kvar]. loc_rw. rewrite !FLOOKUP_UPDATE. dec_solve.
              unfold ValWord. cbn beta iota.
              destruct (bool_decide (@n2w a 1 = n2w 0)) eqn:Eb;
                [apply bool_decide_spec in Eb; exfalso; exact (n2w_1_neq_0 (sr_gd _ _ _ _ Hr) Eb)|].
              cbn [negb]. rewrite evaluate_unfold. cbn [evaluate_body].
              eexists; split; [reflexivity|].
              sframe Hr3; [|exact (sr_clock _ _ _ _ Hr3)|exact (sr_ffi _ _ _ _ Hr3)].
              intros _. pose proof (U vn' ltac:(assumption) ltac:(congruence) eq_refl).
              pose proof (U flag ltac:(assumption) ltac:(congruence) eq_refl).
              unfold set_var. loc_rw. rewrite (sr_locals _ _ _ Hr3). fm_solve.
      * injp H. eexists; split; [reflexivity|].
        sframe (sr_empty _ _ _ _ Hrr); [intros Cf; discriminate Cf|exact (sr_clock _ _ _ _ Hrr)|exact (sr_ffi _ _ _ _ Hrr)].
    + blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
      glob_contra Hr Eg.
  - destruct (FLOOKUP (pan_globals.globals ctxt) rt) as [[sh addr]|] eqn:Eg; cbn beta iota.
    + tgtA Eargs' Elc' Hck Ec. rewrite fix_clock_evaluate, Et.
      destruct r1 as [[| | | |retv|eid1 exn|ff]|]; cbn beta iota in H |- *; try leafA IH Hr Hrr H Hne.
      repeat split_nonrec H; try err H. injp H.
      match goal with E : negb (bool_decide _) = false |- _ =>
        apply Bool.negb_false_iff, bool_decide_spec in E; rename E into Ersh end.
      match goal with E : is_valid_value s Global rt _ = true |- _ =>
        destruct (glob_ret _ _ _ _ _ _ _ _ _ _ _ _ Hr Hrr Eg E Ecall) as (Hsh & m & Hm & Hsr) end.
      rewrite bd_true by exact Hsh. rewrite bd_true by exact Ersh. cbn beta iota.
      rewrite evaluate_unfold. cbn [evaluate_body]. rewrite eval_top_sub. cbn [eval]. loc_rw.
      rewrite FLOOKUP_UPDATE. dec_solve. unfold ValWord. cbn beta iota.
      match goal with |- context [mem_stores ?x ?l ?d ?mm] =>
        replace (mem_stores x l d mm) with (SOME m) by (symmetry; exact Hm) end.
      cbn beta iota zeta. eexists; split; [reflexivity|].
      sframe Hsr; [|exact (sr_clock _ _ _ _ Hrr)|exact (sr_ffi _ _ _ _ Hrr)].
      intros _. cbn [set_kvar]. unfold set_global, set_globals, set_ffi, set_memory, set_var. cbn [locals].
      rewrite (sr_locals _ _ _ Hr). loc_rw. fm_solve.
    + blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
      glob_contra Hr Eg.
  - blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
  - blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
  - blkA IH Hr Hrr H Hne Eargs' Elc' Hck Ec Et.
Qed.


Lemma gc_all : forall x : prog a * state a ffi_t, gc_P (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  assert (IH' : forall p' s', eval_lt (p', s') (p, s) -> gc_P p' s')
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  cbn [fst snd]. destruct p.
  - apply gc_Skip.
  - apply gc_Dec; exact IH'.
  - apply gc_Assign.
  - apply gc_Primitive.
  - apply gc_Store.
  - apply gc_Store32.
  - apply gc_StoreByte.
  - apply gc_Seq; exact IH'.
  - apply gc_If; exact IH'.
  - apply gc_While; exact IH'.
  - apply gc_Break.
  - apply gc_Continue.
  - apply gc_Call; exact IH'.
  - apply gc_DecCall; exact IH'.
  - apply gc_ExtCall.
  - apply gc_Raise.
  - apply gc_Return.
  - apply gc_ShMemLoad.
  - apply gc_ShMemStore.
  - apply gc_Tick.
  - apply gc_Annot.
Qed.

End CompileCorrect.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall {a ffi_t} (p : prog a) (s : state a ffi_t) res ctxt t s',
  state_rel true ctxt s t /\ evaluate (p, s) = (res, s') /\ res <> SOME Error ->
  exists t', evaluate (compile ctxt p, t) = (res, t') /\ state_rel (good_res res) ctxt s' t'.
Proof. intros a ffi_t p s res ctxt t s' (Hr & H & Hne). exact (gc_all (p, s) res ctxt t s' Hr H Hne). Qed.


(** ** Renaming functions *)

Section Fperm.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_code_def" *)
Definition fperm_code (f g : mlstring) (code0 : fmap funname (list (varname * shape) * (prog a * shape)))
    : fmap funname (list (varname * shape) * (prog a * shape)) :=
  FUN_FMAP ((I ## (fperm f g ## I)) ∘ THE ∘ FLOOKUP code0 ∘ fperm_name f g)
           (PREIMAGE (fperm_name f g) (FDOM code0)).

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cancel" *)
Theorem fperm_name_cancel : forall f g name, fperm_name f g (fperm_name f g name) = name.
Proof.
  intros f g name. unfold fperm_name.
  destruct (decide (f = name)), (decide (g = name)); cbn beta iota;
  repeat (match goal with |- context [decide ?P] => destruct (decide P) end; cbn beta iota);
    subst; try reflexivity; try congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cong" *)
Theorem fperm_name_cong : forall f g x y, fperm_name f g x = fperm_name f g y <-> x = y.
Proof.
  intros f g x y; split; [|intros ->; reflexivity].
  intros H. rewrite <- (fperm_name_cancel f g x), <- (fperm_name_cancel f g y), H. reflexivity.
Qed.

Lemma fperm_code_finite f g (code0 : fmap funname (list (varname * shape) * (prog a * shape))) :
  FINITE (PREIMAGE (fperm_name f g) (FDOM code0)).
Proof. apply FINITE_PREIMAGE. split; [apply fperm_name_cong|apply FDOM_FINITE]. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FLOOKUP_fperm_code" *)
Theorem FLOOKUP_fperm_code : forall f g code0 name,
  FLOOKUP (fperm_code f g code0) (fperm_name f g name) =
  OPTION_MAP (I ## (fperm f g ## I)) (FLOOKUP code0 name).
Proof.
  intros f g code0 name. unfold fperm_code. rewrite FLOOKUP_FUN_FMAP by apply fperm_code_finite.
  destruct (classical_dec _) as [Hi|Hn]; unfold PREIMAGE, FDOM, pred_set.IN in *; rewrite fperm_name_cancel in *.
  - destruct (FLOOKUP code0 name) as [x|]; [reflexivity|contradiction Hi; reflexivity].
  - destruct (FLOOKUP code0 name) as [x|]; [|reflexivity]. exfalso; apply Hn; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FLOOKUP_fperm_code'" *)
Theorem FLOOKUP_fperm_code' : forall f g code0 name,
  FLOOKUP (fperm_code f g code0) name =
  OPTION_MAP (I ## (fperm f g ## I)) (FLOOKUP code0 (fperm_name f g name)).
Proof.
  intros f g code0 name. rewrite <- (fperm_name_cancel f g name) at 1. apply FLOOKUP_fperm_code.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_code_FEMPTY" *)
Theorem fperm_code_FEMPTY : forall f g, fperm_code f g FEMPTY = FEMPTY.
Proof. intros f g. apply fmap_ext; intros k. rewrite FLOOKUP_fperm_code'. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_append" *)
Theorem fperm_decs_append : forall f g (xs ys : list (decl a)),
  fperm_decs f g (xs ++ ys) = fperm_decs f g xs ++ fperm_decs f g ys.
Proof. intros f g xs ys; induction xs as [|[]]; cbn; rewrite ?IHxs; reflexivity. Qed.


Lemma fperm_code_FUPDATE f g code0 n (x : list (varname * shape) * (prog a * shape)) :
  fperm_code f g (code0 |+ (n, x)) = fperm_code f g code0 |+ (fperm_name f g n, (I ## (fperm f g ## I)) x).
Proof.
  apply fmap_ext; intros k. rewrite FLOOKUP_fperm_code', !FLOOKUP_UPDATE, FLOOKUP_fperm_code'.
  destruct (decide (n = fperm_name f g k)) as [Hn|Hn]; destruct (decide (fperm_name f g n = k)) as [Hk|Hk].
  - reflexivity.
  - exfalso; apply Hk; rewrite Hn; apply fperm_name_cancel.
  - exfalso; apply Hn; rewrite <- Hk, fperm_name_cancel; reflexivity.
  - reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_code_FUPDATE_LIST_functions" *)
Theorem fperm_code_FUPDATE_LIST_functions : forall f g fm (code0 : list (decl a)),
  fperm_code f g (fm |++ functions code0) = fperm_code f g fm |++ functions (fperm_decs f g code0).
Proof.
  intros f g fm code0; revert fm; induction code0 as [|[fi| | |] ds IH]; intros fm; cbn [functions fperm_decs];
    rewrite ?(proj2 (FUPDATE_LIST_THM _)); try apply IH; [reflexivity|].
  rewrite IH, fperm_code_FUPDATE. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "lookup_code_fperm_code" *)
Theorem lookup_code_fperm_code : forall f g code0 name (args : list (v a)),
  lookup_code (fperm_code f g code0) (fperm_name f g name) args =
  OPTION_MAP (fperm f g ## I) (lookup_code code0 name args).
Proof.
  intros f g code0 name args. unfold lookup_code. rewrite FLOOKUP_fperm_code.
  destruct (FLOOKUP code0 name) as [[vs [p r]]|]; [|reflexivity]. cbn.
  destruct (_ && _); reflexivity.
Qed.

(** HOL's [eval_upd_code_eta] is [eval_upd_code_eq] as a function equality. *)
(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_upd_code_eta" *)
Theorem eval_upd_code_eta : forall code0 (t : state a ffi_t), eval (set_code code0 t) = eval t.
Proof. intros code0 t; apply eval_set_code. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_fperm_decs" *)
Theorem functions_fperm_decs : forall x y (code0 : list (decl a)),
  functions (fperm_decs x y code0) =
  MAP (fun '(a0, (b, (c, d))) => (fperm_name x y a0, (b, (fperm x y c, d)))) (functions code0).
Proof. intros x y code0; induction code0 as [|[]]; cbn; rewrite ?IHcode0; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALL_DISTINCT_fperm_decs" *)
Theorem ALL_DISTINCT_fperm_decs : forall x y (code0 : list (decl a)),
  is_true (ALL_DISTINCT (MAP FST (functions code0))) ->
  is_true (ALL_DISTINCT (MAP FST (functions (fperm_decs x y code0)))).
Proof.
  intros x y code0. rewrite functions_fperm_decs.
  assert (E : MAP FST (MAP (fun '(a0, (b, (c, d))) => (fperm_name x y a0, (b, (fperm x y c, d)))) (functions code0))
              = MAP (fperm_name x y) (MAP FST (functions code0))).
  { induction (functions code0) as [|[n [b [c d]]] l IH]; cbn; [reflexivity|]. f_equal; exact IH. }
  rewrite E. unfold is_true. rewrite !ALL_DISTINCT_NoDup_list.
  generalize (MAP FST (functions code0)) as l. intros l H.
  induction H as [|z l Hz Hl IH]; cbn; constructor; [|exact IH].
  intros Hin. apply Hz. apply in_map_iff in Hin as (w & Hw & Hin). apply fperm_name_cong in Hw. subst; exact Hin.
Qed.

Lemma locals_sc C s : locals (set_code C s) = locals s. Proof. reflexivity. Qed.
Lemma globals_sc C s : globals (set_code C s) = globals s. Proof. reflexivity. Qed.
Lemma structs_sc C s : structs (set_code C s) = structs s. Proof. reflexivity. Qed.
Lemma code_sc C s : code (set_code C s) = C. Proof. reflexivity. Qed.
Lemma eshapes_sc C s : eshapes (set_code C s) = eshapes s. Proof. reflexivity. Qed.
Lemma memory_sc C s : memory (set_code C s) = memory s. Proof. reflexivity. Qed.
Lemma memaddrs_sc C s : memaddrs (set_code C s) = memaddrs s. Proof. reflexivity. Qed.
Lemma sh_memaddrs_sc C s : sh_memaddrs (set_code C s) = sh_memaddrs s. Proof. reflexivity. Qed.
Lemma clock_sc C s : clock (set_code C s) = clock s. Proof. reflexivity. Qed.
Lemma be_sc C s : be (set_code C s) = be s. Proof. reflexivity. Qed.
Lemma ffi_sc C s : ffi (set_code C s) = ffi s. Proof. reflexivity. Qed.
Lemma sl_sc L C s : set_locals L (set_code C s) = set_code C (set_locals L s). Proof. reflexivity. Qed.
Lemma dc_sc C s : dec_clock (set_code C s) = set_code C (dec_clock s). Proof. reflexivity. Qed.
Lemma sv_sc k x C s : set_var k x (set_code C s) = set_code C (set_var k x s). Proof. reflexivity. Qed.

Ltac sc_proj := rewrite ?locals_sc, ?globals_sc, ?structs_sc, ?code_sc, ?eshapes_sc, ?memory_sc,
  ?memaddrs_sc, ?sh_memaddrs_sc, ?clock_sc, ?be_sc, ?ffi_sc,
  ?eval_set_code, ?lookup_kvar_set_code, ?is_valid_value_set_code.

Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.

Ltac split_nonrec2 H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | fix_clock _ _ => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H |- *
      end
  end.

Lemma evaluate_fperm_aux f g : forall (x : prog a * state a ffi_t) res s' C,
  evaluate x = (res, s') ->
  (forall fname (args : list (v a)), lookup_code C (fperm_name f g fname) args =
     OPTION_MAP (fperm f g ## I) (lookup_code (code (snd x)) fname args)) ->
  evaluate (fperm f g (fst x), set_code C (snd x)) = (res, set_code C s').
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res s' C H HC. cbn [fst snd] in *.
  rewrite evaluate_unfold in H |- *.
  destruct p as [|vn sh e p|vk vn e|vn pop es|e1 e2|e1 e2|e1 e2|p1 p2|e p1 p2|e p| | |ct fn args
                 |vn sh fn args p|fn e1 e2 e3 e4|eid e|e|op vk vn e|op e1 e2| |m1 m2];
    cbn [evaluate_body fperm] in H |- *; unfold sh_mem_load, sh_mem_store in H |- *; sc_proj;
    rewrite ?fix_clock_evaluate in H.
  all: try (destruct vk; cbn [evaluate_body] in H |- *).
  all: try (split_all H; try injp H; repeat first [goal_scrut | progress sc_proj]; reflexivity).
  - (* Dec *)
    repeat split_nonrec H; try (injp H; reflexivity). rewrite sl_sc.
    destruct (evaluate (p, set_locals (locals s |+ (vn, _)) s)) as [r st] eqn:Ep.
    match type of Ep with evaluate (p, ?s0) = _ =>
      pose proof (IH (p, s0) ltac:(prove_lt) r st C Ep HC) as F end; cbn [fst snd] in F; rewrite F.
    injp H. reflexivity.
  - (* Seq *)
    rewrite fix_clock_evaluate.
    destruct (evaluate (p1, s)) as [r1 s1] eqn:Ep1.
    pose proof (IH (p1, s) ltac:(prove_lt) r1 s1 C Ep1 HC) as F; cbn [fst snd] in F; rewrite F.
    destruct r1; cbn beta iota in H |- *; [injp H; reflexivity|].
    assert (HC1 : forall fname (args : list (panSem.v a)), lookup_code C (fperm_name f g fname) args =
               OPTION_MAP (fperm f g ## I) (lookup_code (code s1) fname args))
      by (rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (evaluate_invariants _ _ _ _ Ep1)))))))); exact HC).
    exact (IH (p2, s1) ltac:(prove_lt) res s' C H HC1).
  - (* If *)
    repeat split_nonrec H; try (injp H; reflexivity).
    all: match type of H with evaluate (?p0, ?s0) = _ => exact (IH (p0, s0) ltac:(prove_lt) _ _ _ H HC) end.
  - (* While *)
    repeat split_nonrec H; try (injp H; reflexivity).
    rewrite dc_sc, fix_clock_evaluate.
    destruct (evaluate (p, dec_clock s)) as [r1 s1] eqn:Ep1.
    pose proof (IH (p, dec_clock s) ltac:(prove_lt) r1 s1 C Ep1 HC) as F; cbn [fst snd] in F; rewrite F.
    assert (HC1 : forall fname (args : list (panSem.v a)), lookup_code C (fperm_name f g fname) args =
               OPTION_MAP (fperm f g ## I) (lookup_code (code s1) fname args))
      by (rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (evaluate_invariants _ _ _ _ Ep1)))))))); exact HC).
    destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota in H |- *; try (injp H; reflexivity).
    all: exact (IH (While e p, s1) ltac:(prove_lt) res s' C H HC1).
  - (* Call *)
    destruct ct as [[ret [[eid' [evar hp]]|]]|]; cbn beta iota in H |- *.
    all: try (destruct ret as [[[] rt]|]); cbn beta iota in H |- *; sc_proj.
    all: split_nonrec2 H; try (injp H; reflexivity).
    all: rewrite HC; repeat split_nonrec2 H; try (injp H; reflexivity).
    all: cbn [option_map PAIR_MAP combin.I fst snd]; cbn beta iota.
    all: rewrite dc_sc, sl_sc, fix_clock_evaluate; rewrite fix_clock_evaluate in H.
    all: match type of H with context [evaluate (?p0, ?s0)] =>
      let r1 := fresh "r1" in let st := fresh "st" in let Ec := fresh "Ec" in
      destruct (evaluate (p0, s0)) as [r1 st] eqn:Ec;
      let F := fresh "F" in pose proof (IH (p0, s0) ltac:(prove_lt) r1 st C Ec HC) as F;
      cbn [fst snd] in F; rewrite F;
      let HC2 := fresh "HC2" in
      assert (HC2 : forall fname (args : list (panSem.v a)), lookup_code C (fperm_name f g fname) args =
                 OPTION_MAP (fperm f g ## I) (lookup_code (code st) fname args))
        by (rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (evaluate_invariants _ _ _ _ Ec)))))))); exact HC);
      destruct r1 as [[| | | |?retv|?eid ?exn|?ff]|]; cbn beta iota in H |- * end.
    all: repeat split_nonrec H; try (injp H; reflexivity).
    all: rewrite sl_sc, sv_sc.
    all: match type of H with evaluate (?p0, ?s0) = _ =>
      exact (IH (p0, s0) ltac:(prove_lt) _ _ C H ltac:(assumption)) end.
  - (* DecCall *)
    split_nonrec2 H; try (injp H; reflexivity).
    rewrite HC; repeat split_nonrec2 H; try (injp H; reflexivity).
    all: cbn [option_map PAIR_MAP combin.I fst snd]; cbn beta iota.
    all: rewrite dc_sc, sl_sc, fix_clock_evaluate; rewrite fix_clock_evaluate in H.
    match type of H with context [evaluate (?p0, ?s0)] =>
      destruct (evaluate (p0, s0)) as [r1 st] eqn:Ec;
      pose proof (IH (p0, s0) ltac:(prove_lt) r1 st C Ec HC) as F;
      cbn [fst snd] in F; rewrite F end.
    assert (HC2 : forall fname (args : list (panSem.v a)), lookup_code C (fperm_name f g fname) args =
               OPTION_MAP (fperm f g ## I) (lookup_code (code st) fname args))
      by (rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (evaluate_invariants _ _ _ _ Ec)))))))); exact HC).
    destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota in H |- *; try (injp H; reflexivity).
    repeat split_nonrec H; try (injp H; reflexivity).
    rewrite sl_sc, sv_sc.
    destruct (evaluate (p, set_var vn retv (set_locals (locals s) st))) as [r2 st2] eqn:Ep.
    pose proof (IH (p, set_var vn retv (set_locals (locals s) st)) ltac:(prove_lt) r2 st2 C Ep HC2) as F2; cbn [fst snd] in F2. rewrite F2.
    injp H. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm" *)
Theorem evaluate_fperm : forall f g (p : prog a) (s : state a ffi_t) res s',
  evaluate (p, s) = (res, s') ->
  evaluate (fperm f g p, set_code (fperm_code f g (code s)) s) = (res, set_code (fperm_code f g (code s')) s').
Proof.
  intros f g p s res s' H.
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (evaluate_invariants _ _ _ _ H)))))))).
  apply (evaluate_fperm_aux f g (p, s) res s' _ H). intros fname args. apply lookup_code_fperm_code.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm'" *)
Theorem evaluate_fperm' : forall f g (p : prog a) (s : state a ffi_t) k,
  evaluate (fperm f g p, set_clock k (set_code (fperm_code f g (code s)) s)) =
  (fun '(x, s') => (x, set_code (fperm_code f g (code s')) s')) (evaluate (p, set_clock k s)).
Proof.
  intros f g p s k. destruct (evaluate (p, set_clock k s)) as [x s'] eqn:E.
  apply evaluate_fperm with (f := f) (g := g) in E. exact E.
Qed.


(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_fperm" *)
Theorem evaluate_decls_fperm : forall (s : state a ffi_t) (decs : list (decl a)) s' f g,
  evaluate_decls s decs = SOME s' ->
  evaluate_decls (set_code (fperm_code f g (code s)) s) (fperm_decs f g decs) =
  SOME (set_code (fperm_code f g (code s')) s').
Proof.
  intros s decs; revert s; induction decs as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros s s' f g H;
    cbn [evaluate_decls fperm_decs] in H |- *.
  - injection H as <-. reflexivity.
  - rewrite structs_sc. cbn [name params body fun_decl_return].
    destruct (_ && _); [|discriminate].
    pose proof (IH _ s' f g H) as F. cbn [code set_code] in F. rewrite fperm_code_FUPDATE in F.
    cbn [PAIR_MAP combin.I] in F. exact F.
  - rewrite sl_sc, eval_set_code. destruct (eval _ e) as [res|]; [|discriminate].
    destruct (bool_decide _); [|discriminate]. exact (IH _ s' f g H).
  - rewrite eshapes_sc, structs_sc. destruct (_ && _); [|discriminate]. exact (IH _ s' f g H).
  - exact (IH _ s' f g H).
Qed.

End Fperm.

(** ** [semantics] as a function of its clocked runs *)

Section SemOf.
Context {a : N} {ffi_t : Type}.

#[local] Instance behaviour_inhabited' : Inhabited behaviour := Fail.

Definition sem_of (F : N -> option (result a) * state a ffi_t) : behaviour :=
  if classical_dec (exists k,
       match fst (F k) with
       | SOME TimeOut => False
       | SOME (FinalFFI _) => False
       | SOME (Return _) => False
       | _ => True
       end)
  then Fail
  else
    match some (fun res => exists k t r outcome,
             F k = (r, t) /\
             match r with
             | SOME (FinalFFI e) => outcome = FFI_outcome e
             | SOME (Return _) => outcome = Success
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (snd (F k))))) UNIV))
    end.

Lemma semantics_sem_of (s : state a ffi_t) start :
  semantics s start = sem_of (fun k => evaluate (TailCall start [], set_clock k s)).
Proof. reflexivity. Qed.

Definition run_corr (F1 F2 : N -> option (result a) * state a ffi_t) : Prop :=
  forall k, exists k', fst (F1 k) = fst (F2 k') /\
                       io_events (ffi (snd (F1 k))) = io_events (ffi (snd (F2 k'))).

Lemma sem_of_corr F1 F2 : run_corr F1 F2 -> run_corr F2 F1 -> sem_of F1 = sem_of F2.
Proof.
  intros H12 H21; unfold sem_of.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P1 with P2
  end.
  2: { apply propositional_extensionality; split; intros [k Hk].
       - destruct (H21 k) as (k' & E & _). exists k'; rewrite <- E; exact Hk.
       - destruct (H12 k) as (k' & E & _). exists k'; rewrite <- E; exact Hk. }
  destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q1 with Q2
  end.
  - destruct (some _); [reflexivity|].
    match goal with |- Diverge (build_lprefix_lub ?X) = Diverge (build_lprefix_lub ?Y) =>
      replace X with Y; [reflexivity|] end.
    apply functional_extensionality; intros y; apply propositional_extensionality.
    unfold IMAGE, UNIV, pred_set.IN. split; intros [k [-> _]].
    + destruct (H21 k) as (k' & _ & E). exists k'; split; [rewrite E; reflexivity|exact Logic.I].
    + destruct (H12 k) as (k' & _ & E). exists k'; split; [rewrite E; reflexivity|exact Logic.I].
  - apply functional_extensionality; intros res; apply propositional_extensionality.
    split; intros [k [t [r [out [H1 [H2 H3]]]]]].
    + destruct (H21 k) as (k' & E1 & E2). rewrite H1 in E1, E2; cbn in E1, E2.
      exists k', (snd (F1 k')), r, out. split; [rewrite E1; destruct (F1 k'); reflexivity|].
      split; [exact H2|rewrite H3, E2; reflexivity].
    + destruct (H12 k) as (k' & E1 & E2). rewrite H1 in E1, E2; cbn in E1, E2.
      exists k', (snd (F2 k')), r, out. split; [rewrite E1; destruct (F2 k'); reflexivity|].
      split; [exact H2|rewrite H3, E2; reflexivity].
Qed.

Lemma run_corr_same F1 F2 :
  (forall k, fst (F1 k) = fst (F2 k) /\ io_events (ffi (snd (F1 k))) = io_events (ffi (snd (F2 k)))) ->
  run_corr F1 F2 /\ run_corr F2 F1.
Proof.
  intros H; split; intros k; exists k; destruct (H k) as [E1 E2]; split; congruence.
Qed.

End SemOf.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_fperm" *)
Theorem semantics_fperm : forall {a ffi_t} (s : state a ffi_t) f g start,
  semantics (set_code (fperm_code f g (code s)) s) (fperm_name f g start) = semantics s start.
Proof.
  intros a ffi_t s f g start. rewrite !semantics_sem_of.
  destruct (run_corr_same (fun k => evaluate (TailCall (fperm_name f g start) [], set_clock k (set_code (fperm_code f g (code s)) s)))
                          (fun k => evaluate (TailCall start [], set_clock k s))) as [H1 H2].
  - intros k. change (TailCall (fperm_name f g start) []) with (fperm f g (TailCall start [] : prog a)).
    rewrite evaluate_fperm'. destruct (evaluate (TailCall start [], set_clock k s)). split; reflexivity.
  - exact (sem_of_corr _ _ H1 H2).
Qed.

(** ** Declarations *)

Section Decls.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma ev_decls_cons s d (ds : list (decl a)) :
  evaluate_decls s (d :: ds) =
  match evaluate_decls s [d] with SOME s1 => evaluate_decls s1 ds | NONE => NONE end.
Proof. exact (evaluate_decls_append s [d] ds). Qed.

Definition kind_fde (d : decl a) : Prop :=
  match d with Name _ _ => False | _ => True end.

(** Two declarations of different kinds commute. *)
Lemma ev_decls_swap s (x y : decl a) ds :
  kind_fde x -> kind_fde y ->
  (is_function x = false \/ is_function y = false) ->
  (is_decl x = false \/ is_decl y = false) ->
  (is_exn_decl x = false \/ is_exn_decl y = false) ->
  evaluate_decls s (x :: y :: ds) = evaluate_decls s (y :: x :: ds).
Proof.
  intros Kx Ky Hf Hd He.
  destruct x as [fx|shx vx ex|eidx shx|]; destruct y as [fy|shy vy ey|eidy shy|]; cbn in *;
    try contradiction; try (destruct Hf as [C|C]; discriminate C);
    try (destruct Hd as [C|C]; discriminate C); try (destruct He as [C|C]; discriminate C).
  all: cbn [evaluate_decls].
  all: repeat match goal with
         | |- context [eval (set_locals FEMPTY (set_eshapes ?E ?s0)) ?e] =>
           rewrite (eval_state_cong (set_locals FEMPTY (set_eshapes E s0)) (set_locals FEMPTY s0)) by reflexivity
         | |- context [eval (set_locals FEMPTY (set_code ?E ?s0)) ?e] =>
           rewrite (eval_state_cong (set_locals FEMPTY (set_code E s0)) (set_locals FEMPTY s0)) by reflexivity
         end.
  all: repeat match goal with |- context [match ?x with _ => _ end] =>
         lazymatch x with context [evaluate_decls] => fail | _ => destruct x end end.
  all: try reflexivity.
Qed.

Definition kdiff (p d : decl a) : Prop :=
  kind_fde p /\ (is_function p = false \/ is_function d = false) /\
  (is_decl p = false \/ is_decl d = false) /\ (is_exn_decl p = false \/ is_exn_decl d = false).

Lemma ev_decls_move : forall (P : list (decl a)) d R s,
  kind_fde d -> Forall (fun p => kdiff p d) P ->
  evaluate_decls s (P ++ d :: R) = evaluate_decls s (d :: P ++ R).
Proof.
  induction P as [|p P IH]; intros d R s Kd HP; [reflexivity|].
  inversion HP as [|? ? (Kp & H1 & H2 & H3) HP']; subst.
  cbn [app]. rewrite ev_decls_cons. destruct (evaluate_decls s [p]) as [s1|] eqn:E1.
  - rewrite (IH d R s1 Kd HP').
    transitivity (evaluate_decls s (p :: d :: P ++ R)); [rewrite (ev_decls_cons s p), E1; reflexivity|].
    apply ev_decls_swap; try assumption.
  - transitivity (evaluate_decls s (p :: d :: P ++ R)); [rewrite (ev_decls_cons s p), E1; reflexivity|].
    apply ev_decls_swap; try assumption.
Qed.

Definition fde (d : decl a) : bool := is_function d || is_decl d || is_exn_decl d.

Lemma Forall_kdiff (P : list (decl a)) d (f : decl a -> bool) :
  is_true (EVERY fde P) -> (forall p, is_true (f p) -> kdiff p d) -> Forall (fun p => kdiff p d) (FILTER f P).
Proof.
  intros _ H. apply Forall_forall. intros p Hp. apply filter_In in Hp as [_ Hp]. apply H, Hp.
Qed.

Lemma FILTER_is_name_nil (ds : list (decl a)) : is_true (EVERY fde ds) -> FILTER is_name ds = [].
Proof.
  induction ds as [|d ds IH]; [reflexivity|]. intros H.
  change (is_true (fde d && EVERY fde ds)) in H. apply Bool.andb_true_iff in H as [H1 H2].
  destruct d; cbn in *; try discriminate; apply IH, H2.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_evaluate" *)
Theorem resort_decls_evaluate : forall (s : state a ffi_t) (decs : list (decl a)),
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) decs) ->
  evaluate_decls s (resort_decls decs) = evaluate_decls s decs.
Proof.
  intros s decs; revert s; induction decs as [|d ds IH]; intros s Hev; [reflexivity|].
  change (is_true (fde d && EVERY fde ds)) in Hev. apply Bool.andb_true_iff in Hev as [Hd Hds].
  assert (IH' : forall s1, evaluate_decls s1 (resort_decls ds) = evaluate_decls s1 ds) by (intros; apply IH, Hds).
  clear IH. rename IH' into IH. unfold resort_decls in *. rewrite (FILTER_is_name_nil _ Hds) in IH.
  destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [filter is_name is_exn_decl is_decl is_function app] in *;
    rewrite (FILTER_is_name_nil _ Hds); cbn [app].
  - rewrite app_assoc. rewrite ev_decls_move.
    + rewrite ev_decls_cons, (ev_decls_cons s (Function fi) ds).
      destruct (evaluate_decls s [Function fi]); [|reflexivity].
      rewrite <- app_assoc. apply IH.
    + exact Logic.I.
    + apply Forall_app. split; apply Forall_kdiff; try exact Hds;
        intros [] Hp; cbn in Hp; try discriminate; repeat split; cbn; auto.
  - rewrite ev_decls_move.
    + rewrite ev_decls_cons, (ev_decls_cons s (Decl sh v0 e) ds).
      destruct (evaluate_decls s [Decl sh v0 e]); [|reflexivity]. apply IH.
    + exact Logic.I.
    + apply Forall_kdiff; try exact Hds. intros [] Hp; cbn in Hp; try discriminate; repeat split; cbn; auto.
  - rewrite ev_decls_cons, (ev_decls_cons s (ExnDecl eid sh) ds).
    destruct (evaluate_decls s [ExnDecl eid sh]); [|reflexivity]. apply IH.
  - discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_one_fun_last" *)
Theorem evaluate_decls_one_fun_last : forall (y : decl a) (xs : list (decl a)) (s : state a ffi_t),
  is_true (is_function y) /\
  is_true (EVERY (fun d => match d with Decl _ _ _ => true | ExnDecl _ _ => true | _ => false end) xs) ->
  evaluate_decls s (xs ++ [y]) = evaluate_decls s (y :: xs).
Proof.
  intros y xs s [Hy Hxs]. rewrite ev_decls_move, app_nil_r; [reflexivity| |].
  - destruct y; try discriminate; exact Logic.I.
  - apply Forall_forall. intros p Hp. induction xs as [|x xs IH]; [destruct Hp|].
    cbn in Hxs. apply Bool.andb_true_iff in Hxs as [Hx Hxs]. destruct Hp as [E|Hp]; [|exact (IH Hxs Hp)].
    subst x. destruct y; try discriminate; destruct p; try discriminate; repeat split; cbn; auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_evaluate_IMP" *)
Theorem resort_decls_evaluate_IMP : forall (s : state a ffi_t) (decs : list (decl a)) s',
  evaluate_decls s decs = SOME s' /\
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) decs) ->
  evaluate_decls s (resort_decls decs) = SOME s'.
Proof. intros s decs s' [H1 H2]. rewrite resort_decls_evaluate by exact H2. exact H1. Qed.

End Decls.

#[local] Instance decl_inhabited {a} : Inhabited (decl a) := Name ARB [].

Section CompileDecs.
Context {a : N}.

Ltac cd_step E :=
  match goal with
  | H : context [compile_decs ?c ?l] |- _ =>
    destruct (compile_decs c l) as [?d1 [?f1 [?e1 ?c1]]] eqn:E; cbn beta iota zeta in H
  | |- context [compile_decs ?c ?l] =>
    destruct (compile_decs c l) as [?d1 [?f1 [?e1 ?c1]]] eqn:E; cbn beta iota zeta
  end.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_functions_thm" *)
Theorem compile_decs_functions_thm : forall (ctxt : context a) fdecs decls funs exns ctxt',
  compile_decs ctxt fdecs = (decls, (funs, (exns, ctxt'))) /\ is_true (EVERY is_function fdecs) ->
  decls = [] /\ exns = [] /\ ctxt' = ctxt /\
  funs = MAP (fun x => match x with
                       | Function fi => Function {| name := name fi; inline := inline fi; export := export fi;
                                                    params := params fi; body := compile ctxt (body fi);
                                                    fun_decl_return := fun_decl_return fi |}
                       | _ => ARB end) fdecs.
Proof.
  intros ctxt fdecs; induction fdecs as [|d ds IH]; intros decls funs exns ctxt' [H Hf].
  - cbn in H. injection H as <- <- <- <-. repeat split; reflexivity.
  - cbn in Hf. apply Bool.andb_true_iff in Hf as [Hd Hf]. destruct d as [fi| | |]; try discriminate.
    cbn [compile_decs] in H. cd_step E. injection H as <- <- <- <-.
    destruct (IH _ _ _ _ (conj eq_refl Hf)) as (-> & -> & -> & ->). repeat split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_decls_thm" *)
Theorem compile_decs_decls_thm : forall (ctxt : context a) fdecs decls funs exns ctxt',
  compile_decs ctxt fdecs = (decls, (funs, (exns, ctxt'))) /\
  is_true (EVERY (fun d => negb (is_function d)) fdecs) ->
  funs = [].
Proof.
  intros ctxt fdecs; revert ctxt; induction fdecs as [|d ds IH]; intros ctxt decls funs exns ctxt' [H Hf].
  - cbn in H. injection H as <- <- <- <-. reflexivity.
  - cbn in Hf. apply Bool.andb_true_iff in Hf as [Hd Hf].
    destruct d as [fi|sh v0 e|eid sh|nm flds]; try discriminate; cbn [compile_decs] in H.
    + cd_step E. injection H as <- <- <- <-. exact (IH _ _ _ _ _ (conj E Hf)).
    + cd_step E. injection H as <- <- <- <-. exact (IH _ _ _ _ _ (conj E Hf)).
    + exact (IH _ _ _ _ _ (conj H Hf)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_EVERY_is_function" *)
Theorem compile_decs_EVERY_is_function : forall (ctxt : context a) decs decls funs exns ctxt',
  compile_decs ctxt decs = (decls, (funs, (exns, ctxt'))) -> is_true (EVERY is_function funs).
Proof.
  intros ctxt decs; revert ctxt; induction decs as [|d ds IH]; intros ctxt decls funs exns ctxt' H.
  - cbn in H. injection H as <- <- <- <-. reflexivity.
  - destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs] in H; [cd_step E|cd_step E|cd_step E|];
      try (injection H as <- <- <- <-); try exact (IH _ _ _ _ _ E); try exact (IH _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_EVERY" *)
Theorem compile_decs_EVERY : forall (P : decl a -> bool) (ctxt : context a) decs decls funs exns ctxt',
  compile_decs ctxt decs = (decls, (funs, (exns, ctxt'))) /\
  is_true (EVERY (fun d => ⌜forall fi (ctxt : context a), d = Function fi ->
              is_true (P (Function {| name := name fi; inline := inline fi; export := export fi;
                                      params := params fi; body := compile ctxt (body fi);
                                      fun_decl_return := fun_decl_return fi |}))⌝) decs) ->
  is_true (EVERY P funs).
Proof.
  intros P ctxt decs; revert ctxt; induction decs as [|d ds IH]; intros ctxt decls funs exns ctxt' [H Hf].
  - cbn in H. injection H as <- <- <- <-. reflexivity.
  - cbn in Hf. apply Bool.andb_true_iff in Hf as [Hd Hf]. apply bool_decide_spec in Hd.
    destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs] in H; [cd_step E|cd_step E|cd_step E|];
      try (injection H as <- <- <- <-); try exact (IH _ _ _ _ _ (conj E Hf)); try exact (IH _ _ _ _ _ (conj H Hf)).
    all: cbn; apply Bool.andb_true_iff; split; [exact (Hd fi ctxt eq_refl)|exact (IH _ _ _ _ _ (conj E Hf))].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decls_append" *)
Theorem compile_decls_append : forall (decs' : list (decl a)) (ctxt : context a) decs,
  compile_decs ctxt (decs ++ decs') =
  let '(decls, (funs, (exns, ctxt'))) := compile_decs ctxt decs in
  let '(decls', (funs', (exns', ctxt''))) := compile_decs ctxt' decs' in
  (decls ++ decls', (funs ++ funs', (exns ++ exns', ctxt''))).
Proof.
  intros decs' ctxt decs; revert ctxt; induction decs as [|d ds IH]; intros ctxt.
  - cbn [app compile_decs]. destruct (compile_decs ctxt decs') as [? [? [? ?]]]. reflexivity.
  - destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [app compile_decs]; rewrite IH;
      match goal with |- context [compile_decs ?c ds] =>
        destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] end; cbn beta iota zeta;
      destruct (compile_decs c1 decs') as [d2 [f2 [e2 c2]]]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decls_append_IMP" *)
Theorem compile_decls_append_IMP : forall (ctxt : context a) decs decs' X,
  compile_decs ctxt (decs ++ decs') = X ->
  (let '(decls, (funs, (exns, ctxt'))) := compile_decs ctxt decs in
   let '(decls', (funs', (exns', ctxt''))) := compile_decs ctxt' decs' in
   (decls ++ decls', (funs ++ funs', (exns ++ exns', ctxt'')))) = X.
Proof. intros ctxt decs decs' X <-. symmetry; apply compile_decls_append. Qed.

(** HOL's statement has a vacuous quantifier [ys] (of an arbitrary type),
    kept here. *)
(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_decls" *)
Theorem fperm_decs_decls : forall {C : Type} f g (xs : list (decl a)) (ys : C),
  is_true (EVERY (negb ∘ is_function) xs) -> fperm_decs f g xs = xs.
Proof.
  intros C f g xs ys; induction xs as [|d ds IH]; intros H; [reflexivity|].
  cbn in H. apply Bool.andb_true_iff in H as [Hd H].
  destruct d; try discriminate; cbn [fperm_decs]; rewrite (IH H); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_decs_FILTER_is_function" *)
Theorem fperm_decs_FILTER_is_function : forall f g (decs : list (decl a)),
  fperm_decs f g (FILTER is_function decs) = FILTER is_function (fperm_decs f g decs).
Proof. intros f g decs; induction decs as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_FILTER_exn_decl" *)
Theorem functions_FILTER_exn_decl : forall prog : list (decl a), functions (FILTER is_exn_decl prog) = [].
Proof. intros prog; induction prog as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_FILTER_is_name" *)
Theorem functions_FILTER_is_name : forall prog : list (decl a), functions (FILTER is_name prog) = [].
Proof. intros prog; induction prog as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_preserve_functions" *)
Theorem resort_decls_preserve_functions : forall code0 : list (decl a),
  functions (resort_decls code0) = functions code0.
Proof.
  intros code0. unfold resort_decls.
  rewrite !functions_append, functions_FILTER_is_name, functions_FILTER_exn_decl, functions_FILTER',
    functions_FILTER. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_preserve_functions" *)
Theorem compile_decs_preserve_functions : forall (code0 : list (decl a)) ctxt decs funs exns ctxt',
  compile_decs ctxt code0 = (decs, (funs, (exns, ctxt'))) ->
  MAP FST (functions funs) = MAP FST (functions code0).
Proof.
  intros code0; induction code0 as [|d ds IH]; intros ctxt decs funs exns ctxt' H.
  - cbn in H. injection H as <- <- <- <-. reflexivity.
  - destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs] in H;
      try (match type of H with context [compile_decs ?c ds] =>
             destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] eqn:E end;
           injection H as <- <- <- <-); cbn [functions MAP List.map FST fst name].
  all: try (erewrite IH by eassumption; reflexivity).
  all: exact (IH _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "new_main_name_correct" *)
Theorem new_main_name_correct : forall code0 : list (decl a),
  is_true (MEM (new_main_name code0) (MAP FST (functions code0))) -> False.
Proof. intros code0. unfold new_main_name. apply fresh_name_correct. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_exns_are_exns" *)
Theorem compile_decs_exns_are_exns : forall (ctxt : context a) code0 decls funs exns ctxt',
  compile_decs ctxt code0 = (decls, (funs, (exns, ctxt'))) -> exns = FILTER is_exn_decl code0.
Proof.
  intros ctxt code0; revert ctxt; induction code0 as [|d ds IH]; intros ctxt decls funs exns ctxt' H.
  - cbn in H. injection H as <- <- <- <-. reflexivity.
  - destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs filter is_exn_decl] in H |- *;
      try (match type of H with context [compile_decs ?c ds] =>
             destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] eqn:E end;
           injection H as <- <- <- <-); try f_equal; eauto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_FILTER_decs" *)
Theorem compile_decs_FILTER_decs : forall (ctxt : context a) code0 decls funs exns ctxt',
  compile_decs ctxt code0 = (decls, (funs, (exns, ctxt'))) ->
  compile_decs ctxt (FILTER is_decl code0) = (decls, ([], ([], ctxt'))).
Proof.
  intros ctxt code0; revert ctxt; induction code0 as [|d ds IH]; intros ctxt decls funs exns ctxt' H.
  - cbn in H |- *. injection H as <- <- <- <-. reflexivity.
  - destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs filter is_decl] in H |- *;
      try (match type of H with context [compile_decs ?c ds] =>
             destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] eqn:E end;
           injection H as <- <- <- <-); eauto.
    rewrite (IH _ _ _ _ _ E). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_append" *)
Theorem dec_shapes_append : forall xs ys : list (decl a), dec_shapes (xs ++ ys) = dec_shapes xs ++ dec_shapes ys.
Proof. intros xs ys; induction xs as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_functions" *)
Theorem dec_shapes_functions : forall xs : list (decl a), is_true (EVERY is_function xs) -> dec_shapes xs = [].
Proof.
  intros xs; induction xs as [|d ds IH]; intros H; [reflexivity|].
  cbn in H. apply Bool.andb_true_iff in H as [Hd H]. destruct d; try discriminate. exact (IH H).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_FILTER" *)
Theorem dec_shapes_FILTER : forall xs : list (decl a),
  dec_shapes (FILTER (negb ∘ is_function) xs) = dec_shapes xs /\
  dec_shapes (FILTER is_name xs) = [] /\
  dec_shapes (FILTER is_decl xs) = dec_shapes xs /\
  dec_shapes (FILTER is_exn_decl xs) = [].
Proof.
  intros xs; induction xs as [|d ds (IH1 & IH2 & IH3 & IH4)]; [repeat split|].
  destruct d; cbn; rewrite ?IH1, ?IH2, ?IH3, ?IH4; repeat split.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_fperm_decs" *)
Theorem dec_shapes_fperm_decs : forall f g (xs : list (decl a)), dec_shapes (fperm_decs f g xs) = dec_shapes xs.
Proof. intros f g xs; induction xs as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "dec_shapes_resort_decls_def" *)
Theorem dec_shapes_resort_decls_def : forall xs : list (decl a), dec_shapes (resort_decls xs) = dec_shapes xs.
Proof.
  intros xs. unfold resort_decls. rewrite !dec_shapes_append.
  destruct (dec_shapes_FILTER xs) as (_ & -> & -> & ->).
  rewrite (dec_shapes_functions (FILTER is_function xs)); [cbn; rewrite app_nil_r; reflexivity|].
  induction xs as [|d ds IH]; [reflexivity|]. destruct d; cbn; exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "MEM_functions" *)
Theorem MEM_functions : forall (t : funname * (list (varname * shape) * (prog a * shape))) (decs : list (decl a)),
  is_true (MEM t (functions decs)) ->
  exists fi, is_true (MEM (Function fi) decs) /\ t = (name fi, (params fi, (body fi, fun_decl_return fi))).
Proof.
  intros t decs; rewrite MEM_is_true_In. induction decs as [|d ds IH]; [intros []|].
  destruct d as [fi| | |]; cbn [functions]; intros H.
  - destruct H as [<-|H].
    + exists fi. split; [apply MEM_is_true_In; left; reflexivity|reflexivity].
    + destruct (IH H) as (fi' & H1 & H2). exists fi'. split; [|exact H2].
      apply MEM_is_true_In in H1. apply MEM_is_true_In. right; exact H1.
  - destruct (IH H) as (fi' & H1 & H2). exists fi'. split; [|exact H2].
    apply MEM_is_true_In in H1. apply MEM_is_true_In. right; exact H1.
  - destruct (IH H) as (fi' & H1 & H2). exists fi'. split; [|exact H2].
    apply MEM_is_true_In in H1. apply MEM_is_true_In. right; exact H1.
  - destruct (IH H) as (fi' & H1 & H2). exists fi'. split; [|exact H2].
    apply MEM_is_true_In in H1. apply MEM_is_true_In. right; exact H1.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "EVERY_fperm_decs" *)
Theorem EVERY_fperm_decs : forall (P : decl a -> bool) f g (decs : list (decl a)),
  is_true (EVERY (fun d => implb (negb (is_function d)) (P d)) decs) /\
  is_true (EVERY (fun d => ⌜forall fi, d = Function fi ->
              is_true (P (Function {| name := fperm_name f g (name fi); inline := inline fi;
                                      export := export fi; params := params fi;
                                      body := fperm f g (body fi); fun_decl_return := fun_decl_return fi |}))⌝)
             decs) ->
  is_true (EVERY P (fperm_decs f g decs)).
Proof.
  intros P f g decs; induction decs as [|d ds IH]; intros [H1 H2]; [reflexivity|].
  cbn in H1, H2. apply Bool.andb_true_iff in H1 as [Hd1 H1]. apply Bool.andb_true_iff in H2 as [Hd2 H2].
  apply bool_decide_spec in Hd2.
  destruct d as [fi| | |]; cbn [fperm_decs EVERY]; apply Bool.andb_true_iff; (split; [|exact (IH (conj H1 H2))]);
    try exact Hd1. exact (Hd2 fi eq_refl).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_append" *)
Theorem exceptions_append : forall ds ds' : list (decl a), exceptions (ds ++ ds') = exceptions ds ++ exceptions ds'.
Proof. intros ds ds'; induction ds as [|[] l IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_FILTER_is_function" *)
Theorem exceptions_FILTER_is_function : forall decs : list (decl a),
  exceptions (FILTER is_function decs) = [] /\
  exceptions (FILTER (negb ∘ is_function) decs) = exceptions decs /\
  exceptions (FILTER is_exn_decl decs) = exceptions decs /\
  exceptions (FILTER is_name decs) = [] /\
  exceptions (FILTER is_decl decs) = [].
Proof.
  intros decs; induction decs as [|d ds (IH1 & IH2 & IH3 & IH4 & IH5)]; [repeat split|].
  destruct d; cbn; rewrite ?IH1, ?IH2, ?IH3, ?IH4, ?IH5; repeat split.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "not_is_function" *)
Theorem not_is_function : forall x : decl a,
  (is_true (is_name x) -> ~ is_true (is_function x)) /\
  (is_true (is_decl x) -> ~ is_true (is_function x)) /\
  (is_true (is_exn_decl x) -> ~ is_true (is_function x)).
Proof. intros []; cbn; repeat split; intros H C; discriminate. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "decl_distinct" *)
Theorem decl_distinct : forall x : decl a,
  (is_true (is_decl x) /\ is_true (is_name x) <-> False) /\
  (is_true (is_decl x) /\ is_true (is_function x) <-> False) /\
  (is_true (is_decl x) /\ is_true (is_exn_decl x) <-> False).
Proof. intros []; cbn; unfold is_true; intuition discriminate. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FILTER_decs_fperm_decs" *)
Theorem FILTER_decs_fperm_decs : forall f g (code0 : list (decl a)),
  FILTER (negb ∘ is_function) (fperm_decs f g code0) = FILTER (negb ∘ is_function) code0.
Proof. intros f g code0; induction code0 as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_filter_nil" *)
Theorem functions_filter_nil : forall decls : list (decl a), functions (FILTER (negb ∘ is_function) decls) = [].
Proof. intros decls; induction decls as [|[] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

End CompileDecs.

Section AlistHelpers.
Context {K Y Z T W : Type} `{EqDecision K}.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALOOKUP_MAP3" *)
Theorem ALOOKUP_MAP3 : forall (f : Z -> W) (al : list (K * (Y * Z))),
  ALOOKUP (MAP (fun '(x, (y, z)) => (x, (y, f z))) al) = OPTION_MAP (I ## f) ∘ ALOOKUP al.
Proof.
  intros f al. apply functional_extensionality; intros k.
  induction al as [|[x [y z]] l IH]; [reflexivity|]. cbn. destruct (decide (x = k)); [reflexivity|exact IH].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALOOKUP_MAP4" *)
Theorem ALOOKUP_MAP4 : forall (f : Z -> W) (al : list (K * (Y * (Z * T)))),
  ALOOKUP (MAP (fun '(x, (y, (z, t))) => (x, (y, (f z, t)))) al) = OPTION_MAP (I ## (f ## I)) ∘ ALOOKUP al.
Proof.
  intros f al. apply functional_extensionality; intros k.
  induction al as [|[x [y [z t]]] l IH]; [reflexivity|]. cbn. destruct (decide (x = k)); [reflexivity|exact IH].
Qed.

End AlistHelpers.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "map_pick_up_first" *)
Theorem map_pick_up_first : forall {A B C D A' B' C' D'} (f1 : A -> A') (f2 : B -> B') (f3 : C -> C') (f4 : D -> D')
  (l : list (A * (B * (C * D)))),
  MAP FST (MAP (fun '(x, (y, (z, t))) => (f1 x, (f2 y, (f3 z, f4 t)))) l) = MAP f1 (MAP FST l).
Proof. intros; induction l as [|[x [y [z t]]] l IH]; cbn; [reflexivity|]. f_equal; exact IH. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "tuple_4_o" *)
Theorem tuple_4_o : forall {A B C D A1 B1 C1 D1 A2 B2 C2 D2}
  (f1 : A1 -> A2) (f2 : B1 -> B2) (f3 : C1 -> C2) (f4 : D1 -> D2)
  (g1 : A -> A1) (g2 : B -> B1) (g3 : C -> C1) (g4 : D -> D1),
  (fun '(x, (y, (z, t))) => (f1 x, (f2 y, (f3 z, f4 t)))) ∘ (fun '(x, (y, (z, t))) => (g1 x, (g2 y, (g3 z, g4 t)))) =
  (fun '(x, (y, (z, t))) => (f1 (g1 x), (f2 (g2 y), (f3 (g3 z), f4 (g4 t))))).
Proof. intros. apply functional_extensionality; intros [x [y [z t]]]; reflexivity. Qed.

Section CompileTop.
Context {a : N}.

Lemma EVERY_app_ {A} (P : A -> bool) l1 l2 : EVERY P (l1 ++ l2) = EVERY P l1 && EVERY P l2.
Proof. induction l1 as [|x l IH]; cbn; [reflexivity|]. rewrite IH. apply Bool.andb_assoc. Qed.

Lemma EVERY_FILTER_self {A} (P : A -> bool) l : is_true (EVERY P (FILTER P l)).
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|]. destruct (P x) eqn:E; cbn; [rewrite E; exact IH|exact IH].
Qed.

Lemma EVERY_mono {A} (P Q : A -> bool) l : (forall x, is_true (P x) -> is_true (Q x)) ->
  is_true (EVERY P l) -> is_true (EVERY Q l).
Proof.
  intros H; induction l as [|x l IH]; cbn; [reflexivity|].
  unfold is_true; rewrite !Bool.andb_true_iff. intros [H1 H2]; split; [apply H, H1|apply IH, H2].
Qed.

Lemma exceptions_fperm_decs f g (l : list (decl a)) : exceptions (fperm_decs f g l) = exceptions l.
Proof. induction l as [|[] l IH]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma exceptions_functions (l : list (decl a)) : is_true (EVERY is_function l) -> exceptions l = [].
Proof.
  induction l as [|d l IH]; intros H; [reflexivity|]. cbn in H. apply Bool.andb_true_iff in H as [Hd H].
  destruct d; try discriminate. exact (IH H).
Qed.

Lemma functions_exns (l : list (decl a)) : is_true (EVERY is_exn_decl l) -> functions l = [].
Proof.
  induction l as [|d l IH]; intros H; [reflexivity|]. cbn in H. apply Bool.andb_true_iff in H as [Hd H].
  destruct d; try discriminate. exact (IH H).
Qed.

Ltac ct_unfold E :=
  unfold compile_top;
  match goal with |- context [ALOOKUP (functions ?c) ?st] =>
    destruct (ALOOKUP (functions c) st) as [[?args [?bdy ?rsh]]|] eqn:?EA end;
  cbn beta iota zeta;
  [match goal with |- context [compile_decs ?c ?l] =>
     destruct (compile_decs c l) as [?decls [?funs [?exns ?ctxt]]] eqn:E end; cbn beta iota zeta|].

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_only_functions_or_exns" *)
Theorem compile_top_only_functions_or_exns : forall (code0 : list (decl a)) start,
  is_true (EVERY (fun d => is_function d || is_exn_decl d) (compile_top code0 start)).
Proof.
  intros code0 start. ct_unfold E; [|reflexivity].
  rewrite EVERY_app_. apply Bool.andb_true_iff. split.
  - rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ E).
    apply (EVERY_mono is_exn_decl); [intros x Hx; rewrite Hx; apply Bool.orb_true_r|apply EVERY_FILTER_self].
  - cbn [EVERY]. apply Bool.andb_true_iff. split; [reflexivity|].
    apply (EVERY_mono is_function); [intros x Hx; rewrite Hx; reflexivity|].
    exact (compile_decs_EVERY_is_function _ _ _ _ _ _ E).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "exceptions_compile_top" *)
Theorem exceptions_compile_top : forall (code0 : list (decl a)) start x,
  ALOOKUP (functions code0) start = SOME x -> exceptions (compile_top code0 start) = exceptions code0.
Proof.
  intros code0 start x Hx. ct_unfold E; [|congruence].
  rewrite exceptions_append. cbn [exceptions].
  rewrite (exceptions_functions funs (compile_decs_EVERY_is_function _ _ _ _ _ _ E)), app_nil_r.
  rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ E).
  rewrite (proj1 (proj2 (proj2 (exceptions_FILTER_is_function _)))), exceptions_fperm_decs.
  unfold resort_decls. rewrite !exceptions_append.
  destruct (exceptions_FILTER_is_function code0) as (-> & _ & -> & -> & ->). rewrite app_nil_r. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "ALL_DISTINCT_compile_top" *)
Theorem ALL_DISTINCT_compile_top : forall start (code0 : list (decl a)),
  is_true (ALL_DISTINCT (MAP FST (functions code0))) ->
  is_true (ALL_DISTINCT (MAP FST (functions (compile_top code0 start)))).
Proof.
  intros start code0 Hd. ct_unfold E; [|reflexivity].
  rewrite functions_append. rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ E).
  rewrite functions_FILTER_exn_decl. cbn [app functions MAP List.map FST fst name].
  rewrite (compile_decs_preserve_functions _ _ _ _ _ _ E).
  pose proof (ALL_DISTINCT_fperm_decs start (new_main_name code0) (resort_decls code0)) as HA.
  rewrite resort_decls_preserve_functions in HA. specialize (HA Hd).
  cbn [ALL_DISTINCT]. apply Bool.andb_true_iff. split; [|exact HA].
  apply Bool.negb_true_iff. apply Bool.not_true_iff_false. intros Hm.
  rewrite functions_fperm_decs, map_pick_up_first, resort_decls_preserve_functions in Hm.
  apply MEM_is_true_In, in_map_iff in Hm as (n & Hn & Hin).
  apply (new_main_name_correct code0). apply MEM_is_true_In.
  unfold fperm_name in Hn. destruct (decide (start = n)) as [<-|H1].
  - rewrite Hn. exact Hin.
  - destruct (decide (new_main_name code0 = n)) as [<-|H2]; [exact Hin|congruence].
Qed.

End CompileTop.

(** ** Localised programs *)

Section Localised.
Context {a : N}.

(** Induction on programs with an induction hypothesis for the exception
    handler of [Call]. *)
Definition prog_nested_ind (P : prog a -> Prop)
    (Hskip : P Skip)
    (Hdec : forall v s e p, P p -> P (Dec v s e p))
    (Hassign : forall vk v e, P (Assign vk v e))
    (Hprim : forall v op es, P (Primitive v op es))
    (Hstore : forall e1 e2, P (Store e1 e2))
    (Hstore32 : forall e1 e2, P (Store32 e1 e2))
    (Hstoreb : forall e1 e2, P (StoreByte e1 e2))
    (Hseq : forall p q, P p -> P q -> P (Seq p q))
    (Hif : forall e p q, P p -> P q -> P (If e p q))
    (Hwhile : forall e p, P p -> P (While e p))
    (Hbreak : P panLang.Break) (Hcont : P panLang.Continue)
    (Hcall : forall ct f args,
        match ct with Some (_, Some (_, (_, h))) => P h | _ => True end -> P (Call ct f args))
    (Hdeccall : forall v s f args p, P p -> P (DecCall v s f args p))
    (Hext : forall f e1 e2 e3 e4, P (ExtCall f e1 e2 e3 e4))
    (Hraise : forall eid e, P (Raise eid e))
    (Hret : forall e, P (panLang.Return e))
    (Hshl : forall op vk v e, P (ShMemLoad op vk v e))
    (Hshs : forall op e1 e2, P (ShMemStore op e1 e2))
    (Htick : P Tick) (Hannot : forall s1 s2, P (Annot s1 s2)) : forall p, P p :=
  fix go (p : prog a) : P p :=
    match p with
    | Skip => Hskip
    | Dec v s e p => Hdec v s e p (go p)
    | Assign vk v e => Hassign vk v e
    | Primitive v op es => Hprim v op es
    | Store e1 e2 => Hstore e1 e2
    | Store32 e1 e2 => Hstore32 e1 e2
    | StoreByte e1 e2 => Hstoreb e1 e2
    | Seq p q => Hseq p q (go p) (go q)
    | If e p q => Hif e p q (go p) (go q)
    | While e p => Hwhile e p (go p)
    | panLang.Break => Hbreak
    | panLang.Continue => Hcont
    | Call ct f args =>
        Hcall ct f args
          (match ct as ct0 return
                 (match ct0 with Some (_, Some (_, (_, h))) => P h | _ => True end) with
           | Some (_, Some (_, (_, h))) => go h
           | Some (_, None) => Logic.I
           | None => Logic.I
           end)
    | DecCall v s f args p => Hdeccall v s f args p (go p)
    | ExtCall f e1 e2 e3 e4 => Hext f e1 e2 e3 e4
    | Raise eid e => Hraise eid e
    | panLang.Return e => Hret e
    | ShMemLoad op vk v e => Hshl op vk v e
    | ShMemStore op e1 e2 => Hshs op e1 e2
    | Tick => Htick
    | Annot s1 s2 => Hannot s1 s2
    end.

Lemma EVERY_MAP_ {A B} (P : B -> bool) (f : A -> B) l :
  Forall (fun x => is_true (P (f x))) l -> is_true (EVERY P (MAP f l)).
Proof. induction 1 as [|x l Hx _ IH]; cbn; [reflexivity|]. rewrite Hx; exact IH. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_localised" *)
Theorem compile_exp_localised : forall (ctxt : context a) e, is_true (localised_exp (compile_exp ctxt e)).
Proof.
  intros ctxt e. induction e using exp_nested_ind; unfold localised_exp in *; cbn [compile_exp every_exp].
  all: try reflexivity.
  all: try (destruct vk; [reflexivity|]; destruct (FLOOKUP _ _) as [[sh addr]|]; reflexivity).
  all: repeat (apply Bool.andb_true_iff; split); try reflexivity; try assumption.
  all: apply EVERY_MAP_; eapply Forall_impl; [|eassumption]; intros x Hx; exact Hx.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "localised_exp_shape_val" *)
Theorem localised_exp_shape_val :
  (forall sh, is_true (localised_exp (shape_val sh : exp a))) /\
  (forall shs, is_true (EVERY localised_exp (shape_vals shs : list (exp a)))).
Proof.
  assert (G : forall sh, is_true (localised_exp (shape_val sh : exp a))).
  { intros sh; induction sh as [|l Hl|nm] using shape_nested_ind; [reflexivity| |reflexivity].
    rewrite shape_val_Comb. unfold localised_exp in *. cbn [every_exp]. cbn beta iota.
    induction Hl as [|x l Hx _ IH]; [reflexivity|]. cbn [shape_vals EVERY]. rewrite Hx. exact IH. }
  split; [exact G|]. intros shs; induction shs as [|sh shs IH]; [reflexivity|].
  cbn [shape_vals EVERY]. rewrite G. exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_localised" *)
Theorem compile_localised : forall (ctxt : context a) body, is_true (localised_prog (compile ctxt body)).
Proof.
  intros ctxt body. induction body using prog_nested_ind; cbn [compile localised_prog]; cbn zeta.
  all: try reflexivity.
  all: repeat (apply Bool.andb_true_iff; split); try reflexivity; try assumption;
       try apply compile_exp_localised.
  all: try (destruct vk); try (destruct ct as [[[[[|] rt]|] [[eid' [evar hp]]|]]|]); cbn beta iota.
  all: repeat match goal with |- context [match FLOOKUP ?m ?k with _ => _ end] =>
         destruct (FLOOKUP m k) as [[[| |] ?addr]|] end; cbn beta iota zeta.
  all: repeat first [ reflexivity | assumption | apply compile_exp_localised
                    | apply (proj1 localised_exp_shape_val)
                    | (apply EVERY_MAP_, Forall_forall; intros; apply compile_exp_localised)
                    | (apply Bool.andb_true_iff; split)
                    | progress cbn [localised_prog] ].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_localised" *)
Theorem compile_decs_localised : forall (ctxt : context a) code0,
  is_true (EVERY (localised_prog ∘ FST ∘ SND ∘ SND) (functions (FST (SND (compile_decs ctxt code0))))).
Proof.
  intros ctxt code0; revert ctxt; induction code0 as [|d ds IH]; intros ctxt; [reflexivity|].
  destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs]; cbn zeta;
    try (match goal with |- context [compile_decs ?c ds] =>
           specialize (IH c); destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] end);
    cbn [fst snd functions EVERY body]; try exact IH.
  apply Bool.andb_true_iff; split; [apply compile_localised|exact IH].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_localised'" *)
Theorem compile_decs_localised' : forall (ctxt : context a) code0,
  is_true (EVERY (localised_prog ∘ FST ∘ SND ∘ SND) (functions (FST (SND (SND (compile_decs ctxt code0)))))).
Proof.
  intros ctxt code0; revert ctxt; induction code0 as [|d ds IH]; intros ctxt; [reflexivity|].
  destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs]; cbn zeta;
    try (match goal with |- context [compile_decs ?c ds] =>
           specialize (IH c); destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] end);
    cbn [fst snd functions EVERY body]; exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_decs_localised_main" *)
Theorem compile_decs_localised_main : forall (ctxt : context a) code0,
  is_true (EVERY localised_prog (FST (compile_decs ctxt code0))).
Proof.
  intros ctxt code0; revert ctxt; induction code0 as [|d ds IH]; intros ctxt; [reflexivity|].
  destruct d as [fi|sh v0 e|eid sh|nm flds]; cbn [compile_decs]; cbn zeta;
    try (match goal with |- context [compile_decs ?c ds] =>
           specialize (IH c); destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] end);
    cbn [fst snd EVERY]; try exact IH.
  apply Bool.andb_true_iff; split; [|exact IH]. cbn [localised_prog].
  apply Bool.andb_true_iff; split; [reflexivity|apply compile_exp_localised].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "nested_seqs_localised" *)
Theorem nested_seqs_localised : forall ps : list (prog a),
  localised_prog (nested_seq ps) = EVERY localised_prog ps.
Proof. intros ps; induction ps as [|p ps IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_localised" *)
Theorem compile_top_localised : forall (pan_code : list (decl a)) main,
  is_true (EVERY (localised_prog ∘ FST ∘ SND ∘ SND) (functions (compile_top pan_code main))).
Proof.
  intros pan_code main. unfold compile_top.
  destruct (ALOOKUP (functions pan_code) main) as [[args [bdy rsh]]|]; [|reflexivity]. cbn zeta.
  match goal with |- context [compile_decs ?c ?l] =>
    pose proof (compile_decs_localised c l) as H1; pose proof (compile_decs_localised' c l) as H2;
    pose proof (compile_decs_localised_main c l) as H3;
    destruct (compile_decs c l) as [decls [funs [exns ctxt]]] end.
  cbn [fst snd] in H1, H2, H3. rewrite functions_append, EVERY_app_. cbn [functions EVERY].
  rewrite H2. cbn [andb]. apply Bool.andb_true_iff; split; [|exact H1].
  cbn [fst snd body localised_prog]. rewrite nested_seqs_localised, H3. cbn [andb].
  repeat (apply Bool.andb_true_iff; split); try reflexivity.
  apply EVERY_MAP_. apply Forall_forall. intros [n s] _. reflexivity.
Qed.

End Localised.

(** ** Semantics *)

Section SemProps.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_two" *)
Theorem evaluate_two : forall (p : prog a) t k k' res st res' st',
  evaluate (p, set_clock k t) = (res, st) /\ evaluate (p, set_clock k' t) = (res', st') /\
  res <> SOME TimeOut /\ res' <> SOME TimeOut ->
  res = res' /\ ffi st = ffi st'.
Proof.
  intros p t k k' res st res' st' (H1 & H2 & N1 & N2).
  destruct (N.le_ge_cases k k') as [Hk|Hk].
  - pose proof (evaluate_add_clock_eq p (set_clock k t) res st (k' - k) (conj H1 N1)) as HA.
    cbn [clock set_clock] in HA. rewrite set_clock_set_clock in HA.
    replace (k + (k' - k)) with k' in HA by lia. rewrite H2 in HA. injection HA as -> HA.
    split; [reflexivity|]. rewrite HA. reflexivity.
  - pose proof (evaluate_add_clock_eq p (set_clock k' t) res' st' (k - k') (conj H2 N2)) as HA.
    cbn [clock set_clock] in HA. rewrite set_clock_set_clock in HA.
    replace (k' + (k - k')) with k in HA by lia. rewrite H1 in HA. injection HA as -> HA.
    split; [reflexivity|]. rewrite HA. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "num_cases_lemma" *)
Theorem num_cases_lemma : forall P : N -> Prop, (forall x, P x) -> P 0 /\ forall x, P (SUC x).
Proof. intros P H; split; [apply H|intros x; apply H]. Qed.

Lemma tailcall_facts f (S0 : state a ffi_t) r T :
  evaluate (TailCall f [], S0) = (r, T) ->
  r <> NONE /\ r <> SOME Break /\ r <> SOME Continue /\
  (forall v0, r = SOME (Return v0) -> exists vs b rsh, FLOOKUP (code S0) f = SOME (vs, (b, rsh)) /\ shape_of v0 = rsh).
Proof.
  intros H. rewrite evaluate_unfold in H. cbn [evaluate_body OPT_MMAP] in H. cbn beta iota in H.
  unfold lookup_code in H. destruct (FLOOKUP (code S0) f) as [[vs [b rsh]]|] eqn:EF;
    [|injp H; repeat split; try discriminate; intros v0 C; discriminate].
  destruct (_ && _); [|injp H; repeat split; try discriminate; intros v0 C; discriminate].
  destruct (clock S0 =? 0); [injp H; repeat split; try discriminate; intros v0 C; discriminate|].
  rewrite fix_clock_evaluate in H. destruct (evaluate _) as [r1 st] eqn:E1.
  destruct r1 as [[| | | |retv|eid exn|ff]|]; cbn beta iota in H;
    try (injp H; repeat split; try discriminate; intros v0 C; discriminate).
  destruct (negb _) eqn:En; injp H; repeat split; try discriminate.
  intros v0 C; injection C as <-. exists vs, b, rsh. split; [reflexivity|].
  apply Bool.negb_false_iff, bool_decide_spec in En. exact En.
Qed.

Lemma sc_sl k L (s0 : state a ffi_t) : set_clock k (set_locals L s0) = set_locals L (set_clock k s0).
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_empty_locals" *)
Theorem semantics_empty_locals : forall (t : state a ffi_t) start,
  semantics t start = semantics (set_locals FEMPTY t) start.
Proof.
  intros t start. rewrite !semantics_sem_of.
  destruct (run_corr_same (fun k => evaluate (TailCall start [], set_clock k t))
                          (fun k => evaluate (TailCall start [], set_clock k (set_locals FEMPTY t)))) as [H1 H2];
    [|exact (sem_of_corr _ _ H1 H2)].
  intros k. rewrite sc_sl. rewrite !evaluate_unfold. cbn [evaluate_body OPT_MMAP]. cbn beta iota.
  rewrite code_sl, clock_sl. destruct (lookup_code _ _ _) as [[p0 [nl rsh]]|]; [|split; reflexivity].
  destruct (clock (set_clock k t) =? 0); [split; reflexivity|].
  rewrite sl_dec_clock. destruct (fix_clock _ _) as [r st].
  destruct r as [[| | | |retv|eid exn|ff]|]; try (split; reflexivity).
Qed.

End SemProps.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "LUB_IMAGE_SUC" *)
Theorem LUB_IMAGE_SUC : forall {A} `{EqDecision A} `{Inhabited A} (f : N -> llist A),
  (forall x, LPREFIX (f x) (f (SUC x))) ->
  build_lprefix_lub (IMAGE f UNIV) = build_lprefix_lub (IMAGE (f ∘ SUC) UNIV).
Proof.
  intros A HA HI f Hf.
  assert (Mono : forall x y, x <= y -> LPREFIX (f x) (f y)).
  { intros x y Hxy. replace y with (x + (y - x)) by lia. generalize (y - x) as d. clear Hxy y.
    intros d; induction d as [|d IH] using N.peano_ind; [rewrite N.add_0_r; apply LPREFIX_REFL|].
    apply (LPREFIX_TRANS _ (f (x + d))); split; [exact IH|]. rewrite N.add_succ_r. apply Hf. }
  assert (Chain : forall g : N -> N, lprefix_chain (IMAGE (f ∘ g) UNIV)).
  { intros g ll1 ll2 [[x [-> _]] [y [-> _]]]. destruct (N.le_ge_cases (g x) (g y)) as [Hl|Hl].
    - left; apply Mono, Hl.
    - right; apply Mono, Hl. }
  pose proof (build_lprefix_lub_thm _ (Chain (fun x => x))) as L1.
  pose proof (build_lprefix_lub_thm _ (Chain SUC)) as L2.
  apply (unique_lprefix_lub (IMAGE f UNIV)). split; [exact L1|].
  destruct L2 as [U2 M2]. split.
  - intros ll [x [-> _]]. apply (LPREFIX_TRANS _ (f (SUC x))). split; [apply Hf|].
    apply U2. exists x; split; [reflexivity|exact Logic.I].
  - intros ub Hub. apply M2. intros ll [x [-> _]]. apply Hub. exists (SUC x); split; [reflexivity|exact Logic.I].
Qed.

Section SemInit.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.

Lemma clock_set_clock_ n (s0 : state a ffi_t) : clock (set_clock n s0) = n. Proof. reflexivity. Qed.

Lemma semantics_fail_one (s : state a ffi_t) start k :
  fst (evaluate (TailCall start [], set_clock k s)) = SOME Error -> semantics s start = Fail.
Proof.
  intros H. unfold semantics. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
  exfalso; apply Hn. exists k. rewrite H. exact Logic.I.
Qed.

Lemma init_call_step (s s' : state a ffi_t) start start' body rshape k :
  FLOOKUP (code s) start = SOME ([], (Seq body (TailCall start' []), rshape)) ->
  (forall rv, fst (evaluate (TailCall start' [], set_clock k s')) = SOME (Return rv) -> shape_of rv = rshape) ->
  evaluate (body, set_clock k (set_locals FEMPTY s)) = (NONE, set_clock k s') ->
  fst (evaluate (TailCall start [], set_clock (SUC k) s)) = fst (evaluate (TailCall start' [], set_clock k s')) /\
  io_events (ffi (snd (evaluate (TailCall start [], set_clock (SUC k) s)))) =
  io_events (ffi (snd (evaluate (TailCall start' [], set_clock k s')))).
Proof.
  intros Hm Hsh Hb. rewrite (evaluate_unfold (TailCall start [])). cbn [evaluate_body OPT_MMAP]. cbn beta iota.
  unfold lookup_code. cbn [code set_clock]. rewrite Hm. cbn [MAP List.map ALL_DISTINCT andb].
  rewrite bd_true by constructor. cbn beta iota. cbn [clock set_clock].
  destruct (N.succ k =? 0) eqn:Ek; [apply N.eqb_eq in Ek; lia|]. cbn beta iota.
  match goal with |- context [set_locals ?L (dec_clock (set_clock (SUC k) s))] =>
    replace (set_locals L (dec_clock (set_clock (SUC k) s)))
      with (set_clock k (set_locals FEMPTY s)) by (destruct s; unfold dec_clock, set_clock, set_locals; cbn; f_equal; lia) end.
  rewrite fix_clock_evaluate, evaluate_unfold. cbn [evaluate_body]. rewrite fix_clock_evaluate, Hb.
  cbn beta iota.
  destruct (evaluate (TailCall start' [], set_clock k s')) as [r2 t2] eqn:E2. cbn [fst snd] in Hsh |- *.
  destruct (tailcall_facts _ _ _ _ E2) as (N1 & N2 & N3 & _).
  destruct r2 as [[| | | |retv|eid exn|ff]|]; cbn beta iota; try (split; reflexivity); try congruence.
  rewrite (Hsh retv eq_refl). rewrite bd_true by reflexivity. split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_init_call" *)
Theorem semantics_init_call : forall (s s' : state a ffi_t) start start' body rshape args' body',
  FLOOKUP (code s) start = SOME ([], (Seq body (TailCall start' []), rshape)) /\
  FLOOKUP (code s) start' = SOME (args', (body', rshape)) /\
  (forall k, evaluate (body, set_clock k (set_locals FEMPTY s)) = (NONE, set_clock k s')) /\
  io_events (ffi s') = io_events (ffi s) ->
  semantics s start = semantics s' start'.
Proof.
  intros s s' start start' body rshape args' body' (Hm & Hm' & Hb & Hio).
  assert (Hc : code s' = code s).
  { pose proof (evaluate_invariants _ _ _ _ (Hb 0)) as (_ & _ & _ & _ & _ & _ & Hc & _).
    exact Hc. }
  assert (Hsh : forall k rv, fst (evaluate (TailCall start' [], set_clock k s')) = SOME (Return rv) ->
                  shape_of rv = rshape).
  { intros k rv E. destruct (evaluate (TailCall start' [], set_clock k s')) as [r2 t2] eqn:E2.
    cbn in E. subst r2. destruct (tailcall_facts _ _ _ _ E2) as (_ & _ & _ & HR).
    destruct (HR rv eq_refl) as (vs & b & rsh & EF & Hr). cbn [code set_clock] in EF.
    rewrite Hc, Hm' in EF. injection EF as _ _ <-. exact Hr. }
  destruct (lookup_code (code s') start' ([] : list (v a))) as [[p2 [nl2 rsh2]]|] eqn:Hl'.
  2: { assert (F2 : forall k, fst (evaluate (TailCall start' [], set_clock k s')) = SOME Error).
       { intros k. rewrite evaluate_unfold. cbn [evaluate_body OPT_MMAP]. cbn beta iota.
         cbn [code set_clock]. rewrite Hl'. reflexivity. }
       rewrite (semantics_fail_one s' start' 0 (F2 0)).
       apply (semantics_fail_one s start (SUC 0)).
       rewrite (proj1 (init_call_step s s' start start' body rshape 0 Hm (Hsh 0) (Hb 0))). exact (F2 0). }
  rewrite !semantics_sem_of. apply sem_of_corr.
  - intros k. destruct k as [|k'] using N.peano_ind.
    + exists 0. rewrite !evaluate_unfold. cbn [evaluate_body OPT_MMAP]. cbn beta iota.
      cbn [code set_clock]. rewrite Hl'. unfold lookup_code. rewrite Hm.
      cbn [MAP List.map ALL_DISTINCT andb]. rewrite bd_true by constructor. cbn beta iota.
      cbn [clock set_clock]. split; [reflexivity|]. exact (eq_sym Hio).
    + exists k'. exact (init_call_step s s' start start' body rshape k' Hm (Hsh k') (Hb k')).
  - intros k. exists (SUC k). destruct (init_call_step s s' start start' body rshape k Hm (Hsh k) (Hb k)) as [E1 E2].
    split; symmetry; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "semantics_init_call'" *)
Theorem semantics_init_call' : forall (s s' : state a ffi_t) start start' body rshape args' body',
  FLOOKUP (code s) start = SOME ([], (Seq body (TailCall start' []), rshape)) /\
  FLOOKUP (code s) start' = SOME (args', (body', rshape)) /\
  evaluate (body, set_locals FEMPTY s) = (NONE, s') /\
  clock s' = clock s /\
  io_events (ffi s') = io_events (ffi s) ->
  semantics s start = semantics s' start'.
Proof.
  intros s s' start start' body rshape args' body' (Hm & Hm' & Hb & Hck & Hio).
  apply (semantics_init_call s s' start start' body rshape args' body'). split; [exact Hm|split; [exact Hm'|split; [|exact Hio]]].
  intros k.
  assert (H0 : evaluate (body, set_clock (clock (set_locals FEMPTY s) - clock s) (set_locals FEMPTY s)) =
               (NONE, set_clock 0 s')).
  { apply evaluate_clock_sub. split; [|discriminate]. rewrite Hb. f_equal.
    rewrite set_clock_set_clock. cbn [clock set_clock]. rewrite N.add_0_l, <- Hck. symmetry; apply set_clock_id. }
  rewrite clock_sl, N.sub_diag in H0.
  assert (Hnt : (NONE : option (result a)) <> SOME TimeOut) by discriminate.
  pose proof (evaluate_add_clock_eq body (set_clock 0 (set_locals FEMPTY s)) NONE (set_clock 0 s') k
                (conj H0 Hnt)) as HA.
  rewrite !clock_set_clock_, N.add_0_l, !set_clock_set_clock in HA. exact HA.
Qed.

Lemma sr_set_clock ls ctxt s t k : state_rel ls ctxt s t -> state_rel ls ctxt (set_clock k s) (set_clock k t).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
  unfold state_rel, set_clock; cbn [locals globals structs code eshapes memory memaddrs sh_memaddrs clock be ffi
    base_addr top_addr]. repeat split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics : forall ctxt (s t : state a ffi_t) start,
  state_rel true ctxt s t /\ semantics s start <> Fail -> semantics t start = semantics s start.
Proof.
  intros ctxt s t start [Hr Hs].
  assert (Hne : forall k, fst (evaluate (TailCall start [], set_clock k s)) <> SOME Error).
  { intros k E. apply Hs. exact (semantics_fail_one s start k E). }
  rewrite !semantics_sem_of. symmetry.
  destruct (run_corr_same (fun k => evaluate (TailCall start [], set_clock k s))
                          (fun k => evaluate (TailCall start [], set_clock k t))) as [H1 H2];
    [|exact (sem_of_corr _ _ H1 H2)].
  intros k. specialize (Hne k).
  destruct (evaluate (TailCall start [], set_clock k s)) as [r st] eqn:E. cbn [fst snd] in Hne |- *.
  destruct (compile_correct (TailCall start []) (set_clock k s) r ctxt (set_clock k t) st
              (conj (sr_set_clock _ _ _ _ k Hr) (conj E Hne))) as (t' & Et & Hr').
  cbn [compile MAP List.map] in Et. rewrite Et. split; [reflexivity|]. rewrite (sr_ffi _ _ _ _ Hr'). reflexivity.
Qed.

End SemInit.

(** ** Initialising the globals *)

Section InitGlobals.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_state_rel_is_wf_shape" *)
Theorem eval_state_rel_is_wf_shape : forall (s : state a ffi_t) (exp0 : exp a) v0 b ctxt t,
  eval s exp0 = SOME v0 /\ state_rel b ctxt s t /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (locals s) ->
  is_true (is_wf_shape_nil (shape_of v0)).
Proof.
  intros s exp0 v0 b ctxt t (He & Hr & Hl).
  destruct Hr as (_ & _ & _ & _ & _ & _ & Hs & _ & H9 & _).
  apply is_wf_shape_of_v. rewrite <- Hs.
  apply (eval_is_wf_shape_v s exp0 v0). split; [exact He|split; [exact Hl|]].
  intros k x Hx. destruct (H9 k x Hx) as (addr & _ & Hw & _). rewrite Hs.
  rewrite <- (is_wf_shape_v_nil_thm x [] eq_refl). exact Hw.
Qed.

Lemma FEVERY_upd_ {K V} `{EqDecision K} (P : K * V -> Prop) (m : fmap K V) k x :
  FEVERY P m -> P (k, x) -> FEVERY P (m |+ (k, x)).
Proof.
  intros Hm Hx k' v' E. rewrite FLOOKUP_UPDATE in E. destruct (decide (k = k')) as [<-|]; [injection E as <-; exact Hx|].
  exact (Hm _ _ E).
Qed.

Lemma DISJOINT_SUBSET_r_ {A} (s1 s2 s3 : A -> Prop) : DISJOINT s1 s2 -> s3 SUBSET s2 -> DISJOINT s1 s3.
Proof.
  intros H Hs. apply DISJOINT_ALT. intros x H1 H3. exact (proj1 (DISJOINT_ALT _ _) H x H1 (Hs x H3)).
Qed.

Lemma DISJOINT_sym_ {A} (s1 s2 : A -> Prop) : DISJOINT s1 s2 -> DISJOINT s2 s1.
Proof. intros H. apply DISJOINT_ALT. intros x H2 H1. exact (proj1 (DISJOINT_ALT _ _) H x H1 H2). Qed.

Lemma addresses_sub_l (B : word a) n m : addresses B n SUBSET addresses B (n + m).
Proof. rewrite addresses_split. intros x Hx. apply IN_UNION. left; exact Hx. Qed.

Lemma addresses_sub_r (B : word a) n m : addresses (B + bytes_in_word * n2w n) m SUBSET addresses B (n + m).
Proof. rewrite addresses_split. intros x Hx. apply IN_UNION. right; exact Hx. Qed.

Ltac injp H := let H1 := fresh "Hp" in let H2 := fresh "Hp" in
  apply pair_equal_spec in H as [H1 H2];
  match type of H1 with _ = ?r => subst r end; match type of H2 with _ = ?r => subst r end.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_init_globals_lemma" *)
Theorem evaluate_decls_init_globals_lemma :
  forall (s : state a ffi_t) decls s' decls' funs exns ctxt' ctxt t free_addrs,
  evaluate_decls s decls = SOME s' /\
  is_true (EVERY is_decl decls) /\
  compile_decs ctxt decls = (decls', (funs, (exns, ctxt'))) /\
  state_rel false ctxt s t /\
  free_addrs = addresses (top_addr t - bytes_in_word * n2w (SUM (MAP size_of_shape (dec_shapes decls)))
                          - globals_size ctxt) (SUM (MAP size_of_shape (dec_shapes decls))) /\
  DISJOINT (memaddrs s) free_addrs /\
  free_addrs SUBSET memaddrs t /\
  is_true (byte_aligned (globals_size ctxt)) /\
  code s = FEMPTY /\
  (forall v0 sh addr', is_true (IS_SOME (FLOOKUP (globals s) v0)) /\
     FLOOKUP (pan_globals.globals ctxt) v0 = SOME (sh, addr') ->
     DISJOINT (addresses (top_addr t - addr') (size_of_shape sh)) free_addrs) /\
  (w2n (bytes_in_word : word a) * SUM (MAP size_of_shape (dec_shapes decls)) < dimword a)%N ->
  exists t', evaluate (nested_seq decls', t) = (NONE, t') /\ state_rel false ctxt' s' t' /\
    clock t' = clock t /\ ffi t' = ffi t /\ locals t' = locals t /\ is_true (byte_aligned (globals_size ctxt')).
Proof.
  intros s decls; revert s; induction decls as [|d ds IH];
    intros s s' decls' funs exns ctxt' ctxt t free_addrs (Hev & Hd & Hc & Hr & Hfree & Hdis & Hsub & Hal & Hcode & Hglob & Hbnd).
  - cbn in Hev, Hc. injection Hev as <-. injection Hc as <- <- <- <-.
    exists t. split; [reflexivity|]. split; [exact Hr|]. repeat split; try reflexivity; exact Hal.
  - cbn in Hd. apply Bool.andb_true_iff in Hd as [Hd0 Hd]. destruct d as [|sh v0 e| |]; try discriminate.
    cbn [evaluate_decls] in Hev.
    destruct (eval (set_locals FEMPTY s) e) as [res|] eqn:Ee; [|discriminate].
    destruct (bool_decide (sh = shape_of res)) eqn:Esh; [|discriminate]. apply bool_decide_spec in Esh. subst sh.
    cbn [compile_decs] in Hc. cbn zeta in Hc.
    match type of Hc with context [compile_decs ?c1 ds] =>
      destruct (compile_decs c1 ds) as [decs1 [f1 [e1 c1']]] eqn:Ec1; set (ctxt1 := c1) in Ec1 end.
    injection Hc as <- <- <- <-.
    cbn [dec_shapes MAP List.map SUM] in Hfree, Hbnd.
    pose proof Hr as Hr0.
    destruct Hr as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & Hg).
    remember (size_of_shape (shape_of res)) as sz eqn:Hsz.
    remember (SUM (MAP size_of_shape (dec_shapes ds))) as N' eqn:HN.
    remember (globals_size ctxt) as G eqn:HG.
    remember (top_addr t) as T eqn:HT.
    set (gs := (G + bytes_in_word * n2w sz)%w).
    set (B := (T - bytes_in_word * n2w (sz + N') - G)%w).
    pose proof (proj2 (state_rel_empty_locals true ctxt s t) Hr0) as Hrt.
    pose proof (compile_exp_correct _ _ _ _ _ (conj Hrt Ee)) as Ce.
    pose proof (eval_empty_locals_IMP t _ res Ce) as Ce'.
    pose proof (eval_state_rel_is_wf_shape (set_locals FEMPTY s) e res true ctxt (empty_locals t)
                  (conj Ee (conj Hrt (FEVERY_FEMPTY _)))) as Hwf.
    pose proof (length_flatten_eq_size_of_shape res Hwf) as Hlen. rewrite <- Hsz in Hlen.
    pose proof (w2n_bw Hg) as Hbw.
    assert (Eb1 : (T - gs = B + bytes_in_word * n2w N')%w).
    { unfold gs, B. rewrite <- word_add_n2w. word_ring. }
    assert (Eb2 : (T - bytes_in_word * n2w N' - gs = B)%w).
    { unfold gs, B. rewrite <- word_add_n2w. word_ring. }
    assert (Hfree' : free_addrs = addresses B (N' + sz)) by (rewrite Hfree; unfold B; rewrite (N.add_comm N' sz); reflexivity).
    assert (Sub1 : addresses (T - gs)%w sz SUBSET free_addrs)
      by (rewrite Eb1, Hfree'; apply addresses_sub_r).
    assert (Sub2 : addresses B N' SUBSET free_addrs) by (rewrite Hfree'; apply addresses_sub_l).
    assert (Dis12 : DISJOINT (addresses B N') (addresses (T - gs)%w sz)).
    { rewrite Eb1. apply addresses_disjoint_off; [exact Hg|]. rewrite <- Hbw, N.mul_comm, (N.add_comm N' sz). exact Hbnd. }
    destruct (mem_stores_addrs_IS_SOME (T - gs)%w (flatten res) (memaddrs t) (memory t)) as [m Hm].
    { rewrite Hlen. intros x Hx. apply Hsub, Sub1, Hx. }
    assert (Hgs : is_true (byte_aligned gs)).
    { unfold gs. apply byte_aligned_add. split; [exact Hal|apply byte_aligned_bytes_in_word_mul, Hg]. }
    assert (HsrN : state_rel false ctxt1 (set_globals (globals s |+ (v0, res)) s) (set_memory m t)).
    { unfold state_rel, set_globals, set_memory. cbn [locals globals structs code eshapes memory memaddrs
        sh_memaddrs clock be ffi base_addr top_addr]. subst ctxt1. cbn [pan_globals.globals max_globals_size].
      rewrite <- HT.
      split; [exact H1|split; [intros C; discriminate C|]].
      do 6 (split; [assumption|]).
      split.
      { intros v val Hv. rewrite FLOOKUP_UPDATE in Hv. destruct (decide (v0 = v)) as [<-|Hne].
        - injection Hv as <-. exists gs. rewrite FLOOKUP_UPDATE.
          destruct (decide (v0 = v0)) as [_|C]; [|contradiction C; reflexivity].
          split; [reflexivity|split; [exact Hwf|split; [|split; [|exact Hgs]]]].
          + apply (proj1 mem_stores_mem_load_back _ _ _ (memory t) _ []).
            repeat split; try assumption. rewrite Hlen, N.mul_comm. lia.
          + rewrite <- Hsz. exact (DISJOINT_SUBSET_r_ _ _ _ Hdis Sub1).
        - destruct (H9 v val Hv) as (addr' & A1 & A2 & A3 & A4 & A5). exists addr'.
          rewrite FLOOKUP_UPDATE. destruct (decide (v0 = v)) as [C|_]; [contradiction|].
          split; [exact A1|split; [exact A2|split; [|split; assumption]]].
          try rewrite <- HT in A3, A4.
          assert (Hd' : DISJOINT (addresses (T - addr') (size_of_shape (shape_of val)))
                                 (addresses (T - gs) (LENGTH (flatten res)))).
          { rewrite Hlen. apply (DISJOINT_SUBSET_r_ _ free_addrs); [|exact Sub1].
            apply (Hglob v). rewrite Hv. split; [reflexivity|exact A1]. }
          rewrite (proj1 mem_stores_load_disjoint _ _ _ _ _ m [] _ (conj Hm (conj eq_refl (conj A2 Hd')))).
          exact A3. }
      split; [apply FEVERY_upd_; [exact H10|exact Hwf]|].
      split; [exact H11|split; [exact H12|]].
      split.
      { intros x Hx. rewrite (H13 x Hx). symmetry.
        assert (Hn : x NOTIN addresses (T - gs)%w (LENGTH (flatten res))).
        { rewrite Hlen. intros Hin. exact (proj1 (DISJOINT_ALT _ _) Hdis x Hx (Sub1 x Hin)). }
        exact (mem_stores_lookup _ _ _ _ _ _ (conj Hm Hn)). }
      split; [exact H14|].
      split; [intros f vs p r Hf; rewrite Hcode in Hf; discriminate|].
      split.
      { intros v1 v2 sh1 a1 sh2 a2 (Hn & Hs1 & Hs2 & C1 & C2).
        rewrite FLOOKUP_UPDATE in Hs1. rewrite FLOOKUP_UPDATE in Hs2. rewrite FLOOKUP_UPDATE in C1. rewrite FLOOKUP_UPDATE in C2.
        destruct (decide (v0 = v1)) as [<-|N1]; destruct (decide (v0 = v2)) as [<-|N2].
        - contradiction.
        - injection C1 as <- <-. rewrite <- Hsz. apply DISJOINT_sym_.
          apply (DISJOINT_SUBSET_r_ _ free_addrs); [|exact Sub1].
          apply (Hglob v2). split; [exact Hs2|exact C2].
        - injection C2 as <- <-. rewrite <- Hsz.
          apply (DISJOINT_SUBSET_r_ _ free_addrs); [|exact Sub1].
          apply (Hglob v1). split; [exact Hs1|exact C1].
        - exact (H16 v1 v2 sh1 a1 sh2 a2 (conj Hn (conj Hs1 (conj Hs2 (conj C1 C2))))). }
      split; [exact H17|split; [exact H18|exact Hg]]. }
    destruct (IH (set_globals (globals s |+ (v0, res)) s) s' decs1 f1 e1 c1' ctxt1 (set_memory m t)
                (addresses B N')) as (t' & Et' & Hr' & Hck & Hff & Hlc & Hal').
    { split; [exact Hev|split; [exact Hd|split; [exact Ec1|split; [exact HsrN|]]]].
      split; [subst ctxt1; cbn [globals_size top_addr set_memory]; try rewrite <- HT; try rewrite <- HN; rewrite <- Eb2; reflexivity|].
      split; [exact (DISJOINT_SUBSET_r_ _ _ _ Hdis Sub2)|].
      split; [intros x Hx; apply Hsub, Sub2, Hx|].
      split; [exact Hgs|].
      split; [exact Hcode|].
      split.
      - intros v sh addr' (Hs & Hc). subst ctxt1. cbn [pan_globals.globals globals set_globals top_addr set_memory] in Hs, Hc |- *.
        try rewrite <- HT. rewrite FLOOKUP_UPDATE in Hs. rewrite FLOOKUP_UPDATE in Hc. destruct (decide (v0 = v)) as [<-|Hne].
        + injection Hc as <- <-. rewrite <- Hsz. exact (DISJOINT_sym_ _ _ Dis12).
        + apply (DISJOINT_SUBSET_r_ _ free_addrs); [|exact Sub2].
          apply (Hglob v). split; [exact Hs|exact Hc].
      - rewrite N.mul_add_distr_l in Hbnd. lia. }
    exists t'. cbn [nested_seq]. split.
    + rewrite evaluate_unfold. cbn [evaluate_body]. rewrite fix_clock_evaluate. rewrite evaluate_unfold. cbn [evaluate_body]. rewrite eval_top_sub, Ce'. unfold ValWord. cbn beta iota.
      rewrite <- HT. fold gs. rewrite Hm. cbn beta iota. exact Et'.
    + split; [exact Hr'|]. split; [exact Hck|split; [exact Hff|split; [exact Hlc|exact Hal']]].
Qed.

End InitGlobals.

(** ** Evaluating the compiled declarations *)

Section TopDecls.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma EVERY_bd {A} (Q : A -> Prop) l : is_true (EVERY (fun d => ⌜Q d⌝) l) <-> forall d, In d l -> Q d.
Proof.
  induction l as [|x l IH]; cbn; [split; [intros _ d []|reflexivity]|].
  unfold is_true in *. rewrite Bool.andb_true_iff, IH, bool_decide_spec. split.
  - intros [Hx Hl] d [<-|Hd]; [exact Hx|exact (Hl d Hd)].
  - intros H. split; [apply H; left; reflexivity|intros d Hd; apply H; right; exact Hd].
Qed.

Lemma EVERY_In {A} (P : A -> bool) l : is_true (EVERY P l) <-> forall d, In d l -> is_true (P d).
Proof.
  induction l as [|x l IH]; cbn; [split; [intros _ d []|reflexivity]|].
  unfold is_true in *. rewrite Bool.andb_true_iff, IH. split.
  - intros [Hx Hl] d [<-|Hd]; [exact Hx|exact (Hl d Hd)].
  - intros H. split; [apply H; left; reflexivity|intros d Hd; apply H; right; exact Hd].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_functions_wf" *)
Theorem evaluate_decls_functions_wf : forall (s : state a ffi_t) (decs : list (decl a)) s' fi,
  evaluate_decls s decs = SOME s' /\ is_true (MEM (Function fi) decs) /\
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) decs) ->
  is_true (EVERY (is_wf_shape (structs s) ∘ SND) (params fi)) /\
  is_true (is_wf_shape (structs s) (fun_decl_return fi)).
Proof.
  intros s decs; revert s; induction decs as [|d ds IH]; intros s s' fi (H & Hm & He);
    [apply MEM_is_true_In in Hm; destruct Hm|].
  apply MEM_is_true_In in Hm. cbn in He. apply Bool.andb_true_iff in He as [Hd He].
  rewrite evaluate_decls_cons_cases in H.
  destruct d as [fi'|sh v0 e|eid sh|nm flds]; [| | |discriminate].
  - destruct (_ && _) eqn:Ew; [|discriminate]. apply Bool.andb_true_iff in Ew as [W1 W2].
    destruct Hm as [Hm|Hm]; [injection Hm as ->; split; assumption|].
    exact (IH _ _ fi (conj H (conj (proj2 (MEM_is_true_In _ _) Hm) He))).
  - destruct (eval _ e); [|discriminate]. destruct (bool_decide _); [|discriminate].
    destruct Hm as [Hm|Hm]; [discriminate|].
    exact (IH _ _ fi (conj H (conj (proj2 (MEM_is_true_In _ _) Hm) He))).
  - destruct (_ && _); [|discriminate]. destruct Hm as [Hm|Hm]; [discriminate|].
    exact (IH _ _ fi (conj H (conj (proj2 (MEM_is_true_In _ _) Hm) He))).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_only_functions_SOME" *)
Theorem evaluate_decls_only_functions_SOME : forall (s : state a ffi_t) (pan_code : list (decl a)),
  is_true (EVERY is_function pan_code) /\
  is_true (EVERY (fun d => ⌜forall fi, d = Function fi ->
       is_true (EVERY (is_wf_shape (structs s) ∘ SND) (params fi)) /\
       is_true (is_wf_shape (structs s) (fun_decl_return fi))⌝) pan_code) ->
  evaluate_decls s pan_code = SOME (set_code (code s |++ functions pan_code) s).
Proof.
  intros s pan_code; revert s; induction pan_code as [|d ds IH]; intros s [Hf Hw].
  - cbn. f_equal. destruct s; reflexivity.
  - cbn in Hf, Hw. apply Bool.andb_true_iff in Hf as [Hd Hf]. apply Bool.andb_true_iff in Hw as [Hwd Hw].
    apply bool_decide_spec in Hwd. destruct d as [fi| | |]; try discriminate.
    destruct (Hwd fi eq_refl) as [W1 W2].
    rewrite evaluate_decls_cons_cases. rewrite W1, W2. cbn [andb]. rewrite IH; [reflexivity|].
    split; [exact Hf|exact Hw].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_only_functions_and_exns_SOME" *)
Theorem evaluate_decls_only_functions_and_exns_SOME : forall (s : state a ffi_t) (pan_code : list (decl a)),
  is_true (EVERY (fun d => is_function d || is_exn_decl d) pan_code) /\
  is_true (EVERY (fun d => ⌜forall fi, d = Function fi ->
       is_true (EVERY (is_wf_shape (structs s) ∘ SND) (params fi)) /\
       is_true (is_wf_shape (structs s) (fun_decl_return fi))⌝) pan_code) /\
  is_true (ALL_DISTINCT (MAP FST (exceptions pan_code))) /\
  is_true (EVERY (fun '(eid, sh) => ⌜FLOOKUP (eshapes s) eid = NONE⌝) (exceptions pan_code)) /\
  is_true (EVERY (is_wf_shape (structs s) ∘ SND) (exceptions pan_code)) ->
  evaluate_decls s pan_code =
  SOME (set_eshapes (eshapes s |++ exceptions pan_code) (set_code (code s |++ functions pan_code) s)).
Proof.
  intros s pan_code; revert s; induction pan_code as [|d ds IH]; intros s (Hf & Hw & D & F & W).
  - cbn. f_equal. destruct s; reflexivity.
  - cbn in Hf, Hw. apply Bool.andb_true_iff in Hf as [Hd Hf]. apply Bool.andb_true_iff in Hw as [Hwd Hw].
    apply bool_decide_spec in Hwd. rewrite evaluate_decls_cons_cases.
    destruct d as [fi| |eid sh|]; try discriminate.
    + destruct (Hwd fi eq_refl) as [W1 W2]. rewrite W1, W2. cbn [andb].
      rewrite IH; [reflexivity|]. cbn [exceptions] in D, F, W.
      repeat split; assumption.
    + cbn [exceptions MAP List.map FST fst ALL_DISTINCT EVERY] in D, F, W.
      apply Bool.andb_true_iff in D as [Dn D]. apply Bool.andb_true_iff in F as [F1 F].
      apply Bool.andb_true_iff in W as [W1 W]. cbn [snd] in W1.
      match goal with |- context [if ?b then _ else _] =>
        replace b with true by (symmetry; apply Bool.andb_true_iff; split;
                                 [apply bool_decide_spec; exact (proj1 (bool_decide_spec _) F1)|exact W1]) end.
      rewrite IH; [reflexivity|]. cbn [structs eshapes set_eshapes].
      split; [exact Hf|split; [exact Hw|split; [exact D|split; [|exact W]]]].
      apply Bool.negb_true_iff, Bool.not_true_iff_false in Dn.
      clear -F Dn. induction (exceptions ds) as [|[x y] l IHl]; [reflexivity|].
      cbn in F, Dn |- *. apply Bool.andb_true_iff in F as [F1 F2]. apply Bool.andb_true_iff; split.
      * apply bool_decide_spec. rewrite ?FLOOKUP_UPDATE. destruct (decide (eid = x)) as [->|Hne].
        -- exfalso; apply Dn. apply Bool.orb_true_iff; left; apply bool_decide_spec; reflexivity.
        -- exact (proj1 (bool_decide_spec _) F1).
      * apply IHl; (exact F2 || (intros Hm; apply Dn; apply Bool.orb_true_iff; right; exact Hm)).
Qed.

Lemma compile_decs_In_fun (ctxt : context a) l decls funs exns ctxt' fi :
  compile_decs ctxt l = (decls, (funs, (exns, ctxt'))) -> In (Function fi) funs ->
  exists fi0, In (Function fi0) l /\ params fi = params fi0 /\ fun_decl_return fi = fun_decl_return fi0.
Proof.
  revert ctxt decls funs exns ctxt'; induction l as [|d ds IH]; intros ctxt decls funs exns ctxt' H Hin.
  - cbn in H. injection H as _ <- _ _. destruct Hin.
  - destruct d as [fi'|sh v0 e|eid sh|nm flds]; cbn [compile_decs] in H; cbn zeta in H;
      try (match type of H with context [compile_decs ?c ds] =>
             destruct (compile_decs c ds) as [d1 [f1 [e1 c1]]] eqn:E end;
           injection H as _ <- _ _).
    + destruct Hin as [Hin|Hin].
      * injection Hin as <-. exists fi'. split; [left; reflexivity|split; reflexivity].
      * destruct (IH _ _ _ _ _ E Hin) as (fi0 & H1 & H2 & H3). exists fi0. split; [right; exact H1|split; assumption].
    + destruct (IH _ _ _ _ _ E Hin) as (fi0 & H1 & H2 & H3). exists fi0. split; [right; exact H1|split; assumption].
    + destruct (IH _ _ _ _ _ E Hin) as (fi0 & H1 & H2 & H3). exists fi0. split; [right; exact H1|split; assumption].
    + destruct (IH _ _ _ _ _ E Hin) as (fi0 & H1 & H2 & H3). exists fi0. split; [right; exact H1|split; assumption].
Qed.

Lemma fperm_decs_In_fun f g (l : list (decl a)) fi :
  In (Function fi) (fperm_decs f g l) ->
  exists fi0, In (Function fi0) l /\ params fi = params fi0 /\ fun_decl_return fi = fun_decl_return fi0.
Proof.
  induction l as [|d ds IH]; intros Hin; [destruct Hin|].
  destruct d as [fi'| | |]; cbn [fperm_decs] in Hin; destruct Hin as [Hin|Hin];
    try discriminate;
    try (destruct (IH Hin) as (fi0 & H1 & H2 & H3); exists fi0; split; [right; exact H1|split; assumption]).
  injection Hin as <-. exists fi'. split; [left; reflexivity|split; reflexivity].
Qed.

Lemma resort_decls_In (l : list (decl a)) d : In d (resort_decls l) -> In d l.
Proof.
  unfold resort_decls. rewrite !in_app_iff. intros [H|[H|[H|H]]]; apply filter_In in H as [H _]; exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf" *)
Theorem compile_top_shape_wf : forall (s : state a ffi_t) (code0 : list (decl a)) s' start,
  evaluate_decls s code0 = SOME s' /\
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) code0) ->
  is_true (EVERY (fun d => ⌜forall fi, d = Function fi ->
       is_true (EVERY (is_wf_shape (structs s) ∘ SND) (params fi)) /\
       is_true (is_wf_shape (structs s) (fun_decl_return fi))⌝) (compile_top code0 start)).
Proof.
  intros s code0 s' start [H He]. apply EVERY_bd. intros d Hd fi ->.
  assert (WF : forall fi0, In (Function fi0) code0 ->
            is_true (EVERY (is_wf_shape (structs s) ∘ SND) (params fi0)) /\
            is_true (is_wf_shape (structs s) (fun_decl_return fi0))).
  { intros fi0 Hin. exact (evaluate_decls_functions_wf s code0 s' fi0 (conj H (conj (proj2 (MEM_is_true_In _ _) Hin) He))). }
  unfold compile_top in Hd. destruct (ALOOKUP (functions code0) start) as [[args [bdy rsh]]|] eqn:EA; [|destruct Hd].
  cbn zeta in Hd. destruct (compile_decs _ _) as [decls [funs [exns ctxt]]] eqn:E.
  apply in_app_iff in Hd as [Hd|[Hd|Hd]].
  - rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ E) in Hd. apply filter_In in Hd as [_ Hd]. discriminate.
  - injection Hd as <-. cbn [params fun_decl_return].
    apply ALOOKUP_MEM, MEM_functions in EA as (fi0 & Hm & Ht). injection Ht as _ -> _ ->.
    apply WF, MEM_is_true_In, Hm.
  - destruct (compile_decs_In_fun _ _ _ _ _ _ _ E Hd) as (fi1 & H1 & P1 & R1).
    destruct (fperm_decs_In_fun _ _ _ _ H1) as (fi2 & H2 & P2 & R2).
    rewrite P1, P2, R1, R2. apply WF, resort_decls_In, H2.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_shape_wf_nil" *)
Theorem compile_top_shape_wf_nil : forall (s : state a ffi_t) (code0 : list (decl a)) s' start,
  evaluate_decls s code0 = SOME s' /\ structs s = [] /\
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) code0) ->
  is_true (EVERY (fun d => ⌜forall fi, d = Function fi ->
       is_true (EVERY (is_wf_shape_nil ∘ SND) (params fi)) /\
       is_true (is_wf_shape_nil (fun_decl_return fi))⌝) (compile_top code0 start)).
Proof.
  intros s code0 s' start (H & Hs & He). pose proof (compile_top_shape_wf s code0 s' start (conj H He)) as G.
  rewrite Hs in G. exact G.
Qed.

Lemma EVERY_neg_fun_FILTER (l : list (decl a)) (f : decl a -> bool) :
  (forall d, is_true (f d) -> is_true (negb (is_function d))) -> is_true (EVERY (negb ∘ is_function) (FILTER f l)).
Proof.
  intros H. apply EVERY_In. intros d Hd. apply filter_In in Hd as [_ Hd]. exact (H d Hd).
Qed.

Lemma EVERY_fun_fperm_FILTER f g (l : list (decl a)) : is_true (EVERY is_function (fperm_decs f g (FILTER is_function l))).
Proof. induction l as [|[] l IH]; cbn; try exact IH; reflexivity. Qed.

Lemma functions_MAP_compile c (l : list (decl a)) : is_true (EVERY is_function l) ->
  functions (MAP (fun x => match x with
                           | Function fi => Function {| name := name fi; inline := inline fi; export := export fi;
                                                        params := params fi; body := compile c (body fi);
                                                        fun_decl_return := fun_decl_return fi |}
                           | _ => ARB end) l) =
  MAP (fun '(x, (y, (z, t))) => (x, (y, (compile c z, t)))) (functions l).
Proof.
  induction l as [|d l IH]; intros H; [reflexivity|]. cbn in H. apply Bool.andb_true_iff in H as [Hd H].
  destruct d; try discriminate. cbn. rewrite (IH H). reflexivity.
Qed.

Lemma compile_top_funs (ctxt0 : context a) f g (decs : list (decl a)) ndecls nfuns nexns nctxt :
  compile_decs ctxt0 (fperm_decs f g (resort_decls decs)) = (ndecls, (nfuns, (nexns, nctxt))) ->
  functions nfuns = MAP (fun '(x, (y, (z, t))) => (x, (y, (compile nctxt z, t)))) (functions (fperm_decs f g decs)).
Proof.
  intros H. unfold resort_decls in H. rewrite !fperm_decs_append in H.
  rewrite (fperm_decs_decls f g (FILTER is_name decs) tt) in H
    by (apply EVERY_neg_fun_FILTER; intros [] Hd; cbn in *; congruence).
  rewrite (fperm_decs_decls f g (FILTER is_exn_decl decs) tt) in H
    by (apply EVERY_neg_fun_FILTER; intros [] Hd; cbn in *; congruence).
  rewrite (fperm_decs_decls f g (FILTER is_decl decs) tt) in H
    by (apply EVERY_neg_fun_FILTER; intros [] Hd; cbn in *; congruence).
  rewrite !app_assoc in H. rewrite compile_decls_append in H.
  destruct (compile_decs ctxt0 _) as [d1 [f1 [e1 c1]]] eqn:E1.
  destruct (compile_decs c1 (fperm_decs f g (FILTER is_function decs))) as [d2 [f2 [e2 c2]]] eqn:E2.
  injection H as _ <- _ <-.
  assert (Hf1 : f1 = []).
  { eapply compile_decs_decls_thm. split; [exact E1|].
    rewrite !EVERY_app_. apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|];
      apply EVERY_neg_fun_FILTER; intros [] Hd; cbn in *; congruence. }
  subst f1. cbn [app].
  destruct (compile_decs_functions_thm c1 _ d2 f2 e2 c2 (conj E2 (EVERY_fun_fperm_FILTER f g decs))) as (_ & _ & -> & ->).
  rewrite functions_MAP_compile by apply EVERY_fun_fperm_FILTER.
  rewrite fperm_decs_FILTER_is_function, functions_FILTER. reflexivity.
Qed.

Lemma exceptions_nexns (ctxt0 : context a) f g (decs : list (decl a)) ndecls nfuns nexns nctxt :
  compile_decs ctxt0 (fperm_decs f g (resort_decls decs)) = (ndecls, (nfuns, (nexns, nctxt))) ->
  exceptions nexns = exceptions decs.
Proof.
  intros H. rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ H).
  rewrite (proj1 (proj2 (proj2 (exceptions_FILTER_is_function _)))), exceptions_fperm_decs.
  unfold resort_decls. rewrite !exceptions_append.
  destruct (exceptions_FILTER_is_function decs) as (-> & _ & -> & -> & ->). rewrite app_nil_r. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_compile_top" *)
Theorem evaluate_decls_compile_top :
  forall (s : state a ffi_t) decs s' start args body rshape ndecls nfuns nexns nctxt,
  evaluate_decls s decs = SOME s' /\
  ALOOKUP (functions decs) start = SOME (args, (body, rshape)) /\
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) decs) /\
  compile_decs {| pan_globals.globals := FEMPTY; globals_size := n2w 0;
                  max_globals_size := (bytes_in_word * n2w (SUM (MAP size_of_shape (dec_shapes decs))))%w |}
    (fperm_decs start (new_main_name decs) (resort_decls decs)) = (ndecls, (nfuns, (nexns, nctxt))) ->
  evaluate_decls s (compile_top decs start) =
  SOME (set_eshapes (eshapes s |++ exceptions nexns)
          (set_code (code s |+ (start, (args, (Seq (nested_seq ndecls)
                                                  (TailCall (new_main_name decs) (MAP (Var Local ∘ FST) args)),
                                              rshape)))
                     |++ MAP (fun '(x, (y, (z, t))) => (x, (y, (compile nctxt z, t))))
                             (functions (fperm_decs start (new_main_name decs) decs))) s)).
Proof.
  intros s decs s' start args body rshape ndecls nfuns nexns nctxt (H & EA & He & Hc).
  pose proof (compile_top_shape_wf s decs s' start (conj H He)) as Hwf.
  pose proof (evaluate_decls_exns_wf s decs s' H) as (D & F & W).
  pose proof (exceptions_nexns _ _ _ _ _ _ _ _ Hc) as Ex.
  pose proof (compile_top_funs _ _ _ _ _ _ _ _ Hc) as Fn.
  unfold compile_top in Hwf |- *. rewrite EA in Hwf |- *. cbn zeta in Hwf |- *.
  rewrite dec_shapes_fperm_decs, dec_shapes_resort_decls_def in Hwf |- *. rewrite Hc in Hwf |- *.
  rewrite evaluate_decls_append.
  rewrite (exns_wf_evaluate_decls s nexns).
  2: { rewrite Ex. split; [|split; [exact D|split; [exact F|exact W]]].
       rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ Hc). apply EVERY_FILTER_self. }
  rewrite EVERY_app_ in Hwf. apply Bool.andb_true_iff in Hwf as [_ Hwf].
  rewrite evaluate_decls_only_functions_SOME.
  2: { split; [|exact Hwf]. cbn [EVERY is_function andb]. exact (compile_decs_EVERY_is_function _ _ _ _ _ _ Hc). }
  cbn [functions name params panLang.body fun_decl_return]. rewrite Fn. reflexivity.
Qed.

End TopDecls.

(** ** Semantics of [compile_top] *)

Section TopSem.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Local Open Scope word_scope.

(** HOL [s with top_addr := x]. *)
Definition set_top_addr x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) s.(code) s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) x.

Lemma FLOOKUP_FUPDATE_LIST_ALOOKUP {K V} `{EqDecision K} (l : list (K * V)) (fm : fmap K V) k :
  is_true (ALL_DISTINCT (MAP FST l)) ->
  FLOOKUP (fm |++ l) k = match ALOOKUP l k with SOME v0 => SOME v0 | NONE => FLOOKUP fm k end.
Proof.
  revert fm; induction l as [|[k0 v0] l IH]; intros fm Hd; [reflexivity|].
  - cbn in Hd. apply Bool.andb_true_iff in Hd as [Hn Hd].
    change (FLOOKUP ((fm |+ (k0, v0)) |++ l) k = match ALOOKUP ((k0, v0) :: l) k with SOME v1 => SOME v1 | NONE => FLOOKUP fm k end).
    rewrite (IH _ Hd). cbn [ALOOKUP]. rewrite FLOOKUP_UPDATE. destruct (decide (k0 = k)) as [<-|Hne].
    + destruct (ALOOKUP l k0) as [v1|] eqn:EA; [|reflexivity]. exfalso.
      apply Bool.negb_true_iff, Bool.not_true_iff_false in Hn. apply Hn.
      apply ALOOKUP_MEM in EA. apply MEM_is_true_In in EA. apply MEM_is_true_In, in_map_iff.
      exists (k0, v1). split; [reflexivity|exact EA].
    + reflexivity.
Qed.

Lemma FILTER_is_decl_fperm f g (l : list (decl a)) : FILTER is_decl (fperm_decs f g l) = FILTER is_decl l.
Proof. induction l as [|[] l IH]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma FILTER_FILTER_ {A} (P Q : A -> bool) (l : list A) :
  FILTER P (FILTER Q l) = FILTER (fun x => andb (Q x) (P x)) l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (Q x); cbn; [destruct (P x)|]; rewrite ?IH; reflexivity. Qed.

Lemma FILTER_ext_ {A} (P Q : A -> bool) l : (forall x, P x = Q x) -> FILTER P l = FILTER Q l.
Proof. intros H; induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Lemma FILTER_nil_ {A} (P : A -> bool) l : (forall x, P x = false) -> FILTER P l = [].
Proof. intros H; induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Lemma FILTER_is_decl_resort (l : list (decl a)) : FILTER is_decl (resort_decls l) = FILTER is_decl l.
Proof.
  unfold resort_decls. rewrite !filter_app, !FILTER_FILTER_.
  rewrite (FILTER_nil_ (fun x => andb (is_name x) (is_decl x))) by (intros []; reflexivity).
  rewrite (FILTER_nil_ (fun x => andb (is_exn_decl x) (is_decl x))) by (intros []; reflexivity).
  rewrite (FILTER_nil_ (fun x => andb (is_function x) (is_decl x))) by (intros []; reflexivity).
  rewrite (FILTER_ext_ (fun x => andb (is_decl x) (is_decl x)) is_decl) by (intros []; reflexivity).
  cbn [app]. apply app_nil_r.
Qed.

Lemma FILTER_is_exn_decl_resort (l : list (decl a)) : FILTER is_exn_decl (resort_decls l) = FILTER is_exn_decl l.
Proof.
  unfold resort_decls. rewrite !filter_app, !FILTER_FILTER_.
  rewrite (FILTER_nil_ (fun x => andb (is_name x) (is_exn_decl x))) by (intros []; reflexivity).
  rewrite (FILTER_nil_ (fun x => andb (is_decl x) (is_exn_decl x))) by (intros []; reflexivity).
  rewrite (FILTER_nil_ (fun x => andb (is_function x) (is_exn_decl x))) by (intros []; reflexivity).
  rewrite (FILTER_ext_ (fun x => andb (is_exn_decl x) (is_exn_decl x)) is_exn_decl) by (intros []; reflexivity).
  cbn [app]. apply app_nil_r.
Qed.

Lemma MAP_FST_functions_fperm f g (l : list (decl a)) :
  MAP FST (functions (fperm_decs f g l)) = MAP (fperm_name f g) (MAP FST (functions l)).
Proof. rewrite functions_fperm_decs. apply map_pick_up_first. Qed.

Lemma ALOOKUP_fperm f g (l : list (decl a)) n :
  ALOOKUP (functions (fperm_decs f g l)) (fperm_name f g n) = OPTION_MAP (I ## (fperm f g ## I)) (ALOOKUP (functions l) n).
Proof.
  rewrite functions_fperm_decs. induction (functions l) as [|[x [y [z w]]] r IH]; [reflexivity|].
  cbn [MAP List.map ALOOKUP]. destruct (decide (fperm_name f g x = fperm_name f g n)) as [E|E];
    destruct (decide (x = n)) as [E'|E']; try reflexivity.
  - apply fperm_name_cong in E. contradiction.
  - subst; contradiction.
  - exact IH.
Qed.

Lemma fperm_name_self f g : fperm_name f g f = g.
Proof. unfold fperm_name. destruct (decide (f = f)) as [|C]; [reflexivity|contradiction C; reflexivity]. Qed.

Lemma sr_code_locals ls ctxt s t C :
  state_rel ls ctxt s t ->
  (forall f vs p r, FLOOKUP C f = SOME (vs, (p, r)) -> FLOOKUP (code t) f = SOME (vs, (compile ctxt p, r))) ->
  state_rel true ctxt (set_locals (locals t) (set_code C s)) t.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19) HC.
  unfold state_rel, set_locals, set_code. cbn [locals globals structs code eshapes memory memaddrs sh_memaddrs clock be ffi
    base_addr top_addr]. repeat split; try assumption; intros _; reflexivity.
Qed.

End TopSem.

Section TopSemMain.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma FUPDATE_LIST_cons_ {K V} (fm : fmap K V) x l : fm |++ (x :: l) = (fm |+ x) |++ l.
Proof. reflexivity. Qed.

Lemma FUPDATE_LIST_nil_ {K V} (fm : fmap K V) : fm |++ [] = fm.
Proof. reflexivity. Qed.

Lemma FLOOKUP_UPDATE_SAME_ {K V} `{EqDecision K} (fm : fmap K V) k x : FLOOKUP (fm |+ (k, x)) k = SOME x.
Proof. rewrite FLOOKUP_UPDATE. destruct (decide (k = k)) as [|C]; [reflexivity|contradiction C; reflexivity]. Qed.

Lemma MAP_FST_compile_fn c (l : list (funname * (list (varname * shape) * (prog a * shape)))) :
  MAP FST (MAP (fun '(x, (y, (z, w))) => (x, (y, (compile c z, w)))) l) = MAP FST l.
Proof. induction l as [|[x [y [z w]]] l IH]; cbn; [reflexivity|]. f_equal; exact IH. Qed.

(*! HOL "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_semantics_decls" *)
Theorem compile_top_semantics_decls :
  forall (s t : state a ffi_t) start (code0 : list (decl a)) mgs free_addrs tmem tlocals,
  is_true (ALL_DISTINCT (MAP FST (functions code0))) /\
  t = set_locals tlocals (set_memory tmem (set_memaddrs (memaddrs s UNION free_addrs)
        (set_top_addr (top_addr s + mgs)%w s))) /\
  code s = FEMPTY /\
  globals s = FEMPTY /\
  is_true (byte_aligned (top_addr s)) /\
  good_dimindex a /\
  mgs = (bytes_in_word * n2w (SUM (MAP size_of_shape (dec_shapes code0))))%w /\
  free_addrs = addresses (top_addr s) (SUM (MAP size_of_shape (dec_shapes code0))) /\
  DISJOINT (memaddrs s) free_addrs /\
  (forall addr', addr' IN memaddrs s -> memory s addr' = tmem addr') /\
  (top_addr s + mgs)%w NOTIN memaddrs s /\
  w2n (bytes_in_word : word a) * SUM (MAP size_of_shape (dec_shapes code0)) < dimword a /\
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) code0) /\
  semantics_decls s start code0 <> Fail ->
  semantics_decls s start code0 = semantics_decls t start (compile_top code0 start).
Proof.
  intros s t start code0 mgs free_addrs tmem tlocals
    (Hd & Ht & Hcode & Hglob & Hal & Hg & Hmgs & Hfree & Hdis & Hmem & Hnot & Hbnd & He & Hsem).
  remember (SUM (MAP size_of_shape (dec_shapes code0))) as N0 eqn:HN0.
  (* the main function *)
  destruct (semantics_decls_has_main' s start code0 Hsem) as (body & rshape & Hmain).
  rewrite Hcode, FLOOKUP_FUPDATE_LIST_ALOOKUP in Hmain by exact Hd.
  destruct (ALOOKUP (functions code0) start) as [x|] eqn:EA; [|discriminate]. injection Hmain as ->.
  assert (Hst' : ~ In (new_main_name code0) (MAP FST (functions code0))).
  { intros Hin. apply (new_main_name_correct code0). apply MEM_is_true_In. exact Hin. }
  (* the source declarations *)
  unfold semantics_decls in Hsem |- *.
  rewrite (decs_stcnames_only_functions [] code0 He) in Hsem |- *.
  assert (Hfe : is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) (compile_top code0 start))).
  { apply (EVERY_mono (fun d => is_function d || is_exn_decl d)); [|apply compile_top_only_functions_or_exns].
    intros [] Hx; cbn in *; congruence. }
  rewrite (decs_stcnames_only_functions [] _ Hfe).
  destruct (evaluate_decls (set_structs [] s) code0) as [s1|] eqn:Es; [|contradiction Hsem; reflexivity].
  cbn beta iota in Hsem.
  subst t mgs free_addrs.
  set (ctxt0 := {| pan_globals.globals := FEMPTY; globals_size := n2w 0;
                   max_globals_size := (bytes_in_word * n2w N0)%w |} : context a).
  destruct (compile_decs ctxt0 (fperm_decs start (new_main_name code0) (resort_decls code0)))
    as [ndecls [nfuns [nexns nctxt]]] eqn:Ec.
  set (L := MAP (fun '(x, (y, (z, w))) => (x, (y, (compile nctxt z, w))))
                (functions (fperm_decs start (new_main_name code0) code0))).
  assert (Hfun : functions (compile_top code0 start) =
     (start, ([], (Seq (nested_seq ndecls) (TailCall (new_main_name code0) []), rshape))) :: L).
  { unfold compile_top. rewrite EA. cbn zeta. rewrite dec_shapes_fperm_decs, dec_shapes_resort_decls_def, <- HN0.
    fold ctxt0. rewrite Ec. rewrite functions_append.
    rewrite (functions_exns nexns) by (rewrite (compile_decs_exns_are_exns _ _ _ _ _ _ Ec); apply EVERY_FILTER_self).
    cbn [app functions name params panLang.body fun_decl_return MAP List.map]. f_equal.
    apply (compile_top_funs _ _ _ _ _ _ _ _ Ec). }
  pose proof (evaluate_decls_exns_wf _ _ _ Es) as (D & F & W).
  rewrite evaluate_decls_only_functions_and_exns_SOME.
  2: { rewrite (exceptions_compile_top code0 start _ EA).
       split; [apply compile_top_only_functions_or_exns|].
       split; [exact (compile_top_shape_wf (set_structs [] s) code0 s1 start (conj Es He))|].
       split; [exact D|split; [|exact W]].
       apply EVERY_In. intros [eid sh] Hin. apply bool_decide_spec.
       pose proof (proj1 (EVERY_In _ _) F _ Hin) as X. cbn in X. apply bool_decide_spec in X. exact X. }
  cbn beta iota.
  set (T1 := set_eshapes _ _).
  (* the source declarations, in resorted order *)
  rewrite <- (resort_decls_evaluate (set_structs [] s) code0 He) in Es.
  unfold resort_decls in Es. rewrite (FILTER_is_name_nil _ He) in Es. cbn [app] in Es.
  rewrite !evaluate_decls_append in Es.
  destruct (evaluate_decls (set_structs [] s) (FILTER is_exn_decl code0)) as [S1|] eqn:E1;
    cbn beta iota in Es; [|discriminate].
  rewrite evaluate_decls_append in Es.
  destruct (evaluate_decls S1 (FILTER is_decl code0)) as [S2|] eqn:E2; cbn beta iota in Es; [|discriminate].
  pose proof (evaluate_decls_only_exn_decls _ _ _ (conj (EVERY_FILTER_self _ _) E1)) as HS1.
  pose proof (evaluate_decls_only_functions _ _ _ (conj (EVERY_FILTER_self _ _) Es)) as Hs1.
  pose proof (evaluate_decls_functions _ _ _ E2) as Hc2. rewrite functions_FILTER' in Hc2.
  pose proof (compile_decs_FILTER_decs _ _ _ _ _ _ Ec) as EcD.
  rewrite FILTER_is_decl_fperm, FILTER_is_decl_resort in EcD.
  pose proof (w2n_bw Hg) as Hbw.
  assert (HsrI : state_rel false ctxt0 S1 (set_locals FEMPTY T1)).
  { rewrite HS1. unfold state_rel, T1, ctxt0.
    cbn [locals globals structs code eshapes memory memaddrs sh_memaddrs clock be ffi base_addr top_addr
         set_locals set_memory set_memaddrs set_top_addr set_eshapes set_code set_structs
         pan_globals.globals max_globals_size].
    split; [word_ring|]. split; [intros C; discriminate C|].
    split; [reflexivity|split; [reflexivity|]].
    split; [rewrite (exceptions_compile_top code0 start _ EA), (proj1 (proj2 (proj2 (exceptions_FILTER_is_function _))));
            reflexivity|].
    split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
    split; [intros v0 val Hv; rewrite Hglob in Hv; discriminate|].
    split; [apply FEVERY_FEMPTY|].
    split; [intros x Hx; apply IN_UNION; left; exact Hx|].
    split; [reflexivity|]. split; [exact Hmem|]. split; [reflexivity|].
    split; [intros f vs p r Hf; rewrite Hcode in Hf; discriminate|].
    split; [intros v1 v2 sh1 a1 sh2 a2 (_ & Hq1 & _); rewrite Hglob in Hq1; discriminate|].
    split.
    - intros Hin. apply IN_UNION in Hin as [Hin|Hin]; [exact (Hnot Hin)|].
      apply in_addresses in Hin as (i & Hi & Hlt).
      assert (E : ((n2w N0 : word a) * bytes_in_word)%w = (n2w i * bytes_in_word)%w).
      { apply (proj1 (WORD_EQ_ADD_LCANCEL (top_addr s) _ _)). rewrite <- Hi. word_ring. }
      apply n2w_mul_bw_inj in E; [lia|exact Hg| |].
      + rewrite <- Hbw, N.mul_comm. exact Hbnd.
      + apply (N.le_lt_trans _ (N0 * (dimindex a / 8))); [apply N.mul_le_mono_r; lia|].
        rewrite <- Hbw, N.mul_comm. exact Hbnd.
    - split; [apply byte_aligned_add; split; [exact Hal|apply byte_aligned_bytes_in_word_mul, Hg]|exact Hg]. }
  assert (HD0 : SUM (MAP size_of_shape (dec_shapes (FILTER is_decl code0))) = N0)
    by (rewrite (proj1 (proj2 (proj2 (dec_shapes_FILTER code0)))); exact (eq_sym HN0)).
  destruct (evaluate_decls_init_globals_lemma S1 (FILTER is_decl code0) S2 ndecls [] [] nctxt ctxt0
              (set_locals FEMPTY T1) (addresses (top_addr s) N0)) as (t2 & Et2 & Hr2 & Hck2 & Hff2 & Hlc2 & Hal2).
  { split; [exact E2|]. split; [apply EVERY_FILTER_self|]. split; [exact EcD|]. split; [exact HsrI|].
    rewrite HD0. split.
    { f_equal. unfold T1, ctxt0. cbn [top_addr set_locals set_memory set_memaddrs set_top_addr set_eshapes set_code
        set_structs globals_size]. word_ring. }
    split; [rewrite HS1; exact Hdis|].
    split; [intros x Hx; apply IN_UNION; right; exact Hx|].
    split; [apply (proj1 aligned_0)|].
    split; [rewrite HS1; exact Hcode|].
    split; [intros v0 sh addr' (Hq & _); rewrite HS1 in Hq; cbn [globals set_eshapes set_structs] in Hq;
            rewrite Hglob in Hq; discriminate|].
    exact Hbnd. }
  set (start' := new_main_name code0) in *.
  set (M := functions (fperm_decs start start' code0)) in *.
  assert (HdM : is_true (ALL_DISTINCT (MAP FST M))) by (apply ALL_DISTINCT_fperm_decs, Hd).
  assert (HdL : is_true (ALL_DISTINCT (MAP FST L))) by (unfold L; rewrite MAP_FST_compile_fn; exact HdM).
  assert (HnM : ALOOKUP M start = NONE).
  { apply ALOOKUP_NONE. intros Hm. apply MEM_is_true_In in Hm. unfold M in Hm.
    rewrite MAP_FST_functions_fperm in Hm. apply in_map_iff in Hm as (n & Hn & Hin).
    assert (n = start') by (rewrite <- (fperm_name_cancel start start' n), Hn; apply fperm_name_self).
    subst n. exact (Hst' Hin). }
  assert (HnL : ALOOKUP L start = NONE) by (unfold L; rewrite ALOOKUP_MAP4; cbn; rewrite HnM; reflexivity).
  assert (HM' : ALOOKUP M start' = SOME ([], (fperm start start' body, rshape))).
  { unfold M. rewrite <- (fperm_name_self start start') at 2. rewrite ALOOKUP_fperm, EA. reflexivity. }
  assert (HL' : ALOOKUP L start' = SOME ([], (compile nctxt (fperm start start' body), rshape)))
    by (unfold L; rewrite ALOOKUP_MAP4; cbn beta; rewrite HM'; reflexivity).
  assert (HcT1 : code T1 = (FEMPTY |+ (start, ([], (Seq (nested_seq ndecls) (TailCall start' []), rshape)))) |++ L).
  { unfold T1. cbn [code set_eshapes set_code set_structs set_locals set_memory set_memaddrs set_top_addr].
    rewrite Hcode, Hfun. reflexivity. }
  assert (Hinit : semantics T1 start = semantics t2 start').
  { apply (semantics_init_call' T1 t2 start start' (nested_seq ndecls) rshape [] (compile nctxt (fperm start start' body))).
    split; [rewrite HcT1, FLOOKUP_FUPDATE_LIST_ALOOKUP, HnL by exact HdL; apply FLOOKUP_UPDATE_SAME_|].
    split; [rewrite HcT1, FLOOKUP_FUPDATE_LIST_ALOOKUP, HL' by exact HdL; reflexivity|].
    split; [exact Et2|]. split; [exact Hck2|]. rewrite Hff2. reflexivity. }
  rewrite Hinit.
  pose proof (semantics_fperm s1 start start' start) as Hsf. rewrite fperm_name_self in Hsf.
  set (C := fperm_code start start' (code s1)) in Hsf.
  assert (HC : C = FEMPTY |++ M).
  { unfold C, M. rewrite Hs1. cbn [code set_code]. rewrite Hc2, HS1. cbn [code set_eshapes set_structs].
    rewrite Hcode, ?FUPDATE_LIST_nil_, functions_FILTER, fperm_code_FUPDATE_LIST_functions. cbn [FUPDATE_LIST FOLDL]. rewrite fperm_code_FEMPTY.
    reflexivity. }
  rewrite <- Hsf, (semantics_empty_locals (set_code C s1)). symmetry.
  apply (state_rel_imp_semantics nctxt). split.
  - assert (HCrel : forall f vs p r, FLOOKUP C f = SOME (vs, (p, r)) ->
                      FLOOKUP (code t2) f = SOME (vs, (compile nctxt p, r))).
    { intros f vs p r Hf. rewrite HC, FLOOKUP_FUPDATE_LIST_ALOOKUP in Hf by exact HdM.
      destruct (ALOOKUP M f) as [y|] eqn:EM; [injection Hf as ->|discriminate].
      pose proof (evaluate_invariants _ _ _ _ Et2) as (_ & _ & _ & _ & _ & _ & Hct & _).
      rewrite Hct. change (code (set_locals FEMPTY T1)) with (code T1).
      rewrite HcT1, FLOOKUP_FUPDATE_LIST_ALOOKUP by exact HdL.
      unfold L. rewrite ALOOKUP_MAP4. cbn beta. fold M. rewrite EM. reflexivity. }
    pose proof (sr_code_locals false nctxt S2 t2 C Hr2 HCrel) as G.
    rewrite Hlc2 in G. rewrite Hs1. exact G.
  - rewrite <- semantics_empty_locals, Hsf. exact Hsem.
Qed.

End TopSemMain.
