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
      statement. *)

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
