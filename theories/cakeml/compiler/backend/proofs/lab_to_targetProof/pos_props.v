(** * CakeML [lab_to_targetProof]: positions of the assembled instructions

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 6570-6957): FFI entry points are disjoint from executed
    instructions, monotonicity and injectivity of [pos_val], [pos_val] at
    [num_pcs], and memory reads through the machine state.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [pos_val_asm_fetch_aux_distinct]: HOL's free variable [a] (an
      offset) is renamed [a0], [a] being the word size here.
    - HOL's [EVERY (\x. ∃op. x = SharedMem op)] and [FILTER (λx. ∃s. x =
      ExtCall s)] decide the predicates classically ([⌜_⌝]).
    - The ML helpers [map_first_cj], [enc_is_valid_mapped_access_tac],
      [share_mem_load_compile_correct_tac] and
      [share_mem_store_compile_correct_tac] (tactics, not theorems) are
      not ported. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target lab_filter.
From Galette.cakeml.compiler.backend.semantics Require backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute code_props.
Import backendProps (restrict_zero, restrict_nonzero).
Open Scope N_scope.

Section FfiDisjoint.
Context {a : N} {B C Ffi : Type}.

Lemma ffi_entry_pcs_disjoint_of (mc_conf : machine_config a B C) (t1 : asm_state a) p pos len :
  t1.(asmSem.pc) = (p + n2w pos)%w ->
  DISJOINT (set mc_conf.(ffi_entry_pcs))
    (fun x => exists a0, x = (p + n2w a0 + n2w pos)%w /\ a0 < len) ->
  ffi_entry_pcs_disjoint mc_conf t1 len.
Proof.
  intros Hpc H. unfold ffi_entry_pcs_disjoint. rewrite IN_DISJOINT in H |- *.
  intros (x & Hx1 & (a0 & -> & Ha0)). apply H. exists (t1.(asmSem.pc) + n2w a0)%w.
  split; [exact Hx1|]. exists a0. split; [|exact Ha0]. rewrite Hpc. word_ring.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_ffi_entry_pcs_disjoint_Asm" *)
Theorem IMP_ffi_entry_pcs_disjoint_Asm : forall (s1 : labSem.state a config Ffi)
    (mc_conf : machine_config a B C) code2 labs ffi_names instr _bytes _len p bytes' (t1 : asm_state a),
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  asm_fetch_aux s1.(pc) s1.(code) = SOME (Asm instr _bytes _len) /\
  (forall op re a0, instr <> ShareMem op re a0) /\
  share_mem_domain_code_rel mc_conf p code2 s1.(shared_mem_domain) /\
  bytes_in_mem (p + n2w (pos_val s1.(pc) 0 code2))%w bytes' t1.(asmSem.mem)
    t1.(asmSem.mem_domain) s1.(mem_domain) /\
  pos_val (s1.(pc) + 1) 0 code2 = LENGTH bytes' + pos_val s1.(pc) 0 code2 /\
  t1.(asmSem.pc) = (p + n2w (pos_val s1.(pc) 0 code2))%w ->
  ffi_entry_pcs_disjoint mc_conf t1 (LENGTH bytes').
Proof.
  intros s1 mc_conf code2 labs ffi_names instr _bytes _len p bytes' t1
    (Hs & Hok & Hf & Hi & Hsh & _ & Hpv & Hpc).
  pose proof (code_similar_IMP_asm_fetch_aux_line_similar s1.(pc) _ _ Hs) as Hr.
  rewrite Hf in Hr. destruct Hr as [[Hc _]|(x0 & y0 & E & Hy & Hsim)]; [discriminate|].
  injection E as <-. destruct y0 as [| b bytes2 len2 |]; cbn in Hsim; try contradiction. subst b.
  apply (ffi_entry_pcs_disjoint_of _ _ p (pos_val s1.(pc) 0 code2)); [exact Hpc|].
  destruct Hsh as (_ & Hsh & _).
  rewrite <- (asm_fetch_aux_pos_val_LENGTH_EQ _ _ _ bytes' s1.(pc) 0 code2 _ (conj Hy (conj Hok Hpv))).
  apply (Hsh s1.(pc) (Asm instr bytes2 len2)). split; [exact Hy|].
  intros op re a0 inst len E. injection E as E _ _. exact (Hi _ _ _ E).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_ffi_entry_pcs_disjoint_LabAsm" *)
Theorem IMP_ffi_entry_pcs_disjoint_LabAsm : forall (s1 : labSem.state a config Ffi)
    (mc_conf : machine_config a B C) code2 labs ffi_names instr _pos _bytes _len p bytes' (t1 : asm_state a),
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  asm_fetch_aux s1.(pc) s1.(code) = SOME (LabAsm instr _pos _bytes _len) /\
  share_mem_domain_code_rel mc_conf p code2 s1.(shared_mem_domain) /\
  bytes_in_mem (p + n2w (pos_val s1.(pc) 0 code2))%w bytes' t1.(asmSem.mem)
    t1.(asmSem.mem_domain) s1.(mem_domain) /\
  pos_val (s1.(pc) + 1) 0 code2 = LENGTH bytes' + pos_val s1.(pc) 0 code2 /\
  t1.(asmSem.pc) = (p + n2w (pos_val s1.(pc) 0 code2))%w ->
  ffi_entry_pcs_disjoint mc_conf t1 (LENGTH bytes').
Proof.
  intros s1 mc_conf code2 labs ffi_names instr _pos _bytes _len p bytes' t1
    (Hs & Hok & Hf & Hsh & _ & Hpv & Hpc).
  pose proof (code_similar_IMP_asm_fetch_aux_line_similar s1.(pc) _ _ Hs) as Hr.
  rewrite Hf in Hr. destruct Hr as [[Hc _]|(x0 & y0 & E & Hy & Hsim)]; [discriminate|].
  injection E as <-. destruct y0 as [| |x w bytes2 len2]; cbn in Hsim; try contradiction. subst x.
  apply (ffi_entry_pcs_disjoint_of _ _ p (pos_val s1.(pc) 0 code2)); [exact Hpc|].
  destruct Hsh as (_ & Hsh & _).
  rewrite <- (asm_fetch_aux_pos_val_LENGTH_EQ _ _ _ bytes' s1.(pc) 0 code2 _ (conj Hy (conj Hok Hpv))).
  apply (Hsh s1.(pc) (LabAsm instr w bytes2 len2)). split; [exact Hy|].
  intros op re a0 inst len E. discriminate E.
Qed.

End FfiDisjoint.

Section PosVal.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_SOME_IMP_LESS_num_pcs" *)
Theorem asm_fetch_SOME_IMP_LESS_num_pcs : forall pc (secs : list (sec a)) x,
  asm_fetch_aux pc secs = SOME x ->
  pc < num_pcs secs.
Proof.
  intros pc secs. revert pc.
  induction secs as [|k ys IH|k y ys xs IH] using code_ind; intros pc x H.
  - discriminate.
  - exact (IH _ _ H).
  - rewrite (proj2 (proj2 asm_fetch_aux_def)) in H. rewrite (proj2 (proj2 (num_pcs_def k y ys xs))).
    destruct (is_Label y); [exact (IH _ _ H)|].
    destruct (N.eqb_spec pc 0); [lia|]. specialize (IH _ _ H). lia.
Qed.

Lemma GENLIST_ext_lt {X} (f g : N -> X) n : (forall i, i < n -> f i = g i) -> GENLIST f n = GENLIST g n.
Proof.
  induction n as [|n IH] using N.peano_ind; intros H; [reflexivity|].
  rewrite !(proj2 (GENLIST_thm _ n)), IH by (intros i Hi; apply H; lia). f_equal. apply H; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "GENLIST_asm_fetch_aux_next" *)
Theorem GENLIST_asm_fetch_aux_next : forall (x : line a) k xs rest n,
  ~ is_Label x ->
  GENLIST (fun i => (i, asm_fetch_aux i (Section_ k (x :: xs) :: rest))) (n + 1) =
  (0, SOME x) :: GENLIST (fun i => (i + 1, asm_fetch_aux i (Section_ k xs :: rest))) n.
Proof.
  intros x k xs rest n Hx. rewrite N.add_1_r, GENLIST_CONS_aux.
  rewrite (proj2 (proj2 asm_fetch_aux_def)). apply Bool.not_true_iff_false in Hx. rewrite Hx.
  cbn [N.eqb]. f_equal. apply GENLIST_ext_lt. intros i _.
  rewrite (proj2 (proj2 asm_fetch_aux_def)), Hx.
  rewrite (proj2 (N.eqb_neq _ _)) by lia. rewrite N.add_1_r. f_equal. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_acc_sum" *)
Theorem pos_val_acc_sum : forall i pos (secs : list (sec a)) x y,
  x + y = pos ->
  x + pos_val i y secs = pos_val i pos secs.
Proof.
  intros i pos secs. revert i pos.
  induction secs as [|k ys IH|k y0 ys xs IH] using code_ind; intros i pos x y H.
  - exact H.
  - exact (IH _ _ _ _ H).
  - rewrite !(proj2 (proj2 (pos_val_def _ _ k xs y0 ys))).
    destruct (is_Label y0); [apply IH; lia|]. destruct (i =? 0); [exact H|]. apply IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_acc_0" *)
Theorem pos_val_acc_0 : forall i pos (secs : list (sec a)),
  pos + pos_val i 0 secs = pos_val i pos secs.
Proof. intros i pos secs. apply pos_val_acc_sum. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_GE_pc" *)
Theorem pos_val_GE_pc : forall i p (code2 : list (sec a)),
  p <= pos_val i p code2.
Proof. intros i p code2. rewrite <- pos_val_acc_0. lia. Qed.

End PosVal.

Lemma EL_cons_succ {A} `{Inhabited A} n (x : A) l : EL (N.succ n) (x :: l) = EL n l.
Proof. rewrite EL_SUC. reflexivity. Qed.

Lemma EL_app_lt {A} `{Inhabited A} n (l1 l2 : list A) : n < LENGTH l1 -> EL n (l1 ++ l2) = EL n l1.
Proof.
  revert n; induction l1 as [|x l1 IH]; intros n Hn; cbn [LENGTH] in Hn; [lia|].
  destruct (N.zero_or_succ n) as [->|[m ->]]; [reflexivity|].
  rewrite <- app_comm_cons, !EL_cons_succ. apply IH. lia.
Qed.

Lemma EL_app_ge {A} `{Inhabited A} n (l1 l2 : list A) :
  LENGTH l1 <= n -> EL n (l1 ++ l2) = EL (n - LENGTH l1) l2.
Proof.
  revert n; induction l1 as [|x l1 IH]; intros n Hn; cbn [LENGTH app] in *; [f_equal; lia|].
  destruct (N.zero_or_succ n) as [->|[m ->]]; [lia|].
  rewrite EL_cons_succ, IH by lia. f_equal. lia.
Qed.

Lemma EL_In_lt {A} `{Inhabited A} n (l : list A) : n < LENGTH l -> In (EL n l) l.
Proof.
  revert n; induction l as [|x l IH]; intros n Hn; cbn [LENGTH] in Hn; [lia|].
  destruct (N.zero_or_succ n) as [->|[m ->]]; [left; reflexivity|].
  rewrite EL_cons_succ. right. apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "FILTER_mmio_pcs_min_index" *)
Theorem FILTER_mmio_pcs_min_index : forall (l ffis : list ffiname),
  EVERY (fun x => ⌜exists op, x = SharedMem op⌝) l ->
  mmio_pcs_min_index
    (FILTER (fun x => ⌜exists s, x = ExtCall s⌝) ffis ++ l) =
  SOME (LENGTH (FILTER (fun x => ⌜exists s, x = ExtCall s⌝) ffis)).
Proof.
  intros l ffis Hl. set (F := FILTER (fun x => ⌜exists s, x = ExtCall s⌝) ffis).
  assert (HF : forall x, In x F -> exists s, x = ExtCall s).
  { intros x Hx. unfold F in Hx. apply filter_In in Hx as [_ Hx]. apply bool_decide_spec in Hx. exact Hx. }
  assert (HL : forall x, In x l -> exists op, x = SharedMem op).
  { intros x Hx. unfold is_true in Hl. rewrite EVERY_Forall, List.Forall_forall in Hl.
    apply (proj1 (bool_decide_spec _)), Hl, Hx. }
  assert (Hp : forall x,
    (x <= LENGTH (F ++ l) /\
     (forall j, j < x -> exists s, EL j (F ++ l) = ExtCall s) /\
     (forall j, x <= j /\ j < LENGTH (F ++ l) -> exists op, EL j (F ++ l) = SharedMem op)) <->
    x = LENGTH F).
  { intros x. rewrite LENGTH_app. split.
    - intros (H1 & H2 & H3). destruct (N.lt_trichotomy x (LENGTH F)) as [Hx|[Hx|Hx]]; [|exact Hx|].
      + exfalso. assert (Hx' : x < LENGTH F + LENGTH l) by lia.
        destruct (H3 x (conj (N.le_refl _) Hx')) as [op Hop].
        rewrite EL_app_lt in Hop by exact Hx.
        destruct (HF (EL x F) (EL_In_lt _ _ Hx)) as [s Hs]. rewrite Hs in Hop. discriminate.
      + exfalso. destruct (H2 (LENGTH F) Hx) as [s Hs].
        rewrite EL_app_ge in Hs by lia. rewrite N.sub_diag in Hs.
        assert (H0 : 0 < LENGTH l) by lia.
        destruct (HL (EL 0 l) (EL_In_lt _ _ H0)) as [op Hop]. rewrite Hop in Hs. discriminate.
    - intros ->. split; [lia|]. split.
      + intros j Hj. rewrite EL_app_lt by exact Hj. apply HF, EL_In_lt, Hj.
      + intros j [Hj1 Hj2]. rewrite EL_app_ge by exact Hj1. apply HL, EL_In_lt. lia. }
  unfold mmio_pcs_min_index. unfold some.
  destruct (classical_dec _) as [Hex|Hn].
  - f_equal. apply Hp. apply (select_spec _ Hex).
  - exfalso. apply Hn. exists (LENGTH F). apply Hp. reflexivity.
Qed.

Section PosValMono.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_ok_LENGTH_GT_0" *)
Theorem enc_ok_LENGTH_GT_0 : forall (c : asm_config a) l,
  enc_ok c ->
  0 < LENGTH (encode c l).
Proof. intros c l (_ & H & _). apply N.neq_0_lt_0, (proj2 (H l)). Qed.

Lemma line_ok_not_Label_pos (c : asm_config a) labs ffis pos (y : line a) :
  enc_ok c -> line_ok c labs ffis pos y -> ~ is_Label y -> 0 < line_length y.
Proof.
  intros Hc Hy Hl. destruct y as [k1 k2 l|b bytes l|x w bytes l]; [exfalso; apply Hl; reflexivity| |];
    cbn [line_ok line_length] in Hy |- *.
  - destruct Hy as (He & _). apply enc_with_nop_thm in He as [nn ->]. rewrite LENGTH_app.
    pose proof (enc_ok_LENGTH_GT_0 c (cbw_to_asm b) Hc). lia.
  - destruct x as [[l1 l2]|cc r ri [l1 l2]|v|r [l1 l2]|s| |]; cbn [get_label] in Hy; cbv zeta in Hy;
      try contradiction;
      try (destruct (lab_lookup l1 l2 labs); [|contradiction]);
      destruct Hy as (He & _); apply enc_with_nop_thm in He as [nn ->]; rewrite LENGTH_app;
      match goal with |- 0 < LENGTH (encode c ?i) + _ => pose proof (enc_ok_LENGTH_GT_0 c i Hc) end; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_mono" *)
Theorem pos_val_mono : forall i p (code2 : list (sec a)) j p' c labs ffis,
  i < j /\
  j <= num_pcs code2 /\
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c ->
  pos_val i p code2 < pos_val j p code2.
Proof.
  intros i p code2. revert i p.
  induction code2 as [|k ys IH|k y ys xs IH] using code_ind; intros i p j p' c labs ffis (Hij & Hj & Hok & Hc).
  - cbn in Hj. lia.
  - destruct Hok as [_ Hok]. exact (IH _ _ _ _ _ _ _ (conj Hij (conj Hj (conj Hok Hc)))).
  - destruct Hok as [Hy Hok]. rewrite (proj2 (proj2 (num_pcs_def k y ys xs))) in Hj.
    rewrite !(proj2 (proj2 (pos_val_def _ _ k xs y ys))).
    destruct (is_Label y) eqn:Hl; [exact (IH _ _ _ _ _ _ _ (conj Hij (conj Hj (conj Hok Hc))))|].
    destruct (N.eqb_spec j 0); [lia|]. destruct (N.eqb_spec i 0) as [->|Hi].
    + assert (Hnl : ~ is_Label y) by (rewrite Hl; discriminate).
      pose proof (line_ok_not_Label_pos _ _ _ _ _ Hc Hy Hnl).
      pose proof (pos_val_GE_pc (j - 1) (p + line_length y) (Section_ k ys :: xs)). lia.
    + apply (IH _ _ _ (p' + line_length y) c labs ffis). split; [lia|split; [lia|split; [exact Hok|exact Hc]]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_mono_inv" *)
Theorem pos_val_mono_inv : forall i p (code2 : list (sec a)) j c labs ffis p',
  pos_val i p code2 < pos_val j p code2 /\
  i <= num_pcs code2 /\
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c ->
  i < j.
Proof.
  intros i p code2 j c labs ffis p' (H & Hi & Hok & Hc).
  destruct (N.lt_ge_cases i j) as [Hl|Hl]; [exact Hl|exfalso].
  destruct (N.eq_dec i j) as [->|Hne]; [lia|].
  assert (Hji : j < i) by lia.
  pose proof (pos_val_mono j p code2 i p' c labs ffis (conj Hji (conj Hi (conj Hok Hc)))). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_inj" *)
Theorem pos_val_inj : forall i p (code2 : list (sec a)) j c labs ffis p',
  pos_val i p code2 = pos_val j p code2 /\
  i <= num_pcs code2 /\ j <= num_pcs code2 /\
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c ->
  i = j.
Proof.
  intros i p code2 j c labs ffis p' (H & Hi & Hj & Hok & Hc).
  destruct (N.lt_trichotomy i j) as [Hl|[E|Hl]]; [exfalso| exact E |exfalso].
  - pose proof (pos_val_mono i p code2 j p' c labs ffis (conj Hl (conj Hj (conj Hok Hc)))). lia.
  - pose proof (pos_val_mono j p code2 i p' c labs ffis (conj Hl (conj Hi (conj Hok Hc)))). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_num_pcs" *)
Theorem pos_val_num_pcs : forall c labs ffis p' (code2 : list (sec a)) p,
  all_enc_ok c labs ffis p' code2 ->
  pos_val (num_pcs code2) p code2 = p + LENGTH (prog_to_bytes code2).
Proof.
  intros c labs ffis p' code2. revert p'.
  induction code2 as [|k ys IH|k y ys xs IH] using code_ind; intros p' p H.
  - cbn. lia.
  - destruct H as [_ H]. exact (IH _ _ H).
  - destruct H as [Hy H]. rewrite (proj2 (proj2 (num_pcs_def k y ys xs))).
    rewrite (proj2 (proj2 (prog_to_bytes_def k y ys xs))), LENGTH_app, (line_ok_line_byte_length _ _ _ _ _ Hy).
    rewrite (proj2 (proj2 (pos_val_def _ _ k xs y ys))).
    destruct (is_Label y); [rewrite (IH _ _ H); lia|].
    rewrite (proj2 (N.eqb_neq _ _)) by lia. replace (1 + num_pcs (Section_ k ys :: xs) - 1)
      with (num_pcs (Section_ k ys :: xs)) by lia.
    rewrite (IH _ _ H). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_GE_num_pcs" *)
Theorem pos_val_GE_num_pcs : forall pc p (code2 : list (sec a)),
  num_pcs code2 <= pc ->
  pos_val (num_pcs code2) p code2 = pos_val pc p code2.
Proof.
  intros pc p code2. revert pc p.
  induction code2 as [|k ys IH|k y ys xs IH] using code_ind; intros pc p H.
  - reflexivity.
  - exact (IH _ _ H).
  - rewrite (proj2 (proj2 (num_pcs_def k y ys xs))) in H |- *.
    rewrite !(proj2 (proj2 (pos_val_def _ _ k xs y ys))).
    destruct (is_Label y); [apply IH, H|].
    rewrite !(proj2 (N.eqb_neq _ _)) by lia.
    replace (1 + num_pcs (Section_ k ys :: xs) - 1) with (num_pcs (Section_ k ys :: xs)) by lia.
    apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_0_aux" *)
Theorem pos_val_0_aux : forall c labs ffis p (xs : list (sec a)) pos,
  all_enc_ok c labs ffis p xs -> pos_val 0 pos xs = pos.
Proof.
  intros c labs ffis p xs pos H. pose proof (pos_val_0 xs c labs ffis p H) as H0.
  rewrite <- (pos_val_acc_0 0 p xs) in H0. rewrite <- pos_val_acc_0. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_aux_pos_val_SUC" *)
Theorem asm_fetch_aux_pos_val_SUC : forall pc p (code2 : list (sec a)) p' c labs ffi line,
  all_enc_ok c labs ffi p' code2 /\
  asm_fetch_aux pc code2 = SOME line ->
  LENGTH (line_bytes line) + pos_val pc p code2 = pos_val (pc + 1) p code2.
Proof.
  intros pc p code2. revert pc p.
  induction code2 as [|k ys IH|k y ys xs IH] using code_ind; intros pc p p' c labs ffi line (Hok & Hf).
  - discriminate.
  - destruct Hok as [_ Hok]. exact (IH _ _ _ _ _ _ _ (conj Hok Hf)).
  - destruct Hok as [Hy Hok]. rewrite (proj2 (proj2 asm_fetch_aux_def)) in Hf.
    rewrite !(proj2 (proj2 (pos_val_def _ _ k xs y ys))).
    destruct (is_Label y); [exact (IH _ _ _ _ _ _ _ (conj Hok Hf))|].
    rewrite (proj2 (N.eqb_neq (pc + 1) 0)) by lia.
    destruct (N.eqb_spec pc 0) as [->|Hpc].
    + injection Hf as <-. cbn [N.add]. rewrite (pos_val_0_aux c labs ffi (p' + line_length y) (Section_ k ys :: xs) _ Hok).
      rewrite (line_ok_line_byte_length _ _ _ _ _ Hy). lia.
    + replace (pc + 1 - 1) with (pc - 1 + 1) by lia. exact (IH _ _ _ _ _ _ _ (conj Hok Hf)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_asm_fetch_aux_distinct" *)
Theorem pos_val_asm_fetch_aux_distinct : forall c labs ffis p' (code2 : list (sec a)) pc line a0 pc' p,
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c /\
  asm_fetch_aux pc code2 = SOME line /\
  a0 < LENGTH (line_bytes line) /\
  LENGTH (prog_to_bytes code2) < dimword a /\
  pc' <> pc ->
  a0 + pos_val pc p code2 <> pos_val pc' p code2.
Proof.
  intros c labs ffis p' code2 pc line a0 pc' p (Hok & Hc & Hf & Ha & _ & Hne) E.
  pose proof (asm_fetch_SOME_IMP_LESS_num_pcs _ _ _ Hf) as Hlt.
  pose proof (asm_fetch_aux_pos_val_SUC pc p code2 p' c labs ffis line (conj Hok Hf)) as Hsuc.
  destruct (N.lt_ge_cases pc' pc) as [Hl|Hg].
  - assert (Hle : pc <= num_pcs code2) by lia.
    pose proof (pos_val_mono pc' p code2 pc p' c labs ffis (conj Hl (conj Hle (conj Hok Hc)))). lia.
  - assert (Hg' : pc + 1 <= pc') by lia.
    destruct (N.le_gt_cases pc' (num_pcs code2)) as [Hn|Hn].
    + destruct (N.eq_dec (pc + 1) pc') as [<-|Hne'].
      * lia.
      * assert (Hl1 : pc + 1 < pc') by lia.
        pose proof (pos_val_mono (pc + 1) p code2 pc' p' c labs ffis
                      (conj Hl1 (conj Hn (conj Hok Hc)))). lia.
    + rewrite <- (pos_val_GE_num_pcs pc' p code2) in E by lia.
      destruct (N.eq_dec (pc + 1) (num_pcs code2)) as [Hq|Hq].
      * rewrite <- Hq in E. lia.
      * assert (Hl1 : pc + 1 < num_pcs code2) by lia.
        pose proof (pos_val_mono (pc + 1) p code2 (num_pcs code2) p' c labs ffis
                      (conj Hl1 (conj (N.le_refl _) (conj Hok Hc)))). lia.
Qed.

End PosValMono.

Section MemEq.
Context {a : N} {B C : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_memory_eq_mem" *)
Theorem bytes_in_memory_eq_mem : forall (t1 : asm_state a) (mc_conf : machine_config a B C) ms1 pc bytes,
  (forall a0, a0 IN t1.(asmSem.mem_domain) -> get_byte mc_conf.(target) ms1 a0 = t1.(asmSem.mem) a0) /\
  bytes_in_memory pc bytes t1.(asmSem.mem) t1.(asmSem.mem_domain) ->
  bytes_in_memory pc bytes (get_byte mc_conf.(target) ms1) t1.(asmSem.mem_domain).
Proof.
  intros t1 mc_conf ms1 pc bytes; revert pc. induction bytes as [|b bytes IH]; intros pc (Hm & Hb);
    [exact Logic.I|].
  destruct Hb as (H1 & H2 & H3). split; [rewrite Hm by exact H2; exact H1|]. split; [exact H2|].
  apply IH. split; assumption.
Qed.

End MemEq.

