(** * CakeML [arm8_configProof]: the ARMv8 compiler configuration is well formed

    Port of [cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml]:
    [is_arm8_machine_config], [arm8_backend_config_ok],
    [arm8_machine_config_ok] and [arm8_init_ok].

    HOL proves the configuration obligations with [EVAL_TAC] and
    [blastLib.BBLAST_TAC]; here the arithmetic obligations are discharged by
    [vm_compute] and a few explicit lemmas ([land_mask_64] for
    [valid_immediate], [store_offset_w2i] for [store_offset], and
    [arm8_names_domain]/[arm8_names_BIJ] for the register-name map).

    HOL's [arm8_compile_correct] is not ported: it instantiates the
    compiler-level [compile_correct] theorem, which Galette does not have
    (only the Pancake-level [pan_to_target_compile_semantics] is ported).

    The Lean counterpart in Flapjack
    ([Flapjack/Compiler/Backend/Arm8Config/Proofs.lean]) proves
    [arm8MachineConfigOk] and [arm8InitOk] for its closed target; its
    [isArm8MachineConfig] is stated for different carriers and is
    deliberately untagged. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.examples.l3_machine_code.arm8.model Require Import arm8.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmProps.
From Galette.cakeml.compiler.encoders.arm8 Require Import arm8_target.
From Galette.cakeml.compiler.encoders.arm8.proofs Require Import arm8_targetProof.
From Galette.cakeml.compiler.backend Require Import
  backend backend_common stackLang stack_remove stack_names stack_to_lab.
From Galette.cakeml.compiler.backend.semantics Require Import
  targetSem stackProps.
From Galette.cakeml.compiler.backend.proofs Require Import backendProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  init_defs.
From Galette.cakeml.compiler.backend.arm8 Require Import arm8_config.
Open Scope N_scope.

(** The projection carrier of [arm8_target].  HOL writes this type inline;
    naming it keeps the statements below readable. *)
Definition arm8_proj_type : Type :=
  ProcState * (SCTLRType * (TCR_EL1 * (exception *
    ((word5 -> word64) * ((word64 * word8 -> Prop) * word64))))).

(*! HOL "cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml" "is_arm8_machine_config_def" *)
Definition is_arm8_machine_config
    (mc : targetSem.machine_config 64 arm8_state arm8_proj_type) : Prop :=
  mc.(targetSem.target) = arm8_target /\
  mc.(targetSem.len_reg) = 1 /\
  mc.(targetSem.ptr_reg) = 0 /\
  mc.(targetSem.len2_reg) = 3 /\
  mc.(targetSem.ptr2_reg) = 2 /\
  mc.(targetSem.callee_saved_regs) = [19; 20; 21; 22; 23; 24; 25; 26; 27; 28].

(** ** Arithmetic helpers for the backend configuration *)

Lemma aligned_0 {a : N} (w : word a) : aligned 0 w = true.
Proof.
  unfold aligned, align. cbn [N.pow]. rewrite N.div_1_r, N.mul_1_r, n2w_w2n.
  apply bool_decide_spec. reflexivity.
Qed.

Lemma w2i_off_min9 : w2i (off_min9 : word64) = (-256)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma w2i_off_max12 : w2i (off_max12 : word64) = (4095)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma w2i_off_min : w2i (off_min : word64) = (-4351)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma w2i_off_max : w2i (off_max : word64) = (4350)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma w2i_8 : w2i (n2w 8 : word64) = (8)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma w2i_neg8 : w2i (word_2comp (n2w 8 : word64)) = (-8)%Z.
Proof. vm_compute. reflexivity. Qed.

(** [x] below [4096] has no bits in common with [2^64 - 4096]. *)
Lemma land_mask_64 (x : N) : x < 4096 -> N.land x (2 ^ 64 - 4096) = 0.
Proof.
  intros Hx.
  replace (2 ^ 64 - 4096) with (N.lnot (N.ones 12) 64) by (vm_compute; reflexivity).
  replace x with (N.land x (N.ones 12)).
  - rewrite <- N.land_assoc.
    replace (N.land (N.ones 12) (N.lnot (N.ones 12) 64)) with 0 by (vm_compute; reflexivity).
    rewrite N.land_0_r. reflexivity.
  - rewrite N.land_ones, N.mod_small by lia. reflexivity.
Qed.

Lemma word_and_mask (x : N) : x < 4096 ->
  word_and (word_1comp (n2w 4095 : word64)) (n2w x : word64) = (n2w 0 : word64).
Proof.
  intros Hx. apply w2n_eq_0.
  unfold word_and, word_1comp.
  repeat rewrite w2n_n2w.
  replace (dimword 64) with (2 ^ 64) by (vm_compute; reflexivity).
  assert (Hpow : 4096 < 2 ^ 64) by (vm_compute; reflexivity).
  replace (4095 MOD 2 ^ 64) with 4095 by (symmetry; apply N.mod_small; lia).
  replace ((2 ^ 64 - 1 - 4095) MOD 2 ^ 64) with (2 ^ 64 - 4096)
    by (symmetry; apply N.mod_small; lia).
  replace (x MOD 2 ^ 64) with x by (symmetry; apply N.mod_small; lia).
  replace (N.land (2 ^ 64 - 4096) x MOD 2 ^ 64) with (N.land (2 ^ 64 - 4096) x).
  - rewrite N.land_comm. rewrite land_mask_64 by lia. reflexivity.
  - symmetry. apply N.mod_small. pose proof (N.land_le_r (2 ^ 64 - 4096) x). lia.
Qed.

(** [n <= 255] makes [8 * n] a small immediate: it fits the 12-bit
    [word_and (¬ 0xFFF)] test of [valid_immediate]. *)
Lemma valid_imm_mul8 (b : binop) (n : N) :
  (b = asm.Add \/ b = asm.Sub) -> n <= 255 ->
  valid_immediate (inl b) (n2w (n * 8) : word64) = true.
Proof.
  intros Hb Hn. unfold valid_immediate.
  unfold pred_set.IN, pred_set.INSERT, pred_set.EMPTY.
  destruct Hb as [E|E]; subst b; cbn;
    rewrite Bool.orb_true_iff; left; apply bool_decide_spec;
    apply word_and_mask; lia.
Qed.

(** ** The register-name map is a bijection on [N] *)

Lemma INDEX_FIND_bound {A : Type} (i j : N) (P : A -> bool) (l : list A) (h : A) :
  INDEX_FIND i P l = Some (j, h) -> j < i + LENGTH l.
Proof.
  revert i j h. induction l as [|x xs IH]; intros i j h H.
  - discriminate H.
  - cbn [INDEX_FIND] in H. destruct (P x) eqn:E.
    + injection H as Hj _. subst j. cbn [LENGTH]. lia.
    + apply IH in H. cbn [LENGTH]. lia.
Qed.

Lemma store_pos_bound (s : store_name) : store_pos s <= 48.
Proof.
  unfold store_pos.
  destruct (INDEX_FIND 0 (fun n => bool_decide (n = s)) store_list) as [[j h]|] eqn:E.
  - pose proof (INDEX_FIND_bound 0 j _ _ _ E).
    assert (HL : LENGTH store_list = 48) by (vm_compute; reflexivity).
    rewrite HL in H. lia.
  - lia.
Qed.

Lemma store_offset_w2i (s : store_name) :
  w2i (store_offset (a := 64) s) = (- Z.of_N (8 * store_pos s))%Z.
Proof.
  pose proof (store_pos_bound s) as Hb.
  unfold store_offset, word_sub, word_add, word_offset.
  rewrite w2n_n2w.
  rewrite N.mod_0_l by (vm_compute; discriminate).
  rewrite N.add_0_l.
  rewrite n2w_w2n.
  replace (dimindex 64 DIV 8) with 8 by (vm_compute; reflexivity).
  rewrite w2i_neg.
  - rewrite w2i_n2w_pos.
    + reflexivity.
    + assert (Hm : 384 < words.INT_MIN 64) by (vm_compute; reflexivity). lia.
  - intro H. apply (f_equal w2i) in H.
    rewrite w2i_n2w_pos in H.
    + assert (Hneg : (integer_word.INT_MIN 64 < 0)%Z) by (vm_compute; reflexivity).
      rewrite w2i_INT_MINw in H. lia.
    + assert (Hm : 384 < words.INT_MIN 64) by (vm_compute; reflexivity). lia.
Qed.

(** [tlookup] fixes every key outside the map's domain. *)
Lemma tlookup_id (m : spt N) (k : N) : ~ domain m k -> tlookup m k = k.
Proof.
  intros H. apply lookup_NONE_domain in H. unfold tlookup. rewrite H. reflexivity.
Qed.

Lemma dom_LS (x : N) (n : N) : domain (LS x) n <-> n = 0.
Proof. cbn [domain]. reflexivity. Qed.

Lemma dom_LN (n : N) : domain (@LN N) n <-> False.
Proof. cbn [domain]. tauto. Qed.

Lemma dom_BN_LS_LN (x : N) (n : N) : domain (BN (LS x) (@LN N)) n <-> n = 2.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_LS, ?dom_LN; bsimp; try lia; try intuition congruence.
Qed.

Lemma dom_BN_LS_LS (x y : N) (n : N) : domain (BN (LS x) (LS y)) n <-> n = 1 \/ n = 2.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_LS, ?dom_LN; bsimp; try lia; try intuition congruence.
Qed.

Lemma dom_L1 (n : N) :
  domain (BN (BN (LS 26) (@LN N)) (BN (LS 25) (LS 4))) n <-> n = 3 \/ n = 5 \/ n = 6.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_BN_LS_LN, ?dom_BN_LS_LS, ?dom_LS, ?dom_LN; bsimp;
    try lia; try intuition congruence.
Qed.

Lemma dom_R1 (n : N) :
  domain (BN (BN (LS 18) (@LN N)) (BN (LS 29) (@LN N))) n <-> n = 5 \/ n = 6.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_BN_LS_LN, ?dom_BN_LS_LS, ?dom_LS, ?dom_LN; bsimp;
    try lia; try intuition congruence.
Qed.

Lemma dom_L (n : N) :
  domain (BS (BN (BN (LS 26) (@LN N)) (BN (LS 25) (LS 4))) 1 (LS 3)) n <->
  n = 0 \/ n = 1 \/ n = 8 \/ n = 12 \/ n = 14.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_L1, ?dom_BN_LS_LN, ?dom_BN_LS_LS, ?dom_LS, ?dom_LN; bsimp;
    try lia; try intuition congruence.
Qed.

Lemma dom_R (n : N) :
  domain (BS (BN (BN (LS 18) (@LN N)) (BN (LS 29) (@LN N))) 0 (LS 2)) n <->
  n = 0 \/ n = 1 \/ n = 12 \/ n = 14.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_R1, ?dom_BN_LS_LN, ?dom_BN_LS_LS, ?dom_LS, ?dom_LN; bsimp;
    try lia; try intuition congruence.
Qed.

Lemma dom_root (n : N) :
  domain (BS (BS (BN (BN (LS 26) (@LN N)) (BN (LS 25) (LS 4))) 1 (LS 3)) 30
            (BS (BN (BN (LS 18) (@LN N)) (BN (LS 29) (@LN N))) 0 (LS 2))) n <->
  n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 18 \/ n = 25 \/ n = 26 \/ n = 29 \/ n = 30.
Proof.
  bitcase n; rewrite ?domain_0, ?domain_1, ?domain_2;
    cbn [spt_center spt_left spt_right]; bsimp;
    rewrite ?dom_L, ?dom_R, ?dom_L1, ?dom_R1, ?dom_BN_LS_LN, ?dom_BN_LS_LS, ?dom_LS, ?dom_LN; bsimp;
    try lia; try intuition congruence.
Qed.

Lemma arm8_names_domain (k : N) :
  domain arm8_names k <->
  k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/
  k = 18 \/ k = 25 \/ k = 26 \/ k = 29 \/ k = 30.
Proof. cbn [arm8_names]. apply dom_root. Qed.

(** [arm8_names] maps its domain onto itself (it is a permutation of the
    ten register names), so [tlookup] preserves domain membership. *)
Lemma arm8_tlookup_domain (k : N) :
  domain arm8_names k -> domain arm8_names (tlookup arm8_names k).
Proof.
  intros H. apply arm8_names_domain in H.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
  all: vm_compute; apply arm8_names_domain; intuition.
Qed.

Lemma arm8_names_INJ : INJ (tlookup arm8_names) UNIV UNIV.
Proof.
  split.
  - intros x _. exact I.
  - intros x y [_ _] Hxy.
    destruct (decide (domain arm8_names x)) as [Hx|Hx];
      destruct (decide (domain arm8_names y)) as [Hy|Hy].
    + apply arm8_names_domain in Hx, Hy.
      destruct Hx as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
      destruct Hy as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
      all: first [reflexivity | (vm_compute in Hxy; discriminate Hxy)].
    + pose proof Hy as Hny. apply tlookup_id in Hy. rewrite Hy in Hxy.
      apply arm8_tlookup_domain in Hx. rewrite Hxy in Hx. exfalso. exact (Hny Hx).
    + pose proof Hx as Hnx. apply tlookup_id in Hx. rewrite Hx in Hxy.
      apply arm8_tlookup_domain in Hy. rewrite <- Hxy in Hy. exfalso. exact (Hnx Hy).
    + apply tlookup_id in Hx, Hy. rewrite Hx, Hy in Hxy. exact Hxy.
Qed.

Lemma arm8_names_SURJ : SURJ (tlookup arm8_names) UNIV UNIV.
Proof.
  split.
  - intros x _. exact I.
  - intros y _.
    destruct (decide (domain arm8_names y)) as [Hy|Hy].
    { apply arm8_names_domain in Hy.
      destruct Hy as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
      all: first [ (exists 1; split; [exact I|vm_compute; reflexivity])
                 | (exists 2; split; [exact I|vm_compute; reflexivity])
                 | (exists 3; split; [exact I|vm_compute; reflexivity])
                 | (exists 4; split; [exact I|vm_compute; reflexivity])
                 | (exists 18; split; [exact I|vm_compute; reflexivity])
                 | (exists 29; split; [exact I|vm_compute; reflexivity])
                 | (exists 26; split; [exact I|vm_compute; reflexivity])
                 | (exists 30; split; [exact I|vm_compute; reflexivity])
                 | (exists 25; split; [exact I|vm_compute; reflexivity])
                 | (exists 0; split; [exact I|vm_compute; reflexivity]) ]. }
    { exists y. split; [exact I | apply tlookup_id; exact Hy]. }
Qed.

Lemma arm8_names_BIJ : BIJ (tlookup arm8_names) UNIV UNIV.
Proof. split; [apply arm8_names_INJ | apply arm8_names_SURJ]. Qed.

(** ** The configuration obligations *)

Lemma byte_offset_w (w : word64) :
  word_le (word_2comp (n2w 8 : word64)) w ->
  word_le w (n2w 8 : word64) ->
  byte_offset_ok arm8_config w.
Proof.
  intros H1 H2.
  unfold byte_offset_ok, offset_ok, arm8_config. cbn [byte_offset].
  apply andb_true_iff; split; [apply andb_true_iff; split|].
  - apply word_le_w2i. rewrite w2i_off_min9. apply word_le_w2i in H1. rewrite w2i_neg8 in H1. lia.
  - apply word_le_w2i. rewrite w2i_off_max12. apply word_le_w2i in H2. rewrite w2i_8 in H2. lia.
  - apply aligned_0.
Qed.

Lemma addr_offset_0 : addr_offset_ok arm8_config (n2w 0 : word64).
Proof.
  unfold addr_offset_ok, offset_ok, arm8_config. cbn [addr_offset].
  vm_compute. reflexivity.
Qed.

Lemma hw_offset_0 : hw_offset_ok arm8_config (n2w 0 : word64).
Proof.
  unfold hw_offset_ok, offset_ok, arm8_config. cbn [hw_offset].
  vm_compute. reflexivity.
Qed.

Lemma store_offset_addr_ok (s : store_name) :
  addr_offset_ok arm8_config (store_offset (a := 64) s).
Proof.
  unfold addr_offset_ok, offset_ok, arm8_config. cbn [addr_offset].
  apply andb_true_iff; split; [apply andb_true_iff; split|].
  - apply word_le_w2i. rewrite w2i_off_min. rewrite store_offset_w2i.
    pose proof (store_pos_bound s). lia.
  - apply word_le_w2i. rewrite w2i_off_max. rewrite store_offset_w2i.
    pose proof (store_pos_bound s). lia.
  - apply aligned_0.
Qed.

Lemma store_offset_hw_ok (s : store_name) :
  hw_offset_ok arm8_config (store_offset (a := 64) s).
Proof.
  unfold hw_offset_ok, offset_ok, arm8_config. cbn [hw_offset].
  apply andb_true_iff; split; [apply andb_true_iff; split|].
  - apply word_le_w2i. rewrite w2i_off_min. rewrite store_offset_w2i.
    pose proof (store_pos_bound s). lia.
  - apply word_le_w2i. rewrite w2i_off_max. rewrite store_offset_w2i.
    pose proof (store_pos_bound s). lia.
  - apply aligned_0.
Qed.

(*! HOL "cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml" "arm8_backend_config_ok" *)
Theorem arm8_backend_config_ok :
  backendProof.backend_config_ok arm8_config arm8_backend_config.
Proof.
  unfold backendProof.backend_config_ok.
  split. { reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; intros H; discriminate H. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; repeat split; try reflexivity; try (intros H; discriminate H). }
  split. { vm_compute; intros H; discriminate H. }
  split. { vm_compute; intros _; left; reflexivity. }
  split. { vm_compute; split; intros H;
             [discriminate H | destruct H as [H1 _]; discriminate H1]. }
  split. { vm_compute; split; intros H; discriminate H. }
  split. { vm_compute; intros H; discriminate H. }
  split. { vm_compute; reflexivity. }
  split. { apply addr_offset_0. }
  split. { apply hw_offset_0. }
  split. { intros w [H1 H2]. apply byte_offset_w; assumption. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { cbn. apply arm8_names_BIJ. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { intro s. apply store_offset_addr_ok. }
  split. { intro s. apply store_offset_hw_ok. }
  (* valid immediates n * 8 for n <= max_stack_alloc *)
  intros n Hn. split.
  - cbn [valid_imm arm8_config]. apply valid_imm_mul8; [right; reflexivity|exact Hn].
  - cbn [valid_imm arm8_config]. apply valid_imm_mul8; [left; reflexivity|exact Hn].
Qed.

(*! HOL "cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml" "arm8_machine_config_ok" *)
Theorem arm8_machine_config_ok
    (mc : targetSem.machine_config 64 arm8_state arm8_proj_type) :
  is_arm8_machine_config mc -> init_defs.mc_conf_ok mc.
Proof.
  intros [Ht [Hlen [Hptr [Hlen2 [Hptr2 _]]]]].
  unfold init_defs.mc_conf_ok. rewrite Ht, Hlen, Hptr, Hlen2, Hptr2.
  split; [right; reflexivity|].
  split; [exact arm8_encoder_correct|].
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  split. { vm_compute; reflexivity. }
  exact arm8_enc_ok.
Qed.

(*! HOL "cakeml/compiler/backend/arm8/proofs/arm8_configProofScript.sml" "arm8_init_ok" *)
Theorem arm8_init_ok
    (mc : targetSem.machine_config 64 arm8_state arm8_proj_type) :
  is_arm8_machine_config mc ->
  backendProof.mc_init_ok arm8_config arm8_backend_config mc.
Proof.
  intros [Ht [Hlen [Hptr [Hlen2 [Hptr2 Hcallee]]]]].
  unfold backendProof.mc_init_ok.
  rewrite Ht, Hlen, Hptr, Hlen2, Hptr2, Hcallee.
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  split. { vm_compute. try reflexivity; try exact I; try (intros H; discriminate H). }
  reflexivity.
Qed.
