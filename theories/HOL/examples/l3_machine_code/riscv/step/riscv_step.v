(** * HOL4 [riscv_step]: the simplified RISC-V step function

    Port of [HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml]
    (partial): the simplified [Fetch] and [NextRISCV] used by CakeML's
    RISC-V target, and the evaluation theorems that are stated in the
    script.

    HOL's [Fetch_def] here is a second constant [riscv_step$Fetch]
    (distinct from the model's [riscv$Fetch]); in Rocq it is
    [riscv_step.Fetch], and the model's is [riscv.Fetch].

    Not ported: the theorems produced by the step evaluator
    ([utilsLib.STEP]: [Skip], [update_pc] and the per-instruction
    theorems [ADDI], [ADDI_NOP], ..., whose statements are computed by
    ML code; Rocq proofs evaluate the model directly instead), the
    [select] operation (deleted at the end of the script), and the theorems
    [Fetch32], [Fetch16]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words bitstring.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
Open Scope N_scope.

(** ** Simplified Fetch and Next functions *)

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "Fetch_def" *)
Definition Fetch (s : riscv_state) : rawInstType * riscv_state :=
  let '(w, s) := translateAddr (PC s, Instruction, Read) s in
  rawReadInst (THE w) s.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "update_pc_def" *)
Definition update_pc (v : word64) (s : riscv_state) : option riscv_state :=
  Some (write'PC v s).

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DecodeAny_def" *)
Definition DecodeAny (f : rawInstType) : instruction :=
  match f with Half h => DecodeRVC h | Word w => Decode w end.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "NextRISCV_def" *)
Definition NextRISCV (s : riscv_state) : option riscv_state :=
  let '(f, s) := Fetch s in
  let s := Run (DecodeAny f) s in
  if negb (bool_decide (riscv_state_exception s = NoException)) then
    None
  else
    let pc := PC s in
    match NextFetch s with
    | None => update_pc (word_add pc (Skip s)) s
    | Some (BranchTo a) => update_pc a (write'NextFetch None s)
    | _ => None
    end.

(** ** Evaluation theorems *)

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "NextRISCV" 59 *)
Theorem NextRISCV_thm : forall s w s' i nxt,
  Fetch s = (w, s') /\
  DecodeAny w = i /\
  Run i s' = nxt /\
  riscv_state_exception nxt = NoException /\
  riscv_state_c_NextFetch nxt (riscv_state_procID nxt) = None ->
  NextRISCV s =
  update_pc (word_add (riscv_state_c_PC nxt (riscv_state_procID nxt)) (Skip nxt)) nxt.
Proof.
  intros s w s' i nxt (HF & HD & HR & HE & HN).
  unfold NextRISCV; rewrite HF, HD, HR, HE.
  unfold NextFetch; rewrite HN; reflexivity.
Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "NextRISCV_branch" *)
Theorem NextRISCV_branch : forall s w s' i nxt a,
  Fetch s = (w, s') /\
  DecodeAny w = i /\
  Run i s' = nxt /\
  riscv_state_exception nxt = NoException /\
  riscv_state_c_NextFetch nxt (riscv_state_procID nxt) = Some (BranchTo a) ->
  NextRISCV s =
  update_pc a
    (riscv_state_c_NextFetch_fupd
       (fun _ => UPDATE (riscv_state_procID nxt) None (riscv_state_c_NextFetch nxt)) nxt).
Proof.
  intros s w s' i nxt a (HF & HD & HR & HE & HN).
  unfold NextRISCV; rewrite HF, HD, HR, HE.
  unfold NextFetch; rewrite HN; reflexivity.
Qed.

Lemma riscv_state_c_NextFetch_fupd_id (nxt : riscv_state) :
  riscv_state_c_NextFetch nxt (riscv_state_procID nxt) = None ->
  riscv_state_c_NextFetch_fupd
    (fun _ => UPDATE (riscv_state_procID nxt) None (riscv_state_c_NextFetch nxt)) nxt = nxt.
Proof.
  intros H; destruct nxt; unfold riscv_state_c_NextFetch_fupd; cbn in *; f_equal.
  apply functional_extensionality; intros x; unfold UPDATE.
  destruct (decide (riscv_state_procID = x)) as [->|]; [exact (eq_sym H)|reflexivity].
Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "NextRISCV_cond_branch" *)
Theorem NextRISCV_cond_branch : forall s w s' i nxt (b : bool) a,
  Fetch s = (w, s') /\
  DecodeAny w = i /\
  Run i s' = nxt /\
  riscv_state_exception nxt = NoException /\
  riscv_state_c_NextFetch nxt (riscv_state_procID nxt) =
    (if b then Some (BranchTo a) else None) ->
  NextRISCV s =
  update_pc
    (if b then a else word_add (riscv_state_c_PC nxt (riscv_state_procID nxt)) (Skip nxt))
    (riscv_state_c_NextFetch_fupd
       (fun _ => UPDATE (riscv_state_procID nxt) None (riscv_state_c_NextFetch nxt)) nxt).
Proof.
  intros s w s' i nxt b a (HF & HD & HR & HE & HN); destruct b.
  - apply NextRISCV_branch with w s' i; auto.
  - rewrite riscv_state_c_NextFetch_fupd_id by exact HN.
    apply NextRISCV_thm with w s' i; auto.
Qed.

(** ** Simplifying rewrites *)

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "word_bit_1_0" *)
Theorem word_bit_1_0 : forall x0 x1 x2 x3 x4 x5 x6 x7,
  word_bit 1 (v2w [x0; x1; x2; x3; x4; x5; x6; x7] : word8) = x6 /\
  word_bit 0 (v2w [x0; x1; x2; x3; x4; x5; x6; x7] : word8) = x7.
Proof.
  intros [] [] [] [] [] [] [] []; split; vm_compute; reflexivity.
Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "word_bit_0_lemmas" *)
Theorem word_bit_0_lemmas : forall (w v : word64),
  ~ word_bit 0 (word_and (n2w 0xFFFFFFFFFFFFFFFE) w) /\
  word_bit 0 (word_add (word_and (n2w 0xFFFFFFFFFFFFFFFE) w) v) = word_bit 0 v.
Proof.
  intros w v.
  assert (Hev : N.testbit (N.land 0xFFFFFFFFFFFFFFFE (w2n w)) 0 = false)
    by (rewrite N.land_spec; reflexivity).
  unfold word_bit, fcp_index; rewrite !BIT_testbit; replace (0 <=? dimindex 64 - 1) with true by reflexivity; cbn [andb].
  unfold word_and, word_add; rewrite !w2n_n2w.
  change (dimword 64) with (2 ^ 64).
  split.
  - rewrite N.mod_pow2_bits_low by lia.
    rewrite (N.mod_small 0xFFFFFFFFFFFFFFFE) by (vm_compute; reflexivity).
    rewrite Hev; discriminate.
  - rewrite N.mod_pow2_bits_low by lia.
    rewrite !N.bit0_odd.
    rewrite (N.mod_small 0xFFFFFFFFFFFFFFFE) by (vm_compute; reflexivity).
    rewrite N.odd_add, <- (N.bit0_odd (_ mod _)), N.mod_pow2_bits_low, Hev by lia.
    reflexivity.
Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "v2w_0_rwts" *)
Theorem v2w_0_rwts : forall b0 b1 b2 b3,
  (v2w [false; false; false; false; true] = (n2w 1 : word5)) /\
  (v2w [false; false; false; false; false] = (n2w 0 : word5)) /\
  ((bool_decide (v2w [true; b3; b2; b1; b0] = (n2w 0 : word5))) = false) /\
  ((bool_decide (v2w [b3; true; b2; b1; b0] = (n2w 0 : word5))) = false) /\
  ((bool_decide (v2w [b3; b2; true; b1; b0] = (n2w 0 : word5))) = false) /\
  ((bool_decide (v2w [b3; b2; b1; true; b0] = (n2w 0 : word5))) = false) /\
  ((bool_decide (v2w [b3; b2; b1; b0; true] = (n2w 0 : word5))) = false).
Proof.
  intros [] [] [] []; repeat split; reflexivity.
Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "Decode_IMP_DecodeAny" *)
Theorem Decode_IMP_DecodeAny : forall w i, Decode w = i -> DecodeAny (Word w) = i.
Proof. intros w i H; exact H. Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "DecodeRVC_IMP_DecodeAny" *)
Theorem DecodeRVC_IMP_DecodeAny : forall h i, DecodeRVC h = i -> DecodeAny (Half h) = i.
Proof. intros h i H; exact H. Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "avoid_signalAddressException" *)
Theorem avoid_signalAddressException : forall (b : bool) t u s,
  ~ b -> (if b then signalAddressException t u else s) = s.
Proof. intros [] t u s H; [exfalso; apply H; reflexivity|reflexivity]. Qed.

(*! HOL "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml" "word_bit_add_lsl_simp" *)
Theorem word_bit_add_lsl_simp : forall (x w : word64),
  word_bit 0 (word_add x (word_lsl w 1)) = word_bit 0 x.
Proof.
  intros x w.
  unfold word_bit, fcp_index; rewrite !BIT_testbit; replace (0 <=? dimindex 64 - 1) with true by reflexivity; cbn [andb].
  unfold word_add, word_lsl; cbn [dimindex N.max N.ltb N.compare]; rewrite !w2n_n2w.
  change (dimword 64) with (2 ^ 64).
  rewrite N.mod_pow2_bits_low by lia.
  rewrite !N.bit0_odd.
  replace (dimindex 64 - 1 <? 1) with false by reflexivity; rewrite w2n_n2w.
  change (dimword 64) with (2 ^ 64).
  rewrite N.odd_add, <- (N.bit0_odd ((w2n w * 2 ^ 1) mod 2 ^ 64)), N.mod_pow2_bits_low by lia.
  rewrite N.mul_pow2_bits_low by lia.
  destruct (N.odd (w2n x)); reflexivity.
Qed.
