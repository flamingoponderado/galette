(** * CakeML [lab_to_targetProof]: bytes in memory

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 1154-1783): locating the encoding of the fetched instruction in
    the code memory ([IMP_bytes_in_memory_*]) and the byte-array lemmas for
    FFI calls.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's [mc_conf.target.config] (only the configuration of a machine
      configuration is used) is [asmProps.config mc_conf.(target)].
    - Not ported: the ML values [prog_to_bytes_lemma] (the [pos = 0]
      instance of the theorem of the same name, used inline), [s1],
      [case_eq_thms0], [bool_case_eq_thms].
    - Untagged Galette helpers: [good_dimindex_get_byte_set_byte] and
      [get_byte_set_byte_diff] (HOL [misc] theorems, not yet in [misc.v]),
      [line_bytes_Label], [line_ok_LabAsm_lab]. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.relation Require Import relation.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import evaluateProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import basic.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray).
Open Scope N_scope.

Section ProgToBytes.
Context {a : N} {B C : Type}.

Lemma line_ok_Label_len (c : asm_config a) labs ffis pos (x : line a) :
  is_Label x -> line_ok c labs ffis pos x -> line_length x = 0 /\ line_bytes x = [].
Proof.
  destruct x as [l1 l2 l3| |]; cbn; try discriminate.
  intros _ [_ ->]. split; reflexivity.
Qed.

Lemma is_Label_similar (x y : line a) : line_similar x y -> is_Label x = is_Label y.
Proof. destruct x, y; cbn; tauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "prog_to_bytes_lemma" 1155 *)
Theorem prog_to_bytes_lemma : forall (mc_conf : machine_config a B C) labs ffi_names
    code2 code1 pc i pos,
  code_similar code1 code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names pos code2 /\
  asm_fetch_aux pc code1 = SOME i ->
  exists bs j bs2,
    prog_to_bytes code2 = bs ++ line_bytes j ++ bs2 /\
    LENGTH bs + pos = pos_val pc pos code2 /\
    LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc + 1) pos code2 /\
    line_similar i j /\
    line_ok (asmProps.config mc_conf.(target)) labs ffi_names (pos_val pc pos code2) j.
Proof.
  intros mc_conf labs ffi_names code2.
  set (cfg := asmProps.config mc_conf.(target)).
  induction code2 as [|[k ys] xs IH]; intros code1 pc i pos (Hs & Hok & Hf).
  { destruct code1 as [|[]]; [discriminate|contradiction]. }
  destruct code1 as [|[k1 ys1] xs1]; [contradiction|].
  destruct Hs as (Hxs & Hys & ->).
  revert ys1 pc pos Hys Hok Hf. induction ys as [|y ys IHy]; intros ys1 pc pos Hys Hok Hf.
  - inversion Hys; subst. destruct Hok as [_ Hok].
    exact (IH xs1 pc i pos (conj Hxs (conj Hok Hf))).
  - inversion Hys as [|y1 y' ys1' ys' Hy Hys']; subst.
    rewrite (proj2 (proj2 asm_fetch_aux_def)) in Hf.
    destruct Hok as [Hy_ok Hok].
    rewrite (is_Label_similar _ _ Hy) in Hf.
    change (pos_val pc pos (Section_ k (y :: ys) :: xs)) with
      (if is_Label y then pos_val pc (pos + line_length y) (Section_ k ys :: xs)
       else if pc =? 0 then pos else pos_val (pc - 1) (pos + line_length y) (Section_ k ys :: xs)).
    change (pos_val (pc + 1) pos (Section_ k (y :: ys) :: xs)) with
      (if is_Label y then pos_val (pc + 1) (pos + line_length y) (Section_ k ys :: xs)
       else if pc + 1 =? 0 then pos
            else pos_val (pc + 1 - 1) (pos + line_length y) (Section_ k ys :: xs)).
    rewrite (proj2 (proj2 (prog_to_bytes_def k y ys xs))).
    destruct (is_Label y) eqn:Hl.
    + destruct (line_ok_Label_len cfg labs ffi_names pos y Hl Hy_ok) as [E1 E2].
      rewrite E1, N.add_0_r in *. rewrite E2. cbn [app].
      exact (IHy ys1' pc pos Hys' Hok Hf).
    + destruct (N.eqb_spec pc 0) as [->|Hpc].
      * injection Hf as <-.
        exists [], y, (prog_to_bytes (Section_ k ys :: xs)).
        rewrite (proj2 (N.eqb_neq (0 + 1) 0)) by lia.
        rewrite N.add_sub, (pos_val_0 (Section_ k ys :: xs) cfg labs ffi_names _ Hok).
        rewrite <- (LENGTH_line_bytes y) by (rewrite Hl; discriminate).
        split; [reflexivity|]. split; [reflexivity|]. split; [cbn [LENGTH]; lia|].
        split; [exact Hy|exact Hy_ok].
      * destruct (IHy ys1' (pc - 1) (pos + line_length y) Hys' Hok Hf)
          as (bs & j & bs2 & E1 & E2 & E3 & E4 & E5).
        exists (line_bytes y ++ bs), j, bs2.
        rewrite (proj2 (N.eqb_neq (pc + 1) 0)) by lia.
        replace (pc + 1 - 1) with (pc - 1 + 1) by lia.
        rewrite <- (LENGTH_line_bytes y) in * by (rewrite Hl; discriminate).
        rewrite E1, <- app_assoc. split; [reflexivity|].
        rewrite LENGTH_app. split; [lia|]. split; [lia|]. split; [exact E4|exact E5].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_APPEND" *)
Theorem bytes_in_mem_APPEND : forall {X} (xs ys : list X) (a0 : word a) m md md1,
  bytes_in_mem a0 (xs ++ ys) m md md1 <->
  bytes_in_mem a0 xs m md md1 /\
  bytes_in_mem (a0 + n2w (LENGTH xs))%w ys m md md1.
Proof.
  intros X xs; induction xs as [|x xs IH]; intros ys a0 m md md1; cbn [app bytes_in_mem LENGTH].
  - rewrite (proj1 WORD_ADD_0). tauto.
  - rewrite IH. replace (a0 + n2w 1 + n2w (LENGTH xs))%w with (a0 + n2w (N.succ (LENGTH xs)))%w
      by word_arith. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_UPDATE" *)
Theorem bytes_in_mem_UPDATE : forall {X} (ls : list X) (a0 : word a) m md md2 w1 w2,
  (forall n, n < LENGTH ls -> (a0 + n2w n)%w <> w1) /\
  bytes_in_mem a0 ls m md md2 ->
  bytes_in_mem a0 ls ((w1 =+ w2) m) md md2.
Proof.
  intros X ls; induction ls as [|x ls IH]; intros a0 m md md2 w1 w2 [Hn H]; cbn in *; [exact Logic.I|].
  destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
  - rewrite APPLY_UPDATE_THM. destruct (decide (w1 = a0)) as [E|]; [|exact H3].
    exfalso. apply (Hn 0); [lia|]. rewrite (proj1 WORD_ADD_0). symmetry; exact E.
  - apply IH. split; [|exact H4]. intros n Hlt.
    replace (a0 + n2w 1 + n2w n)%w with (a0 + n2w (n + 1))%w by word_arith.
    apply Hn. lia.
Qed.

End ProgToBytes.

Section Fetch.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory" *)
Theorem IMP_bytes_in_memory : forall (mc_conf : machine_config a B C) code1 code2 labs ffi_names pc i (p : word a)
    (m : word a -> word8) (dm dm1 : word a -> Prop),
  code_similar code1 code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  asm_fetch_aux pc code1 = SOME i /\
  bytes_in_mem p (prog_to_bytes code2) m dm dm1 ->
  exists j,
    bytes_in_mem (p + n2w (pos_val pc 0 code2))%w (line_bytes j) m dm dm1 /\
    line_ok (asmProps.config mc_conf.(target)) labs ffi_names (pos_val pc 0 code2) j /\
    pos_val (pc + 1) 0 code2 = pos_val pc 0 code2 + LENGTH (line_bytes j) /\
    line_similar i j.
Proof.
  intros mc_conf code1 code2 labs ffi_names pc i p m dm dm1 (Hs & Hok & Hf & Hb).
  destruct (prog_to_bytes_lemma mc_conf labs ffi_names code2 code1 pc i 0 (conj Hs (conj Hok Hf)))
    as (bs & j & bs2 & E1 & E2 & E3 & E4 & E5).
  exists j. rewrite E1 in Hb. apply bytes_in_mem_APPEND in Hb as [_ Hb].
  apply bytes_in_mem_APPEND in Hb as [Hb _].
  rewrite N.add_0_r in E2, E3. rewrite E2 in Hb.
  split; [exact Hb|]. split; [exact E5|]. split; [lia|exact E4].
Qed.

Lemma asm_fetch_aux_of (s1 : labSem.state a config Ffi) x : asm_fetch s1 = SOME x -> asm_fetch_aux s1.(pc) s1.(code) = SOME x.
Proof. intros H; exact H. Qed.

Lemma bytes_in_mem_enc_prefix (p : word a) (bytes e nops : list word8) m md md1 :
  bytes = e ++ nops -> bytes_in_mem p bytes m md md1 -> bytes_in_memory p e m md.
Proof.
  intros -> H. apply bytes_in_mem_IMP in H. apply bytes_in_memory_APPEND in H. apply H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_JumpReg" *)
Theorem IMP_bytes_in_memory_JumpReg : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p r1 l n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (Asm (Asmi (JumpReg r1)) l n) ->
  bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w
    (encode (asmProps.config mc_conf.(target)) (JumpReg r1)) t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
  asm_ok (JumpReg r1) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p r1 l n (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & _ & Hsim).
  destruct j as [| b' bytes' l' |]; cbn in Hsim; try contradiction. subst b'.
  destruct Hl as (He & _ & Hasm). cbn [cbw_to_asm] in He, Hasm.
  apply enc_with_nop_thm in He as [k Hk].
  split; [|exact Hasm]. exact (bytes_in_mem_enc_prefix _ _ _ _ _ _ _ Hk Hj).
Qed.

Lemma line_ok_lab (cfg : asm_config a) labs ffis pos (x : asm_with_lab a) w bytes l :
  (forall v, x <> Call v) -> (forall s, x <> CallFFI s) -> x <> labLang.Halt -> x <> Install ->
  line_ok cfg labs ffis pos (LabAsm x w bytes l) ->
  exists t, lab_lookup (match get_label x with Lab l1 l2 => l1 end)
                       (match get_label x with Lab l1 l2 => l2 end) labs = SOME t /\
    enc_with_nop (encode cfg) (lab_inst (n2w t - n2w pos)%w x) bytes /\
    LENGTH bytes = l /\ asm_ok (lab_inst (n2w t - n2w pos)%w x) cfg.
Proof.
  intros H1 H2 H3 H4. destruct x as [[l1 l2]|c r ri [l1 l2]|v|r [l1 l2]|s| |];
    try (exfalso; first [exact (H1 _ eq_refl)|exact (H2 _ eq_refl)|exact (H3 eq_refl)|exact (H4 eq_refl)]);
    cbn [line_ok get_label];
    destruct (lab_lookup l1 l2 labs) as [t|]; try contradiction; intros H; exists t; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_Jump" *)
Theorem IMP_bytes_in_memory_Jump : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p jtarget l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n) ->
  exists tt enc,
    tt = (n2w (find_pos jtarget labs) - n2w (pos_val s1.(pc) 0 code2))%w /\
    enc = encode (asmProps.config mc_conf.(target)) (asm.Jump tt) /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w enc t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    asm_ok (asm.Jump tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p jtarget l bytes n (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & _ & Hsim).
  destruct j as [| | x' w' bytes' l']; cbn in Hsim; try contradiction. subst x'.
  apply line_ok_lab in Hl; try discriminate. destruct Hl as (t & Ht & He & _ & Hasm).
  destruct jtarget as [l1 l2]. cbn in Ht. apply lab_lookup_IMP in Ht.
  cbn [lab_inst] in He, Hasm. rewrite Ht.
  apply enc_with_nop_thm in He as [k Hk].
  eexists; eexists; split; [reflexivity|]. split; [reflexivity|].
  split; [|exact Hasm]. exact (bytes_in_mem_enc_prefix _ _ _ _ _ _ _ Hk Hj).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_JumpCmp" *)
Theorem IMP_bytes_in_memory_JumpCmp : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p cmp rr ri jtarget
    l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n) ->
  exists tt enc,
    tt = (n2w (find_pos jtarget labs) - n2w (pos_val s1.(pc) 0 code2))%w /\
    enc = encode (asmProps.config mc_conf.(target)) (asm.JumpCmp cmp rr ri tt) /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w enc t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    asm_ok (asm.JumpCmp cmp rr ri tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p cmp rr ri jtarget l bytes n (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & _ & Hsim).
  destruct j as [| | x' w' bytes' l']; cbn in Hsim; try contradiction. subst x'.
  apply line_ok_lab in Hl; try discriminate. destruct Hl as (t & Ht & He & _ & Hasm).
  destruct jtarget as [l1 l2]. cbn in Ht. apply lab_lookup_IMP in Ht.
  cbn [lab_inst] in He, Hasm. rewrite Ht.
  apply enc_with_nop_thm in He as [k Hk].
  eexists; eexists; split; [reflexivity|]. split; [reflexivity|].
  split; [|exact Hasm]. exact (bytes_in_mem_enc_prefix _ _ _ _ _ _ _ Hk Hj).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_JumpCmp_1" *)
Theorem IMP_bytes_in_memory_JumpCmp_1 : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p cmp rr ri
    jtarget l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n) ->
  exists tt bytes,
    tt = (n2w (find_pos jtarget labs) - n2w (pos_val s1.(pc) 0 code2))%w /\
    enc_with_nop (encode (asmProps.config mc_conf.(target))) (asm.JumpCmp cmp rr ri tt) bytes /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    pos_val (s1.(pc) + 1) 0 code2 = pos_val s1.(pc) 0 code2 + LENGTH bytes /\
    asm_ok (asm.JumpCmp cmp rr ri tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p cmp rr ri jtarget l bytes n (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & Hpos & Hsim).
  destruct j as [| | x' w' bytes' l']; cbn in Hsim; try contradiction. subst x'.
  apply line_ok_lab in Hl; try discriminate. destruct Hl as (t & Ht & He & _ & Hasm).
  destruct jtarget as [l1 l2]. cbn in Ht. apply lab_lookup_IMP in Ht.
  cbn [lab_inst] in He, Hasm. rewrite Ht.
  exists (n2w t - n2w (pos_val s1.(pc) 0 code2))%w, bytes'.
  split; [reflexivity|]. split; [exact He|].
  split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hj)|]. split; [exact Hpos|exact Hasm].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_Call" *)
Theorem IMP_bytes_in_memory_Call : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p ww l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm (Call ww) l bytes n) ->
  False.
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p ww l bytes n (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & _ & Hsim).
  destruct j as [| | x' w' bytes' l']; cbn in Hsim; try contradiction. subst x'. exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_LocValue" *)
Theorem IMP_bytes_in_memory_LocValue : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p reg l1 l2
    l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) l bytes n) ->
  exists tt bytes,
    tt = (n2w (find_pos (Lab l1 l2) labs) - n2w (pos_val s1.(pc) 0 code2))%w /\
    enc_with_nop (encode (asmProps.config mc_conf.(target))) (asm.Loc reg tt) bytes /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    pos_val (s1.(pc) + 1) 0 code2 = pos_val s1.(pc) 0 code2 + LENGTH bytes /\
    asm_ok (asm.Loc reg tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p reg l1 l2 l bytes n (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & Hpos & Hsim).
  destruct j as [| | x' w' bytes' l']; cbn in Hsim; try contradiction. subst x'.
  apply line_ok_lab in Hl; try discriminate. destruct Hl as (t & Ht & He & _ & Hasm).
  cbn in Ht. apply lab_lookup_IMP in Ht.
  cbn [lab_inst] in He, Hasm. rewrite Ht.
  exists (n2w t - n2w (pos_val s1.(pc) 0 code2))%w, bytes'.
  split; [reflexivity|]. split; [exact He|].
  split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hj)|]. split; [exact Hpos|exact Hasm].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_Inst" *)
Theorem IMP_bytes_in_memory_Inst : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p i bytes len,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (Asm (Asmi (Inst i)) bytes len) ->
  exists bytes,
    enc_with_nop (encode (asmProps.config mc_conf.(target))) (Inst i) bytes /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    bytes_in_mem (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem)
      t1.(asmSem.mem_domain) s1.(mem_domain) /\
    pos_val (s1.(pc) + 1) 0 code2 = pos_val s1.(pc) 0 code2 + LENGTH bytes /\
    asm_ok (Inst i) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p i bytes len (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & Hpos & Hsim).
  destruct j as [| b' bytes' l' |]; cbn in Hsim; try contradiction. subst b'.
  destruct Hl as (He & _ & Hasm). cbn [cbw_to_asm] in He, Hasm.
  exists bytes'. split; [exact He|]. split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hj)|].
  split; [exact Hj|]. split; [exact Hpos|exact Hasm].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_Cbw" *)
Theorem IMP_bytes_in_memory_Cbw : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p r1 r2 bytes len,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (Asm (Cbw r1 r2) bytes len) ->
  exists bytes,
    enc_with_nop (encode (asmProps.config mc_conf.(target)))
      (Inst (Mem Store8 r2 (Addr r1 (n2w 0)))) bytes /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    bytes_in_mem (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem)
      t1.(asmSem.mem_domain) s1.(mem_domain) /\
    pos_val (s1.(pc) + 1) 0 code2 = pos_val s1.(pc) 0 code2 + LENGTH bytes /\
    asm_ok (Inst (Mem Store8 r2 (Addr r1 (n2w 0)))) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p r1 r2 bytes len (Hs & Hok & Hb & Hf).
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & Hpos & Hsim).
  destruct j as [| b' bytes' l' |]; cbn in Hsim; try contradiction. subst b'.
  destruct Hl as (He & _ & Hasm). cbn [cbw_to_asm] in He, Hasm.
  exists bytes'. split; [exact He|]. split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hj)|].
  split; [exact Hj|]. split; [exact Hpos|exact Hasm].
Qed.

Ltac fixed_jump_tac mc_conf s1 code2 labs ffi_names p Hs Hok Hb Hf :=
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj (asm_fetch_aux_of _ _ Hf) Hb)))) as (j & Hj & Hl & _ & Hsim);
  destruct j as [| | x' w' bytes' l']; cbn in Hsim; try contradiction; subst x';
  cbn [line_ok] in Hl; destruct Hl as (He & _ & Hasm);
  apply enc_with_nop_thm in He as [k Hk];
  eexists; eexists; split; [reflexivity|]; split; [reflexivity|];
  split; [exact (bytes_in_mem_enc_prefix _ _ _ _ _ _ _ Hk Hj)|exact Hasm].

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_CallFFI" *)
Theorem IMP_bytes_in_memory_CallFFI : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p name l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm (CallFFI name) l bytes n) ->
  exists tt enc,
    tt = (n2w 0 - n2w (pos_val s1.(pc) 0 code2 +
                       (3 + get_ffi_index ffi_names (ExtCall name)) * ffi_offset))%w /\
    enc = encode (asmProps.config mc_conf.(target)) (asm.Jump tt) /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w enc t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    asm_ok (asm.Jump tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p name l bytes n (Hs & Hok & Hb & Hf).
  fixed_jump_tac mc_conf s1 code2 labs ffi_names p Hs Hok Hb Hf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_Halt" *)
Theorem IMP_bytes_in_memory_Halt : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p l bytes n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm labLang.Halt l bytes n) ->
  exists tt enc,
    tt = (n2w 0 - n2w (pos_val s1.(pc) 0 code2 + ffi_offset))%w /\
    enc = encode (asmProps.config mc_conf.(target)) (asm.Jump tt) /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w enc t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    asm_ok (asm.Jump tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p l bytes n (Hs & Hok & Hb & Hf).
  fixed_jump_tac mc_conf s1 code2 labs ffi_names p Hs Hok Hb Hf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_Install" *)
Theorem IMP_bytes_in_memory_Install : forall (mc_conf : machine_config a B C) (s1 : labSem.state a config Ffi) (t1 : asm_state a)
    code2 labs ffi_names p c l n,
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) /\
  asm_fetch s1 = SOME (LabAsm Install c l n) ->
  exists tt enc,
    tt = (n2w 0 - n2w (pos_val s1.(pc) 0 code2 + 2 * ffi_offset))%w /\
    enc = encode (asmProps.config mc_conf.(target)) (asm.Jump tt) /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w enc t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    asm_ok (asm.Jump tt) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p c l n (Hs & Hok & Hb & Hf).
  fixed_jump_tac mc_conf s1 code2 labs ffi_names p Hs Hok Hb Hf.
Qed.

End Fetch.

Section FetchLemmas.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_asm_fetch_aux_IMP_line_ok" *)
Theorem all_enc_ok_asm_fetch_aux_IMP_line_ok : forall (c : asm_config a) labs ffis line pc n code2,
  all_enc_ok c labs ffis n code2 /\ asm_fetch_aux pc code2 = SOME line ->
  line_ok c labs ffis (pos_val pc n code2) line.
Proof.
  intros c labs ffis line pc n code2. revert pc n.
  induction code2 as [|k xs IH|k y ys xs IH] using code_ind; intros pc n [Hok Hf].
  - discriminate.
  - destruct Hok as [_ Hok]. exact (IH pc n (conj Hok Hf)).
  - destruct Hok as [Hy Hok]. rewrite (proj2 (proj2 asm_fetch_aux_def)) in Hf.
    rewrite (proj2 (proj2 (pos_val_def pc n k xs y ys))).
    destruct (is_Label y); [exact (IH pc _ (conj Hok Hf))|].
    destruct (N.eqb_spec pc 0); [injection Hf as <-; exact Hy|].
    exact (IH (pc - 1) _ (conj Hok Hf)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "code_similar_IMP_asm_fetch_aux_line_similar" *)
Theorem code_similar_IMP_asm_fetch_aux_line_similar : forall pc (code1 code2 : list (sec a)),
  code_similar code1 code2 ->
  OPTREL line_similar (asm_fetch_aux pc code1) (asm_fetch_aux pc code2).
Proof.
  intros pc code1; revert pc.
  induction code1 as [|k xs IH|k y ys xs IH] using code_ind; intros pc code2 Hs.
  - destruct code2 as [|[]]; [|contradiction]. left; split; reflexivity.
  - destruct code2 as [|[k2 [|y2 ys2]] xs2]; try contradiction.
    + destruct Hs as (Hs & _ & _). exact (IH pc _ Hs).
    + destruct Hs as (_ & Hl & _). inversion Hl.
  - destruct code2 as [|[k2 [|y2 ys2]] xs2]; try contradiction.
    + destruct Hs as (_ & Hl & _). inversion Hl.
    + destruct Hs as (Hs & Hl & ->). inversion Hl as [|? ? ? ? Hy Hl']; subst.
      rewrite !(proj2 (proj2 asm_fetch_aux_def)).
      rewrite (is_Label_similar _ _ Hy).
      assert (Hs' : code_similar (Section_ k2 ys :: xs) (Section_ k2 ys2 :: xs2))
        by (split; [exact Hs|split; [exact Hl'|reflexivity]]).
      destruct (is_Label y2); [exact (IH pc _ Hs')|].
      destruct (N.eqb_spec pc 0); [right; do 2 eexists; split; [reflexivity|split; [reflexivity|exact Hy]]|exact (IH (pc - 1) _ Hs')].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_aux_pos_val_LENGTH_EQ" *)
Theorem asm_fetch_aux_pos_val_LENGTH_EQ : forall (conf : asm_config a) labs ffi_names
    (bytes' : list word8) pc n code2 line,
  asm_fetch_aux pc code2 = SOME line /\
  all_enc_ok conf labs ffi_names n code2 /\
  pos_val (pc + 1) n code2 = LENGTH bytes' + pos_val pc n code2 ->
  LENGTH (line_bytes line) = LENGTH bytes'.
Proof.
  intros conf labs ffi_names bytes' pc n code2. revert pc n.
  induction code2 as [|k xs IH|k y ys xs IH] using code_ind; intros pc n line (Hf & Hok & Hp).
  - discriminate.
  - destruct Hok as [_ Hok]. exact (IH pc n line (conj Hf (conj Hok Hp))).
  - destruct Hok as [Hy Hok]. rewrite (proj2 (proj2 asm_fetch_aux_def)) in Hf.
    rewrite !(proj2 (proj2 (pos_val_def _ n k xs y ys))) in Hp.
    destruct (is_Label y) eqn:Hl; [exact (IH pc _ line (conj Hf (conj Hok Hp)))|].
    rewrite (proj2 (N.eqb_neq (pc + 1) 0)) in Hp by lia.
    destruct (N.eqb_spec pc 0) as [->|Hpc].
    + injection Hf as <-. cbn [N.add] in Hp. rewrite N.sub_diag in Hp.
      rewrite (pos_val_0 (Section_ k ys :: xs) conf labs ffi_names _ Hok) in Hp.
      rewrite (LENGTH_line_bytes y) by (rewrite Hl; discriminate). lia.
    + replace (pc + 1 - 1) with (pc - 1 + 1) in Hp by lia.
      exact (IH (pc - 1) _ line (conj Hf (conj Hok Hp))).
Qed.

End FetchLemmas.

Section ShareMemFetch.
Context {a : N} {B C Ffi : Type}.

Lemma enc_nops_LENGTH_eq (e sk : list word8) n1 n2 :
  LENGTH (e ++ FLAT (REPLICATE n1 sk)) = LENGTH (e ++ FLAT (REPLICATE n2 sk)) ->
  e ++ FLAT (REPLICATE n1 sk) = e ++ FLAT (REPLICATE n2 sk).
Proof.
  intros H. destruct sk as [|x sk'] eqn:E.
  - rewrite !FLAT_REPLICATE_NIL. reflexivity.
  - rewrite <- E in *. rewrite !LENGTH_app, !LENGTH_FLAT_REPLICATE in H.
    assert (0 < LENGTH sk) by (rewrite E; cbn [LENGTH]; lia).
    assert (n1 = n2) by nia. subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_bytes_in_memory_ShareMem" *)
Theorem IMP_bytes_in_memory_ShareMem : forall (mc_conf : machine_config a B C)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) code2 labs ffi_names p mop r ad l n,
  asm_fetch_aux s1.(pc) s1.(code) = SOME (Asm (ShareMem mop r ad) l n) /\
  code_similar s1.(code) code2 /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) ->
  exists bytes,
    asm_fetch_aux s1.(pc) code2 = SOME (Asm (ShareMem mop r ad) bytes (LENGTH bytes)) /\
    enc_with_nop (encode (asmProps.config mc_conf.(target))) (Inst (Mem mop r ad)) bytes /\
    bytes_in_memory (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem) t1.(asmSem.mem_domain) /\
    bytes_in_mem (p + n2w (pos_val s1.(pc) 0 code2))%w bytes t1.(asmSem.mem)
      t1.(asmSem.mem_domain) s1.(mem_domain) /\
    pos_val (s1.(pc) + 1) 0 code2 = pos_val s1.(pc) 0 code2 + LENGTH bytes /\
    asm_ok (Inst (Mem mop r ad)) (asmProps.config mc_conf.(target)).
Proof.
  intros mc_conf s1 t1 code2 labs ffi_names p mop r ad l n (Hf & Hs & Hok & Hb).
  set (cfg := asmProps.config mc_conf.(target)) in *.
  destruct (IMP_bytes_in_memory mc_conf s1.(code) code2 labs ffi_names s1.(pc) _ p _ _ _
              (conj Hs (conj Hok (conj Hf Hb)))) as (j & Hj & Hl & Hpos & Hsim).
  destruct j as [| b' bytes' l' |]; cbn in Hsim; try contradiction. subst b'.
  destruct Hl as (He & _ & Hasm). cbn [cbw_to_asm] in He, Hasm.
  pose proof (code_similar_IMP_asm_fetch_aux_line_similar s1.(pc) _ _ Hs) as Ho.
  rewrite Hf in Ho. destruct Ho as [[? _]|(x0 & y0 & E1 & E2 & Hy0)]; [discriminate|].
  injection E1 as <-.
  destruct y0 as [| b0 bytes0 l0 |]; cbn in Hy0; try contradiction. subst b0.
  pose proof (all_enc_ok_asm_fetch_aux_IMP_line_ok cfg labs ffi_names _ s1.(pc) 0 code2
                (conj Hok E2)) as (He0 & Hl0 & _).
  cbn [cbw_to_asm] in He0.
  cbn [line_bytes] in Hj, Hpos.
  assert (Hp2 : pos_val (s1.(pc) + 1) 0 code2 = LENGTH bytes' + pos_val s1.(pc) 0 code2) by lia.
  pose proof (asm_fetch_aux_pos_val_LENGTH_EQ cfg labs ffi_names bytes' s1.(pc) 0 code2 _
                (conj E2 (conj Hok Hp2))) as Hlen.
  cbn [line_bytes] in Hlen.
  assert (Eb : bytes0 = bytes').
  { apply enc_with_nop_thm in He as [k1 Hk1]. apply enc_with_nop_thm in He0 as [k0 Hk0].
    rewrite Hk0, Hk1 in *. apply enc_nops_LENGTH_eq. exact Hlen. }
  subst bytes0. exists bytes'. rewrite E2, <- Hl0.
  split; [reflexivity|]. split; [exact He|].
  split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hj)|]. split; [exact Hj|].
  split; [exact Hpos|exact Hasm].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_IMP_memory" *)
Theorem bytes_in_mem_IMP_memory : forall (dm dm1 : word a -> Prop) (m m1 : word a -> word8) xs a0,
  (forall a0, a0 NOTIN dm1 -> m a0 = m1 a0) ->
  bytes_in_mem a0 xs m dm dm1 ->
  bytes_in_memory a0 xs m1 dm.
Proof.
  intros dm dm1 m m1 xs; induction xs as [|x xs IH]; intros a0 Hm H; cbn in *; [exact Logic.I|].
  destruct H as (H1 & H2 & H3 & H4). rewrite <- (Hm _ H2).
  split; [exact H3|]. split; [exact H1|]. exact (IH _ Hm H4).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "read_bytearray_state_rel" *)
Theorem read_bytearray_state_rel : forall (mc_conf : machine_config a B C) code2 labs p
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) (ms1 : B) n a0 x,
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 /\
  read_bytearray a0 n (mem_load_byte_aux s1.(mem) s1.(mem_domain) s1.(be)) = SOME x ->
  read_bytearray a0 n
    (fun a0 => if classical_dec (a0 IN mc_conf.(prog_addresses))
               then SOME (t1.(asmSem.mem) a0) else NONE) = SOME x.
Proof.
  intros mc_conf code2 labs p s1 t1 ms1 n. induction n as [|n IH] using N.peano_ind;
    intros a0 x [Hs H]; [exact H|].
  rewrite (proj2 (read_bytearray_def a0 _ n)) in H. rewrite (proj2 (read_bytearray_def a0 _ n)).
  destruct (mem_load_byte_aux s1.(mem) s1.(mem_domain) s1.(be) a0) as [b|] eqn:Eb; [|discriminate].
  destruct (read_bytearray (a0 + n2w 1)%w n _) as [bs|] eqn:Ebs; [|discriminate].
  rewrite (IH _ bs (conj Hs Ebs)).
  apply state_rel_iff in Hs.
  unfold mem_load_byte_aux in Eb.
  destruct (mem s1 (byte_align a0)) as [v|] eqn:Em; [|discriminate].
  destruct (classical_dec (byte_align a0 IN mem_domain s1)) as [Hd|]; [|discriminate].
  injection Eb as <-.
  destruct (sr_mem Hs a0 Hd) as (Ht & _ & Hv).
  unfold word_loc_val_byte in Hv. rewrite Em in Hv. cbn in Hv. injection Hv as Hv.
  rewrite (sr_prog_addresses Hs). destruct (classical_dec _) as [_|]; [|contradiction].
  rewrite <- Hv. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "IMP_has_io_name" *)
Theorem IMP_has_io_name : forall (s1 : labSem.state a config Ffi) index l bytes n,
  asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n) ->
  has_io_name index s1.(code).
Proof.
  intros s1 index l bytes n. unfold asm_fetch. generalize (pc s1). generalize (code s1).
  intros code. induction code as [|k xs IH|k y ys xs IH] using code_ind; intros pc Hf.
  - discriminate.
  - exact (IH pc Hf).
  - rewrite (proj2 (proj2 asm_fetch_aux_def)) in Hf.
    change (has_io_name index (Section_ k ys :: xs) \/
            match y with LabAsm (CallFFI i) _ _ _ => i = index | _ => False end).
    destruct (is_Label y); [left; exact (IH pc Hf)|].
    destruct (N.eqb_spec pc 0); [injection Hf as ->; right; reflexivity|].
    left; exact (IH (pc - 1) Hf).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_asm_write_bytearray_lemma" *)
Theorem bytes_in_mem_asm_write_bytearray_lemma : forall {X : Type} (k d : word a -> Prop)
    (m1 m2 : word a -> X) xs p,
  (forall a0, a0 NOTIN k -> m1 a0 = m2 a0) ->
  bytes_in_mem p xs m1 d k ->
  bytes_in_mem p xs m2 d k.
Proof.
  intros X k d m1 m2 xs; induction xs as [|x xs IH]; intros p Hm H; cbn in *; [exact Logic.I|].
  destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|].
  split; [rewrite <- (Hm _ H2); exact H3|]. exact (IH _ Hm H4).
Qed.

Lemma asm_write_bytearray_outside (s1 : labSem.state a config Ffi) (m : word a -> word8) :
  (forall a0, byte_align a0 IN s1.(mem_domain) -> a0 IN s1.(mem_domain)) ->
  forall new_bytes c1 x a0,
  read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.(mem) s1.(mem_domain) s1.(be)) = SOME x ->
  a0 NOTIN s1.(mem_domain) ->
  asm_write_bytearray c1 new_bytes m a0 = m a0.
Proof.
  intros Hd new_bytes; induction new_bytes as [|b bs IH]; intros c1 x a0 Hr Ha; [reflexivity|].
  cbn [LENGTH] in Hr. rewrite (proj2 (read_bytearray_def _ _ _)) in Hr.
  destruct (mem_load_byte_aux _ _ _ c1) as [v|] eqn:Ev; [|discriminate].
  destruct (read_bytearray (c1 + n2w 1)%w _ _) as [ys|] eqn:Ey; [|discriminate].
  cbn [asm_write_bytearray]. rewrite APPLY_UPDATE_THM.
  destruct (decide (c1 = a0)) as [->|].
  - exfalso. apply Ha, Hd. unfold mem_load_byte_aux in Ev.
    destruct (mem s1 (byte_align a0)); [|discriminate].
    destruct (classical_dec _); [assumption|discriminate].
  - exact (IH _ _ _ Ey Ha).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "bytes_in_mem_asm_write_bytearray" *)
Theorem bytes_in_mem_asm_write_bytearray : forall (s1 : labSem.state a config Ffi)
    (t1 : asm_state a) c1 new_bytes x p xs,
  (forall a0, byte_align a0 IN s1.(mem_domain) -> a0 IN s1.(mem_domain)) /\
  read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.(mem) s1.(mem_domain) s1.(be)) = SOME x ->
  bytes_in_mem p xs t1.(asmSem.mem) t1.(asmSem.mem_domain) s1.(mem_domain) ->
  bytes_in_mem p xs (asm_write_bytearray c1 new_bytes t1.(asmSem.mem)) t1.(asmSem.mem_domain)
    s1.(mem_domain).
Proof.
  intros s1 t1 c1 new_bytes x p xs [Hd Hr]. apply bytes_in_mem_asm_write_bytearray_lemma.
  intros a0 Ha. symmetry. exact (asm_write_bytearray_outside s1 _ Hd _ _ _ _ Hr Ha).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "write_bytearray_NOT_Loc" *)
Theorem write_bytearray_NOT_Loc : forall {cc} xs c1 (s1 : labSem.state a cc Ffi) a0 c n n0,
  s1.(mem) a0 = Word c ->
  write_bytearray c1 xs s1.(mem) s1.(mem_domain) s1.(be) a0 <> Loc n n0.
Proof.
  intros cc xs; induction xs as [|x xs IH]; intros c1 s1 a0 c n n0 H; cbn [write_bytearray].
  - rewrite H. discriminate.
  - unfold mem_store_byte_aux.
    destruct (write_bytearray (c1 + n2w 1)%w xs (mem s1) (mem_domain s1) (be s1) (byte_align c1))
      eqn:E; [|rewrite H; discriminate].
    destruct (classical_dec _); [|rewrite H; discriminate].
    rewrite APPLY_UPDATE_THM. destruct (decide _); [discriminate|exact (IH _ _ _ _ _ _ H)].
Qed.

End ShareMemFetch.

Section ByteArray.
Context {a : N} {B C Ffi : Type}.

(** HOL [misc]'s [good_dimindex_get_byte_set_byte] (Galette helper). *)
Lemma good_dimindex_get_byte_set_byte (a0 : word a) b w be :
  good_dimindex a -> byte.get_byte a0 (set_byte a0 b w be) be = b.
Proof. intros H. apply get_byte_set_byte. destruct H as [H|H]; rewrite H; lia. Qed.

Lemma byte_align_pow_good :
  good_dimindex a -> 2 ** LOG2 (dimindex a DIV 8) = dimindex a DIV 8.
Proof. intros [H|H]; rewrite H; reflexivity. Qed.

(** HOL [misc]'s [get_byte_set_byte_diff] (Galette helper). *)
Lemma get_byte_set_byte_diff (a0 a' : word a) b w be :
  good_dimindex a /\ a0 <> a' /\ byte_align a0 = byte_align a' ->
  byte.get_byte a0 (set_byte a' b w be) be = byte.get_byte a0 w be.
Proof.
  intros (Hg & Hne & Hal). apply get_byte_set_byte_irrelevant. split.
  - destruct Hg as [H|H]; rewrite H; lia.
  - intros Hm. apply Hne. apply word_eq_w2n.
    unfold byte_align in Hal. apply (f_equal w2n) in Hal. rewrite !w2n_align in Hal.
    rewrite (byte_align_pow_good Hg) in Hal.
    assert (Hk : dimindex a DIV 8 <> 0) by (destruct Hg as [H|H]; rewrite H; discriminate).
    rewrite (N.div_mod (w2n a0) (dimindex a DIV 8) Hk), (N.div_mod (w2n a') (dimindex a DIV 8) Hk).
    rewrite Hm. f_equal. rewrite !(N.mul_comm (dimindex a DIV 8)). exact Hal.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "CallFFI_bytearray_lemma" *)
Theorem CallFFI_bytearray_lemma : forall (mc_conf : machine_config a B C)
    (s1 : labSem.state a config Ffi) (t1 : asm_state a) p labs (a0 : word a) c1 new_bytes x,
  byte_align a0 IN s1.(mem_domain) /\ good_dimindex a /\
  a0 IN t1.(asmSem.mem_domain) /\
  a0 IN s1.(mem_domain) /\
  s1.(be) = big_endian (asmProps.config mc_conf.(target)) /\
  read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.(mem) s1.(mem_domain) s1.(be)) = SOME x /\
  word_loc_val_byte p labs s1.(mem) a0 (big_endian (asmProps.config mc_conf.(target))) =
    SOME (t1.(asmSem.mem) a0) ->
  word_loc_val_byte p labs (write_bytearray c1 new_bytes s1.(mem) s1.(mem_domain) s1.(be)) a0
    (big_endian (asmProps.config mc_conf.(target))) =
  SOME (asm_write_bytearray c1 new_bytes t1.(asmSem.mem) a0).
Proof.
  intros mc_conf s1 t1 p labs a0 c1 new_bytes. revert c1.
  induction new_bytes as [|b xs IH]; intros c1 x (Hba & Hg & Ht & Hs & Hbe & Hr & Hv); [exact Hv|].
  cbn [LENGTH] in Hr. rewrite (proj2 (read_bytearray_def _ _ _)) in Hr.
  destruct (mem_load_byte_aux _ _ _ c1) as [v0|] eqn:Ev; [|discriminate].
  destruct (read_bytearray (c1 + n2w 1)%w _ _) as [y|] eqn:Ey; [|discriminate].
  specialize (IH (c1 + n2w 1)%w y (conj Hba (conj Hg (conj Ht (conj Hs (conj Hbe (conj Ey Hv))))))).
  unfold mem_load_byte_aux in Ev.
  destruct (mem s1 (byte_align c1)) as [c|] eqn:Emc; [|discriminate].
  destruct (classical_dec (byte_align c1 IN mem_domain s1)) as [Hdc|]; [|discriminate].
  cbn [write_bytearray asm_write_bytearray]. unfold mem_store_byte_aux.
  set (W := write_bytearray (c1 + n2w 1)%w xs (mem s1) (mem_domain s1) (be s1)) in *.
  destruct (W (byte_align c1)) as [v|n1 n2] eqn:EW.
  2: { exfalso. exact (write_bytearray_NOT_Loc xs (c1 + n2w 1)%w s1 _ c n1 n2 Emc EW). }
  destruct (classical_dec _) as [_|]; [|contradiction].
  rewrite Hbe in *. set (bbe := big_endian (asmProps.config mc_conf.(target))) in *.
  unfold word_loc_val_byte in IH |- *. rewrite !APPLY_UPDATE_THM.
  destruct (decide (byte_align c1 = byte_align a0)) as [Eal|Nal].
  - cbn [word_loc_val]. rewrite <- Eal, EW in IH. cbn [word_loc_val] in IH.
    destruct (decide (c1 = a0)) as [->|Ne].
    + rewrite good_dimindex_get_byte_set_byte by exact Hg. reflexivity.
    + rewrite get_byte_set_byte_diff by (split; [exact Hg|split; [congruence|congruence]]).
      exact IH.
  - destruct (decide (c1 = a0)) as [->|Ne]; [contradiction|]. exact IH.
Qed.

End ByteArray.
