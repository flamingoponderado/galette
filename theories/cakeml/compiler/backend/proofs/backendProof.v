(** * Backend correctness infrastructure for the Pancake pipeline.
    Partial port of [cakeml/compiler/backend/proofs/backendProofScript.sml].
    The CakeML source/clos/bvl/data composition theorems are not ported.
    HOL's [PERMUTES] abbreviates [BIJ f s s]; quantified predicates under
    [EVERY] and [OPTION_ALL] are reflected using [bool_decide].
    [OPTION_ALL] is a local notation for its two HOL defining clauses;
    this does not add a declaration to the shared option theory. *)
From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree finite_map.
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.backend Require Import labLang.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmProps.
From Galette.cakeml.compiler.backend Require backend backend_common data_to_word stack_names stack_remove stack_to_lab lab_to_target word_to_word word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.backend.semantics Require stackProps wordConvs.
From Galette.cakeml.compiler.backend.proofs Require stack_removeProof word_to_wordProof.
Open Scope N_scope.
Local Notation "'OPTION_ALL' P opt" := (match opt with NONE => true | SOME x => P x end) (at level 10, P at next level, opt at next level).
Section Backend.
Context {a : N}.
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "byte_aligned_MOD" *)
Theorem byte_aligned_MOD : good_dimindex a -> forall x : word a,
 x IN (fun w => byte_aligned w) -> w2n x MOD (dimindex a DIV 8) = 0.
Proof.
 intros Hd x Hx; unfold byte_aligned in Hx; apply aligned_w2n in Hx.
 destruct Hd as [Hd|Hd]; rewrite Hd in Hx |- *; exact Hx.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "backend_config_ok_def" *)
Definition backend_config_ok (asm_conf : asm_config a) (c : backend.config) : Prop :=
 backend.source_conf c = backend.prim_src_config /\
 0 < clos_to_bvl.max_app (backend.clos_conf c) /\
 bvl_to_bvi.next_name2 (backend.bvl_conf c) = backend_common.bvl_num_stubs + 2 /\
 LENGTH (avoid_regs asm_conf) + 13 <= reg_count asm_conf /\
 lab_to_target.pos (backend.lab_conf c) = 0 /\ lab_to_target.labels (backend.lab_conf c) = LN /\
 data_to_word.conf_ok a (backend.data_conf c) /\
 (data_to_word.has_longdiv (backend.data_conf c) -> ISA asm_conf = x86_64) /\
 (data_to_word.has_div (backend.data_conf c) -> ISA asm_conf = ARMv8 \/ ISA asm_conf = MIPS \/ ISA asm_conf = RISC_V) /\
 (data_to_word.has_fp_tern (backend.data_conf c) <-> ISA asm_conf = ARMv7 /\ 2 < fp_reg_count asm_conf) /\
 (data_to_word.has_fp_ops (backend.data_conf c) <-> 1 < fp_reg_count asm_conf) /\
 stack_remove.max_stack_alloc <= 2 * data_to_word.max_heap_limit a (backend.data_conf c) - 1 /\
 stack_to_lab.perf_calls (backend.stack_conf c) = false /\
 addr_offset_ok asm_conf (n2w 0) /\ hw_offset_ok asm_conf (n2w 0) /\
 (forall w : word a, (word_le (word_2comp (n2w 8)) w /\ word_le w (n2w 8)) -> byte_offset_ok asm_conf w) /\
 valid_imm asm_conf (inl asm.Add) (n2w 8) /\ valid_imm asm_conf (inl asm.Add) (n2w 4) /\
 valid_imm asm_conf (inl asm.Add) (n2w 1) /\ valid_imm asm_conf (inl asm.Sub) (n2w 1) /\
 OPTION_ALL (fun xs => EVERY (fun x => bool_decide (exists s, x = ffi.ExtCall s)) xs) (lab_to_target.ffi_names (backend.lab_conf c)) /\
 BIJ (stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c))) UNIV UNIV /\
 stack_names.names_ok (stack_to_lab.reg_names (backend.stack_conf c)) (reg_count asm_conf) (avoid_regs asm_conf) /\
 stackProps.fixed_names (stack_to_lab.reg_names (backend.stack_conf c)) asm_conf /\
 (forall s, addr_offset_ok asm_conf (@stack_remove.store_offset a s)) /\
 (forall s, hw_offset_ok asm_conf (@stack_remove.store_offset a s)) /\
 (forall n, n <= stack_remove.max_stack_alloc ->
 valid_imm asm_conf (inl asm.Sub) (n2w (n * (dimindex a DIV 8))) /\
 valid_imm asm_conf (inl asm.Add) (n2w (n * (dimindex a DIV 8)))).
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "mc_init_ok_def" *)
Definition mc_init_ok {B C : Type} (asm_conf : asm_config a) (c : backend.config) (mc : machine_config a B C) : Prop :=
 EVERY (fun r => MEM (stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c))
 (r + reg_count (asmProps.config (target mc)) - (LENGTH (avoid_regs (asmProps.config (target mc))) + 5))) (callee_saved_regs mc)) [2;3;4] /\
 stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 4 = len2_reg mc /\
 stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 3 = ptr2_reg mc /\
 stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 2 = len_reg mc /\
 stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 1 = ptr_reg mc /\
 stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 0 =
 (match link_reg (asmProps.config (target mc)) with NONE => 0 | SOME n => n end) /\
 data_to_word.be (backend.data_conf c) = big_endian (asmProps.config (target mc)) /\
 (match link_reg (asmProps.config (target mc)) with NONE => 0 | SOME n => n end) <> len_reg mc /\
 (match link_reg (asmProps.config (target mc)) with NONE => 0 | SOME n => n end) <> ptr_reg mc /\
 (match link_reg (asmProps.config (target mc)) with NONE => 0 | SOME n => n end) <> len2_reg mc /\
 (match link_reg (asmProps.config (target mc)) with NONE => 0 | SOME n => n end) <> ptr2_reg mc /\
 ~ MEM (match link_reg (asmProps.config (target mc)) with NONE => 0 | SOME n => n end) (callee_saved_regs mc) /\
 asm_conf = asmProps.config (target mc).
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "heap_regs_def" *)
Definition heap_regs reg_names := (stack_names.find_name reg_names 2, stack_names.find_name reg_names 4).
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "word_list_exists_imp" *)
Theorem word_list_exists_imp : forall (ad : word a) n dm (m1 : word a -> wordLang.word_loc a),
 dm = stack_removeProof.addresses ad n /\ dimindex a DIV 8 * n < dimword a /\ good_dimindex a ->
 word_list_exists ad n (fun2set (m1,dm)).
Proof. intros ad n dm m1 [-> H]; apply stack_removeProof.word_list_exists_addresses; exact H. Qed.
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "read_limits_def" *)
Definition read_limits {B C : Type} (asm_conf : asm_config a) (c : backend.config) (mc : machine_config a B C) (ms : B) :=
 stack_removeProof.get_stack_heap_limit (2 * data_to_word.max_heap_limit a (backend.data_conf c) - 1)
 (get_reg (target mc) ms (stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 2),
 (get_reg (target mc) ms (stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 3),
 get_reg (target mc) ms (stack_names.find_name (stack_to_lab.reg_names (backend.stack_conf c)) 4))).

(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_lab_LENGTH" *)
Theorem compile_lab_LENGTH : forall (asm_conf : asm_config a) c secs bytes c',
 lab_to_target.compile_lab asm_conf c secs = SOME (bytes,c') ->
 lab_to_target.pos c' = LENGTH bytes + lab_to_target.pos c.
Proof.
 intros ac c secs bytes c' H; unfold lab_to_target.compile_lab in H.
 destruct (lab_to_target.ffi_names c) as [ffis|]; cbn beta iota zeta in H.
 all: try (destruct (list_subset (lab_to_target.find_ffi_names secs) ffis); [|discriminate]).
 all: destruct (lab_to_target.remove_labels (lab_to_target.init_clock c) ac (lab_to_target.pos c) (lab_to_target.labels c) _ secs) as [[secs0 l1]|]; [|discriminate].
 all: destruct (lab_to_target.get_shmem_info secs0 (lab_to_target.pos c) [] []) as [new_ffis infos].
 all: injection H as <- <-; reflexivity.
Qed.

Local Lemma compile_prog_frame_bitmap (ac : asm_config a) perf p n k bm1 bm2 :
 FST (SND (word_to_stack.compile_prog ac perf p n k bm1)) =
 FST (SND (word_to_stack.compile_prog ac perf p n k bm2)).
Proof.
 unfold word_to_stack.compile_prog; cbv zeta.
 repeat match goal with |- context [word_to_stack.comp ?ac ?pf ?pr ?bm ?ctx] =>
 destruct (word_to_stack.comp ac pf pr bm ctx) as [? ?] end; reflexivity.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_word_to_stack_sfs_aux" *)
Theorem compile_word_to_stack_sfs_aux : forall (ac : asm_config a) perf k p bm progs' fs' bitmaps,
 word_to_stack.compile_word_to_stack ac perf k p bm = (progs',(fs',bitmaps)) /\ perf = false ->
 fromAList (MAP (fun kv => (FST kv,
 (fun '(arg_count,prog) => FST (SND (word_to_stack.compile_prog ac perf prog arg_count k (Nil,0)))) (SND kv))) p) =
 fromAList (MAP (fun '((i,_),n) => (i,n)) (ZIP (progs',fs'))).
Proof.
 intros ac perf k p; revert perf; induction p as [|[i [n p]] ps IH]; intros perf bm progs fs bitmaps [H ->].
 - cbn [word_to_stack.compile_word_to_stack] in H; injection H as <- <- <-; reflexivity.
 - cbn [word_to_stack.compile_word_to_stack] in H.
   destruct (word_to_stack.compile_prog ac false p n k bm) as [q [f bm1]] eqn:E.
   destruct (word_to_stack.compile_word_to_stack ac false k ps bm1) as [qs [fs0 bm2]] eqn:Et.
   injection H as <- <- <-; cbn [MAP FST SND ZIP fromAList].
   rewrite (IH false bm1 qs fs0 bm2 (conj Et eq_refl)).
   rewrite (compile_prog_frame_bitmap ac false p n k (Nil,0) bm), E; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_lab_IMP_mmio_pcs_min_index" *)
Theorem compile_lab_IMP_mmio_pcs_min_index : forall (asm_conf : asm_config a) c secs bytes c',
 lab_to_target.compile_lab asm_conf c secs = SOME (bytes,c') /\
 OPTION_ALL (fun xs => EVERY (fun x => bool_decide (exists s, x = ExtCall s)) xs) (lab_to_target.ffi_names c) ->
 exists ffi_names, lab_to_target.ffi_names c' = SOME ffi_names /\
 exists x, mmio_pcs_min_index ffi_names = SOME x.
Proof.
 assert (Hfresh : forall (e : ffiname) xs,
   (exists s, e = ExtCall s) -> Forall (fun x => exists s, x = ExtCall s) xs ->
   Forall (fun x => exists s, x = ExtCall s) (lab_to_target.list_add_if_fresh e xs)).
 { intros e xs He Hxs; induction Hxs as [|x xs Hx Hxs IH]; cbn [lab_to_target.list_add_if_fresh].
   - constructor; [exact He|constructor].
   - destruct (decide (e = x)); constructor; assumption. }
 assert (Hfind : forall secs : list (sec a), Forall (fun x => exists s, x = ExtCall s) (lab_to_target.find_ffi_names secs)).
 { induction secs as [|[k xs] rest IH]; [constructor|].
   induction xs as [|ln xs IHxs]; [exact IH|].
   destruct ln; cbn [lab_to_target.find_ffi_names]; try exact IHxs.
   destruct a0; cbn [lab_to_target.find_ffi_names]; try exact IHxs.
   apply Hfresh; [eexists; reflexivity|exact IHxs]. }
 assert (Hshared : forall (secs : list (sec a)) pos names infos,
   Forall (fun x => exists op, x = SharedMem op) names ->
   Forall (fun x => exists op, x = SharedMem op) (FST (lab_to_target.get_shmem_info secs pos names infos))).
 { induction secs as [|[k xs] rest IH]; intros pos names infos Hnames; [exact Hnames|].
   revert pos names infos Hnames; induction xs as [|ln xs IHxs]; intros pos names infos Hnames.
   - exact (IH pos names infos Hnames).
   - destruct ln; cbn [lab_to_target.get_shmem_info]; try (apply IHxs; exact Hnames).
     destruct a0; cbn [lab_to_target.get_shmem_info]; try (apply IHxs; exact Hnames).
     destruct (lab_to_target.get_memop_info m) as [name nb].
     apply IHxs; apply Forall_app; split; [exact Hnames|constructor; [eexists; reflexivity|constructor]]. }
 assert (Hboundary : forall ext shared : list ffiname,
 Forall (fun x => exists s, x = ExtCall s) ext ->
 Forall (fun x => exists op, x = SharedMem op) shared ->
 exists x, x <= LENGTH (ext ++ shared) /\
 (forall j, j < x -> exists s, EL j (ext ++ shared) = ExtCall s) /\
 (forall j, x <= j /\ j < LENGTH (ext ++ shared) -> exists op, EL j (ext ++ shared) = SharedMem op)).
 { intros ext shared He Hs; exists (LENGTH ext); split; [rewrite !LENGTH_length, length_app; lia|].
   rewrite Forall_forall in He,Hs; split.
   - intros j Hj; assert (Hnat : (N.to_nat j < length ext)%nat).
     { rewrite LENGTH_length in Hj; lia. }
     rewrite EL_nth by (rewrite !LENGTH_length, length_app; lia).
     rewrite app_nth1 by exact Hnat; apply He; apply nth_In; exact Hnat.
   - intros j [Hlo Hhi]; assert (Hnat : (length ext <= N.to_nat j < length (ext ++ shared))%nat).
     { rewrite LENGTH_length in Hlo,Hhi; lia. }
     rewrite EL_nth by exact Hhi; rewrite app_nth2 by lia.
     apply Hs; apply nth_In; rewrite length_app in Hnat; lia. }
 intros ac c secs bytes c' [H Hff]; unfold lab_to_target.compile_lab in H.
 destruct (lab_to_target.ffi_names c) as [ffis|] eqn:Ec; cbn beta iota zeta in H,Hff.
 all: try (destruct (list_subset (lab_to_target.find_ffi_names secs) ffis); [|discriminate]).
 all: destruct (lab_to_target.remove_labels (lab_to_target.init_clock c) ac (lab_to_target.pos c) (lab_to_target.labels c) _ secs) as [[secs0 l1]|]; [|discriminate].
 all: destruct (lab_to_target.get_shmem_info secs0 (lab_to_target.pos c) [] []) as [new_ffis infos] eqn:Es.
 all: injection H as <- <-; eexists; split; [reflexivity|].
 all: unfold mmio_pcs_min_index, some; destruct (classical_dec _) as [Hex|Hnone]; [eexists; reflexivity|].
 all: exfalso; apply Hnone; apply Hboundary.
 - apply EVERY_Forall in Hff; eapply Forall_impl; [|exact Hff]; intros x Hx; exact (proj1 (bool_decide_spec _) Hx).
 - pose proof (Hshared secs0 (lab_to_target.pos c) [] [] (Forall_nil _)) as Hs; rewrite Es in Hs; exact Hs.
 - apply Hfind.
 - pose proof (Hshared secs0 (lab_to_target.pos c) [] [] (Forall_nil _)) as Hs; rewrite Es in Hs; exact Hs.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_to_word_conventions2" *)
Theorem compile_to_word_conventions2 : forall (wc : word_to_word.config) (ac : asm_config a) (p : list (N * (N * wordLang.prog a))) ign ps,
  word_to_word.compile wc ac p = (ign,ps) /\
  EVERY (fun '(_, (_, prg)) => ⌜wordConvs.no_share_inst prg \/ ISA ac <> Ag32⌝) p ->
  MAP FST ps = MAP FST p /\
  LIST_REL wordConvs.labels_rel (MAP (wordConvs.extract_labels ∘ SND ∘ SND) p) (MAP (wordConvs.extract_labels ∘ SND ∘ SND) ps) /\
  EVERY (fun '(n, (m, prog)) =>
    ⌜wordConvs.flat_exp_conventions prog /\
     wordConvs.post_alloc_conventions (reg_count ac - (5 + LENGTH (avoid_regs ac))) prog /\
     (EVERY (fun '(n, (m, prog)) => wordConvs.every_inst (wordConvs.inst_ok_less ac) prog) p /\
      addr_offset_ok ac (n2w 0) /\ hw_offset_ok ac (n2w 0) /\ byte_offset_ok ac (n2w 0) ->
      wordConvs.full_inst_ok_less ac prog) /\
     (two_reg_arith ac -> wordConvs.every_inst wordConvs.two_reg_inst prog) /\
     (wordConvs.no_share_inst prog \/ ISA ac <> Ag32)⌝) ps.
Proof.
 intros wc ac p ign ps [Hc Hp]; pose proof (word_to_wordProof.compile_to_word_conventions wc ac p Hp) as H.
 rewrite Hc in H; exact H.
Qed.
End Backend.
