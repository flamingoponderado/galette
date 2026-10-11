(** * CakeML [lab_to_targetProof]: [compile_correct]

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml]: the
    theorem [compile_correct] (HOL lines 7528-9353), assembled from its
    cases ([lab_to_targetProof/cc_asm.v], [cc_jump.v], [cc_ffi.v],
    [cc_install.v], [cc_share.v]).

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - HOL's free variable [p] (the code start address) is universally
      quantified; HOL's unused existential [t2] is kept.
    - Not ported: the ML binding [say]. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
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
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute rl_remove
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install cc_share.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.




Ltac ev_error Hev Hres := injection Hev as <- _; exfalso; apply Hres; reflexivity.

Section CompileCorrect.
Context {a : N} {B C Ffi : Type}.

Lemma cc_goal_all p : forall n (s1 : labSem.state a config Ffi), clock s1 = n -> @cc_goal a B C Ffi p s1.
Proof.
  intros n. induction n as [n IHn] using (well_founded_induction N.lt_wf_0).
  intros s1 Hn res mc_conf s2 code2 labs t1 ms1 (Ho & Hev & Hres & Henc & R).
  assert (IH : forall s', clock s' < clock s1 -> @cc_goal a B C Ffi p s')
    by (intros s' Hs'; apply (IHn (clock s')); [lia|reflexivity]).
  clear IHn Hn.
  rewrite labSem.evaluate_def in Hev.
  destruct (N.eqb_spec (clock s1) 0) as [Hc0|Hc].
  { injection Hev as <- <-. exists 0, t1, ms1. rewrite N.add_0_r, Hc0, targetSem.evaluate_eqn. reflexivity. }
  destruct (asm_fetch s1) as [line|] eqn:Hf; [|ev_error Hev Hres].
  destruct line as [k1 k2 l | b bytes len | x w bytes len].
  - ev_error Hev Hres.
  - destruct b as [i | r1 r2 | m r ad].
    + destruct i as [i | w0 | cmp0 rr ri w0 | w0 | r | r w0]; try (ev_error Hev Hres).
      * cbv zeta in Hev. destruct (failed (asm_inst i s1)) eqn:Efl; [ev_error Hev Hres|].
        apply (cc_Asm_Inst p s1 i bytes len Hc Hf ltac:(rewrite Efl; discriminate) IH
                 res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
      * destruct (regs s1 r) as [w1|n1 n2] eqn:Er; [ev_error Hev Hres|].
        destruct (loc_to_pc n1 n2 (code s1)) as [x|] eqn:Ex; [|ev_error Hev Hres].
        apply (cc_Asm_JumpReg p s1 r bytes len n1 n2 x Hc Hf Er Ex IH
                 res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
    + destruct (regs s1 r1) as [w1|] eqn:Er1; [|ev_error Hev Hres].
      destruct (regs s1 r2) as [w2|] eqn:Er2; [|ev_error Hev Hres].
      destruct (wordSem.buffer_write (code_buffer s1) w1 (w2w w2)) as [new_cb|] eqn:Ebw; [|ev_error Hev Hres].
      apply (cc_Cbw p s1 r1 r2 bytes len w1 w2 new_cb Hc Hf Er1 Er2 Ebw IH
               res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
    + apply (cc_ShareMem p s1 m r ad bytes len Hc Hf IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
  - destruct x as [[l1 l2]|cmp0 rr ri [l1 l2]|lab|r [l1 l2]|name| |].
    + (* Jump *)
      cbn [get_pc_value] in Hev.
      destruct (loc_to_pc l1 l2 (code s1)) as [x|] eqn:Ex; [|ev_error Hev Hres].
      apply (cc_Jump p s1 l1 l2 w bytes len x Hc Hf Ex IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
    + (* JumpCmp *)
      destruct (wordSem.word_cmp cmp0 (regs s1 rr) (labSem.reg_imm ri s1)) as [[|]|] eqn:Ecmp;
        [|apply (cc_JumpCmp_false p s1 cmp0 rr ri (Lab l1 l2) w bytes len Hc Hf Ecmp IH
                   res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R)|ev_error Hev Hres].
      cbn [get_pc_value] in Hev.
      destruct (loc_to_pc l1 l2 (code s1)) as [x|] eqn:Ex; [|ev_error Hev Hres].
      apply (cc_JumpCmp_true p s1 cmp0 rr ri l1 l2 w bytes len x Hc Hf Ecmp Ex IH
               res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
    + (* Call *)
      exfalso. exact (cc_Call s1 lab w bytes len Hf p mc_conf code2 labs t1 ms1 R).
    + (* LocValue *)
      cbn [get_pc_value lab_to_loc] in Hev.
      destruct (loc_to_pc l1 l2 (code s1)) as [x|] eqn:Ex.
      * rewrite (bool_decide_false (SOME x = NONE)) in Hev by discriminate. cbv zeta in Hev.
        apply (cc_LocValue p s1 r l1 l2 w bytes len x Hc Hf Ex IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
      * rewrite (proj2 (bool_decide_spec (NONE = @NONE N)) eq_refl) in Hev. ev_error Hev Hres.
    + (* CallFFI *)
      destruct (regs s1 (len_reg s1)) as [wl|] eqn:El1; [|ev_error Hev Hres].
      destruct (regs s1 (ptr_reg s1)) as [wp|] eqn:Ep1; [|ev_error Hev Hres].
      destruct (regs s1 (len2_reg s1)) as [wl2|] eqn:El2; [|ev_error Hev Hres].
      destruct (regs s1 (ptr2_reg s1)) as [wp2|] eqn:Ep2; [|ev_error Hev Hres].
      destruct (regs s1 (link_reg s1)) as [wlk|n1 n2] eqn:Elk; [ev_error Hev Hres|].
      destruct (read_bytearray wp (w2n wl) (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1)))
        as [xb|] eqn:Exb; [|ev_error Hev Hres].
      destruct (read_bytearray wp2 (w2n wl2) (mem_load_byte_aux (mem s1) (mem_domain s1) (be s1)))
        as [xb2|] eqn:Exb2; [|ev_error Hev Hres].
      destruct (loc_to_pc n1 n2 (code s1)) as [new_pc|] eqn:Enp; [|ev_error Hev Hres].
      apply (cc_CallFFI p s1 name w bytes len wl wp wl2 wp2 n1 n2 xb xb2 new_pc Hc Hf El1 Ep1 El2 Ep2 Elk
               Exb Exb2 Enp IH res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
    + (* Install *)
      destruct (regs s1 (ptr_reg s1)) as [w1|] eqn:Ep1; [|ev_error Hev Hres].
      destruct (regs s1 (len_reg s1)) as [w2|] eqn:El1; [|ev_error Hev Hres].
      destruct (regs s1 (link_reg s1)) as [wlk|n1 n2] eqn:Elk; [ev_error Hev Hres|].
      destruct (wordSem.buffer_flush (code_buffer s1) w1 w2) as [[bytes0 cb]|] eqn:Ebf; [|ev_error Hev Hres].
      destruct (loc_to_pc n1 n2 (code s1)) as [new_pc|] eqn:Enp; [|ev_error Hev Hres].
      destruct (compile_oracle s1 0) as [cfg prog0] eqn:Eorc.
      cbv zeta in Hev.
      destruct (compile s1 cfg prog0) as [[bytes' cfg']|] eqn:Ecomp; [|ev_error Hev Hres].
      destruct prog0 as [|[k lines] rest]; [ev_error Hev Hres|].
      destruct (bool_decide (bytes0 = bytes') && ⌜FST (shift_seq 1 (compile_oracle s1) 0) = cfg'⌝) eqn:Eok;
        [|ev_error Hev Hres].
      apply Bool.andb_true_iff in Eok as [Eb Ecfg]. apply bool_decide_spec in Eb, Ecfg.
      apply (cc_Install p s1 w bytes len w1 w2 n1 n2 bytes0 cb new_pc cfg (Section_ k lines :: rest) bytes' cfg'
               k lines rest Hc Hf Ep1 El1 Elk Ebf Enp Eorc Ecomp eq_refl Eb Ecfg IH
               res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
    + (* Halt *)
      apply (cc_Halt p s1 w bytes len Hc Hf res mc_conf s2 code2 labs t1 ms1 Ho Hev Hres Henc R).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall (s1 : labSem.state a config Ffi) res (mc_conf : machine_config a B C)
    s2 code2 labs (t1 : asm_state a) ms1 p,
  oracle_tie mc_conf ms1 s1 /\
  labSem.evaluate s1 = (res, s2) /\ res <> Error /\
  encoder_correct mc_conf.(target) /\
  state_rel (mc_conf, (code2, (labs, p))) s1 t1 ms1 ->
  exists k (t2 : asm_state a) ms2,
    targetSem.evaluate mc_conf s1.(ffi) (s1.(clock) + k) ms1 = (res, (ms2, s2.(ffi))).
Proof.
  intros s1 res mc_conf s2 code2 labs t1 ms1 p H.
  exact (cc_goal_all p (clock s1) s1 eq_refl res mc_conf s2 code2 labs t1 ms1 H).
Qed.

End CompileCorrect.
