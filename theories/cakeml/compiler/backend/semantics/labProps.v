(** * CakeML [labProps]: properties of labLang and its semantics

    Port of [cakeml/compiler/backend/semantics/labPropsScript.sml].

    - HOL's [s with f := v] is [set_<f> v s] ([labSem]); HOL's overload
      [read_reg r s] is [regs s r].
    - HOL's sets are [pred_set] sets ([_ -> Prop]); [{(n1,n2)}] is
      [INSERT (n1,n2) EMPTY].
    - HOL's [evaluate_ind] (recursion induction on the clock) is replaced by
      induction on the clock.
    - Not ported: [case_eq_thms] (an ML-generated list of HOL's
      [case_eq] rewrites; Rocq case splits do this job).
    - [all_enc_ok_pre] (an HOL overload) is an [Abbreviation].
    - Prefix facts on [isPREFIX] (HOL [rich_list]'s [IS_PREFIX_REFL],
      [IS_PREFIX_TRANS], [IS_PREFIX_APPEND]) are local untagged helpers. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import semanticsProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem targetSem.
From Galette.cakeml.compiler.backend.semantics Require Import labSem.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, mem_load_32, mem_store_32,
  write_bytearray).
Import targetSem (machine_result(..)).
Open Scope N_scope.

(** ** Labels of programs *)

Section Labels.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "extract_labels_def" *)
Fixpoint extract_labels (l : list (line a)) : list (N * N) :=
  match l with
  | [] => []
  | Label l1 l2 _ :: xs => (l1, l2) :: extract_labels xs
  | _ :: xs => extract_labels xs
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "extract_labels_append" *)
Theorem extract_labels_append : forall A B,
  extract_labels (A ++ B) = extract_labels A ++ extract_labels B.
Proof.
  induction A as [|h A IH]; intros B; [reflexivity|].
  destruct h; cbn; rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "labs_of_def" *)
Definition labs_of (x : asm_with_lab a) : N * N -> Prop :=
  match x with
  | LocValue _ (Lab n1 n2) => (n1, n2) INSERT {}
  | Jump (Lab n1 n2) => (n1, n2) INSERT {}
  | JumpCmp _ _ _ (Lab n1 n2) => (n1, n2) INSERT {}
  | _ => {}
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_get_labels_def" *)
Definition line_get_labels (l : line a) : N * N -> Prop :=
  match l with
  | LabAsm a0 _ _ _ => labs_of a0
  | _ => {}
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_get_labels_def" *)
Definition sec_get_labels (s : sec a) : N * N -> Prop :=
  match s with
  | Section_ _ lines => BIGUNION (IMAGE line_get_labels (set lines))
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_labels_def" *)
Definition get_labels (code : list (sec a)) : N * N -> Prop :=
  BIGUNION (IMAGE sec_get_labels (set code)).

Lemma BIGUNION_IMAGE_cons {A B} (f : A -> B -> Prop) x xs :
  BIGUNION (IMAGE f (set (x :: xs))) = f x UNION BIGUNION (IMAGE f (set xs)).
Proof.
  rewrite (proj2 (LIST_TO_SET_thm x xs)), IMAGE_INSERT, BIGUNION_INSERT; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_labels_cons" *)
Theorem get_labels_cons : forall x xs,
  get_labels (x :: xs) = sec_get_labels x UNION get_labels xs.
Proof. intros; unfold get_labels; apply BIGUNION_IMAGE_cons. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_get_code_labels_def" *)
Definition line_get_code_labels (l : line a) : N -> Prop :=
  match l with
  | Label _ l0 _ => l0 INSERT {}
  | _ => {}
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_get_code_labels_def" *)
Definition sec_get_code_labels (s : sec a) : N * N -> Prop :=
  match s with
  | Section_ n1 lines =>
      (n1, 0) INSERT
      IMAGE (fun n2 => (n1, n2)) (BIGUNION (IMAGE line_get_code_labels (set lines)))
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_def" *)
Definition get_code_labels (code : list (sec a)) : N * N -> Prop :=
  BIGUNION (IMAGE sec_get_code_labels (set code)).

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_nil" *)
Theorem get_code_labels_nil : get_code_labels [] = {}.
Proof.
  unfold get_code_labels; rewrite (proj1 (LIST_TO_SET_thm (inhabitant (sec a)) [])).
  rewrite IMAGE_EMPTY, BIGUNION_EMPTY; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_cons" *)
Theorem get_code_labels_cons : forall s secs,
  get_code_labels (s :: secs) = sec_get_code_labels s UNION get_code_labels secs.
Proof. intros; unfold get_code_labels; apply BIGUNION_IMAGE_cons. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_ends_with_label_def" *)
Definition sec_ends_with_label (s : sec a) : bool :=
  match s with
  | Section_ _ ls => negb (NULL ls) && is_Label (LAST ls)
  end.

End Labels.

(** ** Simple facts about the state operations *)

Section StateOps.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : state a c ffi_t).

(** Reduce record projections of the state updates (Galette tactic). *)
Ltac st_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg dec_clock inc_pc assert] in *.

(** Destruct the first [match] scrutinee of the goal. *)
Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E
  end.

Ltac unfold_ops :=
  unfold asm_inst, arith_upd, binop_upd, fp_upd, mem_op, mem_load, mem_store, mem_load32,
    mem_store32, mem_load_byte, mem_store_byte, addr, reg_imm, read_fp_reg in *.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "reg_imm_with_clock" *)
Theorem reg_imm_with_clock : forall r z s, reg_imm r (set_clock z s) = reg_imm r s.
Proof. intros [] z s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_inst_with_clock" *)
Theorem asm_inst_with_clock : forall (i : asm.inst a) z s,
  asm_inst i (set_clock z s) = set_clock z (asm_inst i s).
Proof.
  intros i z [];
    destruct i as [|? ?|[]|[] ? []|[]]; unfold_ops; st_cbn;
    repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_reg_inc_pc" *)
Theorem read_reg_inc_pc : forall r s, read_reg r (inc_pc s) = read_reg r s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "with_same_clock" *)
Theorem with_same_clock : forall s, set_clock (clock s) s = s.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "inc_pc_dec_clock" *)
Theorem inc_pc_dec_clock : forall x : state a c ffi_t, inc_pc (dec_clock x) = dec_clock (inc_pc x).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "update_simps" *)
Theorem update_simps : forall (x : N) s,
    (ffi (upd_pc x s) = ffi s) /\
    (ffi (dec_clock s) = ffi s) /\
    (pc (upd_pc x s) = x) /\
    (pc (dec_clock s) = pc s) /\
    (clock (upd_pc x s) = clock s) /\
    (ffi (upd_pc x s) = ffi s) /\
    (clock (dec_clock s) = clock s - 1) /\
    (len_reg (dec_clock s) = len_reg s) /\
    (len2_reg (dec_clock s) = len2_reg s) /\
    (link_reg (dec_clock s) = link_reg s) /\
    (code (dec_clock s) = code s) /\
    (ptr_reg (dec_clock s) = ptr_reg s) /\
    (ptr2_reg (dec_clock s) = ptr2_reg s) /\
    (ffi (dec_clock s) = ffi s) /\
    (len_reg (upd_pc x s) = len_reg s) /\
    (len2_reg (upd_pc x s) = len2_reg s) /\
    (link_reg (upd_pc x s) = link_reg s) /\
    (code (upd_pc x s) = code s) /\
    (ptr_reg (upd_pc x s) = ptr_reg s) /\
    (ptr2_reg (upd_pc x s) = ptr2_reg s) /\
    (mem_domain (upd_pc x s) = mem_domain s) /\
    (shared_mem_domain (upd_pc x s) = shared_mem_domain s) /\
    (failed (upd_pc x s) = failed s) /\
    (be (upd_pc x s) = be s) /\
    (mem (upd_pc x s) = mem s) /\
    (regs (upd_pc x s) = regs s) /\
    (fp_regs (upd_pc x s) = fp_regs s) /\
    (ffi (upd_pc x s) = ffi s) /\
    (ptr_reg (inc_pc s) = ptr_reg s) /\
    (ptr2_reg (inc_pc s) = ptr2_reg s) /\
    (len_reg (inc_pc s) = len_reg s) /\
    (len2_reg (inc_pc s) = len2_reg s) /\
    (link_reg (inc_pc s) = link_reg s) /\
    (code (inc_pc s) = code s) /\
    (be (inc_pc s) = be s) /\
    (failed (inc_pc s) = failed s) /\
    (mem_domain (inc_pc s) = mem_domain s) /\
    (shared_mem_domain (inc_pc s) = shared_mem_domain s) /\
    (io_regs (inc_pc s) = io_regs s) /\
    (io_fp_regs (inc_pc s) = io_fp_regs s) /\
    (cc_regs (inc_pc s) = cc_regs s) /\
    (cc_fp_regs (inc_pc s) = cc_fp_regs s) /\
    (compile (inc_pc s) = compile s) /\
    (compile_oracle (inc_pc s) = compile_oracle s) /\
    (code_buffer (inc_pc s) = code_buffer s) /\
    (mem (inc_pc s) = mem s) /\
    (regs (inc_pc s) = regs s) /\
    (fp_regs (inc_pc s) = fp_regs s) /\
    (pc (inc_pc s) = pc s + 1) /\
    (ffi (inc_pc s) = ffi s).
Proof. intros; repeat split. Qed.

Ltac consts_tac :=
  unfold_ops; st_cbn;
  repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "binop_upd_consts" *)
Theorem binop_upd_consts : forall a0 b c0 d (x : state a c ffi_t),
   mem_domain (binop_upd a0 b c0 d x) = mem_domain x /\
   shared_mem_domain (binop_upd a0 b c0 d x) = shared_mem_domain x /\
   ptr_reg (binop_upd a0 b c0 d x) = ptr_reg x /\
   ptr2_reg (binop_upd a0 b c0 d x) = ptr2_reg x /\
   len_reg (binop_upd a0 b c0 d x) = len_reg x /\
   len2_reg (binop_upd a0 b c0 d x) = len2_reg x /\
   link_reg (binop_upd a0 b c0 d x) = link_reg x /\
   code (binop_upd a0 b c0 d x) = code x /\
   be (binop_upd a0 b c0 d x) = be x /\
   mem (binop_upd a0 b c0 d x) = mem x /\
   io_regs (binop_upd a0 b c0 d x) = io_regs x /\
   io_fp_regs (binop_upd a0 b c0 d x) = io_fp_regs x /\
   cc_regs (binop_upd a0 b c0 d x) = cc_regs x /\
   cc_fp_regs (binop_upd a0 b c0 d x) = cc_fp_regs x /\
   compile (binop_upd a0 b c0 d x) = compile x /\
   compile_oracle (binop_upd a0 b c0 d x) = compile_oracle x /\
   code_buffer (binop_upd a0 b c0 d x) = code_buffer x /\
   pc (binop_upd a0 b c0 d x) = pc x /\
   ffi (binop_upd a0 b c0 d x) = ffi x.
Proof. intros a0 [] c0 d x; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "arith_upd_consts" *)
Theorem arith_upd_consts : forall a0 (x : state a c ffi_t),
   mem_domain (arith_upd a0 x) = mem_domain x /\
   shared_mem_domain (arith_upd a0 x) = shared_mem_domain x /\
   ptr_reg (arith_upd a0 x) = ptr_reg x /\
   ptr2_reg (arith_upd a0 x) = ptr2_reg x /\
   len_reg (arith_upd a0 x) = len_reg x /\
   len2_reg (arith_upd a0 x) = len2_reg x /\
   link_reg (arith_upd a0 x) = link_reg x /\
   code (arith_upd a0 x) = code x /\
   be (arith_upd a0 x) = be x /\
   mem (arith_upd a0 x) = mem x /\
   io_regs (arith_upd a0 x) = io_regs x /\
   io_fp_regs (arith_upd a0 x) = io_fp_regs x /\
   cc_regs (arith_upd a0 x) = cc_regs x /\
   cc_fp_regs (arith_upd a0 x) = cc_fp_regs x /\
   compile (arith_upd a0 x) = compile x /\
   compile_oracle (arith_upd a0 x) = compile_oracle x /\
   code_buffer (arith_upd a0 x) = code_buffer x /\
   pc (arith_upd a0 x) = pc x /\
   ffi (arith_upd a0 x) = ffi x.
Proof. intros [] x; repeat split; consts_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "fp_upd_consts" *)
Theorem fp_upd_consts : forall f (x : state a c ffi_t),
   mem_domain (fp_upd f x) = mem_domain x /\
   shared_mem_domain (fp_upd f x) = shared_mem_domain x /\
   ptr_reg (fp_upd f x) = ptr_reg x /\
   len_reg (fp_upd f x) = len_reg x /\
   ptr2_reg (fp_upd f x) = ptr2_reg x /\
   len2_reg (fp_upd f x) = len2_reg x /\
   link_reg (fp_upd f x) = link_reg x /\
   code (fp_upd f x) = code x /\
   cc_regs (fp_upd f x) = cc_regs x /\
   cc_fp_regs (fp_upd f x) = cc_fp_regs x /\
   code_buffer (fp_upd f x) = code_buffer x /\
   compile (fp_upd f x) = compile x /\
   compile_oracle (fp_upd f x) = compile_oracle x /\
   be (fp_upd f x) = be x /\
   mem (fp_upd f x) = mem x /\
   io_regs (fp_upd f x) = io_regs x /\
   io_fp_regs (fp_upd f x) = io_fp_regs x /\
   pc (fp_upd f x) = pc x /\
   ffi (fp_upd f x) = ffi x.
Proof. intros [] x; repeat split; consts_tac. Qed.

End StateOps.

Section LineLength.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_length_def" *)
Definition line_length (l : line a) : N :=
  match l with
  | Label k1 k2 l0 => if l0 =? 0 then 0 else 1
  | Asm b bytes l0 => LENGTH bytes
  | LabAsm a0 w bytes l0 => LENGTH bytes
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "LENGTH_line_bytes" *)
Theorem LENGTH_line_bytes : forall x2 : line a,
  ~ is_Label x2 -> LENGTH (line_bytes x2) = line_length x2.
Proof. intros [] H; cbn in *; [exfalso; apply H; reflexivity|reflexivity|reflexivity]. Qed.

End LineLength.

(** ** Clock and io-event properties of [evaluate] *)

(** Prefix order on lists (HOL [rich_list]'s [IS_PREFIX_REFL],
    [IS_PREFIX_TRANS], [IS_PREFIX_APPEND]); local helpers. *)
Local Lemma isPREFIX_refl {A} {HA : EqDecision A} (l : list A) : is_true (isPREFIX l l).
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  unfold is_true; rewrite Bool.andb_true_iff; split; [apply bool_decide_spec; reflexivity|exact IH].
Qed.

Local Lemma isPREFIX_trans {A} {HA : EqDecision A} (l1 l2 l3 : list A) :
  is_true (isPREFIX l1 l2) -> is_true (isPREFIX l2 l3) -> is_true (isPREFIX l1 l3).
Proof.
  revert l2 l3; induction l1 as [|x l1 IH]; intros [|y l2] [|z l3] H1 H2; cbn in *;
    try reflexivity; try discriminate.
  unfold is_true in *; rewrite Bool.andb_true_iff in *. destruct H1 as [H1 H1'], H2 as [H2 H2'].
  apply bool_decide_spec in H1, H2; subst.
  split; [apply bool_decide_spec; reflexivity|eapply IH; eassumption].
Qed.

Local Lemma isPREFIX_app {A} {HA : EqDecision A} (l1 l2 : list A) : is_true (isPREFIX l1 (l1 ++ l2)).
Proof.
  induction l1 as [|x l1 IH]; cbn; [reflexivity|].
  unfold is_true; rewrite Bool.andb_true_iff; split; [apply bool_decide_spec; reflexivity|exact IH].
Qed.

Local Lemma call_FFI_prefix {F} (st st' : ffi_state F) n conf bytes bytes' :
  call_FFI st n conf bytes = FFI_return st' bytes' ->
  is_true (isPREFIX (io_events st) (io_events st')).
Proof.
  unfold call_FFI. intros H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; try discriminate
         | context [if ?x then _ else _] => destruct x; try discriminate
         end;
  injection H as <- <-; cbn; apply isPREFIX_app || apply isPREFIX_refl.
Qed.

Section Evaluate.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : state a c ffi_t).

Ltac st_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg dec_clock inc_pc assert] in *.

(** Induction on the clock (replaces HOL's [evaluate_ind]). *)
Lemma evaluate_clock_ind (P : state a c ffi_t -> Prop) :
  (forall s, (forall s', clock s' < clock s -> P s') -> P s) -> forall s, P s.
Proof.
  intros H. apply (Wf_nat.induction_ltof1 _ (fun s => N.to_nat (clock s))).
  intros s IH. apply H. intros s' Hs. apply IH. unfold Wf_nat.ltof. lia.
Qed.

Lemma share_mem_op_final m r ad s f s' :
  share_mem_op m r ad s = SOME (FFI_final f, s') -> s' = s.
Proof.
  destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store; intros H;
    repeat match type of H with
           | context [match ?z with _ => _ end] =>
               let E := fresh "E" in destruct z eqn:E; cbn beta iota zeta in H
           end; try discriminate; injection H as _ <-; reflexivity.
Qed.

Lemma share_mem_op_prefix m r ad s f l s' :
  share_mem_op m r ad s = SOME (FFI_return f l, s') ->
  is_true (isPREFIX (io_events (ffi s)) (io_events (ffi s'))).
Proof.
  destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store; intros H;
    repeat match type of H with
           | context [match ?z with _ => _ end] =>
               let E := fresh "E" in destruct z eqn:E; cbn beta iota zeta in H
           end; try discriminate; injection H as _ _ <-; st_cbn;
    eapply call_FFI_prefix; eassumption.
Qed.

Lemma asm_inst_ffi i s : ffi (asm_inst i s) = ffi s.
Proof. apply asm_inst_consts. Qed.

Ltac clock_lt :=
  repeat match goal with
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         | H : share_mem_op _ _ _ _ = SOME (FFI_return _ _, _) |- _ =>
             apply share_mem_op_clock in H
         end;
  st_cbn; rewrite ?asm_inst_clock; lia.

Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E
  end.

Ltac split_hyp H :=
  match type of H with
  | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E
  end.

Ltac ffi_prefix :=
  st_cbn; rewrite ?asm_inst_ffi;
  first [ apply isPREFIX_refl
        | match goal with E : call_FFI _ _ _ _ = FFI_return _ _ |- _ =>
            eapply call_FFI_prefix; exact E end
        | match goal with E : share_mem_op _ _ _ _ = SOME (FFI_return _ _, _) |- _ =>
            eapply share_mem_op_prefix; exact E end ].

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall s1 r s2,
  evaluate s1 = (r, s2) -> is_true (isPREFIX (io_events (ffi s1)) (io_events (ffi s2))).
Proof.
  intros s1; induction s1 as [s IH] using evaluate_clock_ind; intros r s2 H.
  rewrite evaluate_def in H.
  repeat (split_hyp H; cbn beta iota zeta in H);
    try (injection H as _ <-; first [apply isPREFIX_refl
         | match goal with E : share_mem_op _ _ _ _ = SOME (FFI_final _, _) |- _ =>
             apply share_mem_op_final in E; subst; apply isPREFIX_refl end]);
    (apply IH in H; [eapply isPREFIX_trans; [|exact H]; ffi_prefix|clock_lt]).
Qed.

(** Equality of states from equality of all fields (Galette helper). *)
Lemma state_eq_intro (x y : state a c ffi_t) :
  regs x = regs y -> fp_regs x = fp_regs y -> mem x = mem y -> mem_domain x = mem_domain y ->
  shared_mem_domain x = shared_mem_domain y -> pc x = pc y -> be x = be y -> ffi x = ffi y ->
  io_regs x = io_regs y -> cc_regs x = cc_regs y -> io_fp_regs x = io_fp_regs y ->
  cc_fp_regs x = cc_fp_regs y -> code x = code y -> compile x = compile y ->
  compile_oracle x = compile_oracle y -> code_buffer x = code_buffer y -> clock x = clock y ->
  failed x = failed y -> ptr_reg x = ptr_reg y -> len_reg x = len_reg y ->
  ptr2_reg x = ptr2_reg y -> len2_reg x = len2_reg y -> link_reg x = link_reg y -> x = y.
Proof. destruct x, y; cbn; intros; subst; reflexivity. Qed.

Lemma share_mem_op_set_clock m r ad z s :
  share_mem_op m r ad (set_clock z s) =
  match share_mem_op m r ad s with
  | SOME (FFI_return f l, s') => SOME (FFI_return f l, set_clock (z - 1) s')
  | SOME (FFI_final f, s') => SOME (FFI_final f, set_clock z s')
  | NONE => NONE
  end.
Proof.
  destruct s; destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store, addr;
    st_cbn; repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.
Qed.

Ltac clock_facts :=
  repeat match goal with
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         | H : share_mem_op _ _ _ _ = SOME (FFI_return _ _, _) |- _ =>
             lazymatch goal with
             | _ : clock _ = (clock _ - 1)%N |- _ => fail
             | _ => pose proof (share_mem_op_clock _ _ _ _ _ _ _ H)
             end
         end.

Ltac state_eq :=
  apply state_eq_intro; st_cbn; rewrite ?asm_inst_clock; try reflexivity; clock_facts; lia.

(** HOL's [evaluate_ADD_clock] and the TimeOut case together (Galette
    helper): a run that times out continues from its final state. *)
Lemma evaluate_add_clock_gen : forall s res r k,
  evaluate s = (res, r) ->
  evaluate (set_clock (clock s + k) s) =
  match res with
  | TimeOut => evaluate (set_clock k r)
  | _ => (res, set_clock (clock r + k) r)
  end.
Proof.
  intros s; induction s as [s IH] using evaluate_clock_ind; intros res r k H.
  rewrite evaluate_def in H.
  destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. apply N.eqb_eq in Ec. rewrite Ec. reflexivity. }
  rewrite (evaluate_def (set_clock (clock s + k) s)).
  replace (clock (set_clock (clock s + k) s) =? 0) with false
    by (symmetry; apply N.eqb_neq; cbn; apply N.eqb_neq in Ec; lia).
  unfold asm_fetch, get_pc_value, get_ret_Loc in *; st_cbn.
  repeat (split_hyp H; cbn beta iota zeta in *; st_cbn;
          rewrite ?asm_inst_with_clock, ?reg_imm_with_clock, ?share_mem_op_set_clock in *;
          st_cbn).
  all: try (injection H as <- <-; cbn beta iota zeta;
            try (match goal with E : share_mem_op _ _ _ _ = SOME (FFI_final _, _) |- _ =>
                   apply share_mem_op_final in E; subst end);
            reflexivity).
  all: match goal with
       | H : evaluate ?Y = _ |- evaluate ?Y' = _ =>
           transitivity (evaluate (set_clock (clock Y + k) Y));
           [f_equal; state_eq | apply IH; [clock_lt|exact H]]
       end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_ADD_clock" *)
Theorem evaluate_ADD_clock : forall s res r k,
  evaluate s = (res, r) /\ res <> TimeOut ->
  evaluate (set_clock (clock s + k) s) = (res, set_clock (clock r + k) r).
Proof.
  intros s res r k [H Hr]. rewrite (evaluate_add_clock_gen s res r k H).
  destruct res; [reflexivity|reflexivity|contradiction].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "addr_add_clock_eq" *)
Theorem addr_add_clock_eq : forall (ad : asm.addr a) extra s,
  addr ad (set_clock (extra + clock s) s) = addr ad s.
Proof. intros [] extra s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "share_mem_op_add_clock_same" *)
Theorem share_mem_op_add_clock_same : forall m n ad s extra f l' r f2 r2,
   (clock s <> 0 /\ share_mem_op m n ad s = NONE ->
    share_mem_op m n ad (set_clock (extra + clock s) s) = NONE) /\
   (clock s <> 0 /\ share_mem_op m n ad s = SOME (FFI_return f l', r) ->
    share_mem_op m n ad (set_clock (extra + clock s) s) =
      SOME (FFI_return f l', set_clock (extra + clock r) r)) /\
   (clock s <> 0 /\ share_mem_op m n ad s = SOME (FFI_final f2, r2) ->
    share_mem_op m n ad (set_clock (extra + clock s) s) =
      SOME (FFI_final f2, set_clock (extra + clock r2) r2)).
Proof.
  intros; rewrite share_mem_op_set_clock; repeat split; intros [Hc H]; rewrite H; [reflexivity| |].
  - apply share_mem_op_clock in H. rewrite H. do 3 f_equal. lia.
  - apply share_mem_op_final in H. subst. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_add_clock_io_events_mono" *)
Theorem evaluate_add_clock_io_events_mono : forall extra s,
   is_true (isPREFIX (io_events (ffi (SND (evaluate s))))
     (io_events (ffi (SND (evaluate (set_clock (clock s + extra) s)))))).
Proof.
  intros extra s. destruct (evaluate s) as [res r] eqn:H.
  rewrite (evaluate_add_clock_gen s res r extra H). cbn [SND snd].
  destruct res; cbn [SND snd ffi set_clock]; try apply isPREFIX_refl.
  destruct (evaluate (set_clock extra r)) as [res' r'] eqn:H'.
  apply evaluate_io_events_mono in H'. exact H'.
Qed.

End Evaluate.

(** ** Aligned data-memory domain: [align_dm] *)

Local Lemma bool_decide_iff (P Q : Prop) {dP : Decision P} {dQ : Decision Q} :
  (P <-> Q) -> bool_decide P = bool_decide Q.
Proof. unfold bool_decide; destruct (decide P), (decide Q); tauto. Qed.

Section AlignHelpers.
Context {a : N}.
Local Open Scope word_scope.

Lemma byte_aligned_iff (w : word a) :
  good_dimindex a -> (is_true (byte_aligned w) <-> w2n w MOD (dimindex a DIV 8) = 0).
Proof.
  intros Hg; unfold byte_aligned; rewrite aligned_iff.
  destruct Hg as [H|H]; rewrite H; reflexivity.
Qed.

Lemma byte_align_IN_INTER (w : word a) (d : word a -> Prop) :
  (byte_align w IN (d INTER (fun w => byte_aligned w))) = (byte_align w IN d).
Proof.
  apply propositional_extensionality; rewrite IN_INTER; split; [tauto|].
  intros H; split; [exact H|]. apply aligned_align.
Qed.

Lemma aligned_IN_INTER (w : word a) (d : word a -> Prop) :
  good_dimindex a -> w2n w MOD (dimindex a DIV 8) = 0 ->
  (w IN (d INTER (fun w => byte_aligned w))) = (w IN d).
Proof.
  intros Hg Hw; apply propositional_extensionality; rewrite IN_INTER; split; [tauto|].
  intros H; split; [exact H|]. apply (byte_aligned_iff w Hg), Hw.
Qed.

Lemma aligned_cond_INTER (w : word a) (d : word a -> Prop)
    {d1 : Decision (w IN (d INTER (fun w => byte_aligned w)))} {d2 : Decision (w IN d)} :
  good_dimindex a ->
  andb (w2n w MOD (dimindex a DIV 8) =? 0) (@bool_decide _ d1) =
  andb (w2n w MOD (dimindex a DIV 8) =? 0) (@bool_decide _ d2).
Proof.
  intros Hg; destruct (N.eqb_spec (w2n w MOD (dimindex a DIV 8)) 0) as [Hw|Hw]; [|reflexivity].
  cbn [andb]; apply bool_decide_iff; rewrite (aligned_IN_INTER w d Hg Hw); reflexivity.
Qed.

Lemma mem_load_byte_aux_INTER m (d : word a -> Prop) be :
  mem_load_byte_aux m (d INTER (fun w => byte_aligned w)) be = mem_load_byte_aux m d be.
Proof.
  apply functional_extensionality; intros w; unfold mem_load_byte_aux.
  rewrite byte_align_IN_INTER; reflexivity.
Qed.

Lemma mem_store_byte_aux_INTER m (d : word a -> Prop) be :
  mem_store_byte_aux m (d INTER (fun w => byte_aligned w)) be = mem_store_byte_aux m d be.
Proof.
  apply functional_extensionality; intros w; unfold mem_store_byte_aux.
  rewrite byte_align_IN_INTER; reflexivity.
Qed.

Lemma mem_load_32_INTER m (d : word a -> Prop) be :
  mem_load_32 m (d INTER (fun w => byte_aligned w)) be = mem_load_32 m d be.
Proof.
  apply functional_extensionality; intros w; unfold mem_load_32.
  rewrite byte_align_IN_INTER; reflexivity.
Qed.

Lemma mem_store_32_INTER m (d : word a -> Prop) be :
  mem_store_32 m (d INTER (fun w => byte_aligned w)) be = mem_store_32 m d be.
Proof.
  apply functional_extensionality; intros w; unfold mem_store_32.
  rewrite byte_align_IN_INTER; reflexivity.
Qed.

Lemma write_bytearray_INTER x y m (d : word a -> Prop) be :
  write_bytearray x y m (d INTER (fun w => byte_aligned w)) be = write_bytearray x y m d be.
Proof.
  revert x; induction y as [|b y IH]; intros x; [reflexivity|].
  cbn [write_bytearray]; rewrite IH, mem_store_byte_aux_INTER; reflexivity.
Qed.

End AlignHelpers.

Section AlignDm.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : state a c ffi_t).
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_dm_def" *)
Definition align_dm (s : state a c ffi_t) : state a c ffi_t :=
  set_mem_domain (mem_domain s INTER (fun w => byte_aligned w)) s.

Ltac st_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg dec_clock inc_pc assert align_dm] in *.

Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E
  end.

Ltac unfold_ops :=
  unfold asm_inst, arith_upd, binop_upd, fp_upd, mem_op, mem_load, mem_store, mem_load32,
    mem_store32, mem_load_byte, mem_store_byte, addr, reg_imm, read_fp_reg in *.

Ltac comm_tac :=
  unfold_ops; st_cbn;
  repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_dm_const" *)
Theorem align_dm_const : forall s,
   clock (align_dm s) = clock s /\
   pc (align_dm s) = pc s /\
   code (align_dm s) = code s /\
   mem (align_dm s) = mem s /\
   shared_mem_domain (align_dm s) = shared_mem_domain s /\
   be (align_dm s) = be s /\
   len_reg (align_dm s) = len_reg s /\
   link_reg (align_dm s) = link_reg s /\
   ptr_reg (align_dm s) = ptr_reg s /\
   ptr2_reg (align_dm s) = ptr2_reg s /\
   len2_reg (align_dm s) = len2_reg s /\
   io_regs (align_dm s) = io_regs s /\
   io_fp_regs (align_dm s) = io_fp_regs s /\
   code_buffer (align_dm s) = code_buffer s /\
   compile (align_dm s) = compile s /\
   compile_oracle (align_dm s) = compile_oracle s /\
   ffi (align_dm s) = ffi s /\
   failed (align_dm s) = failed s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_dm_with_clock" *)
Theorem align_dm_with_clock : forall s k,
  align_dm (set_clock k s) = set_clock k (align_dm s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_fetch_align_dm" *)
Theorem asm_fetch_align_dm : forall s, asm_fetch (align_dm s) = asm_fetch s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_reg_align_dm" *)
Theorem read_reg_align_dm : forall n s, read_reg n (align_dm s) = read_reg n s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_reg_align_dm" *)
Theorem upd_reg_align_dm : forall x y s, upd_reg x y (align_dm s) = align_dm (upd_reg x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_mem_align_dm" *)
Theorem upd_mem_align_dm : forall x y s, upd_mem x y (align_dm s) = align_dm (upd_mem x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "binop_upd_align_dm" *)
Theorem binop_upd_align_dm : forall x y z w s,
  binop_upd x y z w (align_dm s) = align_dm (binop_upd x y z w s).
Proof. intros x [] z w s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "reg_imm_align_dm" *)
Theorem reg_imm_align_dm : forall r s, reg_imm r (align_dm s) = reg_imm r s.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "assert_align_dm" *)
Theorem assert_align_dm : forall b s, assert b (align_dm s) = align_dm (assert b s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "arith_upd_align_dm" *)
Theorem arith_upd_align_dm : forall x s, arith_upd x (align_dm s) = align_dm (arith_upd x s).
Proof. intros [] []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "fp_upd_align_dm" *)
Theorem fp_upd_align_dm : forall f s, fp_upd f (align_dm s) = align_dm (fp_upd f s).
Proof. intros [] []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "addr_align_dm" *)
Theorem addr_align_dm : forall ad s, addr ad (align_dm s) = addr ad s.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_align_dm" *)
Theorem mem_load_align_dm : forall n (ad : asm.addr a) s,
  good_dimindex a -> mem_load n ad (align_dm s) = align_dm (mem_load n ad s).
Proof.
  intros n ad s Hg; unfold mem_load; rewrite addr_align_dm.
  destruct (addr ad s); [|reflexivity]. st_cbn. rewrite (aligned_cond_INTER _ _ Hg). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_32_align_dm" *)
Theorem mem_load_32_align_dm : forall s be x y,
  mem_load_32 (mem s) (mem_domain s) be x = SOME y ->
  mem_load_32 (mem s) (mem_domain (align_dm s)) be x = SOME y.
Proof. intros; st_cbn; rewrite mem_load_32_INTER; assumption. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load32_align_dm" *)
Theorem mem_load32_align_dm : forall n (ad : asm.addr a) s,
  good_dimindex a -> mem_load32 n ad (align_dm s) = align_dm (mem_load32 n ad s).
Proof.
  intros n ad s Hg; unfold mem_load32; rewrite addr_align_dm.
  destruct (addr ad s); [|reflexivity]. st_cbn. rewrite mem_load_32_INTER.
  destruct (mem_load_32 _ _ _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_byte_aux_align_dm" *)
Theorem mem_load_byte_aux_align_dm : forall s be x y,
  mem_load_byte_aux (mem s) (mem_domain s) be x = SOME y ->
  mem_load_byte_aux (mem s) (mem_domain (align_dm s)) be x = SOME y.
Proof. intros; st_cbn; rewrite mem_load_byte_aux_INTER; assumption. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_byte_align_dm" *)
Theorem mem_load_byte_align_dm : forall n (ad : asm.addr a) s,
  good_dimindex a -> mem_load_byte n ad (align_dm s) = align_dm (mem_load_byte n ad s).
Proof.
  intros n ad s Hg; unfold mem_load_byte; rewrite addr_align_dm.
  destruct (addr ad s); [|reflexivity]. st_cbn. rewrite mem_load_byte_aux_INTER.
  destruct (mem_load_byte_aux _ _ _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_align_dm" *)
Theorem mem_store_align_dm : forall n (ad : asm.addr a) s,
  good_dimindex a -> mem_store n ad (align_dm s) = align_dm (mem_store n ad s).
Proof.
  intros n ad s Hg; unfold mem_store; rewrite addr_align_dm.
  destruct (addr ad s); [|reflexivity]. st_cbn. rewrite (aligned_cond_INTER _ _ Hg). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_32_align_dm" *)
Theorem mem_store_32_align_dm : forall m s be x c0 y,
  mem_store_32 m (mem_domain s) be x c0 = SOME y ->
  mem_store_32 m (mem_domain (align_dm s)) be x c0 = SOME y.
Proof. intros; st_cbn; rewrite mem_store_32_INTER; assumption. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store32_align_dm" *)
Theorem mem_store32_align_dm : forall n (ad : asm.addr a) s,
  good_dimindex a -> mem_store32 n ad (align_dm s) = align_dm (mem_store32 n ad s).
Proof.
  intros n ad s Hg; unfold mem_store32; rewrite addr_align_dm.
  destruct (addr ad s); [|reflexivity]. st_cbn. rewrite mem_store_32_INTER.
  destruct (regs s n); [|reflexivity]. destruct (mem_store_32 _ _ _ _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_byte_aux_align_dm" *)
Theorem mem_store_byte_aux_align_dm : forall m s be x c0 y,
  mem_store_byte_aux m (mem_domain s) be x c0 = SOME y ->
  mem_store_byte_aux m (mem_domain (align_dm s)) be x c0 = SOME y.
Proof. intros; st_cbn; rewrite mem_store_byte_aux_INTER; assumption. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_byte_align_dm" *)
Theorem mem_store_byte_align_dm : forall n (ad : asm.addr a) s,
  good_dimindex a -> mem_store_byte n ad (align_dm s) = align_dm (mem_store_byte n ad s).
Proof.
  intros n ad s Hg; unfold mem_store_byte; rewrite addr_align_dm.
  destruct (addr ad s); [|reflexivity]. st_cbn. rewrite mem_store_byte_aux_INTER.
  destruct (regs s n); [|reflexivity]. destruct (mem_store_byte_aux _ _ _ _ _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_op_align_dm" *)
Theorem mem_op_align_dm : forall m n (ad : asm.addr a) s,
  good_dimindex a -> mem_op m n ad (align_dm s) = align_dm (mem_op m n ad s).
Proof.
  intros [] n ad s Hg; cbn [mem_op];
    auto using mem_load_align_dm, mem_load32_align_dm, mem_load_byte_align_dm,
      mem_store_align_dm, mem_store32_align_dm, mem_store_byte_align_dm.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_inst_align_dm" *)
Theorem asm_inst_align_dm : forall (i : asm.inst a) s,
  good_dimindex a -> asm_inst i (align_dm s) = align_dm (asm_inst i s).
Proof.
  intros [] s Hg; cbn [asm_inst];
    auto using mem_op_align_dm, arith_upd_align_dm, fp_upd_align_dm.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "dec_clock_align_dm" *)
Theorem dec_clock_align_dm : forall s, dec_clock (align_dm s) = align_dm (dec_clock s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "inc_pc_align_dm" *)
Theorem inc_pc_align_dm : forall s, inc_pc (align_dm s) = align_dm (inc_pc s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_pc_align_dm" *)
Theorem upd_pc_align_dm : forall p s, upd_pc p (align_dm s) = align_dm (upd_pc p s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_pc_value_align_dm" *)
Theorem get_pc_value_align_dm : forall x s, get_pc_value x (align_dm s) = get_pc_value x s.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_ret_Loc_align_dm" *)
Theorem get_ret_Loc_align_dm : forall s, get_ret_Loc (align_dm s) = get_ret_Loc s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_bytearray_mem_load_byte_aux_align_dm" *)
Theorem read_bytearray_mem_load_byte_aux_align_dm : forall s y x,
  read_bytearray x y (mem_load_byte_aux (mem s) (mem_domain (align_dm s)) (be s)) =
  read_bytearray x y (mem_load_byte_aux (mem s) (mem_domain s) (be s)).
Proof. intros; st_cbn; rewrite mem_load_byte_aux_INTER; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "write_bytearray_align_dm" *)
Theorem write_bytearray_align_dm : forall s y x,
  write_bytearray x y (mem s) (mem_domain (align_dm s)) (be s) =
  write_bytearray x y (mem s) (mem_domain s) (be s).
Proof. intros; st_cbn; apply write_bytearray_INTER. Qed.

(** [share_mem_op] does not read [mem_domain] (Galette helper). *)
Lemma share_mem_op_align_dm_eq m r ad s :
  share_mem_op m r ad (align_dm s) =
  match share_mem_op m r ad s with
  | SOME (res, s') => SOME (res, align_dm s')
  | NONE => NONE
  end.
Proof.
  destruct s; destruct m; cbn [share_mem_op]; unfold share_mem_load, share_mem_store, addr;
    st_cbn; repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "share_mem_op_align_dm_simp" *)
Theorem share_mem_op_align_dm_simp : forall m r ad s f s' fs l,
  (share_mem_op m r ad s = NONE -> share_mem_op m r ad (align_dm s) = NONE) /\
  (share_mem_op m r ad s = SOME (FFI_final f, s') ->
   share_mem_op m r ad (align_dm s) = SOME (FFI_final f, align_dm s')) /\
  (share_mem_op m r ad s = SOME (FFI_return fs l, s') ->
   share_mem_op m r ad (align_dm s) = SOME (FFI_return fs l, align_dm s')).
Proof. intros; rewrite share_mem_op_align_dm_eq; repeat split; intros H; rewrite H; reflexivity. Qed.

End AlignDm.

Section AlignSem.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : state a c ffi_t).

(** Two states whose clocked runs agree up to a final-state map that keeps
    the ffi state have the same semantics (Galette helper). *)
Lemma semantics_eq_transform (s1 s2 : state a c ffi_t) (G : state a c ffi_t -> state a c ffi_t) :
  (forall k, evaluate (set_clock k s1) =
             let (r, t) := evaluate (set_clock k s2) in (r, G t)) ->
  (forall t, ffi (G t) = ffi t) ->
  semantics s1 = semantics s2.
Proof.
  intros H HG. unfold semantics.
  assert (E1 : (exists k, FST (evaluate (set_clock k s1)) = Error) =
               (exists k, FST (evaluate (set_clock k s2)) = Error)).
  { apply propositional_extensionality; split; intros [k Hk]; exists k;
      rewrite H in *; destruct (evaluate (set_clock k s2)); exact Hk. }
  rewrite E1.
  assert (E2 : (fun res => exists k t outcome,
                  evaluate (set_clock k s1) = (Halt outcome, t) /\
                  res = Terminate outcome (io_events (ffi t))) =
               (fun res => exists k t outcome,
                  evaluate (set_clock k s2) = (Halt outcome, t) /\
                  res = Terminate outcome (io_events (ffi t)))).
  { apply functional_extensionality; intros res; apply propositional_extensionality.
    split; intros (k & t & o & Hk & ->).
    - rewrite H in Hk. destruct (evaluate (set_clock k s2)) as [r t'] eqn:Ev.
      injection Hk as -> <-. exists k, t', o. rewrite HG. split; [exact Ev|reflexivity].
    - exists k, (G t), o. rewrite H, Hk, HG. split; reflexivity. }
  rewrite E2.
  assert (E3 : (fun k => fromList (io_events (ffi (SND (evaluate (set_clock k s1)))))) =
               (fun k => fromList (io_events (ffi (SND (evaluate (set_clock k s2))))))).
  { apply functional_extensionality; intros k. rewrite H.
    destruct (evaluate (set_clock k s2)); cbn [SND snd]; rewrite HG; reflexivity. }
  rewrite E3. reflexivity.
Qed.

Lemma implements_eq (s1 s2 : state a c ffi_t) :
  semantics s2 = semantics s1 ->
  implements' true ((semantics s1) INSERT {}) ((semantics s2) INSERT {}).
Proof.
  intros E _. rewrite E. unfold extend_with_resource_limit'. intros x Hx; exact Hx.
Qed.

Ltac st_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg dec_clock inc_pc assert align_dm] in *.

Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | context [match _ with _ => _ end] => fail
      | _ => let E := fresh "E" in destruct x eqn:E
      end
  end.

Ltac clock_lt :=
  repeat match goal with
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         | H : share_mem_op _ _ _ _ = SOME (FFI_return _ _, _) |- _ =>
             apply share_mem_op_clock in H
         end;
  st_cbn; rewrite ?asm_inst_clock; lia.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_align_dm" *)
Theorem evaluate_align_dm : good_dimindex a ->
  forall s : state a c ffi_t,
    evaluate (align_dm s) = let (r, s') := evaluate s in (r, align_dm s').
Proof.
  intros Hg s; induction s as [s IH] using evaluate_clock_ind.
  rewrite (evaluate_def (align_dm s)), (evaluate_def s).
  unfold asm_fetch, get_pc_value, get_ret_Loc in *; st_cbn.
  repeat (split_goal; cbn beta iota zeta; st_cbn;
          rewrite ?(asm_inst_align_dm _ _ Hg), ?reg_imm_align_dm, ?share_mem_op_align_dm_eq,
            ?mem_load_byte_aux_INTER, ?write_bytearray_INTER; st_cbn).
  all: try reflexivity.
  all: match goal with
       | |- evaluate ?X = let (r, s') := evaluate ?Y in _ =>
           replace X with (align_dm Y) by (apply state_eq_intro; st_cbn; reflexivity);
           apply IH; clock_lt
       end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "implements_align_dm" *)
Theorem implements_align_dm : good_dimindex a -> forall s : state a c ffi_t,
  implements' true ((semantics s) INSERT {}) ((semantics (align_dm s)) INSERT {}).
Proof.
  intros Hg s. apply implements_eq.
  apply (semantics_eq_transform _ _ align_dm); [|reflexivity].
  intros k. rewrite <- align_dm_with_clock. apply evaluate_align_dm, Hg.
Qed.

End AlignSem.

(** ** Aligned shared-memory domain: [align_sdm] *)

Section AlignSdm.
Context {a : N} {c ffi_t : Type}.
Implicit Types (s : state a c ffi_t).
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_def" *)
Definition align_sdm (s : state a c ffi_t) : state a c ffi_t :=
  set_shared_mem_domain (shared_mem_domain s INTER (fun w => byte_aligned w)) s.

Ltac st_cbn :=
  cbn [regs fp_regs mem mem_domain shared_mem_domain pc be ffi io_regs cc_regs io_fp_regs
       cc_fp_regs code compile compile_oracle code_buffer clock failed ptr_reg len_reg
       ptr2_reg len2_reg link_reg
       set_regs set_fp_regs set_mem set_mem_domain set_shared_mem_domain set_pc set_be
       set_ffi set_io_regs set_cc_regs set_io_fp_regs set_cc_fp_regs set_code set_compile
       set_compile_oracle set_code_buffer set_clock set_failed set_ptr_reg set_len_reg
       set_ptr2_reg set_len2_reg set_link_reg
       upd_pc upd_reg upd_mem upd_fp_reg dec_clock inc_pc assert align_sdm] in *.

Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | evaluate _ => fail
      | context [match _ with _ => _ end] => fail
      | _ => let E := fresh "E" in destruct x eqn:E
      end
  end.

Ltac unfold_ops :=
  unfold asm_inst, arith_upd, binop_upd, fp_upd, mem_op, mem_load, mem_store, mem_load32,
    mem_store32, mem_load_byte, mem_store_byte, addr, reg_imm, read_fp_reg in *.

Ltac comm_tac :=
  unfold_ops; st_cbn;
  repeat (split_goal; cbn beta iota zeta; st_cbn); reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_const" *)
Theorem align_sdm_const : forall s,
   clock (align_sdm s) = clock s /\
   pc (align_sdm s) = pc s /\
   code (align_sdm s) = code s /\
   mem (align_sdm s) = mem s /\
   mem_domain (align_sdm s) = mem_domain s /\
   be (align_sdm s) = be s /\
   len_reg (align_sdm s) = len_reg s /\
   link_reg (align_sdm s) = link_reg s /\
   ptr_reg (align_sdm s) = ptr_reg s /\
   ptr2_reg (align_sdm s) = ptr2_reg s /\
   len2_reg (align_sdm s) = len2_reg s /\
   io_regs (align_sdm s) = io_regs s /\
   io_fp_regs (align_sdm s) = io_fp_regs s /\
   code_buffer (align_sdm s) = code_buffer s /\
   compile (align_sdm s) = compile s /\
   compile_oracle (align_sdm s) = compile_oracle s /\
   ffi (align_sdm s) = ffi s /\
   failed (align_sdm s) = failed s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_with_clock" *)
Theorem align_sdm_with_clock : forall s k,
  align_sdm (set_clock k s) = set_clock k (align_sdm s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_fetch_align_sdm" *)
Theorem asm_fetch_align_sdm : forall s, asm_fetch (align_sdm s) = asm_fetch s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_reg_align_sdm" *)
Theorem read_reg_align_sdm : forall n s, read_reg n (align_sdm s) = read_reg n s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_reg_align_sdm" *)
Theorem upd_reg_align_sdm : forall x y s, upd_reg x y (align_sdm s) = align_sdm (upd_reg x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_mem_align_sdm" *)
Theorem upd_mem_align_sdm : forall x y s, upd_mem x y (align_sdm s) = align_sdm (upd_mem x y s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "binop_upd_align_sdm" *)
Theorem binop_upd_align_sdm : forall x y z w s,
  binop_upd x y z w (align_sdm s) = align_sdm (binop_upd x y z w s).
Proof. intros x [] z w s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "reg_imm_align_sdm" *)
Theorem reg_imm_align_sdm : forall r s, reg_imm r (align_sdm s) = reg_imm r s.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "assert_align_sdm" *)
Theorem assert_align_sdm : forall b s, assert b (align_sdm s) = align_sdm (assert b s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "arith_upd_align_sdm" *)
Theorem arith_upd_align_sdm : forall x s, arith_upd x (align_sdm s) = align_sdm (arith_upd x s).
Proof. intros [] []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "fp_upd_align_sdm" *)
Theorem fp_upd_align_sdm : forall f s, fp_upd f (align_sdm s) = align_sdm (fp_upd f s).
Proof. intros [] []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "addr_align_sdm" *)
Theorem addr_align_sdm : forall ad s, addr ad (align_sdm s) = addr ad s.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_align_sdm" *)
Theorem mem_load_align_sdm : forall n (ad : asm.addr a) s,
  mem_load n ad (align_sdm s) = align_sdm (mem_load n ad s).
Proof. intros n ad []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load32_align_sdm" *)
Theorem mem_load32_align_sdm : forall n (ad : asm.addr a) s,
  mem_load32 n ad (align_sdm s) = align_sdm (mem_load32 n ad s).
Proof. intros n ad []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_byte_align_sdm" *)
Theorem mem_load_byte_align_sdm : forall n (ad : asm.addr a) s,
  mem_load_byte n ad (align_sdm s) = align_sdm (mem_load_byte n ad s).
Proof. intros n ad []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_align_sdm" *)
Theorem mem_store_align_sdm : forall n (ad : asm.addr a) s,
  mem_store n ad (align_sdm s) = align_sdm (mem_store n ad s).
Proof. intros n ad []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store32_align_sdm" *)
Theorem mem_store32_align_sdm : forall n (ad : asm.addr a) s,
  mem_store32 n ad (align_sdm s) = align_sdm (mem_store32 n ad s).
Proof. intros n ad []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_byte_align_sdm" *)
Theorem mem_store_byte_align_sdm : forall n (ad : asm.addr a) s,
  mem_store_byte n ad (align_sdm s) = align_sdm (mem_store_byte n ad s).
Proof. intros n ad []; comm_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_op_align_sdm" *)
Theorem mem_op_align_sdm : forall m n (ad : asm.addr a) s,
  mem_op m n ad (align_sdm s) = align_sdm (mem_op m n ad s).
Proof.
  intros [] n ad s; cbn [mem_op];
    auto using mem_load_align_sdm, mem_load32_align_sdm, mem_load_byte_align_sdm,
      mem_store_align_sdm, mem_store32_align_sdm, mem_store_byte_align_sdm.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_inst_align_sdm" *)
Theorem asm_inst_align_sdm : forall (i : asm.inst a) s,
  asm_inst i (align_sdm s) = align_sdm (asm_inst i s).
Proof.
  intros [] s; cbn [asm_inst];
    auto using mem_op_align_sdm, arith_upd_align_sdm, fp_upd_align_sdm.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "dec_clock_align_sdm" *)
Theorem dec_clock_align_sdm : forall s, dec_clock (align_sdm s) = align_sdm (dec_clock s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "inc_pc_align_sdm" *)
Theorem inc_pc_align_sdm : forall s, inc_pc (align_sdm s) = align_sdm (inc_pc s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_pc_align_sdm" *)
Theorem upd_pc_align_sdm : forall p s, upd_pc p (align_sdm s) = align_sdm (upd_pc p s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_pc_value_align_sdm" *)
Theorem get_pc_value_align_sdm : forall x s, get_pc_value x (align_sdm s) = get_pc_value x s.
Proof. intros [] s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_ret_Loc_align_sdm" *)
Theorem get_ret_Loc_align_sdm : forall s, get_ret_Loc (align_sdm s) = get_ret_Loc s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_bytearray_mem_load_byte_aux_align_sdm" *)
Theorem read_bytearray_mem_load_byte_aux_align_sdm : forall s y x,
  read_bytearray x y (mem_load_byte_aux (mem s) (mem_domain (align_sdm s)) (be s)) =
  read_bytearray x y (mem_load_byte_aux (mem s) (mem_domain s) (be s)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "write_bytearray_align_sdm" *)
Theorem write_bytearray_align_sdm : forall s y x,
  write_bytearray x y (mem s) (mem_domain (align_sdm s)) (be s) =
  write_bytearray x y (mem s) (mem_domain s) (be s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_aligned" *)
Theorem align_sdm_aligned : forall (x : word a) s,
  good_dimindex a ->
  ((x IN shared_mem_domain s /\ w2n x MOD (dimindex a DIV 8) = 0) <->
    x IN shared_mem_domain (align_sdm s)).
Proof.
  intros x s Hg; st_cbn; rewrite IN_INTER; pose proof (byte_aligned_iff x Hg) as B.
  split; intros [H1 H2]; split; try exact H1; [apply B; exact H2|apply B; exact H2].
Qed.

Lemma share_mem_load_align_sdm_eq r (ad : asm.addr a) s n :
  good_dimindex a ->
  share_mem_load r ad (align_sdm s) n =
  match share_mem_load r ad s n with
  | SOME (res, s') => SOME (res, align_sdm s')
  | NONE => NONE
  end.
Proof.
  intros Hg; destruct s; unfold share_mem_load, addr; st_cbn;
    repeat (split_goal; cbn beta iota zeta; st_cbn;
            rewrite ?(aligned_cond_INTER _ _ Hg), ?byte_align_IN_INTER);
    reflexivity.
Qed.

Lemma share_mem_store_align_sdm_eq r (ad : asm.addr a) s n :
  good_dimindex a ->
  share_mem_store r ad (align_sdm s) n =
  match share_mem_store r ad s n with
  | SOME (res, s') => SOME (res, align_sdm s')
  | NONE => NONE
  end.
Proof.
  intros Hg; destruct s; unfold share_mem_store, addr; st_cbn;
    repeat (split_goal; cbn beta iota zeta; st_cbn;
            rewrite ?(aligned_cond_INTER _ _ Hg), ?byte_align_IN_INTER);
    reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "share_mem_load_align_sdm" *)
Theorem share_mem_load_align_sdm : forall r (ad : asm.addr a) s n res s',
  good_dimindex a ->
  (share_mem_load r ad (align_sdm s) n = NONE <-> share_mem_load r ad s n = NONE) /\
  (share_mem_load r ad s n = SOME (res, s') ->
   share_mem_load r ad (align_sdm s) n = SOME (res, align_sdm s')).
Proof.
  intros r ad s n res s' Hg; rewrite (share_mem_load_align_sdm_eq _ _ _ _ Hg).
  split; [destruct (share_mem_load r ad s n) as [[]|]; split; congruence|].
  intros H; rewrite H; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "share_mem_store_align_sdm" *)
Theorem share_mem_store_align_sdm : forall r (ad : asm.addr a) s n res s',
  good_dimindex a ->
  (share_mem_store r ad (align_sdm s) n = NONE <-> share_mem_store r ad s n = NONE) /\
  (share_mem_store r ad s n = SOME (res, s') ->
   share_mem_store r ad (align_sdm s) n = SOME (res, align_sdm s')).
Proof.
  intros r ad s n res s' Hg; rewrite (share_mem_store_align_sdm_eq _ _ _ _ Hg).
  split; [destruct (share_mem_store r ad s n) as [[]|]; split; congruence|].
  intros H; rewrite H; reflexivity.
Qed.

Lemma share_mem_op_align_sdm_eq m r (ad : asm.addr a) s :
  good_dimindex a ->
  share_mem_op m r ad (align_sdm s) =
  match share_mem_op m r ad s with
  | SOME (res, s') => SOME (res, align_sdm s')
  | NONE => NONE
  end.
Proof.
  intros Hg; destruct m; cbn [share_mem_op];
    first [apply share_mem_load_align_sdm_eq | apply share_mem_store_align_sdm_eq]; exact Hg.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "share_mem_op_align_sdm_simp" *)
Theorem share_mem_op_align_sdm_simp : forall m r (ad : asm.addr a) s res s',
  good_dimindex a ->
  (share_mem_op m r ad s = NONE <-> share_mem_op m r ad (align_sdm s) = NONE) /\
  (share_mem_op m r ad s = SOME (res, s') ->
   share_mem_op m r ad (align_sdm s) = SOME (res, align_sdm s')).
Proof.
  intros m r ad s res s' Hg; rewrite (share_mem_op_align_sdm_eq _ _ _ _ Hg).
  split; [destruct (share_mem_op m r ad s) as [[]|]; split; congruence|].
  intros H; rewrite H; reflexivity.
Qed.

Ltac clock_lt :=
  repeat match goal with
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         | H : share_mem_op _ _ _ _ = SOME (FFI_return _ _, _) |- _ =>
             apply share_mem_op_clock in H
         end;
  st_cbn; rewrite ?asm_inst_clock; lia.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_align_sdm" *)
Theorem evaluate_align_sdm : good_dimindex a ->
  forall s : state a c ffi_t,
    evaluate (align_sdm s) = let (r, s') := evaluate s in (r, align_sdm s').
Proof.
  intros Hg s; induction s as [s IH] using evaluate_clock_ind.
  rewrite (evaluate_def (align_sdm s)), (evaluate_def s).
  unfold asm_fetch, get_pc_value, get_ret_Loc in *; st_cbn.
  repeat (split_goal; cbn beta iota zeta; st_cbn;
          rewrite ?asm_inst_align_sdm, ?reg_imm_align_sdm,
            ?(share_mem_op_align_sdm_eq _ _ _ _ Hg); st_cbn).
  all: try reflexivity.
  all: match goal with
       | |- evaluate ?X = let (r, s') := evaluate ?Y in _ =>
           replace X with (align_sdm Y) by (apply state_eq_intro; st_cbn; reflexivity);
           apply IH; clock_lt
       end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "implements_align_sdm" *)
Theorem implements_align_sdm : good_dimindex a -> forall s : state a c ffi_t,
  implements' true ((semantics s) INSERT {}) ((semantics (align_sdm s)) INSERT {}).
Proof.
  intros Hg s. apply implements_eq.
  apply (semantics_eq_transform _ _ align_sdm); [|reflexivity].
  intros k. rewrite <- align_sdm_with_clock. apply evaluate_align_sdm, Hg.
Qed.

End AlignSdm.

(** ** Invariants of the input of [lab_to_target] *)

Section Ok.
Context {a : N}.

(** asm_ok checks coming into lab_to_target *)
(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_ok_pre_def" *)
Definition line_ok_pre (c : asm_config a) (l : line a) : bool :=
  match l with
  | Asm b bytes l0 => asm_ok (cbw_to_asm b) c
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_ok_pre_def" *)
Definition sec_ok_pre (c : asm_config a) (s : sec a) : bool :=
  match s with
  | Section_ k ls => EVERY (line_ok_pre c) ls
  end.

(** invariant: labels have correct section number and are non-zero *)
(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_label_ok_def" *)
Definition sec_label_ok (k : N) (l : line a) : bool :=
  match l with
  | Label l1 l2 len => (l1 =? k) && negb (l2 =? 0)
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_labels_ok_def" *)
Definition sec_labels_ok (s : sec a) : bool :=
  match s with
  | Section_ k ls => EVERY (sec_label_ok k) ls
  end.

Lemma In_extract_labels n1 n2 (lines : list (line a)) :
  In (n1, n2) (extract_labels lines) <-> exists k, In (Label n1 n2 k) lines.
Proof.
  induction lines as [|l lines IH]; cbn; [split; [tauto|intros [k []]]|].
  destruct l; cbn; rewrite IH; split.
  - intros [E|[k Hk]]; [injection E as -> ->; eauto|eauto].
  - intros [k [E|Hk]]; [injection E as -> -> ->; auto|eauto].
  - intros [k Hk]; eauto.
  - intros [k [E|Hk]]; [discriminate|eauto].
  - intros [k Hk]; eauto.
  - intros [k [E|Hk]]; [discriminate|eauto].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "sec_label_ok_extract_labels" *)
Theorem sec_label_ok_extract_labels : forall n1 lines n1' n2,
   is_true (EVERY (sec_label_ok n1) lines) /\
   is_true (MEM (n1', n2) (extract_labels lines)) ->
   n1' = n1 /\ n2 <> 0.
Proof.
  intros n1 lines n1' n2 [H1 H2].
  apply MEM_In, In_extract_labels in H2. destruct H2 as [k Hk].
  apply EVERY_Forall in H1; rewrite List.Forall_forall in H1. specialize (H1 _ Hk). cbn in H1.
  apply Bool.andb_true_iff in H1. destruct H1 as [H1 H1'].
  apply N.eqb_eq in H1. apply Bool.negb_true_iff, N.eqb_neq in H1'. auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "EVERY_sec_label_ok" *)
Theorem EVERY_sec_label_ok : forall n l,
   is_true (EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0)) (extract_labels l)) <->
   is_true (EVERY (sec_label_ok n) l).
Proof. intros n l; induction l as [|[] l IH]; cbn; [tauto| |tauto|tauto].
  unfold is_true in *; rewrite !Bool.andb_true_iff, IH; tauto.
Qed.

Lemma IN_BIGUNION_IMAGE_set {A B} (f : A -> B -> Prop) l x :
  x IN BIGUNION (IMAGE f (set l)) <-> exists y, In y l /\ x IN f y.
Proof.
  rewrite IN_BIGUNION; split.
  - intros (t & Ht & Hs). apply IN_IMAGE in Hs. destruct Hs as (y & -> & Hy).
    apply IN_set in Hy. eauto.
  - intros (y & Hy & Hx). exists (f y). split; [exact Hx|].
    apply IN_IMAGE. exists y. split; [reflexivity|apply IN_set, Hy].
Qed.

Lemma IN_IMAGE_set {A B} (f : A -> B) l x :
  x IN IMAGE f (set l) <-> exists y, x = f y /\ In y l.
Proof.
  rewrite IN_IMAGE; split; intros (y & -> & Hy); exists y; split; auto; apply IN_set; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "line_get_code_labels_extract_labels" *)
Theorem line_get_code_labels_extract_labels : forall l : list (line a),
   BIGUNION (IMAGE line_get_code_labels (set l)) =
   IMAGE SND (set (extract_labels l)).
Proof.
  intros l; apply EXTENSION; intros x.
  rewrite IN_BIGUNION_IMAGE_set, IN_IMAGE_set. split.
  - intros (y & Hy & Hx). destruct y as [l1 l2 k| |]; cbn in Hx;
      [|exfalso; exact Hx|exfalso; exact Hx].
    apply IN_SING in Hx; subst l2. exists (l1, x). split; [reflexivity|].
    apply In_extract_labels. eauto.
  - intros ([l1 l2] & -> & Hy). apply In_extract_labels in Hy. destruct Hy as [k Hk].
    exists (Label l1 l2 k). split; [exact Hk|]. cbn. apply IN_SING. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_code_labels_extract_labels" *)
Theorem get_code_labels_extract_labels : forall code : list (sec a),
   is_true (EVERY sec_labels_ok code) ->
   get_code_labels code =
   IMAGE (fun s => (Section_num s, 0)) (set code) UNION
   set (FLAT (MAP (fun s => extract_labels (Section_lines s)) code)).
Proof.
  intros code Hok; apply EXTENSION; intros [n1 n2].
  apply EVERY_Forall in Hok; rewrite List.Forall_forall in Hok.
  unfold get_code_labels. rewrite IN_BIGUNION_IMAGE_set, IN_UNION, IN_IMAGE_set, IN_set.
  rewrite in_concat. split.
  - intros ([k lines] & Hs & Hx). cbn in Hx. apply IN_INSERT in Hx.
    destruct Hx as [E|Hx]; [left; exists (Section_ k lines); split; [exact E|exact Hs]|].
    right. apply IN_IMAGE in Hx. destruct Hx as (n2' & E & Hx). injection E as -> ->.
    apply IN_BIGUNION_IMAGE_set in Hx. destruct Hx as (y & Hy & Hx).
    destruct y as [l1 l2 kk| |]; cbn in Hx; [|exfalso; exact Hx|exfalso; exact Hx].
    apply IN_SING in Hx; subst.
    exists (extract_labels lines). split; [apply in_map_iff; exists (Section_ k lines); auto|].
    specialize (Hok _ Hs). cbn in Hok. apply EVERY_Forall in Hok; rewrite List.Forall_forall in Hok.
    specialize (Hok _ Hy). cbn in Hok. apply Bool.andb_true_iff in Hok.
    destruct Hok as [Hk _]. apply N.eqb_eq in Hk; subst.
    apply In_extract_labels; eauto.
  - intros [(s & E & Hs)|(ls & Hls & Hx)].
    + exists s. split; [exact Hs|]. destruct s as [k lines]. cbn in E |- *.
      apply IN_INSERT. left; exact E.
    + apply in_map_iff in Hls. destruct Hls as ([k lines] & <- & Hs). cbn in Hx.
      exists (Section_ k lines). split; [exact Hs|]. cbn. apply IN_INSERT. right.
      apply In_extract_labels in Hx. destruct Hx as [kk Hkk].
      specialize (Hok _ Hs). cbn in Hok. apply EVERY_Forall in Hok; rewrite List.Forall_forall in Hok.
      specialize (Hok _ Hkk). cbn in Hok. apply Bool.andb_true_iff in Hok.
      destruct Hok as [Hk _]. apply N.eqb_eq in Hk; subst k.
      apply IN_IMAGE. exists n2. split; [reflexivity|].
      apply IN_BIGUNION_IMAGE_set. exists (Label n1 n2 kk). split; [exact Hkk|].
      cbn. apply IN_SING. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "no_install_def" *)
Definition no_install (code : list (sec a)) : Prop :=
  forall p w bytes l,
    asm_fetch_aux p code <> SOME (LabAsm Install w bytes l).

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "no_share_mem_inst_def" *)
Definition no_share_mem_inst (code : list (sec a)) : Prop :=
  forall p op re a0 inst len,
    asm_fetch_aux p code <> SOME (Asm (ShareMem op re a0) inst len).

End Ok.

(*! HOL "cakeml/compiler/backend/semantics/labPropsScript.sml" "all_enc_ok_pre" *)
Abbreviation all_enc_ok_pre c ls := (EVERY (sec_ok_pre c) ls).
