(** * CakeML [stack_rawcallProof]: correctness of [stack_rawcall]

    Port of [cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml].

    Notes:
    - HOL's local overloads [comp] and [compile] are [stack_rawcall]'s;
      the state field [compile] is written [stackSem.compile].
    - HOL's [s with f := v] is [set_f v s] ([stackSem]).
    - [state_rel_thm] is HOL's [state_rel_def] simplified with
      [state_component_equality]: the record equation [t = s with code := c]
      becomes the field equations (in the record's field order), and the
      existential [c] is eliminated by [t.code].
    - HOL's [comp_ind] (recursion induction for [stack_rawcall$comp]) is not
      ported; proofs use induction on a program size ([psz], Galette-only).

    Proof method of [comp_correct]: well-founded induction on [eval_lt]
    ([stackSem]); the Galette-only helpers below (commutation of the
    semantic primitives with [set_code], the code-independent cases) have
    no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.finite_maps Require sptree.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend Require Import stack_rawcall.
Import wordLang (word_loc, Word, Loc).
Import sptree (spt, LN, lookup, domain, fromAList, toAList, insert, union, subspt).
Open Scope N_scope.

(** ** Program size (Galette-only) *)

Section Size.
Context {a : N}.

Fixpoint psz (p : prog a) : nat :=
  match p with
  | Seq p1 p2 => Datatypes.S (psz p1 + psz p2)
  | If _ _ _ p1 p2 => Datatypes.S (psz p1 + psz p2)
  | Loop p1 => Datatypes.S (psz p1)
  | Call ret _ h =>
      Datatypes.S (match ret with SOME (p1, _) => psz p1 | NONE => 0 end +
                   match h with SOME (p2, _) => psz p2 | NONE => 0 end)
  | _ => 1
  end.

Lemma psz_ind (P : prog a -> Prop) :
  (forall p, (forall q, (psz q < psz p)%nat -> P q) -> P p) -> forall p, P p.
Proof.
  intros H p. induction p as [p IH] using (Wf_nat.induction_ltof1 _ psz).
  apply H; intros q Hq; apply IH; exact Hq.
Qed.

End Size.

Section Defs.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_ok_def" *)
Definition state_ok (i : spt N) (code0 : spt (prog a)) : Prop :=
  forall n v, lookup n i = SOME v ->
    exists p, lookup n code0 = SOME (Seq (StackAlloc v) p).

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_rel_def" *)
Definition state_rel (i : spt N) (s t : state a c ffi_t) : Prop :=
  exists c0,
    domain c0 = domain (code s) /\
    t = set_code c0 s /\
    state_ok i (code s) /\
    forall n b, lookup n (code s) = SOME b ->
      exists i, state_ok i (code s) /\ lookup n c0 = SOME (comp_top i b).

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_rel_thm" *)
Theorem state_rel_thm : forall i (s t : state a c ffi_t),
  state_rel i s t <->
    domain (code t) = domain (code s) /\
    regs t = regs s /\ fp_regs t = fp_regs s /\ store t = store s /\ stack t = stack s /\
    stack_space t = stack_space s /\ memory t = memory s /\ mdomain t = mdomain s /\
    sh_mdomain t = sh_mdomain s /\ bitmaps t = bitmaps s /\
    stackSem.compile t = stackSem.compile s /\ compile_oracle t = compile_oracle s /\
    code_buffer t = code_buffer s /\ data_buffer t = data_buffer s /\ gc_fun t = gc_fun s /\
    use_stack t = use_stack s /\ use_store t = use_store s /\ use_alloc t = use_alloc s /\
    clock t = clock s /\ ffi t = ffi s /\ ffi_save_regs t = ffi_save_regs s /\ be t = be s /\
    state_ok i (code s) /\
    forall n b, lookup n (code s) = SOME b ->
      exists i, state_ok i (code s) /\ lookup n (code t) = SOME (comp_top i b).
Proof.
  intros i s t; split.
  - intros [c0 [D [-> [O L]]]]; cbn. repeat split; auto.
  - intros [D H]; destruct_ands. exists (code t). repeat split; auto.
    destruct s, t; cbn in *; subst; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "with_stack_space" *)
Local Theorem with_stack_space : forall t1 : state a c ffi_t,
  set_stack_space (stack_space t1) t1 = t1.
Proof. intros []; reflexivity. Qed.

End Defs.

(** ** Syntactic lemmas *)

Section Syntax.
Context {a : N}.

Lemma comp_Seq (i : spt N) (p1 p2 : prog a) :
  comp i (Seq p1 p2) = comp_seq p1 p2 i (Seq (comp i p1) (comp i p2)).
Proof. reflexivity. Qed.

Lemma comp_LN_aux : forall b : prog a, comp LN b = b.
Proof.
  intros b; induction b as [b IH] using psz_ind.
  destruct b; cbn [comp]; try reflexivity.
  - destruct o as [[p1 [lr [l1 l2]]]|]; [|reflexivity].
    destruct o0 as [[p2 [k1 k2]]|]; rewrite (IH p1) by (cbn; lia);
      [rewrite (IH p2) by (cbn; lia)|]; reflexivity.
  - unfold comp_seq. rewrite (IH b1), (IH b2) by (cbn; lia).
    destruct (dest_case b1 b2) as [[k dest]|]; reflexivity.
  - rewrite (IH b1), (IH b2) by (cbn; lia); reflexivity.
  - rewrite (IH b) by (cbn; lia); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_LN" *)
Theorem comp_LN : forall (i : spt N) (b : prog a), comp_top LN b = b /\ comp LN b = b.
Proof.
  intros _ b; split; [|apply comp_LN_aux].
  unfold comp_top; destruct b; rewrite ?comp_LN_aux; reflexivity.
Qed.

End Syntax.

Section Syntax2.
Context {a : N}.

Lemma dest_case_SOME (p1 p2 : prog a) k d :
  dest_case p1 p2 = SOME (k, d) -> p1 = StackFree k /\ p2 = Call NONE (inl d) NONE.
Proof.
  unfold dest_case; destruct p1; try discriminate.
  destruct p2; try discriminate. destruct o as [x|]; [discriminate|].
  destruct s as [d'|]; [|discriminate]. destruct o0; [discriminate|].
  intros H; injection H as <- <-; split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_seq_neq_IMP" *)
Theorem comp_seq_neq_IMP : forall (p1 p2 : prog a) i default,
  comp_seq p1 p2 i default <> default ->
  exists k dest, p1 = StackFree k /\ p2 = Call NONE (inl dest) NONE.
Proof.
  intros p1 p2 i default H; unfold comp_seq in H.
  destruct (dest_case p1 p2) as [[k d]|] eqn:E; [|contradiction].
  apply dest_case_SOME in E; destruct E as [-> ->]; eauto.
Qed.

End Syntax2.

(** The syntactic invariance proofs follow HOL's [comp_ind] cases. *)
Ltac syn_cases IH :=
  match goal with b : prog _ |- _ => destruct b end; cbn [comp];
  try match goal with
      | o : option (prog _ * _) , o0 : option (prog _ * _) |- _ =>
          destruct o as [[p1 [lr [l1 l2]]]|]; [destruct o0 as [[p2 [k1 k2]]|]|]
      end;
  try match goal with
      | |- context [comp_seq ?b1 ?b2 ?i _] =>
          unfold comp_seq;
          let Ed := fresh "Ed" in
          destruct (dest_case b1 b2) as [[k dest]|] eqn:Ed;
          [ apply dest_case_SOME in Ed; destruct Ed as [-> ->];
            destruct (lookup dest i) as [l|];
            [ destruct (l =? k); [|destruct (l <? k)] | ]
          | ]
      end;
  cbn [comp].

Ltac rw_ih IH := repeat (rewrite IH by (cbn [psz]; lia)).

Ltac top_cases aux :=
  unfold comp_top; match goal with p : prog _ |- _ => destruct p end;
  rewrite ?aux; try reflexivity.

Section Syntax3.
Context {a : N}.

Lemma get_labels_comp_aux (i : spt N) : forall e : prog a, get_labels (comp i e) = get_labels e.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [get_labels]; rw_ih IH; rewrite ?(proj1 UNION_EMPTY), ?(proj2 UNION_EMPTY); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "get_labels_comp" *)
Theorem get_labels_comp : forall i (e : prog a),
  get_labels (comp i e) = get_labels e /\ get_labels (comp_top i e) = get_labels e.
Proof.
  intros i e; split; [apply get_labels_comp_aux|].
  top_cases (get_labels_comp_aux i). cbn [get_labels]; rewrite !get_labels_comp_aux; reflexivity.
Qed.

Lemma extract_labels_comp_aux (i : spt N) : forall p : prog a, extract_labels (comp i p) = extract_labels p.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [extract_labels]; rw_ih IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "extract_labels_comp" *)
Theorem extract_labels_comp : forall i (p : prog a),
  extract_labels (comp i p) = extract_labels p /\ extract_labels (comp_top i p) = extract_labels p.
Proof.
  intros i p; split; [apply extract_labels_comp_aux|].
  top_cases (extract_labels_comp_aux i). cbn [extract_labels]; rewrite !extract_labels_comp_aux; reflexivity.
Qed.

Lemma stack_asm_name_comp_aux (c : asm_config a) (i : spt N) : forall p : prog a,
  stack_asm_name c (comp i p) = stack_asm_name c p.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [stack_asm_name]; rw_ih IH; reflexivity.
Qed.

Lemma stack_asm_remove_comp_aux (c : asm_config a) (i : spt N) : forall p : prog a,
  stack_asm_remove c (comp i p) = stack_asm_remove c p.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [stack_asm_remove]; rw_ih IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_asm_name_comp" *)
Theorem stack_asm_name_comp : forall (c : asm_config a) i (p : prog a),
  (stack_asm_name c (comp i p) = stack_asm_name c p /\
   stack_asm_name c (comp_top i p) = stack_asm_name c p) /\
  (stack_asm_remove c (comp i p) = stack_asm_remove c p /\
   stack_asm_remove c (comp_top i p) = stack_asm_remove c p).
Proof.
  intros c i p; split; split;
    try apply stack_asm_name_comp_aux; try apply stack_asm_remove_comp_aux.
  - top_cases (stack_asm_name_comp_aux c i).
    cbn [stack_asm_name]; rewrite !stack_asm_name_comp_aux; reflexivity.
  - top_cases (stack_asm_remove_comp_aux c i).
    cbn [stack_asm_remove]; rewrite !stack_asm_remove_comp_aux; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_alloc_stack_asm_convs" *)
Theorem stack_alloc_stack_asm_convs : forall (c : asm_config a) (prog0 : list (N * prog a)),
  EVERY (fun '(n, p) => stack_asm_name c p) (compile prog0) =
  EVERY (fun '(n, p) => stack_asm_name c p) prog0 /\
  EVERY (fun '(n, p) => stack_asm_remove c p) (compile prog0) =
  EVERY (fun '(n, p) => stack_asm_remove c p) prog0.
Proof.
  intros c prog0; unfold compile; generalize (collect_info prog0 LN) as i; intros i.
  split; induction prog0 as [|[n p] l IH]; cbn; try reflexivity; rewrite IH;
    f_equal; apply (stack_asm_name_comp c i p).
Qed.

Lemma reg_bound_comp_aux (s : N) (i : spt N) : forall p : prog a,
  reg_bound (comp i p) s = reg_bound p s.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [reg_bound]; rw_ih IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "reg_bound_comp" *)
Theorem reg_bound_comp : forall s i (p : prog a),
  reg_bound (comp i p) s = reg_bound p s /\ reg_bound (comp_top i p) s = reg_bound p s.
Proof.
  intros s i p; split; [apply reg_bound_comp_aux|].
  top_cases (reg_bound_comp_aux s i). cbn [reg_bound]; rewrite !reg_bound_comp_aux; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_rawcall_reg_bound" *)
Theorem stack_rawcall_reg_bound : forall sp (prog1 : list (N * prog a)),
  EVERY (fun p => reg_bound p sp) (MAP SND (compile prog1)) =
  EVERY (fun p => reg_bound p sp) (MAP SND prog1).
Proof.
  intros sp prog1; unfold compile; generalize (collect_info prog1 LN) as i; intros i.
  induction prog1 as [|[n p] l IH]; cbn; [reflexivity|]. rewrite IH.
  f_equal; apply (reg_bound_comp sp i p).
Qed.

Lemma call_args_comp_aux r1 r2 r3 r4 r5 (i : spt N) : forall p : prog a,
  call_args (comp i p) r1 r2 r3 r4 r5 = call_args p r1 r2 r3 r4 r5.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [call_args]; rw_ih IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "call_args_comp" *)
Theorem call_args_comp : forall r1 r2 r3 r4 r5 i (p : prog a),
  call_args (comp i p) r1 r2 r3 r4 r5 = call_args p r1 r2 r3 r4 r5 /\
  call_args (comp_top i p) r1 r2 r3 r4 r5 = call_args p r1 r2 r3 r4 r5.
Proof.
  intros r1 r2 r3 r4 r5 i p; split; [apply call_args_comp_aux|].
  top_cases (call_args_comp_aux r1 r2 r3 r4 r5 i).
  cbn [call_args]; rewrite !call_args_comp_aux; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_alloc_call_args" *)
Theorem stack_alloc_call_args : forall (prog1 : list (N * prog a)),
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND (compile prog1)) =
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND prog1).
Proof.
  intros prog1; unfold compile; generalize (collect_info prog1 LN) as i; intros i.
  induction prog1 as [|[n p] l IH]; cbn; [reflexivity|]. rewrite IH.
  f_equal; apply (call_args_comp 1 2 3 4 0 i p).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "MAP_FST_compile" *)
Theorem MAP_FST_compile : forall (code0 : list (N * prog a)), MAP FST (compile code0) = MAP FST code0.
Proof.
  intros code0; unfold compile; generalize (collect_info code0 LN) as i; intros i.
  induction code0 as [|[n p] l IH]; cbn; [reflexivity|]. rewrite IH; reflexivity.
Qed.

Lemma alloc_arg_comp_aux (i : spt N) : forall p : prog a, alloc_arg (comp i p) = alloc_arg p.
Proof.
  intros e; induction e as [e IH] using psz_ind.
  syn_cases IH; cbn [alloc_arg]; rw_ih IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "call_arg_comp" *)
Theorem call_arg_comp : forall i (p : prog a),
  alloc_arg (comp i p) = alloc_arg p /\ alloc_arg (comp_top i p) = alloc_arg p.
Proof.
  intros i p; split; [apply alloc_arg_comp_aux|].
  top_cases (alloc_arg_comp_aux i). cbn [alloc_arg]; rewrite !alloc_arg_comp_aux; reflexivity.
Qed.

Lemma stack_get_handler_labels_comp_aux (i : spt N) : forall (p : prog a) k,
  stack_get_handler_labels k (comp i p) = stack_get_handler_labels k p.
Proof.
  intros e; induction e as [e IH] using psz_ind; intros kk.
  syn_cases IH; cbn [stack_get_handler_labels]; rw_ih IH;
    rewrite ?(proj1 UNION_EMPTY), ?(proj2 UNION_EMPTY); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "stack_get_handler_labels_comp" *)
Theorem stack_get_handler_labels_comp : forall i (p : prog a) k,
  stack_get_handler_labels k (comp i p) = stack_get_handler_labels k p /\
  stack_get_handler_labels k (comp_top i p) = stack_get_handler_labels k p.
Proof.
  intros i p k; split; [apply stack_get_handler_labels_comp_aux|].
  top_cases (stack_get_handler_labels_comp_aux i).
  cbn [stack_get_handler_labels]; rewrite !stack_get_handler_labels_comp_aux; reflexivity.
Qed.

End Syntax3.

Section Collect.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "domain_fromAList_compile" *)
Theorem domain_fromAList_compile : forall (code0 : list (N * prog a)),
  domain (fromAList (compile code0)) = domain (fromAList code0).
Proof.
  intros code0; rewrite !sptree.domain_fromAList.
  change (MAP fst (compile code0)) with (MAP FST (compile code0)).
  rewrite MAP_FST_compile; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "lookup_collect_info" *)
Theorem lookup_collect_info : forall (xs : list (N * prog a)) n rest,
  ALL_DISTINCT (MAP FST xs) ->
  lookup n (collect_info xs rest) =
  match ALOOKUP xs n with
  | NONE => lookup n rest
  | SOME body => lookup n (collect_info [(n, body)] rest)
  end.
Proof.
  intros xs; induction xs as [|[p1 b] xs IH]; intros n rest H; [reflexivity|].
  cbn [MAP FST fst ALL_DISTINCT] in H. unfold is_true in H.
  rewrite Bool.andb_true_iff in H. destruct H as [Hm Hd].
  cbn [collect_info ALOOKUP]. rewrite (IH _ _ Hd).
  destruct (decide (p1 = n)) as [<-|Ne].
  - destruct (ALOOKUP xs p1) as [b'|] eqn:A.
    + exfalso. apply ALOOKUP_In in A. rewrite Bool.negb_true_iff in Hm.
      assert (M : is_true (MEM p1 (MAP fst xs))).
      { unfold is_true; rewrite MEM_In, in_map_iff. exists (p1, b'); split; [reflexivity|exact A]. }
      unfold is_true in M; congruence.
    + reflexivity.
  - destruct (ALOOKUP xs n) as [body|]; cbn [collect_info];
      [destruct (seq_stack_alloc body)|]; destruct (seq_stack_alloc b);
      rewrite ?sptree.lookup_insert; repeat (destruct (decide _)); congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_ok_collect_info" *)
Theorem state_ok_collect_info : forall (code0 : list (N * prog a)),
  ALL_DISTINCT (MAP FST code0) -> state_ok (collect_info code0 LN) (fromAList code0).
Proof.
  intros code0 Hd n v H. rewrite (lookup_collect_info _ _ _ Hd) in H.
  rewrite sptree.lookup_fromAList.
  destruct (ALOOKUP code0 n) as [body|]; [|discriminate].
  cbn [collect_info] in H. unfold seq_stack_alloc in H.
  destruct body; try discriminate. destruct body1; try discriminate.
  rewrite sptree.lookup_insert in H. destruct (decide (n = n)); [|contradiction].
  injection H as ->. eauto.
Qed.

End Collect.

(** ** [set_code] commutes with the semantic primitives (Galette-only) *)

Section SetCode.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma regs_set_code k s : regs (set_code k s) = regs s. Proof. reflexivity. Qed.
Lemma fp_regs_set_code k s : fp_regs (set_code k s) = fp_regs s. Proof. reflexivity. Qed.
Lemma store_set_code k s : store (set_code k s) = store s. Proof. reflexivity. Qed.
Lemma stack_set_code k s : stack (set_code k s) = stack s. Proof. reflexivity. Qed.
Lemma stack_space_set_code k s : stack_space (set_code k s) = stack_space s. Proof. reflexivity. Qed.
Lemma memory_set_code k s : memory (set_code k s) = memory s. Proof. reflexivity. Qed.
Lemma mdomain_set_code k s : mdomain (set_code k s) = mdomain s. Proof. reflexivity. Qed.
Lemma sh_mdomain_set_code k s : sh_mdomain (set_code k s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma bitmaps_set_code k s : bitmaps (set_code k s) = bitmaps s. Proof. reflexivity. Qed.
Lemma compile_set_code k s : stackSem.compile (set_code k s) = stackSem.compile s. Proof. reflexivity. Qed.
Lemma compile_oracle_set_code k s : compile_oracle (set_code k s) = compile_oracle s. Proof. reflexivity. Qed.
Lemma code_buffer_set_code k s : code_buffer (set_code k s) = code_buffer s. Proof. reflexivity. Qed.
Lemma data_buffer_set_code k s : data_buffer (set_code k s) = data_buffer s. Proof. reflexivity. Qed.
Lemma gc_fun_set_code k s : gc_fun (set_code k s) = gc_fun s. Proof. reflexivity. Qed.
Lemma use_stack_set_code k s : use_stack (set_code k s) = use_stack s. Proof. reflexivity. Qed.
Lemma use_store_set_code k s : use_store (set_code k s) = use_store s. Proof. reflexivity. Qed.
Lemma use_alloc_set_code k s : use_alloc (set_code k s) = use_alloc s. Proof. reflexivity. Qed.
Lemma clock_set_code k s : clock (set_code k s) = clock s. Proof. reflexivity. Qed.
Lemma ffi_set_code k s : ffi (set_code k s) = ffi s. Proof. reflexivity. Qed.
Lemma ffi_save_regs_set_code k s : ffi_save_regs (set_code k s) = ffi_save_regs s. Proof. reflexivity. Qed.
Lemma be_set_code k s : be (set_code k s) = be s. Proof. reflexivity. Qed.
Lemma code_set_code k s : code (set_code k s) = k. Proof. reflexivity. Qed.
Lemma set_regs_set_code v k s : set_regs v (set_code k s) = set_code k (set_regs v s). Proof. reflexivity. Qed.
Lemma set_fp_regs_set_code v k s : set_fp_regs v (set_code k s) = set_code k (set_fp_regs v s). Proof. reflexivity. Qed.
Lemma set_store_fld_set_code v k s : set_store_fld v (set_code k s) = set_code k (set_store_fld v s). Proof. reflexivity. Qed.
Lemma set_stack_set_code v k s : set_stack v (set_code k s) = set_code k (set_stack v s). Proof. reflexivity. Qed.
Lemma set_stack_space_set_code v k s : set_stack_space v (set_code k s) = set_code k (set_stack_space v s). Proof. reflexivity. Qed.
Lemma set_memory_set_code v k s : set_memory v (set_code k s) = set_code k (set_memory v s). Proof. reflexivity. Qed.
Lemma set_mdomain_set_code v k s : set_mdomain v (set_code k s) = set_code k (set_mdomain v s). Proof. reflexivity. Qed.
Lemma set_sh_mdomain_set_code v k s : set_sh_mdomain v (set_code k s) = set_code k (set_sh_mdomain v s). Proof. reflexivity. Qed.
Lemma set_bitmaps_set_code v k s : set_bitmaps v (set_code k s) = set_code k (set_bitmaps v s). Proof. reflexivity. Qed.
Lemma set_compile_set_code v k s : set_compile v (set_code k s) = set_code k (set_compile v s). Proof. reflexivity. Qed.
Lemma set_compile_oracle_set_code v k s : set_compile_oracle v (set_code k s) = set_code k (set_compile_oracle v s). Proof. reflexivity. Qed.
Lemma set_code_buffer_set_code v k s : set_code_buffer v (set_code k s) = set_code k (set_code_buffer v s). Proof. reflexivity. Qed.
Lemma set_data_buffer_set_code v k s : set_data_buffer v (set_code k s) = set_code k (set_data_buffer v s). Proof. reflexivity. Qed.
Lemma set_gc_fun_set_code v k s : set_gc_fun v (set_code k s) = set_code k (set_gc_fun v s). Proof. reflexivity. Qed.
Lemma set_use_stack_set_code v k s : set_use_stack v (set_code k s) = set_code k (set_use_stack v s). Proof. reflexivity. Qed.
Lemma set_use_store_set_code v k s : set_use_store v (set_code k s) = set_code k (set_use_store v s). Proof. reflexivity. Qed.
Lemma set_use_alloc_set_code v k s : set_use_alloc v (set_code k s) = set_code k (set_use_alloc v s). Proof. reflexivity. Qed.
Lemma set_clock_set_code v k s : set_clock v (set_code k s) = set_code k (set_clock v s). Proof. reflexivity. Qed.
Lemma set_ffi_set_code v k s : set_ffi v (set_code k s) = set_code k (set_ffi v s). Proof. reflexivity. Qed.
Lemma set_ffi_save_regs_set_code v k s : set_ffi_save_regs v (set_code k s) = set_code k (set_ffi_save_regs v s). Proof. reflexivity. Qed.
Lemma set_be_set_code v k s : set_be v (set_code k s) = set_code k (set_be v s). Proof. reflexivity. Qed.
Lemma set_var_set_code v x k s : set_var v x (set_code k s) = set_code k (set_var v x s). Proof. reflexivity. Qed.
Lemma set_fp_var_set_code v x k s : set_fp_var v x (set_code k s) = set_code k (set_fp_var v x s). Proof. reflexivity. Qed.
Lemma set_store_set_code v x k s : set_store v x (set_code k s) = set_code k (set_store v x s). Proof. reflexivity. Qed.
Lemma empty_env_set_code k s : empty_env (set_code k s) = set_code k (empty_env s). Proof. reflexivity. Qed.
Lemma unset_var_set_code v k s : unset_var v (set_code k s) = set_code k (unset_var v s). Proof. reflexivity. Qed.
Lemma dec_clock_set_code k s : dec_clock (set_code k s) = set_code k (dec_clock s). Proof. reflexivity. Qed.
Lemma get_var_set_code v k s : get_var v (set_code k s) = get_var v s. Proof. reflexivity. Qed.
Lemma get_fp_var_set_code v k s : get_fp_var v (set_code k s) = get_fp_var v s. Proof. reflexivity. Qed.
Lemma mem_load_set_code v k s : mem_load v (set_code k s) = mem_load v s. Proof. reflexivity. Qed.

Lemma get_var_imm_set_code ri k s : get_var_imm ri (set_code k s) = get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.

Lemma get_vars_set_code xs k s : get_vars xs (set_code k s) = get_vars xs s.
Proof. induction xs as [|x xs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

Lemma word_exp_set_code k s e : word_exp (set_code k s) e = word_exp s e.
Proof. apply word_exp_cong; reflexivity. Qed.

Lemma mem_store_set_code x y k s :
  mem_store x y (set_code k s) = OPTION_MAP (set_code k) (mem_store x y s).
Proof. unfold mem_store; cbn. destruct (classical_dec _); reflexivity. Qed.

Lemma inst_set_code i k s : inst i (set_code k s) = OPTION_MAP (set_code k) (inst i s).
Proof.
  destruct i as [| | x | m r [ad w] | f]; [| | destruct x | destruct m | destruct f];
    cbn [inst]; unfold assign; rewrite ?word_exp_set_code, ?get_vars_set_code;
    unfold get_var, mem_load, get_fp_var; stk_fields;
    repeat (rewrite ?mem_store_set_code; cbn [option_map];
            match goal with
            | |- context [match ?x with _ => _ end] => destruct x eqn:?; cbn beta iota zeta
            end);
    first [reflexivity | cbn [option_map] in *; congruence].
Qed.

Lemma gc_set_code k s : gc (set_code k s) = OPTION_MAP (set_code k) (gc s).
Proof. unfold gc; stk_fields. stk_split_goal; reflexivity. Qed.

Lemma alloc_set_code w k s : alloc w (set_code k s) = (I ## set_code k) (alloc w s).
Proof.
  unfold alloc. rewrite set_store_set_code, gc_set_code.
  destruct (gc (set_store AllocSize (Word w) s)) as [s2|]; cbn [option_map]; [|reflexivity].
  stk_fields. stk_split_goal; reflexivity.
Qed.

Lemma store_const_sem_set_code t1 t2 k s :
  store_const_sem t1 t2 (set_code k s) = (I ## set_code k) (store_const_sem t1 t2 s).
Proof. unfold store_const_sem, get_var; stk_fields. stk_split_goal; reflexivity. Qed.

Lemma sh_mem_op_set_code op r ad k s :
  sh_mem_op op r ad (set_code k s) = (I ## set_code k) (sh_mem_op op r ad s).
Proof.
  destruct op; cbn [sh_mem_op];
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
      sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32, get_var; stk_fields;
    stk_split_goal; reflexivity.
Qed.

End SetCode.

Global Hint Rewrite @regs_set_code @fp_regs_set_code @store_set_code @stack_set_code @stack_space_set_code @memory_set_code @mdomain_set_code @sh_mdomain_set_code @bitmaps_set_code @compile_set_code @compile_oracle_set_code @code_buffer_set_code @data_buffer_set_code @gc_fun_set_code @use_stack_set_code @use_store_set_code @use_alloc_set_code @clock_set_code @ffi_set_code @ffi_save_regs_set_code @be_set_code @code_set_code @set_regs_set_code @set_fp_regs_set_code @set_store_fld_set_code @set_stack_set_code @set_stack_space_set_code @set_memory_set_code @set_mdomain_set_code @set_sh_mdomain_set_code @set_bitmaps_set_code @set_compile_set_code @set_compile_oracle_set_code @set_code_buffer_set_code @set_data_buffer_set_code @set_gc_fun_set_code @set_use_stack_set_code @set_use_store_set_code @set_use_alloc_set_code @set_clock_set_code @set_ffi_set_code @set_ffi_save_regs_set_code @set_be_set_code @set_var_set_code @set_fp_var_set_code @set_store_set_code @empty_env_set_code @unset_var_set_code @dec_clock_set_code @get_var_set_code @get_fp_var_set_code @mem_load_set_code @get_var_imm_set_code @get_vars_set_code @word_exp_set_code @mem_store_set_code @inst_set_code @alloc_set_code @store_const_sem_set_code @sh_mem_op_set_code : stkcode.

Section Simple.
Context {a : N} {c ffi_t : Type}.

(** Programs whose semantics neither reads nor writes the code store and
    which make no recursive call (Galette-only). *)
Definition simple (p : prog a) : bool :=
  match p with
  | Seq _ _ | If _ _ _ _ _ | Loop _ | Call _ _ _ | JumpLower _ _ _ | RawCall _
  | Install _ _ _ _ _ | LocValue _ _ _ | StoreConsts _ _ _ => false
  | _ => true
  end.

Ltac sc_simpl H :=
  autorewrite with stkcode in H |- *; cbn [option_map PAIR_MAP I fst snd] in H |- *.

Lemma evaluate_simple_set_code (p : prog a) (s : state a c ffi_t) r s1 k :
  simple p = true -> evaluate (p, s) = (r, s1) ->
  code s1 = code s /\ evaluate (p, set_code k s) = (r, set_code k s1).
Proof.
  intros Hs H. rewrite evaluate_eqn in H |- *.
  destruct p; try discriminate Hs; cbn [evaluate_body] in H |- *; sc_simpl H;
    repeat (match type of H with
            | context [match ?x with _ => _ end] =>
                let E := fresh "E" in destruct x eqn:E; sc_simpl H
            end);
    repeat match goal with
           | E : inst _ _ = SOME _ |- _ => pose proof (inst_const _ _ _ E); clear E
           end;
    try (injection H as <- <-; stk_fields; destruct_ands; split; [congruence|reflexivity]);
    repeat match goal with
           | E : alloc _ _ = (_, _) |- _ =>
               pose proof (alloc_const _ _ _ _ E); rewrite E; clear E
           | E : sh_mem_op _ _ _ _ = (_, _) |- _ =>
               pose proof (sh_mem_op_const _ _ _ _ _ _ E); rewrite E; clear E
           end;
    destruct_ands; stk_fields; rewrite ?PAIR_MAP_THM; unfold I; split; congruence.
Qed.

End Simple.

Section Correct.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

(** Galette-only: HOL's conclusion of [comp_correct] for one compiled program. *)
Definition rc_post (i : spt N) (r : option (result a)) (s1 t : state a c ffi_t) (q : prog a) : Prop :=
  exists ck t1 k1,
    state_rel i s1 t1 /\
    evaluate (q, set_clock (clock t + ck) t) = (r, set_stack_space k1 t1) /\
    (r <> SOME TimeOut /\ r <> SOME (Halt (Word (n2w 2))) -> k1 = stack_space t1).

Lemma set_clock_clock t : set_clock (clock t) t = t.
Proof. destruct t; reflexivity. Qed.

Lemma set_clock_set_clock k1 k2 t : set_clock k1 (set_clock k2 t) = set_clock k1 t.
Proof. reflexivity. Qed.

Lemma clock_set_clock' k t : clock (set_clock k t) = k.
Proof. reflexivity. Qed.

Lemma state_rel_inv i s t :
  state_rel i s t -> exists c0, t = set_code c0 s /\ state_rel i s (set_code c0 s).
Proof. intros H; pose proof H as (c0 & _ & -> & _); exists c0; split; [reflexivity|exact H]. Qed.

Lemma state_rel_same_code i s s1 c0 :
  state_rel i s (set_code c0 s) -> code s1 = code s -> state_rel i s1 (set_code c0 s1).
Proof.
  intros (c1 & D & E & O & L) Ec.
  assert (c1 = c0) as -> by (apply (f_equal code) in E; exact (eq_sym E)).
  exists c0; rewrite Ec; repeat split; auto.
Qed.

Lemma simple_comp i (p : prog a) : simple p = true -> comp i p = p /\ comp_top i p = p.
Proof. destruct p; intros H; try discriminate H; split; reflexivity. Qed.

Lemma simple_post i (p : prog a) s t r s1 :
  simple p = true -> evaluate (p, s) = (r, s1) -> state_rel i s t -> rc_post i r s1 t p.
Proof.
  intros Hs He Hr. destruct (state_rel_inv _ _ _ Hr) as (c0 & -> & Hr').
  destruct (evaluate_simple_set_code p s r s1 c0 Hs He) as [Ec E].
  exists 0, (set_code c0 s1), (stack_space s1). split; [|split].
  - exact (state_rel_same_code _ _ _ _ Hr' Ec).
  - rewrite N.add_0_r, set_clock_clock, E. f_equal.
  - intros _; reflexivity.
Qed.

Lemma get_var_set_clock v k s : get_var v (set_clock k s) = get_var v s. Proof. reflexivity. Qed.
Lemma get_var_imm_set_clock ri k s : get_var_imm ri (set_clock k s) = get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.

Lemma state_ok_mono i (c1 c2 : spt (prog a)) : state_ok i c1 -> sptree.subspt c1 c2 -> state_ok i c2.
Proof.
  intros H Hs n v Hn; destruct (H n v Hn) as [q Hq]; exists q.
  exact (proj1 (sptree.subspt_lookup _ _) Hs _ _ Hq).
Qed.

Lemma state_rel_reindex i i' s t : state_rel i s t -> state_ok i' (code s) -> state_rel i' s t.
Proof. intros (c1 & D & E & O & L) O'; exists c1; repeat split; auto. Qed.

Lemma dec_clock_add s ck :
  clock s <> 0 -> dec_clock (set_clock (clock s + ck) s) = set_clock (clock (dec_clock s) + ck) (dec_clock s).
Proof. intros H; unfold dec_clock; rewrite !clock_set_clock', !set_clock_set_clock; f_equal; lia. Qed.

Lemma set_code_set_code k1 k2 s : set_code k1 (set_code k2 s) = set_code k1 s.
Proof. reflexivity. Qed.

Lemma install_set_code (n n0 n1 n2 n3 : N) k s :
  evaluate (Install n n0 n1 n2 n3, set_code k s) =
  match evaluate (Install n n0 n1 n2 n3, s) with
  | (NONE, s') => (NONE, set_code (sptree.union k (sptree.fromAList (FST (SND (compile_oracle s 0))))) s')
  | (r, s') => (r, set_code k s')
  end.
Proof.
  rewrite !evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode.
  destruct (compile_oracle s 0) as [cfg [progs bm]] eqn:Eo; cbn [FST SND].
  repeat (match goal with
          | |- context [match ?x with _ => _ end] =>
              lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x eqn:? end
          end; cbn beta iota zeta); try reflexivity.
  all: autorewrite with stkcode; rewrite ?set_code_set_code; reflexivity.
Qed.

Lemma install_result (n n0 n1 n2 n3 : N) s r s1 :
  evaluate (Install n n0 n1 n2 n3, s) = (r, s1) ->
  (r = NONE /\ code s1 = sptree.union (code s) (sptree.fromAList (FST (SND (compile_oracle s 0))))) \/
  (r = SOME Error /\ s1 = s).
Proof.
  rewrite evaluate_eqn; cbn [evaluate_body].
  destruct (compile_oracle s 0) as [cfg [progs bm]] eqn:Eo; cbn [FST SND].
  repeat (match goal with
          | |- context [match ?x with _ => _ end] =>
              lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x eqn:? end
          end; cbn beta iota zeta).
  all: intros H; injection H as <- <-; auto.
Qed.

Lemma regs_set_clock k s : regs (set_clock k s) = regs s. Proof. reflexivity. Qed.

Lemma find_code_rel i s cd dest (regs0 : fmap N (word_loc a)) b :
  state_rel i s (set_code cd s) -> find_code dest regs0 (code s) = SOME b ->
  exists i', state_ok i' (code s) /\ find_code dest regs0 cd = SOME (comp_top i' b).
Proof.
  intros (c1 & D & Ec1 & O & L) H. apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
  destruct dest as [l|r]; cbn [find_code] in H |- *.
  - exact (L _ _ H).
  - destruct (FLOOKUP regs0 r) as [[w|l n]|]; try discriminate H.
    destruct (n =? 0); [exact (L _ _ H)|discriminate H].
Qed.

Lemma call_state x v s ck :
  clock s <> 0 ->
  dec_clock (set_var x v (set_clock (clock s + ck) s)) =
  set_clock (clock (dec_clock (set_var x v s)) + ck) (dec_clock (set_var x v s)).
Proof. intros H; apply (dec_clock_add (set_var x v s)); exact H. Qed.

Lemma ev_rawcall dest (X : state a c ffi_t) x0 body0 :
  sptree.lookup dest (code X) = SOME (Seq x0 body0) ->
  evaluate (RawCall dest, X) =
  if (clock X =? 0) then (SOME TimeOut, empty_env X) else
  match evaluate (body0, dec_clock X) with
  | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
  end.
Proof. intros H; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite H; reflexivity. Qed.

Lemma ev_seq_none (p1 p2 : prog a) (X Y : state a c ffi_t) :
  evaluate (p1, X) = (NONE, Y) -> evaluate (Seq p1 p2, X) = evaluate (p2, Y).
Proof. intros H; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, H; reflexivity. Qed.

Lemma ev_seq_some (p1 p2 : prog a) (X Y : state a c ffi_t) r :
  evaluate (p1, X) = (SOME r, Y) -> evaluate (Seq p1 p2, X) = (SOME r, Y).
Proof. intros H; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, H; reflexivity. Qed.

Lemma ev_tick (X : state a c ffi_t) :
  evaluate (Tick, X) = if (clock X =? 0) then (SOME TimeOut, empty_env X) else (NONE, dec_clock X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackalloc n (X : state a c ffi_t) :
  use_stack X = true ->
  evaluate (StackAlloc n, X) =
  if (stack_space X <? n) then (SOME (Halt (Word (n2w 2))), empty_env X)
  else (NONE, set_stack_space (stack_space X - n) X).
Proof. intros H; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite H; reflexivity. Qed.

Lemma ev_stackfree n (X : state a c ffi_t) :
  use_stack X = true -> stack_space X + n <= LENGTH (stack X) ->
  evaluate (StackFree n, X) = (NONE, set_stack_space (stack_space X + n) X).
Proof.
  intros H H2; rewrite evaluate_eqn; cbn [evaluate_body]; rewrite H; cbn [negb].
  replace (LENGTH (stack X) <? stack_space X + n) with false by (symmetry; apply N.ltb_ge; lia).
  reflexivity.
Qed.

Lemma state_ss_clock (X : state a c ffi_t) k1 k2 c1 c2 :
  k1 = k2 -> c1 = c2 ->
  set_stack_space k1 (set_clock c1 X) = set_stack_space k2 (set_clock c2 X).
Proof. intros -> ->; reflexivity. Qed.

Lemma post_same_code i (q : prog a) s s1 c0 r :
  state_rel i s (set_code c0 s) -> code s1 = code s ->
  evaluate (q, set_code c0 s) = (r, set_code c0 s1) ->
  rc_post i r s1 (set_code c0 s) q.
Proof.
  intros Hr Ec E. exists 0, (set_code c0 s1), (stack_space s1). split; [|split].
  - exact (state_rel_same_code _ _ _ _ Hr Ec).
  - rewrite N.add_0_r, set_clock_clock, E. reflexivity.
  - intros _; reflexivity.
Qed.

Lemma eval_lt_psize (p q : prog a) s : (psize p < psize q)%nat -> eval_lt (p, s) (q, s).
Proof. intros H; right; split; [reflexivity|exact H]. Qed.

Lemma eval_lt_clock (p q : prog a) s s' : clock s' < clock s -> eval_lt (p, s') (q, s).
Proof. intros H; left; exact H. Qed.

(** Galette-only: equality of states field by field (keeps the
    [comp_correct_gen] record goals small). *)
Lemma state_eq_fields (x y : state a c ffi_t) :
  stackSem.regs x = stackSem.regs y -> stackSem.fp_regs x = stackSem.fp_regs y -> stackSem.store x = stackSem.store y -> stackSem.stack x = stackSem.stack y ->
  stackSem.stack_space x = stackSem.stack_space y -> stackSem.memory x = stackSem.memory y -> stackSem.mdomain x = stackSem.mdomain y ->
  stackSem.sh_mdomain x = stackSem.sh_mdomain y -> stackSem.bitmaps x = stackSem.bitmaps y -> stackSem.compile x = stackSem.compile y ->
  stackSem.compile_oracle x = stackSem.compile_oracle y -> stackSem.code_buffer x = stackSem.code_buffer y ->
  stackSem.data_buffer x = stackSem.data_buffer y -> stackSem.gc_fun x = stackSem.gc_fun y -> stackSem.use_stack x = stackSem.use_stack y ->
  stackSem.use_store x = stackSem.use_store y -> stackSem.use_alloc x = stackSem.use_alloc y -> stackSem.clock x = stackSem.clock y ->
  stackSem.code x = stackSem.code y -> stackSem.ffi x = stackSem.ffi y -> stackSem.ffi_save_regs x = stackSem.ffi_save_regs y -> stackSem.be x = stackSem.be y -> x = y.
Proof. destruct x, y; cbn; intros; subst; reflexivity. Qed.

Theorem comp_correct_gen : forall (x : prog a * state a c ffi_t) t i r s1,
  evaluate x = (r, s1) -> r <> SOME Error -> state_rel i (snd x) t ->
  rc_post i r s1 t (comp_top i (fst x)) /\ rc_post i r s1 t (comp i (fst x)).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros t i r s1 He Hr Hrel; cbn [fst snd] in *.
  destruct (simple p) eqn:Hs.
  { destruct (simple_comp i p Hs) as [E1 E2]; rewrite E1, E2; split; eapply simple_post; eauto. }
  destruct p; try discriminate Hs.
  - (* Call *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    pose proof Hr' as (c1 & D & Ec1 & O & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct o as [[rh [lr [l1 l2]]]|].
    2: { (* no return handler: comp is the identity *)
      cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (Call NONE s0 o0)) by (split; exact G).
      destruct (find_code s0 (regs s) (code s)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
      destruct (find_code_rel _ _ _ _ _ _ Hr' Ef) as (i' & Oi' & Ef').
      destruct (negb (bool_decide (o0 = NONE))) eqn:Eh; [injection He as <- <-; congruence|].
      destruct (clock s =? 0) eqn:Ez.
      { injection He as <- <-. apply post_same_code; [exact Hr'|reflexivity|].
        rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode. rewrite Ef', Eh, Ez; reflexivity. }
      apply N.eqb_neq in Ez. rewrite fix_clock_evaluate in He.
      destruct (evaluate (prog0, dec_clock s)) as [res s'] eqn:Ev.
      destruct (bad_fun_return res) eqn:Eb; injection He as <- <-; [congruence|].
      assert (Hlt : eval_lt (prog0, dec_clock s) (Call NONE s0 o0, s))
        by (apply eval_lt_clock; unfold dec_clock; rewrite clock_set_clock'; lia).
      assert (Hd : state_rel i' (dec_clock s) (set_code cd (dec_clock s)))
        by (apply (state_rel_reindex i); [apply (state_rel_same_code _ _ _ _ Hr'); reflexivity|exact Oi']).
      destruct (IH _ Hlt _ i' res s' Ev Hr Hd) as [(ck & t1 & k1 & R & E & K) _].
      exists ck, t1, k1. split; [|split; [|exact K]].
      + apply (state_rel_reindex i'); [exact R|].
        apply (state_ok_mono _ (code (dec_clock s))); [exact O|exact (proj2 (evaluate_mono _ _ _ _ Ev))].
      + cbn [FST fst] in E; autorewrite with stkcode in E.
        rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode.
        rewrite regs_set_clock, Ef', Eh, clock_set_clock'.
        replace (clock s + ck =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        rewrite dec_clock_add by exact Ez. rewrite fix_clock_evaluate, E, Eb. reflexivity. }
    set (h' := match o0 with None => None | Some (p2, (k1, k2)) => Some (comp i p2, (k1, k2)) end).
    enough (G : rc_post i r s1 (set_code cd s) (Call (Some (comp i rh, (lr, (l1, l2)))) s0 h'))
      by (assert (Hc : comp i (Call (Some (rh, (lr, (l1, l2)))) s0 o0) =
                       Call (Some (comp i rh, (lr, (l1, l2)))) s0 h')
            by (subst h'; destruct o0 as [[? [? ?]]|]; reflexivity);
          cbn [comp_top]; rewrite Hc; split; exact G).
    destruct (find_code s0 (regs s \\ lr) (code s)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
    destruct (find_code_rel _ _ _ _ _ _ Hr' Ef) as (i' & Oi' & Ef').
    destruct (clock s =? 0) eqn:Ez.
    { injection He as <- <-. apply post_same_code; [exact Hr'|reflexivity|].
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode. rewrite Ef', Ez; reflexivity. }
    apply N.eqb_neq in Ez. rewrite fix_clock_evaluate in He.
    destruct (evaluate (prog0, dec_clock (set_var lr (Loc l1 l2) s))) as [res s2] eqn:Ev.
    assert (Hres : res <> SOME Error) by (intros ->; injection He as <- <-; congruence).
    assert (Hcs : clock (dec_clock (set_var lr (Loc l1 l2) s)) < clock s)
      by (unfold dec_clock; rewrite clock_set_clock'; change (clock (set_var lr (Loc l1 l2) s)) with (clock s); lia).
    assert (Hlt : eval_lt (prog0, dec_clock (set_var lr (Loc l1 l2) s)) (Call (Some (rh, (lr, (l1, l2)))) s0 o0, s))
      by (apply eval_lt_clock; exact Hcs).
    assert (Hd : state_rel i' (dec_clock (set_var lr (Loc l1 l2) s)) (set_code cd (dec_clock (set_var lr (Loc l1 l2) s))))
      by (apply (state_rel_reindex i); [apply (state_rel_same_code _ _ _ _ Hr'); reflexivity|exact Oi']).
    destruct (IH _ Hlt _ i' res s2 Ev Hres Hd) as [(ck & t1 & k1 & R & E & K) _].
    cbn [fst FST] in E; autorewrite with stkcode in E.
    pose proof (evaluate_clock _ _ _ _ Ev) as Hcl.
    assert (O2 : state_ok i (code s2))
      by (apply (state_ok_mono _ (code (dec_clock (set_var lr (Loc l1 l2) s)))); [exact O|exact (proj2 (evaluate_mono _ _ _ _ Ev))]).
    assert (R' : state_rel i s2 t1) by (apply (state_rel_reindex i'); [exact R|exact O2]).
    (* the related run up to the callee's result, with [ck'] extra clock *)
    assert (Tcall : forall ck', evaluate (Call (Some (comp i rh, (lr, (l1, l2)))) s0 h',
                                          set_clock (clock (set_code cd s) + ck') (set_code cd s)) =
              match evaluate (comp_top i' prog0, set_code cd (set_clock (clock (dec_clock (set_var lr (Loc l1 l2) s)) + ck')
                                                                  (dec_clock (set_var lr (Loc l1 l2) s)))) with
              | (SOME (Result x), s3) =>
                  if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s3) else evaluate (comp i rh, s3)
              | (SOME (Exception x), s3) =>
                  match h' with
                  | NONE => (SOME (Exception x), s3)
                  | SOME (h, (l1, l2)) => if negb (bool_decide (x = Loc l1 l2)) then (SOME Error, s3) else evaluate (h, s3)
                  end
              | (NONE, s3) => (SOME Error, s3)
              | (SOME (Break _), s3) => (SOME Error, s3)
              | (SOME (Continue _), s3) => (SOME Error, s3)
              | (res, s3) => (res, s3)
              end).
    { intros ck'. rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode.
      rewrite regs_set_clock, Ef', clock_set_clock'.
      replace (clock s + ck' =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite call_state by exact Ez. rewrite fix_clock_evaluate. reflexivity. }
    destruct res as [[x|x|n|n|w| |f|]|]; try (injection He as <- <-; congruence); try congruence.
    + (* Result *)
      destruct (bool_decide (x = Loc l1 l2)) eqn:Ex; cbn [negb] in He; [|injection He as <- <-; congruence].
      assert (Hk : k1 = stack_space t1) by (apply K; split; discriminate). subst k1.
      rewrite with_stack_space in E.
      assert (Hlt2 : eval_lt (rh, s2) (Call (Some (rh, (lr, (l1, l2)))) s0 o0, s)) by (apply eval_lt_clock; lia).
      destruct (IH _ Hlt2 _ i r s1 He Hr R') as [_ (ck2 & t2 & k2 & R2 & E2 & K2)].
      cbn [fst FST] in E2.
      exists (ck + ck2), t2, k2. split; [exact R2|split; [|exact K2]].
      assert (Hnt : SOME (Result x) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock ck2 _ _ _ _ (conj E Hnt)) as E3.
      autorewrite with stkcode in E3. rewrite clock_set_clock', set_clock_set_clock, <- N.add_assoc in E3.
      rewrite Tcall, E3, Ex. exact E2.
    + (* Exception *)
      subst h'. destruct o0 as [[h [k1' k2']]|]; cbn beta iota in He |- *.
      * destruct (bool_decide (x = Loc k1' k2')) eqn:Ex; cbn [negb] in He; [|injection He as <- <-; congruence].
        assert (Hk : k1 = stack_space t1) by (apply K; split; discriminate). subst k1.
        rewrite with_stack_space in E.
        assert (Hlt2 : eval_lt (h, s2) (Call (Some (rh, (lr, (l1, l2)))) s0 (Some (h, (k1', k2'))), s))
          by (apply eval_lt_clock; lia).
        destruct (IH _ Hlt2 _ i r s1 He Hr R') as [_ (ck2 & t2 & k2 & R2 & E2 & K2)].
        cbn [fst FST] in E2.
        exists (ck + ck2), t2, k2. split; [exact R2|split; [|exact K2]].
        assert (Hnt : SOME (Exception x) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock ck2 _ _ _ _ (conj E Hnt)) as E3.
        autorewrite with stkcode in E3. rewrite clock_set_clock', set_clock_set_clock, <- N.add_assoc in E3.
        rewrite Tcall, E3. cbn beta iota. rewrite Ex. exact E2.
      * injection He as <- <-. exists ck, t1, k1. split; [exact R'|split; [|exact K]].
        rewrite Tcall, E. reflexivity.
    + (* Halt *) injection He as <- <-. exists ck, t1, k1. split; [exact R'|split; [|exact K]].
      rewrite Tcall, E. reflexivity.
    + (* TimeOut *) injection He as <- <-. exists ck, t1, k1. split; [exact R'|split; [|exact K]].
      rewrite Tcall, E. reflexivity.
    + (* FinalFFI *) injection He as <- <-. exists ck, t1, k1. split; [exact R'|split; [|exact K]].
      rewrite Tcall, E. reflexivity.
  - (* Seq *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He; rewrite fix_clock_evaluate in He.
    destruct (evaluate (p1, s)) as [res s'] eqn:Ev.
    assert (Hlt1 : eval_lt (p1, s) (Seq p1 p2, s)) by (apply eval_lt_psize; cbn [psize]; lia).
    assert (GA : rc_post i r s1 (set_code cd s) (Seq (comp i p1) (comp i p2))).
    { destruct res as [res0|].
      - injection He as <- <-.
        destruct (IH _ Hlt1 _ i _ _ Ev Hr Hr') as [_ (ck & t1 & k1 & R & E & K)].
        exists ck, t1, k1; split; [exact R|split; [|exact K]].
        cbn [FST fst] in E. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, E. reflexivity.
      - destruct (IH _ Hlt1 _ i NONE s' Ev ltac:(discriminate) Hr') as [_ (ck & t1 & k1 & R & E & K)].
        assert (Hk : k1 = stack_space t1) by (apply K; split; discriminate). subst k1.
        cbn [FST fst] in E; rewrite with_stack_space in E.
        pose proof (evaluate_clock _ _ _ _ Ev) as Hcl.
        assert (Hlt2 : eval_lt (p2, s') (Seq p1 p2, s)).
        { destruct (N.eq_dec (clock s') (clock s)) as [Ec|Ec];
            [right; split; [exact Ec|cbn [psize fst]; lia]|left; cbn [snd]; lia]. }
        destruct (IH _ Hlt2 _ i r s1 He Hr R) as [_ (ck2 & t2 & k2 & R2 & E2 & K2)].
        cbn [FST fst] in E2.
        exists (ck + ck2), t2, k2; split; [exact R2|split; [|exact K2]].
        assert (Hnt : @NONE (result a) <> SOME TimeOut) by discriminate.
        pose proof (evaluate_add_clock ck2 _ _ _ _ (conj E Hnt)) as E3.
        rewrite clock_set_clock', set_clock_set_clock, <- N.add_assoc in E3.
        rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, E3. exact E2. }
    split; [cbn [comp_top]; exact GA|].
    cbn [comp]; unfold comp_seq.
    destruct (dest_case p1 p2) as [[k dest]|] eqn:Edc; [|exact GA].
    destruct (sptree.lookup dest i) as [l|] eqn:Eli; [|exact GA].
    apply dest_case_SOME in Edc as [-> ->]. clear GA Hlt1.
    pose proof Hr' as (c1 & D & Ec1 & O & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
    destruct (O _ _ Eli) as [q Eq].
    destruct (L _ _ Eq) as (i' & Oi' & Eq'). cbn [comp_top comp] in Eq'.
    (* the original run: StackFree k *)
    rewrite evaluate_eqn in Ev; cbn [evaluate_body] in Ev.
    destruct (use_stack s) eqn:Eus; cbn [negb] in Ev; [|injection Ev as <- <-; injection He as <- <-; congruence].
    destruct (LENGTH (stack s) <? stack_space s + k) eqn:Elen;
      [injection Ev as <- <-; injection He as <- <-; congruence|].
    injection Ev as <- <-. apply N.ltb_ge in Elen.
    (* then the call *)
    rewrite evaluate_eqn in He; cbn [evaluate_body find_code] in He.
    change (code (set_stack_space (stack_space s + k) s)) with (code s) in He.
    rewrite Eq, (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl) in He. cbn [negb] in He.
    change (clock (set_stack_space (stack_space s + k) s)) with (clock s) in He.
    set (s'' := set_stack_space (stack_space s + k) s) in He.
    assert (Hcd : forall X : state a c ffi_t, code X = cd -> sptree.lookup dest (code X) = SOME (Seq (StackAlloc l) (comp i' q)))
      by (intros X ->; exact Eq').
    destruct (clock s =? 0) eqn:Ez.
    { (* the call times out *)
      injection He as <- <-. apply N.eqb_eq in Ez.
      destruct (l =? k) eqn:E1; [|destruct (l <? k) eqn:E2].
      - exists 0, (set_code cd (empty_env s'')), (stack_space s). split; [|split].
        + apply (state_rel_same_code _ _ _ _ Hr'); reflexivity.
        + rewrite N.add_0_r, set_clock_clock; erewrite ev_rawcall by (apply Hcd; reflexivity).
          stk_fields; rewrite Ez; reflexivity.
        + intros [H _]; congruence.
      - apply N.ltb_lt in E2.
        exists 0, (set_code cd (empty_env s'')), (stack_space s + (k - l)). split; [|split].
        + apply (state_rel_same_code _ _ _ _ Hr'); reflexivity.
        + rewrite N.add_0_r, set_clock_clock.
          rewrite (ev_seq_none _ _ _ _ (ev_stackfree (k - l) (set_code cd s) Eus ltac:(stk_fields; lia))).
          erewrite ev_rawcall by (apply Hcd; reflexivity). stk_fields; rewrite Ez; reflexivity.
        + intros [H _]; congruence.
      - exists 0, (set_code cd (empty_env s'')), (stack_space s). split; [|split].
        + apply (state_rel_same_code _ _ _ _ Hr'); reflexivity.
        + rewrite N.add_0_r, set_clock_clock.
          rewrite (ev_seq_some _ _ _ (empty_env (set_code cd s)) TimeOut)
            by (rewrite ev_tick; stk_fields; rewrite Ez; reflexivity).
          reflexivity.
        + intros [H _]; congruence. }
    apply N.eqb_neq in Ez.
    rewrite fix_clock_evaluate in He.
    rewrite (evaluate_eqn (Seq (StackAlloc l) q)) in He; cbn [evaluate_body] in He; rewrite fix_clock_evaluate in He.
    rewrite (ev_stackalloc l (dec_clock s'') Eus) in He.
    replace (stack_space (dec_clock s'')) with (stack_space s + k) in He by reflexivity.
    destruct (stack_space s + k <? l) eqn:Ea.
    { (* StackAlloc halts *)
      cbn beta iota in He; cbn [bad_fun_return] in He. injection He as <- <-.
      apply N.ltb_lt in Ea.
      replace (l =? k) with false by (symmetry; apply N.eqb_neq; lia).
      replace (l <? k) with false by (symmetry; apply N.ltb_ge; lia).
      exists 0, (set_code cd (empty_env (dec_clock s''))), (stack_space s). split; [|split].
      + apply (state_rel_same_code _ _ _ _ Hr'); reflexivity.
      + rewrite N.add_0_r, set_clock_clock.
        rewrite (ev_seq_none _ _ _ (dec_clock (set_code cd s)))
          by (rewrite ev_tick; replace (clock (set_code cd s) =? 0) with false
                by (symmetry; apply N.eqb_neq; exact Ez); reflexivity).
        rewrite (ev_seq_some _ _ _ (empty_env (dec_clock (set_code cd s))) (Halt (Word (n2w 2))))
          by (rewrite ev_stackalloc by exact Eus;
              replace (stack_space (dec_clock (set_code cd s)) <? l - k) with true
                by (symmetry; apply N.ltb_lt; unfold dec_clock; stk_fields; lia);
              reflexivity).
        reflexivity.
      + intros [_ H]; congruence. }
    apply N.ltb_ge in Ea. cbn beta iota in He.
    set (s3 := set_stack_space (stack_space s + k - l) (dec_clock s'')) in He.
    destruct (evaluate (q, s3)) as [res2 s4] eqn:Eq3.
    destruct (bad_fun_return res2) eqn:Eb; injection He as <- <-; [congruence|].
    assert (Hc3 : clock s3 = clock s - 1) by reflexivity.
    assert (Hlt3 : eval_lt (q, s3) (Seq (StackFree k) (Call NONE (inl dest) NONE), s))
      by (apply eval_lt_clock; rewrite Hc3; lia).
    assert (Hd3 : state_rel i' s3 (set_code cd s3))
      by (apply (state_rel_reindex i); [apply (state_rel_same_code _ _ _ _ Hr'); reflexivity|exact Oi']).
    destruct (IH _ Hlt3 _ i' res2 s4 Eq3 Hr Hd3) as [_ (ck2 & t2 & k2 & R2 & E2 & K2)].
    cbn [FST fst] in E2. autorewrite with stkcode in E2.
    assert (R2' : state_rel i s4 t2).
    { apply (state_rel_reindex i'); [exact R2|].
      apply (state_ok_mono _ (code s3)); [exact O|exact (proj2 (evaluate_mono _ _ _ _ Eq3))]. }
    destruct (l =? k) eqn:E1; [apply N.eqb_eq in E1; subst l|destruct (l <? k) eqn:E2'].
    + exists ck2, t2, k2. split; [exact R2'|split; [|exact K2]].
      erewrite ev_rawcall by (apply Hcd; reflexivity).
      replace (clock (set_clock (clock (set_code cd s) + ck2) (set_code cd s)) =? 0) with false
        by (symmetry; apply N.eqb_neq; stk_fields; lia).
      replace (dec_clock (set_clock (clock (set_code cd s) + ck2) (set_code cd s)))
        with (set_code cd (set_clock (clock s3 + ck2) s3)).
      * rewrite E2, Eb; reflexivity.
      * subst s3 s''; unfold dec_clock; apply state_eq_fields; stk_fields; try reflexivity; lia.
    + apply N.ltb_lt in E2'.
      exists ck2, t2, k2. split; [exact R2'|split; [|exact K2]].
      match goal with |- context [evaluate (Seq (StackFree ?n) ?p2, ?X)] =>
        rewrite (ev_seq_none _ p2 X _ (ev_stackfree n X Eus
                   ltac:(unfold set_clock, set_code; cbn [stack_space stack]; lia))) end.
      erewrite ev_rawcall by (apply Hcd; reflexivity).
      match goal with |- context [(clock ?X =? 0)] =>
        replace (clock X =? 0) with false by (symmetry; apply N.eqb_neq; unfold dec_clock, set_clock, set_code, set_stack_space; cbn [clock]; lia) end.
      match goal with |- context [evaluate (comp i' q, dec_clock ?X)] =>
        replace (dec_clock X) with (set_code cd (set_clock (clock s3 + ck2) s3)) end.
      * rewrite E2, Eb; reflexivity.
      * subst s3 s''; unfold dec_clock; apply state_eq_fields; stk_fields; try reflexivity; lia.
    + apply N.ltb_ge in E2'. assert (Hlk : k < l) by (apply N.eqb_neq in E1; lia).
      exists (ck2 + 1), t2, k2. split; [exact R2'|split; [|exact K2]].
      rewrite (ev_seq_none _ _ _ (dec_clock (set_clock (clock (set_code cd s) + (ck2 + 1)) (set_code cd s))))
        by (rewrite ev_tick; replace (clock (set_clock (clock (set_code cd s) + (ck2 + 1)) (set_code cd s)) =? 0)
              with false by (symmetry; apply N.eqb_neq; stk_fields; lia); reflexivity).
      match goal with |- context [evaluate (Seq (StackAlloc ?n) _, ?X)] =>
        rewrite (ev_seq_none _ _ _ (set_stack_space (stack_space X - n) X))
          by (rewrite ev_stackalloc by exact Eus;
              replace (stack_space X <? n) with false by (symmetry; apply N.ltb_ge; unfold dec_clock, set_clock, set_code, set_stack_space; cbn [stack_space]; lia);
              reflexivity) end.
      erewrite ev_rawcall by (apply Hcd; reflexivity).
      match goal with |- context [(clock ?X =? 0)] =>
        replace (clock X =? 0) with false by (symmetry; apply N.eqb_neq; unfold dec_clock, set_clock, set_code, set_stack_space; cbn [clock]; lia) end.
      match goal with |- context [evaluate (comp i' q, dec_clock ?X)] =>
        replace (dec_clock X) with (set_code cd (set_clock (clock s3 + ck2) s3)) end.
      * rewrite E2, Eb; reflexivity.
      * subst s3 s''; unfold dec_clock; apply state_eq_fields; stk_fields; try reflexivity; lia.
  - (* If *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (get_var n s) as [x|] eqn:Ex; [|injection He as <- <-; congruence].
    destruct (get_var_imm r0 s) as [y|] eqn:Ey; [|injection He as <- <-; congruence].
    cbn [comp_top comp].
    destruct (wordSem.word_cmp c0 x y) as [[|]|] eqn:Ec; [| |injection He as <- <-; congruence];
      [assert (Hlt : eval_lt (p1, s) (If c0 n r0 p1 p2, s)) by (apply eval_lt_psize; cbn [psize]; lia)
      |assert (Hlt : eval_lt (p2, s) (If c0 n r0 p1 p2, s)) by (apply eval_lt_psize; cbn [psize]; lia)];
      (destruct (IH _ Hlt (set_code cd s) i r s1 He Hr Hr') as [_ (ck & t1 & k1 & R & E & K)];
       enough (G : rc_post i r s1 (set_code cd s) (If c0 n r0 (comp i p1) (comp i p2))) by (split; exact G);
       exists ck, t1, k1; split; [exact R|split; [|exact K]];
       rewrite evaluate_eqn; cbn [evaluate_body];
       rewrite get_var_set_clock, get_var_imm_set_clock, get_var_set_code, get_var_imm_set_code, Ex, Ey, Ec;
       exact E).
  - (* Loop *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (Loop (comp i p))) by (split; exact G).
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He; rewrite fix_clock_evaluate in He.
    destruct (evaluate (p, s)) as [res s'] eqn:Ev.
    assert (Hlt : eval_lt (p, s) (Loop p, s)) by (apply eval_lt_psize; cbn [psize]; lia).
    assert (Hres : res <> SOME Error) by (intros ->; cbn in He; injection He as <- <-; congruence).
    destruct (IH _ Hlt _ i res s' Ev Hres Hr') as [_ (ck & t1 & k1 & R & E & K)].
    cbn [fst FST] in E.
    destruct (cont_loop res) eqn:Ecl.
    2: { injection He as <- <-. exists ck, t1, k1. split; [exact R|split].
         - rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, E, Ecl; reflexivity.
         - intros [H1 H2]; apply K; split; intros ->; [apply H1|apply H2]; reflexivity. }
    assert (Hk : k1 = stack_space t1)
      by (apply K; destruct (cont_loop_IMP res Ecl) as [->| ->]; split; discriminate).
    subst k1. rewrite with_stack_space in E.
    pose proof R as (cd1 & D1 & Et1 & O1 & L1).
    destruct (clock s' =? 0) eqn:Ez.
    { injection He as <- <-. exists ck, (empty_env t1), (stack_space (empty_env t1)). split; [|split].
      - subst t1; rewrite empty_env_set_code; apply (state_rel_same_code _ _ _ _ R); reflexivity.
      - rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, E, Ecl.
        replace (clock t1) with (clock s') by (subst t1; reflexivity). rewrite Ez, with_stack_space; reflexivity.
      - intros [H _]; congruence. }
    apply N.eqb_neq in Ez.
    assert (Hcl : clock s' <= clock s) by exact (evaluate_clock _ _ _ _ Ev).
    assert (Hlt2 : eval_lt (STOP (Loop p), dec_clock s') (Loop p, s))
      by (apply eval_lt_clock; unfold dec_clock; rewrite clock_set_clock'; lia).
    assert (Hd : state_rel i (dec_clock s') (dec_clock t1))
      by (subst t1; rewrite dec_clock_set_code; apply (state_rel_same_code _ _ _ _ R); reflexivity).
    destruct (IH _ Hlt2 _ i r s1 He Hr Hd) as [_ (ck2 & t2 & k2 & R2 & E2 & K2)].
    cbn [fst FST] in E2; unfold STOP in E2; cbn [comp] in E2.
    exists (ck + ck2), t2, k2. split; [exact R2|split; [|exact K2]].
    assert (Hnt : res <> SOME TimeOut) by (destruct (cont_loop_IMP res Ecl) as [->| ->]; discriminate).
    pose proof (evaluate_add_clock ck2 _ _ _ _ (conj E Hnt)) as E3.
    rewrite clock_set_clock', set_clock_set_clock, <- N.add_assoc in E3.
    rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate, E3, Ecl, clock_set_clock'.
    assert (Hc1 : clock t1 = clock s') by (subst t1; reflexivity).
    replace (clock t1 + ck2 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite dec_clock_add by lia. unfold STOP; exact E2.
  - (* JumpLower *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (JumpLower n n0 n1)) by (split; exact G).
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (get_var n s) as [[x|]|] eqn:Ex; try (injection He as <- <-; congruence).
    destruct (get_var n0 s) as [[y|]|] eqn:Ey; try (injection He as <- <-; congruence).
    destruct (word_cmp Lower x y) eqn:Ec.
    2: { injection He as <- <-. apply post_same_code; [exact Hr'|reflexivity|].
         rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode;
         rewrite Ex, Ey, Ec; reflexivity. }
    cbn [find_code] in He.
    destruct (sptree.lookup n1 (code s)) as [prog0|] eqn:El; [|injection He as <- <-; congruence].
    pose proof Hr' as (c1 & D & Ec1 & O & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
    destruct (L _ _ El) as (i' & Oi' & El').
    destruct (clock s =? 0) eqn:Ez.
    { injection He as <- <-. apply post_same_code; [exact Hr'|reflexivity|].
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode; rewrite Ex, Ey, Ec.
      cbn [find_code]; rewrite El', Ez; reflexivity. }
    apply N.eqb_neq in Ez.
    destruct (evaluate (prog0, dec_clock s)) as [res s'] eqn:Ev.
    destruct (bad_fun_return res) eqn:Eb; injection He as <- <-; [congruence|].
    assert (Hlt : eval_lt (prog0, dec_clock s) (JumpLower n n0 n1, s))
      by (apply eval_lt_clock; unfold dec_clock; rewrite clock_set_clock'; lia).
    assert (Hd : state_rel i' (dec_clock s) (set_code cd (dec_clock s)))
      by (apply (state_rel_reindex i); [apply (state_rel_same_code _ _ _ _ Hr'); reflexivity|exact Oi']).
    destruct (IH _ Hlt _ i' res s' Ev Hr Hd) as [(ck & t1 & k1 & R & E & K) _].
    exists ck, t1, k1. split; [|split; [|exact K]].
    + apply (state_rel_reindex i'); [exact R|].
      apply (state_ok_mono _ (code (dec_clock s))); [exact O|exact (proj2 (evaluate_mono _ _ _ _ Ev))].
    + cbn [FST fst] in E; autorewrite with stkcode in E.
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode; rewrite ?get_var_set_clock, Ex, Ey, Ec.
      cbn [find_code]; rewrite El', clock_set_clock'.
      replace (clock s + ck =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite dec_clock_add by exact Ez. rewrite E, Eb. reflexivity.
  - (* StoreConsts *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (StoreConsts n n0 o)) by (split; exact G).
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (negb (use_store s)) eqn:E1; [injection He as <- <-; congruence|].
    destruct (negb (use_alloc s) && IS_SOME o)%bool eqn:E2; [injection He as <- <-; congruence|].
    destruct (check_store_consts_opt n n0 o (code s)) eqn:E3; cbn [negb] in He; [|injection He as <- <-; congruence].
    destruct (store_const_sem n n0 s) as [r' s'] eqn:E4; injection He as -> ->.
    apply post_same_code; [exact Hr'|apply (store_const_sem_const _ _ _ _ _ E4)|].
    rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode; rewrite E1, E2.
    replace (check_store_consts_opt n n0 o cd) with true.
    + cbn [negb]; rewrite E4; reflexivity.
    + symmetry; destruct o as [m|]; [|reflexivity]. cbn [check_store_consts_opt] in E3 |- *.
      apply bool_decide_spec in E3; apply bool_decide_spec.
      destruct Hr' as (c1 & _ & Ec1 & _ & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
      destruct (L _ _ E3) as (i' & _ & ->). reflexivity.
  - (* LocValue *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (LocValue n n0 n1)) by (split; exact G).
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (classical_dec (loc_check (code s) (n0, n1))) as [Hl|]; [|injection He as <- <-; congruence].
    injection He as <- <-.
    apply post_same_code; [exact Hr'|reflexivity|].
    rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode.
    destruct (classical_dec (loc_check cd (n0, n1))) as [_|Hn]; [reflexivity|exfalso; apply Hn].
    destruct Hr' as (c1 & D & Ec1 & _ & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
    destruct Hl as [[-> Hd]|(m & e & Hm & Hin)]; [left; split; [reflexivity|rewrite D; exact Hd]|].
    right. destruct (L _ _ Hm) as (i' & _ & Hm'). exists m, (comp_top i' e); split; [exact Hm'|].
    rewrite (proj2 (get_labels_comp i' e)); exact Hin.
  - (* Install *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (Install n n0 n1 n2 n3)) by (split; exact G).
    pose proof (install_set_code n n0 n1 n2 n3 cd s) as Ei. rewrite He in Ei.
    destruct (install_result _ _ _ _ _ _ _ _ He) as [[-> Ec]|[-> ->]]; [|congruence].
    set (F := sptree.fromAList (FST (SND (compile_oracle s 0)))) in *.
    exists 0, (set_code (sptree.union cd F) s1), (stack_space s1). split; [|split].
    + pose proof Hr' as (c1 & D & Ec1 & O & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
      exists (sptree.union cd F). rewrite Ec. split; [rewrite !sptree.domain_union, D; reflexivity|].
      split; [reflexivity|].
      assert (Hsub : sptree.subspt (code s) (sptree.union (code s) F)).
      { apply sptree.subspt_lookup; intros x y Hx; rewrite sptree.lookup_union, Hx; reflexivity. }
      split; [exact (state_ok_mono _ _ _ O Hsub)|].
      intros m b Hm. rewrite sptree.lookup_union in Hm |- *.
      destruct (sptree.lookup m (code s)) as [b0|] eqn:Em.
      * injection Hm as <-. destruct (L _ _ Em) as (i' & Oi' & Em').
        exists i'; split; [exact (state_ok_mono _ _ _ Oi' Hsub)|rewrite Em'; reflexivity].
      * assert (Hn : sptree.lookup m cd = NONE).
        { destruct (sptree.lookup m cd) eqn:Ec'; [|reflexivity]. exfalso.
          assert (Hd : sptree.domain cd m) by (apply sptree.domain_lookup; eexists; exact Ec').
          rewrite D in Hd; apply sptree.domain_lookup in Hd as [v Hv]; congruence. }
        exists LN; split.
        -- intros x v Hx; discriminate Hx.
        -- rewrite Hn, Hm; f_equal; symmetry; apply (proj1 (comp_LN i b)).
    + rewrite N.add_0_r, set_clock_clock, Ei. reflexivity.
    + intros _; reflexivity.
  - (* RawCall *)
    destruct (state_rel_inv _ _ _ Hrel) as (cd & -> & Hr').
    cbn [comp_top comp]; enough (G : rc_post i r s1 (set_code cd s) (RawCall n)) by (split; exact G).
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (sptree.lookup n (code s)) as [prog0|] eqn:El; [|injection He as <- <-; congruence].
    destruct (dest_Seq prog0) as [[x body]|] eqn:Eds; [|injection He as <- <-; congruence].
    assert (prog0 = Seq x body) as -> by (destruct prog0; cbn in Eds; congruence).
    pose proof Hr' as (c1 & D & Ec1 & O & L). apply (f_equal code) in Ec1; cbn in Ec1; subst c1.
    destruct (L _ _ El) as (i' & Oi' & El'). cbn [comp_top] in El'.
    destruct (clock s =? 0) eqn:Ez.
    { injection He as <- <-. apply post_same_code; [exact Hr'|reflexivity|].
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode.
      rewrite El'; cbn [dest_Seq]; rewrite Ez; reflexivity. }
    apply N.eqb_neq in Ez.
    destruct (evaluate (body, dec_clock s)) as [res s'] eqn:Ev.
    destruct (bad_fun_return res) eqn:Eb; injection He as <- <-; [congruence|].
    assert (Hlt : eval_lt (body, dec_clock s) (RawCall n, s))
      by (apply eval_lt_clock; unfold dec_clock; rewrite clock_set_clock'; lia).
    assert (Hd : state_rel i' (dec_clock s) (set_code cd (dec_clock s)))
      by (apply (state_rel_reindex i); [apply (state_rel_same_code _ _ _ _ Hr'); reflexivity|exact Oi']).
    destruct (IH _ Hlt _ i' res s' Ev Hr Hd) as [_ (ck & t1 & k1 & R & E & K)].
    exists ck, t1, k1. split; [|split; [|exact K]].
    + apply (state_rel_reindex i'); [exact R|].
      apply (state_ok_mono _ (code (dec_clock s))); [exact O|exact (proj2 (evaluate_mono _ _ _ _ Ev))].
    + cbn [FST fst] in E; autorewrite with stkcode in E.
      rewrite evaluate_eqn; cbn [evaluate_body]; autorewrite with stkcode.
      rewrite El'; cbn [dest_Seq]; rewrite clock_set_clock'.
      replace (clock s + ck =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite dec_clock_add by exact Ez. rewrite E, Eb. reflexivity.
Qed.

End Correct.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "evaluate_comp_Inst" *)
Theorem evaluate_comp_Inst {a : N} {c ffi_t : Type} : forall (i : asm.inst a) (s t : state a c ffi_t) i' r s1,
  evaluate (Inst i, s) = (r, s1) /\ r <> SOME Error /\ state_rel i' s t ->
  exists ck t1 k1,
    state_rel i' s1 t1 /\
    evaluate (comp i' (Inst i), set_clock (ck + clock t) t) = (r, set_stack_space k1 t1) /\
    (r <> SOME TimeOut /\ r <> SOME (Halt (Word (n2w 2))) -> k1 = stack_space t1).
Proof.
  intros i s t i' r s1 (He & _ & Hrel).
  destruct (simple_post i' (Inst i) s t r s1 eq_refl He Hrel) as (ck & t1 & k1 & R & E & K).
  exists ck, t1, k1. rewrite N.add_comm. split; [exact R|split; [exact E|exact K]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_correct" *)
Theorem comp_correct {a : N} {c ffi_t : Type} : forall p (s t : state a c ffi_t) i r s1,
  evaluate (p, s) = (r, s1) /\ r <> SOME Error /\ state_rel i s t ->
  (exists ck t1 k1,
     state_rel i s1 t1 /\
     evaluate (comp_top i p, set_clock (clock t + ck) t) = (r, set_stack_space k1 t1) /\
     (r <> SOME TimeOut /\ r <> SOME (Halt (Word (n2w 2))) -> k1 = stack_space t1)) /\
  (exists ck t1 k1,
     state_rel i s1 t1 /\
     evaluate (comp i p, set_clock (clock t + ck) t) = (r, set_stack_space k1 t1) /\
     (r <> SOME TimeOut /\ r <> SOME (Halt (Word (n2w 2))) -> k1 = stack_space t1)).
Proof.
  intros p s t i r s1 (He & Hr & Hrel). exact (comp_correct_gen (p, s) t i r s1 He Hr Hrel).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "compile_semantics" *)
Theorem compile_semantics {a : N} {c ffi_t : Type} : forall (code0 : list (N * prog a)) (s : state a c ffi_t) start,
  ALL_DISTINCT (MAP FST code0) /\ use_stack s /\ code s = fromAList code0 /\ semantics start s <> Fail ->
  semantics start (set_code (fromAList (compile code0)) s) = semantics start s.
Proof.
  intros code0 s start (HD & Hus & Hc & HF).
  apply semantics_sim; [exact HF|].
  intros k r s1 E Hr.
  set (i := collect_info code0 LN).
  assert (Hrel : state_rel i (set_clock k s) (set_clock k (set_code (fromAList (compile code0)) s))).
  { exists (fromAList (compile code0)). split; [|split; [reflexivity|split]].
    - change (code (set_clock k s)) with (code s); rewrite Hc; apply domain_fromAList_compile.
    - change (code (set_clock k s)) with (code s); rewrite Hc; apply state_ok_collect_info; exact HD.
    - change (code (set_clock k s)) with (code s); rewrite Hc. intros n b Hn.
      exists i; split; [apply state_ok_collect_info; exact HD|].
      rewrite sptree.lookup_fromAList in Hn |- *. unfold compile; fold i.
      rewrite ALOOKUP_MAP; cbv beta; rewrite Hn; reflexivity. }
  destruct (comp_correct_gen (Call NONE (inl start) NONE, set_clock k s) _ i r s1 E Hr Hrel)
    as [(ck & t1 & k1 & R & E' & _) _].
  cbn [FST fst] in E'.
  exists ck, (set_stack_space k1 t1). split.
  - exact E'.
  - destruct R as (c1 & _ & -> & _); reflexivity.
Qed.
