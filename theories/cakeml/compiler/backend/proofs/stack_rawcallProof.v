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
