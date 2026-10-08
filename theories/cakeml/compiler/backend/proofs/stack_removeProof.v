(** * CakeML [stack_removeProof]: correctness of [stack_remove]

    Port of [cakeml/compiler/backend/proofs/stack_removeProofScript.sml]
    (in progress: the preliminary lemmas and the state relation).

    Notes:
    - HOL's separation-logic product [p * q] is [set_sep.STAR p q]; HOL's
      binder [SEP_EXISTS x. p x] is [SEP_EXISTS (fun x => p x)].
    - HOL's [s with f := v] is [set_f v s] ([stackSem]).
    - HOL's local overload [num_stubs] is [stack_num_stubs].
    - [memory] is HOL's [memory_def]; the state field is written
      [stackSem.memory]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.finite_maps Require sptree.
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend Require stack_remove.
Import wordLang (word_loc, Word, Loc).
Import sptree (spt, LN, lookup, domain, fromAList, toAList, insert, union, subspt).
Open Scope N_scope.

Lemma LENGTH_cons_N {A} (x : A) l : LENGTH (x :: l) = SUC (LENGTH l).
Proof. rewrite !LENGTH_length; cbn [length]; lia. Qed.

Section WordList.
Context {a : N} {B : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_exists_thm" *)
Theorem word_list_exists_thm : forall (ad : word a) n,
  (@word_list_exists a B ad 0 = emp) /\
  (@word_list_exists a B ad (SUC n) =
     SEP_EXISTS (fun w => STAR (one (ad, w)) (word_list_exists (ad + bytes_in_word)%w n))).
Proof.
  intros ad n; split; apply functional_extensionality; intros s; apply propositional_extensionality;
    unfold word_list_exists; rewrite !SEP_EXISTS_THM.
  - split.
    + intros [xs Hs]. apply (proj2 (cond_STAR _ _ _)) in Hs as [Hl Hw].
      destruct xs; [exact Hw|rewrite LENGTH_cons_N in Hl; lia].
    + intros He. exists []. apply (proj2 (cond_STAR _ _ _)); split; [reflexivity|exact He].
  - split.
    + intros [xs Hs]. apply (proj2 (cond_STAR _ _ _)) in Hs as [Hl Hw].
      destruct xs as [|w ys]; [cbn in Hl; lia|].
      exists w. cbn [word_list] in Hw. apply STAR_alt in Hw as (u & Hu & Ho & Hy).
      apply STAR_alt; exists u; split; [exact Hu|split; [exact Ho|]].
      apply SEP_EXISTS_THM; exists ys. apply (proj2 (cond_STAR _ _ _)); split; [|exact Hy].
      rewrite LENGTH_cons_N in Hl; lia.
    + intros [w Hs]. apply STAR_alt in Hs as (u & Hu & Ho & Hy).
      apply SEP_EXISTS_THM in Hy as [ys Hy]. apply (proj2 (cond_STAR _ _ _)) in Hy as [Hl Hy].
      exists (w :: ys). apply (proj2 (cond_STAR _ _ _)); split; [rewrite LENGTH_cons_N; lia|].
      cbn [word_list]; apply STAR_alt; exists u; auto.
Qed.

Lemma STAR_emp_l (p : (word a * B -> Prop) -> Prop) : STAR emp p = p.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
  (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@SEP_CLAUSES _ unit _ (fun _ => p) p p p True True tt))))))))))))))))))). Qed.

Lemma STAR_SEP_EXISTS_l {C} `{Inhabited C} (f : C -> (word a * B -> Prop) -> Prop) q :
  STAR (SEP_EXISTS (fun v => f v)) q = SEP_EXISTS (fun v => STAR (f v) q).
Proof. exact (proj1 (@SEP_CLAUSES _ C _ f q q q True True (@inhabitant C _))). Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_exists_ADD" *)
Theorem word_list_exists_ADD `{Inhabited B} : forall m n (ad : word a),
  @word_list_exists a B ad (m + n) =
  STAR (word_list_exists ad m) (word_list_exists (ad + bytes_in_word * n2w m)%w n).
Proof.
  intros m; induction m as [|m IH] using N.peano_ind; intros n ad.
  - rewrite (proj1 (word_list_exists_thm ad 0)), STAR_emp_l, N.add_0_l.
    f_equal; word_ring.
  - replace (N.succ m + n) with (SUC (m + n)) by lia.
    rewrite (proj2 (word_list_exists_thm ad (m + n))), (proj2 (word_list_exists_thm ad m)).
    rewrite STAR_SEP_EXISTS_l. f_equal; apply functional_extensionality; intros w.
    rewrite IH, STAR_ASSOC. do 2 f_equal. rewrite <- N.add_1_r, <- word_add_n2w. word_ring.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_APPEND" *)
Theorem word_list_APPEND : forall (xs ys : list B) (ad : word a),
  word_list ad (xs ++ ys) =
  STAR (word_list ad xs) (word_list (ad + bytes_in_word * n2w (LENGTH xs))%w ys).
Proof.
  intros xs; induction xs as [|x xs IH]; intros ys ad; cbn [app word_list].
  - rewrite STAR_emp_l. f_equal; cbn; word_ring.
  - rewrite IH, STAR_ASSOC. do 2 f_equal. rewrite LENGTH_cons_N. rewrite <- N.add_1_r, <- word_add_n2w. word_ring.
Qed.

End WordList.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "LESS_LENGTH_IMP_APPEND" *)
Theorem LESS_LENGTH_IMP_APPEND : forall {A} (xs : list A) n,
  n < LENGTH xs -> exists ys zs, xs = ys ++ zs /\ LENGTH ys = n.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros n Hn; [cbn in Hn; lia|].
  rewrite LENGTH_cons_N in Hn. destruct (N.eq_dec n 0) as [->|Hn0].
  - exists [], (x :: xs); split; reflexivity.
  - destruct (IH (n - 1) ltac:(lia)) as (ys & zs & -> & Hl).
    exists (x :: ys), zs; split; [reflexivity|rewrite LENGTH_cons_N; lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "call_FFI_LENGTH" *)
Theorem call_FFI_LENGTH : forall {ffi} (s : ffi_state ffi) i conf xs n ys,
  call_FFI s i conf xs = FFI_return n ys -> LENGTH ys = LENGTH xs.
Proof.
  intros ffi s i conf xs n ys H; unfold call_FFI in H.
  destruct (negb _); [|injection H as _ <-; reflexivity].
  destruct (ffi_state_oracle s i _ conf xs) as [f' b'|o]; [|discriminate H].
  destruct (LENGTH b' =? LENGTH xs) eqn:E; [|discriminate H].
  injection H as _ <-. apply N.eqb_eq, E.
Qed.

Section StateLemmas.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "with_same_clock" *)
Theorem with_same_clock : forall x : state a c ffi_t, set_clock (clock x) x = x.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "set_var_set_var" *)
Theorem set_var_set_var : forall x (y z : word_loc a) (w : state a c ffi_t), set_var x y (set_var x z w) = set_var x y w.
Proof.
  intros x y z w; unfold set_var.
  transitivity (set_regs ((regs w |+ (x, z)) |+ (x, y)) w); [reflexivity|]. f_equal.
  apply fmap_ext; intros k. rewrite !FLOOKUP_UPDATE. destruct (decide (x = k)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_var_set_var_same" *)
Theorem get_var_set_var_same : forall x (y : word_loc a) (z : state a c ffi_t), get_var x (set_var x y z) = SOME y.
Proof. intros; unfold get_var, set_var; cbn [regs set_regs]; rewrite FLOOKUP_UPDATE; destruct (decide (x = x)); congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_var_set_var" *)
Theorem get_var_set_var : forall x x' (y : word_loc a) (z : state a c ffi_t),
  get_var x (set_var x' y z) = if decide (x = x') then SOME y else get_var x z.
Proof.
  intros; unfold get_var, set_var; cbn [regs set_regs]; rewrite FLOOKUP_UPDATE.
  destruct (decide (x' = x)), (decide (x = x')); congruence.
Qed.

End StateLemmas.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_offset_eq" *)
Theorem word_offset_eq : forall {a : N} n, @stack_remove.word_offset a n = (bytes_in_word * n2w n)%w.
Proof. intros a n; unfold stack_remove.word_offset, bytes_in_word. rewrite word_mul_n2w; reflexivity. Qed.

Section Defs.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_def" *)
Definition memory (m : word a -> word_loc a) (dm : word a -> Prop) : (word a * word_loc a -> Prop) -> Prop :=
  fun s => s = fun2set (m, dm).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_rev_def" *)
Fixpoint word_list_rev {B} (ad : word a) (xs : list B) : (word a * B -> Prop) -> Prop :=
  match xs with
  | [] => emp
  | x :: xs => STAR (one ((ad - bytes_in_word)%w, x)) (word_list_rev (ad - bytes_in_word)%w xs)
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_store_def" *)
Definition word_store (base : word a) (store0 : fmap store_name (word_loc a))
    : (word a * word_loc a -> Prop) -> Prop :=
  word_list_rev base
    (MAP (fun name => match FLOOKUP store0 name with NONE => Word (n2w 0) | SOME x => x end)
         stack_remove.store_list).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "code_rel_def" *)
Definition code_rel (jump : bool) (off : word a * word a) (k : N) (code1 code2 : spt (prog a)) : Prop :=
  (forall n prog0, lookup n code1 = SOME prog0 ->
     reg_bound prog0 k /\ lookup n code2 = SOME (stack_remove.comp jump off k prog0)) /\
  domain code2 = (domain code1 UNION (0 INSERT (1 INSERT (2 INSERT {})))).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "is_SOME_Word_def" *)
Definition is_SOME_Word (x : option (word_loc a)) : bool :=
  match x with SOME (Word w) => true | _ => false end.

(** HOL leaves [the_SOME_Word] unspecified on other arguments. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "the_SOME_Word_def" *)
Definition the_SOME_Word (x : option (word_loc a)) : word a :=
  match x with SOME (Word w) => w | _ => ARB end.

End Defs.

Section StateRel.
Context {a : N} {c ffi_t : Type}.

(** HOL's separation-logic product [*] associates to the left. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_def" *)
Definition state_rel (jump : bool) (off : word a * word a) (k : N) (s1 s2 : state a c ffi_t) : Prop :=
  use_stack s1 /\ use_store s1 /\
  ~ use_stack s2 /\ ~ use_store s2 /\
  ~ use_alloc s2 /\ ~ use_alloc s1 /\
  be s2 = be s1 /\
  gc_fun s2 = gc_fun s1 /\
  clock s2 = clock s1 /\
  ffi s2 = ffi s1 /\
  ffi_save_regs s2 = ffi_save_regs s1 /\
  fp_regs s2 = fp_regs s1 /\
  code_buffer s2 = code_buffer s1 /\
  sh_mdomain s2 = sh_mdomain s1 /\
  compile s1 = (fun c0 p => compile s2 c0 (MAP (stack_remove.prog_comp jump off k) p)) /\
  compile_oracle s2 =
    (fun n => (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) (compile_oracle s1 n)) /\
  (forall n i p, MEM (i, p) (FST (SND (compile_oracle s1 n))) ->
     reg_bound p k /\ stack_num_stubs <= i + 1) /\
  good_dimindex a /\
  (forall n, n < k -> FLOOKUP (regs s2) n = FLOOKUP (regs s1) n) /\
  code_rel jump off k (code s1) (code s2) /\
  lookup stack_remove.stack_err_lab (code s2) = SOME (stack_remove.halt_inst (n2w 2)) /\
  FLOOKUP (regs s2) (k + 2) = FLOOKUP (store s1) CurrHeap /\
  (k INSERT (k + 1 INSERT (k + 2 INSERT {}))) SUBSET ffi_save_regs s2 /\
  is_SOME_Word (FLOOKUP (store s1) BitmapBase) /\
  stack_space s1 <= LENGTH (stack s1) /\
  let bp := (the_SOME_Word (FLOOKUP (store s1) BitmapBase) << word_shift a)%w in
  let all_bitmaps := bitmaps s1 ++ wordSem.buffer_buffer (data_buffer s1) in
  wordSem.position (data_buffer s1) = (bp + bytes_in_word * n2w (LENGTH (bitmaps s1)))%w /\
  match FLOOKUP (regs s2) (k + 1) with
  | SOME (Word base) =>
      dimindex a DIV 8 * stack_remove.max_stack_alloc <= w2n base /\
      w2n base + w2n (bytes_in_word : word a) * LENGTH (stack s1) < dimword a /\
      FLOOKUP (regs s2) k = SOME (Word (base + bytes_in_word * n2w (stack_space s1))%w) /\
      STAR (STAR (STAR (STAR (memory (stackSem.memory s1) (mdomain s1))
                             (word_list bp (MAP Word all_bitmaps)))
                       (word_list_exists (bp + bytes_in_word * n2w (LENGTH all_bitmaps))%w
                                         (wordSem.space_left (data_buffer s1))))
                 (word_store base (store s1)))
           (word_list base (stack s1))
        (fun2set (stackSem.memory s2, mdomain s2))
  | _ => False
  end.

End StateRel.

Section StateRelLemmas.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_get_var" *)
Local Theorem state_rel_get_var : forall jump off k s t n,
  state_rel jump off k s t /\ n < k -> get_var n s = get_var n t.
Proof.
  intros jump off k s t n [H Hn]. unfold state_rel in H. destruct_ands.
  unfold get_var. symmetry; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_with_clock" *)
Local Theorem state_rel_with_clock : forall jump off k s t1 c0,
  state_rel jump off k s t1 -> state_rel jump off k (set_clock c0 s) (set_clock c0 t1).
Proof. intros jump off k s t1 c0 H. unfold state_rel in *; cbn [set_clock] in *; stk_fields. tauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_IMP" *)
Local Theorem state_rel_IMP : forall jump off k s t1,
  state_rel jump off k s t1 -> state_rel jump off k (dec_clock s) (dec_clock t1).
Proof.
  intros jump off k s t1 H. unfold dec_clock.
  replace (clock t1) with (clock s) by (unfold state_rel in H; destruct_ands; congruence).
  apply state_rel_with_clock, H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_const" *)
Theorem state_rel_const : forall jump off k s t,
  state_rel jump off k s t ->
  code_buffer t = code_buffer s /\
  sh_mdomain t = sh_mdomain s /\
  ~ use_stack t /\ use_stack s /\ ffi t = ffi s /\
  compile_oracle t = (fun n => (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) (compile_oracle s n)) /\
  compile s = (fun c0 p => compile t c0 (MAP (stack_remove.prog_comp jump off k) p)).
Proof. intros jump off k s t H; unfold state_rel in H; destruct_ands; tauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "find_code_lemma" *)
Local Theorem find_code_lemma : forall jump off k s t1 dest x,
  state_rel jump off k s t1 /\
  match dest with inl _ => True | inr i => i < k end /\
  find_code dest (regs s) (code s) = SOME x ->
  find_code dest (regs t1) (code t1) = SOME (stack_remove.comp jump off k x) /\ reg_bound x k.
Proof.
  intros jump off k s t1 dest x (H & Hd & Hf). unfold state_rel in H; destruct_ands.
  match goal with H0 : code_rel _ _ _ _ _ |- _ => destruct H0 as [Hcr _] end.
  destruct dest as [l|r]; cbn [find_code] in Hf |- *.
  - destruct (Hcr _ _ Hf) as [Hb Hl]; split; assumption.
  - match goal with Hr : forall n, n < k -> _ |- _ => rewrite (Hr r Hd) end.
    destruct (FLOOKUP (regs s) r) as [[w|l n0]|]; try discriminate Hf.
    destruct (n0 =? 0); [|discriminate Hf].
    destruct (Hcr _ _ Hf) as [Hb Hl]; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "find_code_lemma2" *)
Local Theorem find_code_lemma2 : forall jump off k s t1 dest x x1,
  state_rel jump off k s t1 /\
  match dest with inl _ => True | inr i => i < k end /\
  find_code dest (regs s \\ x1) (code s) = SOME x ->
  find_code dest (regs t1 \\ x1) (code t1) = SOME (stack_remove.comp jump off k x) /\ reg_bound x k.
Proof.
  intros jump off k s t1 dest x x1 (H & Hd & Hf). unfold state_rel in H; destruct_ands.
  match goal with H0 : code_rel _ _ _ _ _ |- _ => destruct H0 as [Hcr _] end.
  destruct dest as [l|r]; cbn [find_code] in Hf |- *.
  - destruct (Hcr _ _ Hf) as [Hb Hl]; split; assumption.
  - rewrite DOMSUB_FLOOKUP_THM in Hf |- *.
    match goal with Hr : forall n, n < k -> _ |- _ => rewrite (Hr r Hd) end.
    destruct (decide (x1 = r)); [discriminate Hf|].
    destruct (FLOOKUP (regs s) r) as [[w|l n0]|]; try discriminate Hf.
    destruct (n0 =? 0); [|discriminate Hf].
    destruct (Hcr _ _ Hf) as [Hb Hl]; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_set_var" *)
Theorem state_rel_set_var : forall jump off k s t1 v x,
  state_rel jump off k s t1 /\ v < k ->
  state_rel jump off k (set_var v x s) (set_var v x t1).
Proof.
  intros jump off k s t1 v x [H Hv]. unfold state_rel, set_var in *; stk_fields.
  rewrite !(FLOOKUP_UPDATE (regs t1)).
  destruct (decide (v = k + 2)) as [|_]; [lia|].
  destruct (decide (v = k + 1)) as [|_]; [lia|].
  destruct (decide (v = k)) as [|_]; [lia|].
  destruct_ands. repeat (split; [assumption|]).
  split; [intros n Hn; rewrite !FLOOKUP_UPDATE; destruct (decide (v = n)); auto|].
  repeat (split; [assumption|]). assumption.
Qed.

End StateRelLemmas.

Section MemLemmas.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_fun2set_IMP_read" *)
Local Theorem memory_fun2set_IMP_read : forall (m m1 : word a -> word_loc a) d d1 p ad,
  STAR (memory m d) p (fun2set (m1, d1)) /\ ad IN d -> ad IN d1 /\ m1 ad = m ad.
Proof.
  intros m m1 d d1 p ad [H Hd]. apply STAR_alt in H as (u & Hu & Hm & _).
  unfold memory in Hm; subst u.
  assert (Hin : fun2set (m, d) (ad, m ad)) by (apply fun2set_thm; split; [reflexivity|exact Hd]).
  apply Hu in Hin. apply fun2set_thm in Hin as [E Hd1]. split; [exact Hd1|exact E].
Qed.

Lemma state_rel_STAR jump off k s t :
  state_rel jump off k s t ->
  exists base p, FLOOKUP (regs t) (k + 1) = SOME (Word base) /\
    STAR (memory (stackSem.memory s) (mdomain s)) p (fun2set (stackSem.memory t, mdomain t)).
Proof.
  intros H; unfold state_rel in H; destruct_ands. cbv zeta in *.
  destruct (FLOOKUP (regs t) (k + 1)) as [[base|]|] eqn:E; try contradiction.
  destruct_ands. eexists base, _; split; [reflexivity|].
  rewrite <- !STAR_ASSOC in *. eassumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_read" *)
Local Theorem state_rel_read : forall jump off k s t ad,
  state_rel jump off k s t /\ ad IN mdomain s ->
  ad IN mdomain t /\ stackSem.memory t ad = stackSem.memory s ad.
Proof.
  intros jump off k s t ad [H Hd]. destruct (state_rel_STAR _ _ _ _ _ H) as (base & p & _ & Hs).
  exact (memory_fun2set_IMP_read _ _ _ _ _ _ (conj Hs Hd)).
Qed.

Lemma state_rel_be jump off k s t : state_rel jump off k s t -> be t = be s.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_32_IMP" *)
Local Theorem mem_load_32_IMP : forall jump off k s t ad x,
  state_rel jump off k s t /\
  wordSem.mem_load_32 (stackSem.memory s) (mdomain s) (be s) ad = SOME x ->
  wordSem.mem_load_32 (stackSem.memory t) (mdomain t) (be t) ad = SOME x.
Proof.
  intros jump off k s t ad x [H E]. rewrite (state_rel_be _ _ _ _ _ H).
  unfold wordSem.mem_load_32 in *. destruct (aligned 2 ad); [|discriminate E].
  destruct (stackSem.memory s (byte_align ad)) as [v|l1 l2] eqn:Em; [|cbn in E; discriminate E].
  destruct (classical_dec (byte_align ad IN mdomain s)) as [Hd|]; [|discriminate E].
  destruct (state_rel_read _ _ _ _ _ _ (conj H Hd)) as [Hd' Et]. rewrite Et, Em.
  destruct (classical_dec _); [exact E|contradiction].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_byte_aux_IMP" *)
Local Theorem mem_load_byte_aux_IMP : forall jump off k s t ad x,
  state_rel jump off k s t /\
  wordSem.mem_load_byte_aux (stackSem.memory s) (mdomain s) (be s) ad = SOME x ->
  wordSem.mem_load_byte_aux (stackSem.memory t) (mdomain t) (be t) ad = SOME x.
Proof.
  intros jump off k s t ad x [H E]. rewrite (state_rel_be _ _ _ _ _ H).
  unfold wordSem.mem_load_byte_aux in *.
  destruct (stackSem.memory s (byte_align ad)) as [v|l1 l2] eqn:Em; [|cbn in E; discriminate E].
  destruct (classical_dec (byte_align ad IN mdomain s)) as [Hd|]; [|discriminate E].
  destruct (state_rel_read _ _ _ _ _ _ (conj H Hd)) as [Hd' Et]. rewrite Et, Em.
  destruct (classical_dec _); [exact E|contradiction].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "read_bytearray_IMP_read_bytearray" *)
Local Theorem read_bytearray_IMP_read_bytearray : forall jump off n ad k s t x,
  state_rel jump off k s t /\
  read_bytearray ad n (wordSem.mem_load_byte_aux (stackSem.memory s) (mdomain s) (be s)) = SOME x ->
  read_bytearray ad n (wordSem.mem_load_byte_aux (stackSem.memory t) (mdomain t) (be t)) = SOME x.
Proof.
  intros jump off n; induction n as [|n IH] using N.peano_ind; intros ad k s t x [H E].
  - rewrite (proj1 (read_bytearray_def _ _ 0)) in *; exact E.
  - rewrite (proj2 (read_bytearray_def _ _ n)) in E. rewrite (proj2 (read_bytearray_def _ _ n)). cbv beta in E |- *.
    revert E. destruct (wordSem.mem_load_byte_aux (stackSem.memory s) (mdomain s) (be s) ad) as [b|] eqn:Eb;
      intros E; [|discriminate E].
    rewrite (mem_load_byte_aux_IMP _ _ _ _ _ _ _ (conj H Eb)).
    revert E. destruct (read_bytearray (ad + n2w 1)%w n (wordSem.mem_load_byte_aux (stackSem.memory s) (mdomain s) (be s))) as [bs|] eqn:Ebs;
      intros E; [|discriminate E].
    rewrite (IH _ _ _ _ _ (conj H Ebs)). exact E.
Qed.

End MemLemmas.

Section WriteBytes.
Context {a : N}.
Implicit Types m : word a -> word_loc a.

Lemma read_bytearray_cons_inv (ad : word a) n (g : word a -> option word8) ys :
  read_bytearray ad (SUC n) g = SOME ys ->
  exists b bs, g ad = SOME b /\ read_bytearray (ad + n2w 1)%w n g = SOME bs.
Proof.
  rewrite (proj2 (read_bytearray_def _ _ n)). cbv beta.
  destruct (g ad) as [b|]; [|discriminate].
  destruct (read_bytearray (ad + n2w 1)%w n g) as [bs|]; [|discriminate]. eauto.
Qed.

Lemma mem_load_byte_aux_SOME m d be (ad : word a) b :
  wordSem.mem_load_byte_aux m d be ad = SOME b ->
  byte_align ad IN d /\ exists v, m (byte_align ad) = Word v.
Proof.
  unfold wordSem.mem_load_byte_aux. destruct (m (byte_align ad)) as [v|l1 l2]; [|discriminate].
  destruct (classical_dec _); [|discriminate]. eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "write_bytearray_IGNORE_non_aligned" *)
Local Theorem write_bytearray_IGNORE_non_aligned : forall m d be (b : word a) new_bytes (ad : word a),
  (forall x, b <> byte_align x) -> wordSem.write_bytearray ad new_bytes m d be b = m b.
Proof.
  intros m d be b new_bytes; induction new_bytes as [|h t IH]; intros ad Hb; [reflexivity|].
  cbn [wordSem.write_bytearray]. unfold wordSem.mem_store_byte_aux.
  destruct (wordSem.write_bytearray (ad + n2w 1)%w t m d be (byte_align ad)); [|reflexivity].
  destruct (classical_dec _); [|reflexivity].
  rewrite APPLY_UPDATE_THM. destruct (decide (byte_align ad = b)) as [E|]; [exfalso; apply (Hb ad); auto|].
  apply IH, Hb.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "write_bytearray_IGNORE" *)
Local Theorem write_bytearray_IGNORE : forall m m1 (d d1 : word a -> Prop) be new_bytes (ad : word a) x xx,
  d1 SUBSET d /\
  read_bytearray ad (LENGTH new_bytes) (wordSem.mem_load_byte_aux m1 d1 be) = SOME x /\ ~ (xx IN d1) ->
  wordSem.write_bytearray ad new_bytes m d be xx = m xx.
Proof.
  intros m m1 d d1 be new_bytes; induction new_bytes as [|h t IH]; intros ad x xx (Hs & Hr & Hx); [reflexivity|].
  rewrite LENGTH_cons_N in Hr. destruct (read_bytearray_cons_inv _ _ _ _ Hr) as (b & bs & Hb & Hbs).
  destruct (mem_load_byte_aux_SOME _ _ _ _ _ Hb) as [Hd1 _].
  cbn [wordSem.write_bytearray]. unfold wordSem.mem_store_byte_aux.
  destruct (wordSem.write_bytearray (ad + n2w 1)%w t m d be (byte_align ad)); [|reflexivity].
  destruct (classical_dec _); [|reflexivity].
  rewrite APPLY_UPDATE_THM. destruct (decide (byte_align ad = xx)) as [<-|]; [contradiction|].
  exact (IH _ _ _ (conj Hs (conj Hbs Hx))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "write_bytearray_EQ" *)
Local Theorem write_bytearray_EQ : forall (d d1 : word a -> Prop) be new_bytes (ad : word a) m1 m y x,
  d1 SUBSET d /\ (forall a0, a0 IN d1 -> m1 a0 = m a0 /\ a0 IN d) /\
  read_bytearray ad (LENGTH new_bytes) (wordSem.mem_load_byte_aux m1 d1 be) = SOME y /\ m1 x = m x ->
  wordSem.write_bytearray ad new_bytes m1 d1 be x = wordSem.write_bytearray ad new_bytes m d be x.
Proof.
  intros d d1 be new_bytes; induction new_bytes as [|h t IH]; intros ad m1 m y x (Hs & Hm & Hr & Hx); [exact Hx|].
  rewrite LENGTH_cons_N in Hr. destruct (read_bytearray_cons_inv _ _ _ _ Hr) as (b & bs & Hb & Hbs).
  destruct (mem_load_byte_aux_SOME _ _ _ _ _ Hb) as [Hd1 _].
  destruct (Hm _ Hd1) as [Hma Hd].
  assert (IHa : forall z, m1 z = m z ->
            wordSem.write_bytearray (ad + n2w 1)%w t m1 d1 be z = wordSem.write_bytearray (ad + n2w 1)%w t m d be z)
    by (intros z Hz; exact (IH _ _ _ _ _ (conj Hs (conj Hm (conj Hbs Hz))))).
  cbn [wordSem.write_bytearray]. unfold wordSem.mem_store_byte_aux.
  rewrite (IHa _ Hma).
  destruct (wordSem.write_bytearray (ad + n2w 1)%w t m d be (byte_align ad)); [|exact Hx].
  destruct (classical_dec (byte_align ad IN d1)) as [_|]; [|contradiction].
  destruct (classical_dec (byte_align ad IN d)) as [_|]; [|contradiction].
  rewrite !APPLY_UPDATE_THM. destruct (decide (byte_align ad = x)); [reflexivity|exact (IHa _ Hx)].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "write_bytearray_lemma" *)
Local Theorem write_bytearray_lemma : forall new_bytes (ad : word a) m1 d1 be x p m d,
  STAR (memory m1 d1) p (fun2set (m, d)) /\
  read_bytearray ad (LENGTH new_bytes) (wordSem.mem_load_byte_aux m1 d1 be) = SOME x ->
  STAR (memory (wordSem.write_bytearray ad new_bytes m1 d1 be) d1) p
    (fun2set (wordSem.write_bytearray ad new_bytes m d be, d)).
Proof.
  intros new_bytes ad m1 d1 be x p m d [H Hr]. apply STAR_alt in H as (u & Hu & Hmu & Hp).
  unfold memory in Hmu; subst u.
  assert (Hin : forall a0, a0 IN d1 -> m1 a0 = m a0 /\ a0 IN d).
  { intros a0 Ha. assert (Hf : fun2set (m1, d1) (a0, m1 a0)) by (apply fun2set_thm; split; [reflexivity|exact Ha]).
    apply Hu, fun2set_thm in Hf as [E Hd]. split; [symmetry; exact E|exact Hd]. }
  assert (Hs : d1 SUBSET d) by (intros a0 Ha; exact (proj2 (Hin a0 Ha))).
  assert (Weq : forall a0, a0 IN d1 ->
            wordSem.write_bytearray ad new_bytes m1 d1 be a0 = wordSem.write_bytearray ad new_bytes m d be a0)
    by (intros a0 Ha; exact (write_bytearray_EQ _ _ _ _ _ _ _ _ _ (conj Hs (conj Hin (conj Hr (proj1 (Hin a0 Ha))))))).
  apply STAR_alt. exists (fun2set (wordSem.write_bytearray ad new_bytes m1 d1 be, d1)).
  split; [|split; [reflexivity|]].
  - intros [a0 z] Hz. apply fun2set_thm in Hz as [E Ha]. apply fun2set_thm.
    split; [rewrite <- E; symmetry; apply Weq, Ha|exact (Hs _ Ha)].
  - replace (fun2set (wordSem.write_bytearray ad new_bytes m d be, d) DIFF
               fun2set (wordSem.write_bytearray ad new_bytes m1 d1 be, d1))
      with (fun2set (m, d) DIFF fun2set (m1, d1)); [exact Hp|].
    apply set_ext; intros [a0 z]. unfold pred_set.DIFF, pred_set.IN.
    rewrite !fun2set_thm. unfold pred_set.IN.
    destruct (classic (d1 a0)) as [Ha|Ha].
    + rewrite (Weq a0 Ha), (proj1 (Hin a0 Ha)).
      split; intros [[E _] Hn]; exfalso; apply Hn; (split; [exact E|exact Ha]).
    + rewrite (write_bytearray_IGNORE m m1 d d1 be new_bytes ad x a0 (conj Hs (conj Hr Ha))).
      split; intros [[E Hd] _]; (split; [split; assumption|intros [_ Ha']; exact (Ha Ha')]).
Qed.

End WriteBytes.
