(** * CakeML [stack_removeProof]: correctness of [stack_remove]

    Port of [cakeml/compiler/backend/proofs/stack_removeProofScript.sml]:
    the state relation, [comp_correct], [compile_semantics], the
    initialisation code ([init_code_thm] ... [make_init_semantics]) and
    the syntactic lemmas.

    Notes:
    - HOL's separation-logic product [p * q] is [set_sep.STAR p q]; HOL's
      binder [SEP_EXISTS x. p x] is [SEP_EXISTS (fun x => p x)].
    - HOL's [s with f := v] is [set_f v s] ([stackSem]).
    - HOL's local overload [num_stubs] is [stack_num_stubs].
    - [memory] is HOL's [memory_def]; the state field is written
      [stackSem.memory]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
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
From Galette.cakeml.semantics Require ast.
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

Section Labels.
Context {a : N}.

Lemma EMPTY_UNION_EMPTY {B} : (EMPTY : B -> Prop) UNION EMPTY = EMPTY.
Proof. sets. Qed.

Ltac lab_simpl := cbn [get_labels stack_remove.single_stack_alloc stack_remove.single_stack_free
                       stack_remove.halt_inst]; rewrite ?EMPTY_UNION_EMPTY.

Lemma get_labels_stack_alloc_f : forall f jump k n,
  get_labels (@stack_remove.stack_alloc_f a f jump k n) = EMPTY.
Proof.
  induction f as [|f IH]; intros jump k n; cbn [stack_remove.stack_alloc_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|]. destruct (n <=? stack_remove.max_stack_alloc);
    lab_simpl; [destruct jump; lab_simpl; reflexivity|].
  rewrite IH. destruct jump; lab_simpl; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_stack_alloc" *)
Local Theorem get_labels_stack_alloc : forall jump k n, get_labels (@stack_remove.stack_alloc a jump k n) = EMPTY.
Proof. intros; apply get_labels_stack_alloc_f. Qed.

Lemma get_labels_stack_free_f : forall f k n, get_labels (@stack_remove.stack_free_f a f k n) = EMPTY.
Proof.
  induction f as [|f IH]; intros k n; cbn [stack_remove.stack_free_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|]. destruct (n <=? stack_remove.max_stack_alloc); lab_simpl; [reflexivity|].
  rewrite IH; lab_simpl; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_stack_free" *)
Local Theorem get_labels_stack_free : forall k n, get_labels (@stack_remove.stack_free a k n) = EMPTY.
Proof. intros; apply get_labels_stack_free_f. Qed.

Lemma get_labels_upshift_f : forall f r n, get_labels (@stack_remove.upshift_f a f r n) = EMPTY.
Proof.
  induction f as [|f IH]; intros r n; cbn [stack_remove.upshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); lab_simpl; [reflexivity|]. rewrite IH; lab_simpl; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_upshift" *)
Local Theorem get_labels_upshift : forall n n0, get_labels (@stack_remove.upshift a n n0) = EMPTY.
Proof. intros; apply get_labels_upshift_f. Qed.

Lemma get_labels_downshift_f : forall f r n, get_labels (@stack_remove.downshift_f a f r n) = EMPTY.
Proof.
  induction f as [|f IH]; intros r n; cbn [stack_remove.downshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); lab_simpl; [reflexivity|]. rewrite IH; lab_simpl; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_downshift" *)
Local Theorem get_labels_downshift : forall n n0, get_labels (@stack_remove.downshift a n n0) = EMPTY.
Proof. intros; apply get_labels_downshift_f. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_labels_comp" *)
Theorem get_labels_comp : forall jump off k (e : prog a),
  get_labels (stack_remove.comp jump off k e) = get_labels e.
Proof.
  intros jump off k e.
  induction e as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|reflexivity].
    destruct h as [[p2 [k1 k2]]|]; cbn [stack_remove.comp get_labels];
      rewrite (Hr p1 _ eq_refl); [rewrite (Hh p2 _ eq_refl)|]; reflexivity.
  - cbn [stack_remove.comp get_labels]; rewrite IH1, IH2; reflexivity.
  - cbn [stack_remove.comp get_labels]; rewrite IH1, IH2; reflexivity.
  - cbn [stack_remove.comp get_labels]; exact IH.
  - destruct p; try contradiction; cbn [stack_remove.comp]; try reflexivity.
    all: repeat (match goal with |- context [if ?b then _ else _] => destruct b end);
         cbn [get_labels stack_remove.stack_store stack_remove.stack_load stack_remove.copy_loop
              stack_remove.copy_each list_Seq];
         rewrite ?get_labels_stack_alloc, ?get_labels_stack_free, ?get_labels_upshift,
                 ?get_labels_downshift, ?EMPTY_UNION_EMPTY; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "code_rel_loc_check" *)
Theorem code_rel_loc_check : forall jump off k (c1 c2 : spt (prog a)) l1 l2,
  code_rel jump off k c1 c2 /\ loc_check c1 (l1, l2) -> loc_check c2 (l1, l2).
Proof.
  intros jump off k c1 c2 l1 l2 [[Hc Hd] Hl]. unfold loc_check in *.
  destruct Hl as [[-> Hin]|(n & e & He & Hin)].
  - left; split; [reflexivity|]. rewrite Hd. left; exact Hin.
  - right. destruct (Hc _ _ He) as [_ He']. exists n, (stack_remove.comp jump off k e).
    split; [exact He'|rewrite get_labels_comp; exact Hin].
Qed.

End Labels.

Section Syntax.
Context {a : N}.

Lemma In_store_list_Temp n : n < 32 -> In (Temp (n2w n)) stack_remove.store_list.
Proof.
  intros H. assert (Hd : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31) by lia.
  unfold stack_remove.store_list.
  repeat (destruct Hd as [->|Hd]; [cbn [In]; repeat (first [left; reflexivity|right])|]).
  subst n; cbn [In]; repeat (first [left; reflexivity|right]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "name_cases" *)
Local Theorem name_cases : forall name, name <> CurrHeap -> MEM name stack_remove.store_list.
Proof.
  intros name H; apply MEM_In. destruct name; try (exfalso; apply H; reflexivity).
  all: try (unfold stack_remove.store_list; cbn [In]; repeat (first [left; reflexivity|right]); fail).
  rewrite <- (n2w_w2n w). apply In_store_list_Temp.
  pose proof (w2n_lt w) as Hl. exact Hl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "prog_comp_eta" *)
Theorem prog_comp_eta : @stack_remove.prog_comp a = fun jump off k '(n, p) => (n, stack_remove.comp jump off k p).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "FST_prog_comp" *)
Theorem FST_prog_comp : forall jump off k (pp : N * prog a), FST (stack_remove.prog_comp jump off k pp) = FST pp.
Proof. intros jump off k [n p]; reflexivity. Qed.

End Syntax.

Section SyntaxThms.
Context {a : N}.

Lemma extract_labels_alloc_f : forall f jump k n,
  extract_labels (@stack_remove.stack_alloc_f a f jump k n) = [].
Proof.
  induction f as [|f IH]; intros jump k n; cbn [stack_remove.stack_alloc_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_alloc stack_remove.halt_inst];
    destruct jump; cbn [extract_labels app]; rewrite ?IH; reflexivity.
Qed.

Lemma extract_labels_free_f : forall f k n, extract_labels (@stack_remove.stack_free_f a f k n) = [].
Proof.
  induction f as [|f IH]; intros k n; cbn [stack_remove.stack_free_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [stack_remove.single_stack_free extract_labels app];
    rewrite ?IH; reflexivity.
Qed.

Lemma extract_labels_upshift_f : forall f r n, extract_labels (@stack_remove.upshift_f a f r n) = [].
Proof.
  induction f as [|f IH]; intros r n; cbn [stack_remove.upshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [extract_labels app]; rewrite ?IH; reflexivity.
Qed.

Lemma extract_labels_downshift_f : forall f r n, extract_labels (@stack_remove.downshift_f a f r n) = [].
Proof.
  induction f as [|f IH]; intros r n; cbn [stack_remove.downshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [extract_labels app]; rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_remove_lab_pres" *)
Theorem stack_remove_lab_pres : forall jump off k (p : prog a),
  extract_labels p = extract_labels (stack_remove.comp jump off k p).
Proof.
  intros jump off k p.
  induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|reflexivity].
    destruct h as [[p2 [k1 k2]]|]; cbn [stack_remove.comp extract_labels];
      rewrite <- (Hr p1 _ eq_refl); [rewrite <- (Hh p2 _ eq_refl)|]; reflexivity.
  - cbn [stack_remove.comp extract_labels]; rewrite <- IH1, <- IH2; reflexivity.
  - cbn [stack_remove.comp extract_labels]; rewrite <- IH1, <- IH2; reflexivity.
  - cbn [stack_remove.comp extract_labels]; exact IH.
  - destruct p; try contradiction; cbn [stack_remove.comp]; try reflexivity.
    all: repeat (match goal with |- context [if ?b then _ else _] => destruct b end);
         unfold stack_remove.stack_store, stack_remove.stack_load, stack_remove.copy_loop,
                stack_remove.copy_each, stack_remove.stack_alloc, stack_remove.stack_free,
                stack_remove.upshift, stack_remove.downshift; cbn [list_Seq];
         cbn [extract_labels app];
         rewrite ?extract_labels_alloc_f, ?extract_labels_free_f, ?extract_labels_upshift_f,
                 ?extract_labels_downshift_f; cbn [app]; reflexivity.
Qed.

Lemma call_args_upshift_f : forall f r n, call_args (@stack_remove.upshift_f a f r n) 1 2 3 4 0 = true.
Proof.
  induction f as [|f IH]; intros r n; cbn [stack_remove.upshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [call_args andb]; rewrite ?IH; reflexivity.
Qed.

Lemma call_args_downshift_f : forall f r n, call_args (@stack_remove.downshift_f a f r n) 1 2 3 4 0 = true.
Proof.
  induction f as [|f IH]; intros r n; cbn [stack_remove.downshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [call_args andb]; rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "upshift_downshift_call_args" *)
Theorem upshift_downshift_call_args : forall n n0,
  call_args (@stack_remove.upshift a n n0) 1 2 3 4 0 /\ call_args (@stack_remove.downshift a n n0) 1 2 3 4 0.
Proof. intros; split; [apply call_args_upshift_f|apply call_args_downshift_f]. Qed.

End SyntaxThms.

Section CallArgs.
Context {a : N}.

Lemma call_args_alloc_f : forall f jump k n, call_args (@stack_remove.stack_alloc_f a f jump k n) 1 2 3 4 0 = true.
Proof.
  induction f as [|f IH]; intros jump k n; cbn [stack_remove.stack_alloc_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); destruct jump; cbn [call_args andb]; rewrite ?IH; reflexivity.
Qed.

Lemma call_args_free_f : forall f k n, call_args (@stack_remove.stack_free_f a f k n) 1 2 3 4 0 = true.
Proof.
  induction f as [|f IH]; intros k n; cbn [stack_remove.stack_free_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc); cbn [call_args andb]; rewrite ?IH; reflexivity.
Qed.

Lemma call_args_comp jump off k : forall p : prog a,
  call_args p 1 2 3 4 0 = true -> call_args (stack_remove.comp jump off k p) 1 2 3 4 0 = true.
Proof.
  intros p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros H.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|exact H].
    destruct h as [[p2 [k1 k2]]|]; cbn [stack_remove.comp call_args] in H |- *;
      repeat (match goal with Hx : (_ && _) = true |- _ => apply andb_true_iff in Hx as [? ?] end);
      repeat (apply andb_true_iff; split); try assumption;
      first [apply (Hr p1 _ eq_refl); assumption|apply (Hh p2 _ eq_refl); assumption].
  - cbn [stack_remove.comp call_args] in H |- *; apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff; split; [apply IH1, H1|apply IH2, H2].
  - cbn [stack_remove.comp call_args] in H |- *; apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff; split; [apply IH1, H1|apply IH2, H2].
  - cbn [stack_remove.comp call_args] in H |- *; apply IH, H.
  - destruct p; try contradiction; cbn [stack_remove.comp]; try exact H.
    all: repeat (match goal with |- context [if ?b then _ else _] => destruct b end);
         unfold stack_remove.stack_store, stack_remove.stack_load, stack_remove.copy_loop,
                stack_remove.copy_each, stack_remove.stack_alloc, stack_remove.stack_free,
                stack_remove.upshift, stack_remove.downshift; cbn [list_Seq call_args andb];
         rewrite ?call_args_alloc_f, ?call_args_free_f, ?call_args_upshift_f, ?call_args_downshift_f;
         reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_remove_call_args" *)
Theorem stack_remove_call_args : forall jump off gen_gc n k pos (p p' : list (N * prog a)),
  stack_remove.compile jump off gen_gc n k pos p = p' /\
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND p) ->
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND p').
Proof.
  intros jump off gen_gc n k pos p p' [<- H]. unfold stack_remove.compile, is_true in *.
  unfold stack_remove.init_stubs; cbn [app MAP EVERY SND].
  do 3 (match goal with |- (?x && _)%bool = true => replace x with true by reflexivity end; cbn [andb]).
  induction p as [|[m q] p IH]; [reflexivity|].
  cbn [MAP EVERY SND stack_remove.prog_comp] in H |- *. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff; split; [apply call_args_comp, H1|apply IH, H2].
Qed.

End CallArgs.


(** ** Galette-only helpers *)

Lemma LENGTH_app_N {A} (l1 l2 : list A) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. rewrite !LENGTH_length, length_app; lia. Qed.

Lemma EL_LENGTH_APPEND_N {A} `{Inhabited A} (ys zs : list A) z : EL (LENGTH ys) (ys ++ z :: zs) = z.
Proof.
  induction ys as [|y ys IH]; [reflexivity|].
  cbn [app]. rewrite LENGTH_cons_N, EL_SUC. exact IH.
Qed.

Lemma LUPDATE_LENGTH_APPEND_N {A} (ys zs : list A) z v :
  LUPDATE v (LENGTH ys) (ys ++ z :: zs) = ys ++ v :: zs.
Proof.
  induction ys as [|y ys IH]; [reflexivity|].
  cbn [app]. rewrite LENGTH_cons_N, (proj2 (proj2 (LUPDATE_def))), IH. reflexivity.
Qed.

Section SepHelpers.
Context {A B : Type}.
Implicit Types p q r : (A -> Prop) -> Prop.

Lemma STAR_mono p p' q s : (forall u, p u -> p' u) -> STAR p q s -> STAR p' q s.
Proof. intros H Hs; apply STAR_alt in Hs as (u & Hu & Hp & Hq); apply STAR_alt; eauto. Qed.

Lemma STAR_rot3 p q r : STAR (STAR p q) r = STAR q (STAR r p).
Proof. rewrite (STAR_COMM p q), <- STAR_ASSOC, (STAR_COMM p r). reflexivity. Qed.

Lemma STAR_swap_l p q r : STAR p (STAR q r) = STAR q (STAR p r).
Proof. rewrite STAR_ASSOC, (STAR_COMM p q), <- STAR_ASSOC; reflexivity. Qed.

End SepHelpers.

Section Fun2setHelpers.
Context {A B : Type} `{EqDecision B}.

(** Read through a separation assertion headed by a single cell. *)
Lemma sep_read (d : B -> Prop) ad (x : A) p f :
  STAR (one (ad, x)) p (fun2set (f, d)) -> f ad = x /\ ad IN d.
Proof. intros Hs; apply one_fun2set in Hs as (H1 & H2 & _); auto. Qed.

(** Write through a separation assertion headed by a single cell. *)
Lemma sep_write (d : B -> Prop) ad (x y : A) p f :
  STAR (one (ad, x)) p (fun2set (f, d)) -> STAR (one (ad, y)) p (fun2set ((ad =+ y) f, d)).
Proof. intros Hs; rewrite STAR_COMM; exact (write_fun2set d y ad x p f Hs). Qed.

End Fun2setHelpers.

Section Batch1.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Local Open Scope word_scope.

Lemma bytes_in_word_shift (Hg : good_dimindex a) : (bytes_in_word : word a) = n2w (2 ** word_shift a).
Proof. unfold bytes_in_word, word_shift. destruct Hg as [E|E]; rewrite E; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "bytes_in_word_word_shift" *)
Theorem bytes_in_word_word_shift : forall n : word a,
  good_dimindex a /\ (w2n (bytes_in_word : word a) * w2n n < dimword a)%N ->
  (bytes_in_word * n) >>> word_shift a = n.
Proof.
  intros n [Hg Hb]. rewrite (bytes_in_word_shift Hg) in *.
  assert (Hp : (2 ** word_shift a < dimword a)%N).
  { rewrite dimword_pow. apply N.pow_lt_mono_r; [lia|]. unfold word_shift.
    destruct Hg as [E|E]; rewrite E; cbn; lia. }
  rewrite w2n_n2w, N.mod_small in Hb by exact Hp.
  apply word_eq_w2n. rewrite w2n_lsr. unfold word_mul. rewrite w2n_n2w, (w2n_n2w (2 ** word_shift a)).
  rewrite (N.mod_small (2 ** word_shift a)) by exact Hp.
  rewrite N.mod_small by exact Hb. rewrite N.mul_comm, N.div_mul; [reflexivity|].
  apply N.pow_nonzero; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "lsl_word_shift" *)
Theorem lsl_word_shift : forall w : word a, good_dimindex a -> w << word_shift a = w * bytes_in_word.
Proof. intros w Hg. rewrite WORD_MUL_LSL, (bytes_in_word_shift Hg). word_ring. Qed.

End Batch1.


Section Batch2.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

(** Galette-only: [state_rel] with its memory assertion split off the
    first conjuncts. *)
Ltac sr_destr H :=
  unfold state_rel in H; cbv zeta in H; destruct_ands;
  match goal with
  | Hm : match FLOOKUP (regs ?t) (?k + 1) with _ => _ end |- _ =>
      let E := fresh "Ebase" in let base := fresh "base" in
      destruct (FLOOKUP (regs t) (k + 1)) as [[base|]|] eqn:E; try contradiction;
      destruct_ands
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_get_var_k" *)
Theorem state_rel_get_var_k : forall jump off k s t,
  state_rel jump off k s t ->
  exists c0 : word a,
    get_var (k + 1) t = SOME (Word c0) /\
    dimindex a DIV 8 * stack_remove.max_stack_alloc <= w2n c0 /\
    w2n c0 + w2n (bytes_in_word : word a) * LENGTH (stack s) < dimword a /\
    get_var k t = SOME (Word (c0 + bytes_in_word * n2w (stack_space s))%w) /\
    STAR (STAR (STAR (STAR (memory (stackSem.memory s) (mdomain s))
        (word_list (the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a)%w
           (MAP Word (bitmaps s) ++ MAP Word (wordSem.buffer_buffer (data_buffer s)))))
        (word_list_exists ((the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a) +
             bytes_in_word * n2w (LENGTH (wordSem.buffer_buffer (data_buffer s)) + LENGTH (bitmaps s)))%w
           (wordSem.space_left (data_buffer s))))
        (word_store c0 (store s)))
      (word_list c0 (stack s))
      (fun2set (stackSem.memory t, mdomain t)).
Proof.
  intros jump off k s t H. sr_destr H.
  exists base. unfold get_var. rewrite Ebase. repeat split; try assumption.
  all: try (rewrite <- map_app, N.add_comm, <- LENGTH_app_N; assumption).
Qed.

Lemma store_list_no_CurrHeap : ~ In CurrHeap stack_remove.store_list.
Proof. unfold stack_remove.store_list; cbn [In]; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_store_CurrHeap" *)
Local Theorem word_store_CurrHeap : forall (base : word a) s x,
  word_store base (store s |+ (CurrHeap, x)) = word_store base (store s).
Proof.
  intros base s x. unfold word_store. apply (f_equal (word_list_rev base)). apply map_ext_in. intros name Hin.
  rewrite FLOOKUP_UPDATE. destruct (decide (CurrHeap = name)) as [<-|]; [|reflexivity].
  exfalso; exact (store_list_no_CurrHeap Hin).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_load_imp" *)
Theorem state_rel_mem_load_imp : forall jump off k s t x w,
  state_rel jump off k s t /\ mem_load x s = SOME w -> mem_load x t = SOME w.
Proof.
  intros jump off k s t x w [H E]. unfold mem_load in *.
  destruct (classical_dec (x IN mdomain s)) as [Hd|]; [|discriminate E].
  destruct (state_rel_read _ _ _ _ _ _ (conj H Hd)) as [Hd' Et].
  destruct (classical_dec (x IN mdomain t)) as [_|]; [|contradiction].
  rewrite Et; exact E.
Qed.

Lemma exp_nested_ind (P : wordLang.exp a -> Prop) :
  (forall w, P (wordLang.Const w)) -> (forall n, P (wordLang.Var n)) ->
  (forall nm, P (wordLang.Lookup nm)) -> (forall e, P e -> P (wordLang.Load e)) ->
  (forall op l, Forall P l -> P (wordLang.Op op l)) ->
  (forall sh e1 e2, P e1 -> P e2 -> P (wordLang.Shift sh e1 e2)) -> forall e, P e.
Proof.
  intros HC HV HL HLd HO HS.
  exact (fix IH e := match e with
    | wordLang.Const w => HC w | wordLang.Var n => HV n | wordLang.Lookup nm => HL nm
    | wordLang.Load e => HLd e (IH e)
    | wordLang.Op op l => HO op l ((fix go l : Forall P l :=
         match l with [] => Forall_nil _ | x :: l => Forall_cons _ (IH x) (go l) end) l)
    | wordLang.Shift sh e1 e2 => HS sh e1 e2 (IH e1) (IH e2) end).
Qed.

Lemma state_rel_regs jump off k s t n :
  state_rel jump off k s t -> n < k -> FLOOKUP (regs t) n = FLOOKUP (regs s) n.
Proof. intros H Hn; unfold state_rel in H; destruct_ands; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_word_exp" *)
Theorem state_rel_word_exp : forall jump off k t s e w,
  state_rel jump off k s t /\ reg_bound_exp e k /\ word_exp s e = SOME w ->
  word_exp t e = SOME w.
Proof.
  intros jump off k t s e. revert e.
  enough (G : forall e, forall w, state_rel jump off k s t -> reg_bound_exp e k = true ->
                word_exp s e = SOME w -> word_exp t e = SOME w)
    by (intros e w (H1 & H2 & H3); exact (G e w H1 H2 H3)).
  induction e as [w0|n|nm|e IH|op l IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros w H Hb He; cbn [word_exp reg_bound_exp] in Hb, He |- *.
  - exact He.
  - apply N.ltb_lt in Hb. rewrite (state_rel_regs _ _ _ _ _ _ H Hb). exact He.
  - discriminate Hb.
  - destruct (word_exp s e) as [w1|] eqn:E1; [|discriminate He].
    rewrite (IH w1 H Hb eq_refl).
    destruct (mem_load w1 s) as [v|] eqn:Em; [|discriminate He].
    rewrite (state_rel_mem_load_imp _ _ _ _ _ _ _ (conj H Em)). exact He.
  - cbv zeta in He |- *.
    assert (Hm : EVERY IS_SOME (MAP (word_exp s) l) = true ->
                 MAP (word_exp t) l = MAP (word_exp s) l).
    { clear He. induction l as [|e l IHl]; intros Hs; [reflexivity|].
      cbn [MAP EVERY] in Hb, Hs |- *. apply andb_true_iff in Hb as [Hb1 Hb2].
      apply andb_true_iff in Hs as [Hs1 Hs2]. inversion IH as [|? ? IHe IHr]; subst.
      rewrite (IHl IHr Hb2 Hs2). f_equal.
      destruct (word_exp s e) as [v|] eqn:Ev; [|discriminate Hs1].
      exact (IHe v H Hb1 eq_refl). }
    destruct (EVERY IS_SOME (MAP (word_exp s) l)) eqn:Ee; [|discriminate He].
    rewrite (Hm eq_refl), Ee. exact He.
  - apply andb_true_iff in Hb as [Hb1 Hb2].
    destruct (word_exp s e1) as [w1|] eqn:E1; [|discriminate He].
    destruct (word_exp s e2) as [w2|] eqn:E2; [|discriminate He].
    rewrite (IH1 w1 H Hb1 eq_refl), (IH2 w2 H Hb2 eq_refl). exact He.
Qed.

(** Galette-only: the memory assertion is preserved by any update that
    agrees with the new abstract memory on its domain and leaves the rest. *)
Lemma memory_frame (sm m sm' m' : word a -> word_loc a) sd dm p :
  STAR (memory sm sd) p (fun2set (m, dm)) ->
  (forall b, b IN sd -> m' b = sm' b) -> (forall b, ~ b IN sd -> m' b = m b) ->
  STAR (memory sm' sd) p (fun2set (m', dm)).
Proof.
  intros H Hin Hout.
  assert (Hag : forall b, b IN sd -> b IN dm /\ m b = sm b)
    by (intros b Hb; exact (memory_fun2set_IMP_read _ _ _ _ _ _ (conj H Hb))).
  apply STAR_alt in H as (u & Hu & Hmu & Hp). unfold memory in Hmu; subst u.
  apply STAR_alt. exists (fun2set (sm', sd)). split; [|split; [reflexivity|]].
  - intros [b z] Hz. apply fun2set_thm in Hz as [E Hb]. apply fun2set_thm.
    split; [rewrite Hin by exact Hb; exact E|exact (proj1 (Hag b Hb))].
  - replace (fun2set (m', dm) DIFF fun2set (sm', sd)) with (fun2set (m, dm) DIFF fun2set (sm, sd)); [exact Hp|].
    apply set_ext; intros [b z]. unfold pred_set.DIFF, pred_set.IN.
    rewrite !fun2set_thm. unfold pred_set.IN.
    destruct (classic (sd b)) as [Hb|Hb].
    + destruct (Hag b Hb) as [_ E1]. rewrite (Hin b Hb), E1.
      split; intros [[E _] Hn]; exfalso; apply Hn; (split; [exact E|exact Hb]).
    + rewrite (Hout b Hb).
      split; intros [[E Hd] _]; (split; [split; assumption|intros [_ Hb']; exact (Hb Hb')]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_write" *)
Theorem memory_write : forall (x : word a) sd dm sm p m y,
  x IN sd /\ x IN dm /\ STAR (memory sm sd) p (fun2set (m, dm)) ->
  STAR (memory ((x =+ y) sm) sd) p (fun2set ((x =+ y) m, dm)).
Proof.
  intros x sd dm sm p m y (Hx & _ & H).
  apply (memory_frame _ _ _ _ _ _ _ H).
  - intros b Hb. rewrite !APPLY_UPDATE_THM. destruct (decide (x = b)); [reflexivity|].
    exact (proj2 (memory_fun2set_IMP_read _ _ _ _ _ _ (conj H Hb))).
  - intros b Hb. rewrite APPLY_UPDATE_THM. destruct (decide (x = b)) as [<-|]; [contradiction|reflexivity].
Qed.

Lemma sr_mem_assoc (M W1 W2 S L : (word a * word_loc a -> Prop) -> Prop) :
  STAR (STAR (STAR (STAR M W1) W2) S) L = STAR M (STAR (STAR (STAR W1 W2) S) L).
Proof. rewrite !STAR_ASSOC. reflexivity. Qed.

(** Galette-only: [state_rel] after the same memory write on both sides. *)
Lemma state_rel_write jump off k s t x y :
  state_rel jump off k s t -> x IN mdomain s ->
  state_rel jump off k (set_memory ((x =+ y) (stackSem.memory s)) s)
                       (set_memory ((x =+ y) (stackSem.memory t)) t).
Proof.
  intros H Hx. pose proof (state_rel_read _ _ _ _ _ _ (conj H Hx)) as [Hxt _].
  unfold state_rel in *; cbv zeta in *; stk_fields.
  destruct_ands. repeat (split; [assumption|]).
  destruct (FLOOKUP (regs t) (k + 1)) as [[base|]|]; try contradiction.
  destruct_ands. repeat (split; [assumption|]).
  rewrite sr_mem_assoc in *. apply memory_write. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_store" *)
Theorem state_rel_mem_store : forall jump off k s t x y s' t',
  state_rel jump off k s t /\ mem_store x y s = SOME s' /\ mem_store x y t = SOME t' ->
  state_rel jump off k s' t'.
Proof.
  intros jump off k s t x y s' t' (H & Es & Et). unfold mem_store in Es, Et.
  destruct (classical_dec (x IN mdomain s)) as [Hx|]; [|discriminate Es].
  destruct (classical_dec (x IN mdomain t)); [|discriminate Et].
  injection Es as <-; injection Et as <-. apply state_rel_write; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_store_32" *)
Theorem state_rel_mem_store_32 : forall jump off k s t (ad : word a) b z,
  state_rel jump off k s t /\ wordSem.mem_store_32 (stackSem.memory s) (mdomain s) (be s) ad b = SOME z ->
  exists y, wordSem.mem_store_32 (stackSem.memory t) (mdomain t) (be t) ad b = SOME y /\
    state_rel jump off k (set_memory z s) (set_memory y t).
Proof.
  intros jump off k s t ad b z [H E]. rewrite (state_rel_be _ _ _ _ _ H).
  unfold wordSem.mem_store_32 in *. destruct (aligned 2 ad); [|discriminate E].
  destruct (stackSem.memory s (byte_align ad)) as [v|l1 l2] eqn:Em; [|discriminate E].
  destruct (classical_dec (byte_align ad IN mdomain s)) as [Hd|]; [|discriminate E].
  destruct (state_rel_read _ _ _ _ _ _ (conj H Hd)) as [Hd' Et]. rewrite Et, Em.
  destruct (classical_dec _); [|contradiction].
  injection E as <-. eexists; split; [reflexivity|]. apply state_rel_write; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_mem_store_byte_aux" *)
Theorem state_rel_mem_store_byte_aux : forall jump off k s t (ad : word a) b z,
  state_rel jump off k s t /\ wordSem.mem_store_byte_aux (stackSem.memory s) (mdomain s) (be s) ad b = SOME z ->
  exists y, wordSem.mem_store_byte_aux (stackSem.memory t) (mdomain t) (be t) ad b = SOME y /\
    state_rel jump off k (set_memory z s) (set_memory y t).
Proof.
  intros jump off k s t ad b z [H E]. rewrite (state_rel_be _ _ _ _ _ H).
  unfold wordSem.mem_store_byte_aux in *.
  destruct (stackSem.memory s (byte_align ad)) as [v|l1 l2] eqn:Em; [|discriminate E].
  destruct (classical_dec (byte_align ad IN mdomain s)) as [Hd|]; [|discriminate E].
  destruct (state_rel_read _ _ _ _ _ _ (conj H Hd)) as [Hd' Et]. rewrite Et, Em.
  destruct (classical_dec _); [|contradiction].
  injection E as <-. eexists; split; [reflexivity|]. apply state_rel_write; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_get_fp_var" *)
Local Theorem state_rel_get_fp_var : forall jump off k s t n,
  state_rel jump off k s t -> get_fp_var n s = get_fp_var n t.
Proof. intros jump off k s t n H; unfold state_rel in H; destruct_ands; unfold get_fp_var; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_set_fp_var" *)
Local Theorem state_rel_set_fp_var : forall jump off k s t n v,
  state_rel jump off k s t -> state_rel jump off k (set_fp_var n v s) (set_fp_var n v t).
Proof.
  intros jump off k s t n v H. unfold state_rel, set_fp_var in *; cbv zeta in *; stk_fields.
  destruct_ands. repeat (split; [try congruence; assumption|]). assumption.
Qed.

End Batch2.


Section Batch3.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

Lemma sr_get_var jump off k s t n :
  state_rel jump off k s t -> n < k -> get_var n t = get_var n s.
Proof. intros H Hn; unfold get_var; exact (state_rel_regs _ _ _ _ _ _ H Hn). Qed.

Lemma sr_exp_addr jump off k s t ad w :
  state_rel jump off k s t -> ad < k ->
  word_exp t (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) =
  word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]).
Proof. intros H Hn; cbn [word_exp MAP]; rewrite (state_rel_regs _ _ _ _ _ _ H Hn); reflexivity. Qed.

Ltac ltb_facts :=
  repeat match goal with
  | Hx : (_ && _) = true |- _ => apply andb_true_iff in Hx as [? ?]
  | Hx : is_true (_ && _) |- _ => apply andb_true_iff in Hx as [? ?]
  | Hx : (_ <? _) = true |- _ => apply N.ltb_lt in Hx
  | Hx : is_true (_ <? _) |- _ => apply N.ltb_lt in Hx
  end.

Ltac sr_inst_rw H :=
  match type of H with state_rel _ _ _ ?s ?t =>
  repeat first
    [ rewrite <- (state_rel_get_fp_var _ _ _ s t _ H)
    | match goal with |- context [get_var ?n t] => rewrite (sr_get_var _ _ _ s t n H) by lia end
    | match goal with |- context [FLOOKUP (regs t) ?n] => rewrite (state_rel_regs _ _ _ s t n H) by lia end
    | match goal with |- context [word_exp t (wordLang.Op asm.Add [wordLang.Var ?ad; wordLang.Const ?w])] =>
        rewrite (sr_exp_addr _ _ _ s t ad w H) by lia end ]
  end.

Ltac sr_sv H :=
  repeat first [ apply state_rel_set_fp_var | apply state_rel_set_var; split; [|lia] ]; exact H.

Ltac sr_fin H He :=
  stk_split He; try discriminate He; injection He as <-;
  eexists; (split; [reflexivity|sr_sv H]).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_inst" *)
Theorem state_rel_inst : forall jump off k s t (i : asm.inst a) s',
  state_rel jump off k s t /\ reg_bound_inst i k /\ inst i s = SOME s' ->
  exists t', inst i t = SOME t' /\ state_rel jump off k s' t'.
Proof.
  intros jump off k s t i s' (H & Hb & He).
  destruct i as [|r w|x|m r [ad w]|x]; cbn [reg_bound_inst] in Hb; unfold is_true in Hb; ltb_facts.
  - cbn [inst] in He; injection He as <-; exists t; split; [reflexivity|exact H].
  - cbn [inst assign word_exp] in He |- *. sr_fin H He.
  - destruct x as [bop r1 r2 ri|sh r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4];
      cbn [reg_bound_inst] in Hb; ltb_facts; cbn [inst] in He |- *.
    + destruct (bool_decide (bop = asm.Or) && bool_decide (ri = Reg r2))%bool eqn:Eb.
      * sr_inst_rw H. sr_fin H He.
      * unfold assign in *.
        destruct (word_exp s (wordLang.Op bop [wordLang.Var r2;
                    match ri with Reg r3 => wordLang.Var r3 | Imm w => wordLang.Const w end])) as [v|] eqn:Ew;
          [|discriminate He].
        rewrite (state_rel_word_exp jump off k t s _ v); [sr_fin H He|].
        split; [exact H|split; [|exact Ew]].
        destruct ri as [r3|w]; cbn [reg_bound_exp EVERY]; ltb_facts;
          rewrite ?(proj2 (N.ltb_lt _ _)) by lia; reflexivity.
    + unfold assign in *.
      destruct (word_exp s (wordLang.Shift sh (wordLang.Var r2)
                  match ri with Reg r3 => wordLang.Var r3 | Imm w => wordLang.Const w end)) as [v|] eqn:Ew;
        [|discriminate He].
      rewrite (state_rel_word_exp jump off k t s _ v); [sr_fin H He|].
      split; [exact H|split; [|exact Ew]].
      destruct ri as [r3|w]; cbn [reg_bound_exp]; ltb_facts;
        rewrite ?(proj2 (N.ltb_lt _ _)) by lia; reflexivity.
    + cbn [get_vars] in He |- *. sr_inst_rw H. sr_fin H He.
    + cbn [get_vars] in He |- *. sr_inst_rw H. sr_fin H He.
    + cbn [get_vars] in He |- *. sr_inst_rw H. sr_fin H He.
    + cbn [get_vars] in He |- *. sr_inst_rw H. sr_fin H He.
    + cbn [get_vars] in He |- *. sr_inst_rw H. sr_fin H He.
    + cbn [get_vars] in He |- *. sr_inst_rw H. sr_fin H He.
  - destruct m; cbn [inst] in He |- *; sr_inst_rw H; try discriminate He.
    + destruct (word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [x|]; [|discriminate He].
      destruct (mem_load x s) as [v|] eqn:Em; [|discriminate He].
      rewrite (state_rel_mem_load_imp _ _ _ _ _ _ _ (conj H Em)). sr_fin H He.
    + destruct (word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [x|]; [|discriminate He].
      destruct (wordSem.mem_load_byte_aux (stackSem.memory s) (mdomain s) (be s) x) as [v|] eqn:Em;
        [|discriminate He].
      rewrite (mem_load_byte_aux_IMP _ _ _ _ _ _ _ (conj H Em)). sr_fin H He.
    + destruct (word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [x|]; [|discriminate He].
      destruct (wordSem.mem_load_32 (stackSem.memory s) (mdomain s) (be s) x) as [v|] eqn:Em;
        [|discriminate He].
      rewrite (mem_load_32_IMP _ _ _ _ _ _ _ (conj H Em)). sr_fin H He.
    + destruct (word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [x|]; [|discriminate He].
      destruct (get_var r s) as [v|]; [|discriminate He].
      destruct (mem_store x v s) as [s1|] eqn:Es; [|discriminate He]. injection He as <-.
      assert (Hx : x IN mdomain s) by (unfold mem_store in Es; destruct (classical_dec _); [assumption|discriminate]).
      destruct (state_rel_read _ _ _ _ _ _ (conj H Hx)) as [Hxt _].
      assert (Et : mem_store x v t = SOME (set_memory ((x =+ v) (stackSem.memory t)) t))
        by (unfold mem_store; destruct (classical_dec _); [reflexivity|contradiction]).
      rewrite Et. eexists; split; [reflexivity|].
      exact (state_rel_mem_store jump off k s t x v _ _ (conj H (conj Es Et))).
    + destruct (word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [x|]; [|discriminate He].
      destruct (get_var r s) as [[v|]|]; try discriminate He.
      destruct (wordSem.mem_store_byte_aux (stackSem.memory s) (mdomain s) (be s) x (w2w v)) as [m1|] eqn:Es;
        [|discriminate He]. injection He as <-.
      destruct (state_rel_mem_store_byte_aux _ _ _ _ _ _ _ _ (conj H Es)) as (y & Ey & Hy).
      rewrite Ey. eexists; split; [reflexivity|exact Hy].
    + destruct (word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [x|]; [|discriminate He].
      destruct (get_var r s) as [[v|]|]; try discriminate He.
      destruct (wordSem.mem_store_32 (stackSem.memory s) (mdomain s) (be s) x (w2w v)) as [m1|] eqn:Es;
        [|discriminate He]. injection He as <-.
      destruct (state_rel_mem_store_32 _ _ _ _ _ _ _ _ (conj H Es)) as (y & Ey & Hy).
      rewrite Ey. eexists; split; [reflexivity|exact Hy].
  - destruct x; cbn [inst reg_bound_inst] in He, Hb |- *; ltb_facts; sr_inst_rw H; sr_fin H He.
Qed.

End Batch3.


(** ** Galette-only: small evaluation lemmas *)

Lemma bd_false (P : Prop) {d : Decision P} : ~ P -> bool_decide P = false.
Proof. intros H; unfold bool_decide; destruct (decide P); [contradiction|reflexivity]. Qed.

Section EvalHelpers.
Context {a : N} {c ffi_t : Type}.
Implicit Types X Y : state a c ffi_t.
Local Open Scope word_scope.

Lemma ev_inst (i : asm.inst a) X :
  evaluate (Inst i, X) = match inst i X with SOME s1 => (NONE, s1) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_inst_some (i : asm.inst a) X Y : inst i X = SOME Y -> evaluate (Inst i, X) = (NONE, Y).
Proof. intros H; rewrite ev_inst, H; reflexivity. Qed.

Lemma ev_seq (p1 p2 : prog a) X :
  evaluate (Seq p1 p2, X) =
  let '(res, s1) := evaluate (p1, X) in match res with NONE => evaluate (p2, s1) | _ => (res, s1) end.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def))))))))) p1 p2 X). Qed.

Lemma ev_seq_none (p1 p2 : prog a) X Y :
  evaluate (p1, X) = (NONE, Y) -> evaluate (Seq p1 p2, X) = evaluate (p2, Y).
Proof. intros H; rewrite ev_seq, H; reflexivity. Qed.

Lemma ev_seq_some (p1 p2 : prog a) X Y r :
  evaluate (p1, X) = (SOME r, Y) -> evaluate (Seq p1 p2, X) = (SOME r, Y).
Proof. intros H; rewrite ev_seq, H; reflexivity. Qed.

Lemma ev_skip X : evaluate (Skip, X) = (NONE, X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_if cmp0 r1 ri (c1 c2 : prog a) X :
  evaluate (If cmp0 r1 ri c1 c2, X) =
  match get_var r1 X, get_var_imm ri X with
  | SOME x, SOME y =>
      match wordSem.word_cmp cmp0 x y with
      | SOME true => evaluate (c1, X)
      | SOME false => evaluate (c2, X)
      | NONE => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_halt v X :
  evaluate (stackLang.Halt v, X) =
  match get_var v X with SOME w => (SOME (Halt w), empty_env X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma word_op_add2 (w1 w2 : word a) : wordLang.word_op asm.Add [w1; w2] = Some (w1 + w2).
Proof. cbn. rewrite (proj1 WORD_ADD_0). reflexivity. Qed.

Lemma inst_binop_imm op r1 r2 (v w : word a) X :
  op <> asm.Or -> FLOOKUP (regs X) r2 = SOME (Word w) ->
  inst (Arith (Binop op r1 r2 (Imm v))) X =
  option_map (fun w' => set_var r1 (Word w') X) (wordLang.word_op op [w; v]).
Proof.
  intros Hop Hr. cbn [inst]. replace (bool_decide (op = asm.Or)) with false
    by (symmetry; apply bd_false; exact Hop).
  cbn [andb]. unfold assign. cbn [word_exp MAP EVERY]. rewrite Hr. cbn [IS_SOME andb MAP THE].
  destruct (wordLang.word_op op [w; v]); reflexivity.
Qed.

Lemma inst_binop_reg op r1 r2 r3 (w v : word a) X :
  op <> asm.Or -> FLOOKUP (regs X) r2 = SOME (Word w) -> FLOOKUP (regs X) r3 = SOME (Word v) ->
  inst (Arith (Binop op r1 r2 (Reg r3))) X =
  option_map (fun w' => set_var r1 (Word w') X) (wordLang.word_op op [w; v]).
Proof.
  intros Hop Hr Hr3. cbn [inst]. replace (bool_decide (op = asm.Or)) with false
    by (symmetry; apply bd_false; exact Hop).
  cbn [andb]. unfold assign. cbn [word_exp MAP EVERY]. rewrite Hr, Hr3. cbn [IS_SOME andb MAP THE].
  destruct (wordLang.word_op op [w; v]); reflexivity.
Qed.

Lemma inst_add_imm r1 r2 (v w : word a) X :
  FLOOKUP (regs X) r2 = SOME (Word w) ->
  inst (Arith (Binop asm.Add r1 r2 (Imm v))) X = SOME (set_var r1 (Word (w + v)) X).
Proof. intros H; rewrite (inst_binop_imm asm.Add r1 r2 v w X ltac:(discriminate) H), word_op_add2; reflexivity. Qed.

Lemma inst_sub_imm r1 r2 (v w : word a) X :
  FLOOKUP (regs X) r2 = SOME (Word w) ->
  inst (Arith (Binop asm.Sub r1 r2 (Imm v))) X = SOME (set_var r1 (Word (w - v)) X).
Proof. intros H; rewrite (inst_binop_imm asm.Sub r1 r2 v w X ltac:(discriminate) H); reflexivity. Qed.

Lemma inst_add_reg r1 r2 r3 (w v : word a) X :
  FLOOKUP (regs X) r2 = SOME (Word w) -> FLOOKUP (regs X) r3 = SOME (Word v) ->
  inst (Arith (Binop asm.Add r1 r2 (Reg r3))) X = SOME (set_var r1 (Word (w + v)) X).
Proof. intros H H3; rewrite (inst_binop_reg asm.Add r1 r2 r3 w v X ltac:(discriminate) H H3), word_op_add2; reflexivity. Qed.

Lemma inst_sub_reg r1 r2 r3 (w v : word a) X :
  FLOOKUP (regs X) r2 = SOME (Word w) -> FLOOKUP (regs X) r3 = SOME (Word v) ->
  inst (Arith (Binop asm.Sub r1 r2 (Reg r3))) X = SOME (set_var r1 (Word (w - v)) X).
Proof. intros H H3; rewrite (inst_binop_reg asm.Sub r1 r2 r3 w v X ltac:(discriminate) H H3); reflexivity. Qed.

Lemma inst_move r1 r2 v X :
  FLOOKUP (regs X) r2 = SOME v ->
  inst (Arith (Binop asm.Or r1 r2 (Reg r2))) X = SOME (set_var r1 v X).
Proof.
  intros H. cbn [inst]. rewrite (proj2 (bool_decide_spec (asm.Or = asm.Or)) eq_refl),
    (proj2 (bool_decide_spec (@Reg a r2 = Reg r2)) eq_refl). cbn [andb]. rewrite H; reflexivity.
Qed.

Lemma inst_const r (w : word a) X : inst (asm.Const r w) X = SOME (set_var r (Word w) X).
Proof. reflexivity. Qed.

Lemma inst_shift_imm sh r1 r2 (v w w' : word a) X :
  FLOOKUP (regs X) r2 = SOME (Word w) -> wordLang.word_sh sh w (w2n v) = Some w' ->
  inst (Arith (Shift sh r1 r2 (Imm v))) X = SOME (set_var r1 (Word w') X).
Proof. intros H Hs. cbn [inst]. unfold assign. cbn [word_exp]. rewrite H, Hs. reflexivity. Qed.

Lemma inst_load r ad (off b : word a) v X :
  FLOOKUP (regs X) ad = SOME (Word b) -> mem_load (b + off) X = SOME v ->
  inst (Mem Load r (Addr ad off)) X = SOME (set_var r v X).
Proof.
  intros H Hm. cbn [inst word_exp MAP EVERY]. rewrite H. cbn [IS_SOME andb MAP THE].
  rewrite word_op_add2, Hm. reflexivity.
Qed.

Lemma inst_store r ad (off b : word a) v X :
  FLOOKUP (regs X) ad = SOME (Word b) -> FLOOKUP (regs X) r = SOME v -> (b + off) IN mdomain X ->
  inst (Mem Store r (Addr ad off)) X = SOME (set_memory (((b + off) =+ v) (stackSem.memory X)) X).
Proof.
  intros H Hr Hd. cbn [inst word_exp MAP EVERY]. rewrite H. cbn [IS_SOME andb MAP THE].
  rewrite word_op_add2. unfold get_var; rewrite Hr. unfold mem_store.
  destruct (classical_dec _); [reflexivity|contradiction].
Qed.

Lemma set_var_regs r v X : regs (set_var r v X) = regs X |+ (r, v).
Proof. reflexivity. Qed.

Lemma FLOOKUP_set_var_same r v X : FLOOKUP (regs (set_var r v X)) r = SOME v.
Proof. rewrite set_var_regs, FLOOKUP_UPDATE; destruct (decide (r = r)); congruence. Qed.

Lemma FLOOKUP_set_var_other r r' v X : r <> r' -> FLOOKUP (regs (set_var r v X)) r' = FLOOKUP (regs X) r'.
Proof. intros H; rewrite set_var_regs, FLOOKUP_UPDATE; destruct (decide (r = r')); congruence. Qed.

End EvalHelpers.

Section Batch4.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Local Open Scope word_scope.

Lemma LENGTH_LUPDATE_N {A} (v : A) : forall l n, LENGTH (LUPDATE v n l) = LENGTH l.
Proof.
  induction l as [|x l IH]; intros n; [reflexivity|]. cbn [LUPDATE].
  destruct (n =? 0); cbn [LENGTH]; [reflexivity|rewrite IH; reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_write" *)
Theorem stack_write : forall {B} (stack0 : list B) (base : word a) p m d (ad : N) v,
  STAR (word_list base stack0) p (fun2set (m, d)) /\ (ad < LENGTH stack0)%N ->
  STAR (word_list base (LUPDATE v ad stack0)) p
    (fun2set (((base + bytes_in_word * n2w ad) =+ v) m, d)).
Proof.
  intros B stack0; induction stack0 as [|x xs IH]; intros base p m d ad v [H Hl];
    [cbn in Hl; lia|].
  rewrite LENGTH_cons_N in Hl. cbn [word_list] in H |- *.
  destruct (N.eq_dec ad 0) as [->|Hn].
  - cbn [LUPDATE N.eqb word_list]. rewrite <- STAR_ASSOC in H |- *.
    replace (base + bytes_in_word * n2w 0) with base by word_ring.
    exact (sep_write _ _ _ _ _ _ H).
  - replace (LUPDATE v ad (x :: xs)) with (x :: LUPDATE v (ad - 1)%N xs)
      by (cbn [LUPDATE]; destruct (N.eqb_spec ad 0); [lia|]; f_equal; f_equal; lia).
    cbn [word_list]. rewrite <- STAR_ASSOC, STAR_swap_l in H |- *.
    replace (base + bytes_in_word * n2w ad) with ((base + bytes_in_word) + bytes_in_word * n2w (ad - 1)%N).
    + apply IH. split; [exact H|lia].
    + replace ad with (ad - 1 + 1)%N at 2 by lia. rewrite <- word_add_n2w. word_ring.
Qed.

Lemma sr_mem_L (M W1 W2 S L : (word a * word_loc a -> Prop) -> Prop) :
  STAR (STAR (STAR (STAR M W1) W2) S) L = STAR L (STAR (STAR (STAR M W1) W2) S).
Proof. apply STAR_COMM. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_stack_store" *)
Theorem state_rel_stack_store : forall jump off k s t st b n ad x,
  state_rel jump off k s t /\ st = stack s /\
  FLOOKUP (regs t) k = SOME (Word b) /\
  (stack_space s + n < LENGTH st)%N /\
  b + bytes_in_word * n2w n = ad ->
  state_rel jump off k (set_stack (LUPDATE x (n + stack_space s) st) s)
    (set_memory ((ad =+ x) (stackSem.memory t)) t).
Proof.
  intros jump off k s t st b n ad x (H & -> & Hb & Hn & <-).
  unfold state_rel in *; cbv zeta in *; stk_fields.
  destruct_ands. rewrite !LENGTH_LUPDATE_N. repeat (split; [assumption|]).
  destruct (FLOOKUP (regs t) (k + 1)%N) as [[base|]|]; try contradiction.
  destruct_ands. repeat (split; [assumption|]).
  match goal with H1 : FLOOKUP (regs t) k = _, H2 : FLOOKUP (regs t) k = _ |- _ =>
    rewrite H1 in H2; injection H2 as <- end.
  rewrite sr_mem_L in *.
  replace (base + bytes_in_word * n2w (stack_space s) + bytes_in_word * n2w n)
    with (base + bytes_in_word * n2w (n + stack_space s)%N)
    by (rewrite <- word_add_n2w; word_ring).
  apply stack_write; split; [assumption|lia].
Qed.

Lemma word_offset_add n m : (stack_remove.word_offset (n + m)%N : word a) =
  stack_remove.word_offset n + stack_remove.word_offset m.
Proof. rewrite !word_offset_eq, <- word_add_n2w. word_ring. Qed.

Lemma regs_update_twice (f : fmap N (word_loc a)) r v1 v2 : (f |+ (r, v1)) |+ (r, v2) = f |+ (r, v2).
Proof. apply fmap_ext; intros x; rewrite !FLOOKUP_UPDATE; destruct (decide (r = x)); reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_upshift" *)
Local Theorem evaluate_upshift : forall r n (st : state a c ffi_t) w,
  FLOOKUP (regs st) r = SOME (Word w) ->
  evaluate (stack_remove.upshift r n, st) =
    (NONE, set_regs (regs st |+ (r, Word (w + stack_remove.word_offset n))) st).
Proof.
  intros r n. induction n as [n IH] using (well_founded_induction (N.lt_wf_0)).
  intros st w Hr. rewrite stack_remove.upshift_def.
  destruct (N.leb_spec n stack_remove.max_stack_alloc) as [Hle|Hgt].
  - rewrite (ev_inst_some _ _ _ (inst_add_imm _ _ _ _ _ Hr)). reflexivity.
  - rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_add_imm _ _ _ _ _ Hr))).
    rewrite (IH (n - stack_remove.max_stack_alloc)%N ltac:(unfold stack_remove.max_stack_alloc in *; lia)
               _ (w + stack_remove.word_offset stack_remove.max_stack_alloc)
               (FLOOKUP_set_var_same _ _ _)).
    unfold set_var; cbn [regs set_regs]. rewrite regs_update_twice.
    replace (w + stack_remove.word_offset stack_remove.max_stack_alloc +
             stack_remove.word_offset (n - stack_remove.max_stack_alloc)%N)
      with (w + stack_remove.word_offset n); [reflexivity|].
    rewrite <- WORD_ADD_ASSOC, <- word_offset_add. f_equal. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_downshift" *)
Local Theorem evaluate_downshift : forall r n (st : state a c ffi_t) w,
  FLOOKUP (regs st) r = SOME (Word w) ->
  evaluate (stack_remove.downshift r n, st) =
    (NONE, set_regs (regs st |+ (r, Word (w - stack_remove.word_offset n))) st).
Proof.
  intros r n. induction n as [n IH] using (well_founded_induction (N.lt_wf_0)).
  intros st w Hr. rewrite stack_remove.downshift_def.
  destruct (N.leb_spec n stack_remove.max_stack_alloc) as [Hle|Hgt].
  - rewrite (ev_inst_some _ _ _ (inst_sub_imm _ _ _ _ _ Hr)). reflexivity.
  - rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_sub_imm _ _ _ _ _ Hr))).
    rewrite (IH (n - stack_remove.max_stack_alloc)%N ltac:(unfold stack_remove.max_stack_alloc in *; lia)
               _ (w - stack_remove.word_offset stack_remove.max_stack_alloc)
               (FLOOKUP_set_var_same _ _ _)).
    unfold set_var; cbn [regs set_regs]. rewrite regs_update_twice.
    replace (w - stack_remove.word_offset stack_remove.max_stack_alloc -
             stack_remove.word_offset (n - stack_remove.max_stack_alloc)%N)
      with (w - stack_remove.word_offset n); [reflexivity|].
    assert (E : (stack_remove.word_offset n : word a) = stack_remove.word_offset stack_remove.max_stack_alloc +
                  stack_remove.word_offset (n - stack_remove.max_stack_alloc)%N)
      by (rewrite <- word_offset_add; f_equal; lia).
    rewrite E. word_ring.
Qed.

End Batch4.


Section Batch5.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

Lemma ev_jumplower r1 r2 dest (X : state a c ffi_t) :
  evaluate (JumpLower r1 r2 dest, X) =
  match get_var r1 X, get_var r2 X with
  | SOME (Word x), SOME (Word y) =>
      if word_cmp Lower x y then
        match find_code (inl dest) (regs X) (code X) with
        | NONE => (SOME Error, X)
        | SOME prog0 =>
            if (clock X =? 0)%N then (SOME TimeOut, empty_env X) else
              match evaluate (prog0, dec_clock X) with
              | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
              end
        end
      else (NONE, X)
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma find_code_inl d (r : fmap N (word_loc a)) (cd : spt (prog a)) : find_code (inl d) r cd = lookup d cd.
Proof. reflexivity. Qed.

Lemma code_set_var r v s : code (set_var r v s) = code s.
Proof. reflexivity. Qed.

Lemma clock_set_var r v s : clock (set_var r v s) = clock s.
Proof. reflexivity. Qed.

Lemma set_stack_space_same s : set_stack_space (stack_space s) s = s.
Proof. destruct s; reflexivity. Qed.

Lemma set_clock_same s : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.

Lemma good_dimindex_d (Hg : good_dimindex a) :
  w2n (bytes_in_word : word a) = dimindex a DIV 8 /\ 0 < dimindex a DIV 8.
Proof.
  unfold bytes_in_word. rewrite w2n_n2w. destruct Hg as [E|E]; rewrite dimword_pow, E; cbn; lia.
Qed.

(** Galette-only: the arithmetic behind [single_stack_alloc]. *)
Lemma alloc_arith (c0 : word a) ss n len :
  good_dimindex a -> dimindex a DIV 8 * stack_remove.max_stack_alloc <= w2n c0 ->
  w2n c0 + w2n (bytes_in_word : word a) * len < dimword a -> ss <= len -> n <= stack_remove.max_stack_alloc ->
  w2n (c0 + bytes_in_word * n2w ss - stack_remove.word_offset n)%w =
    w2n c0 + dimindex a DIV 8 * ss - dimindex a DIV 8 * n /\
  (is_true (c0 + bytes_in_word * n2w ss - stack_remove.word_offset n <+ c0)%w <-> ss < n).
Proof.
  intros Hg Hc Hl Hss Hn. destruct (good_dimindex_d Hg) as [Hd Hd0].
  rewrite Hd in Hl. set (d := dimindex a DIV 8) in *.
  assert (Hdn : d * n <= d * stack_remove.max_stack_alloc) by (apply N.mul_le_mono_l; exact Hn).
  assert (Hds : d * ss <= d * len) by (apply N.mul_le_mono_l; exact Hss).
  assert (E : (c0 + bytes_in_word * n2w ss - stack_remove.word_offset n)%w =
              n2w (w2n c0 + d * ss - d * n)).
  { unfold stack_remove.word_offset, bytes_in_word. fold d. rewrite <- (n2w_w2n c0) at 1.
    word_Z. rewrite N2Z.inj_sub by lia. rewrite !N2Z.inj_add, !N2Z.inj_mul. apply zcong_eq; ring. }
  assert (Hw : w2n (c0 + bytes_in_word * n2w ss - stack_remove.word_offset n)%w = w2n c0 + d * ss - d * n)
    by (rewrite E, w2n_n2w; apply N.mod_small; lia).
  split; [exact Hw|]. rewrite WORD_LO, Hw. split; intros H.
  - destruct (N.lt_ge_cases ss n) as [|Hge]; [assumption|].
    assert (d * n <= d * ss) by (apply N.mul_le_mono_l; exact Hge). lia.
  - assert (d * ss < d * n) by (apply N.mul_lt_mono_pos_l; lia). lia.
Qed.

Lemma state_rel_set_k jump off k s t ss' (base : word a) :
  state_rel jump off k s t -> FLOOKUP (regs t) (k + 1) = SOME (Word base) ->
  ss' <= LENGTH (stack s) ->
  state_rel jump off k (set_stack_space ss' s)
    (set_var k (Word (base + bytes_in_word * n2w ss')%w) t).
Proof.
  intros H Eb Hss. unfold state_rel, set_var in *; cbv zeta in *; stk_fields.
  rewrite !(FLOOKUP_UPDATE (regs t)).
  destruct (decide (k = k + 2)) as [|_]; [lia|].
  destruct (decide (k = k + 1)) as [|_]; [lia|].
  destruct (decide (k = k)) as [_|]; [|congruence].
  destruct_ands. repeat (split; [assumption|]).
  split; [intros n Hn; rewrite FLOOKUP_UPDATE; destruct (decide (k = n)); [lia|auto]|].
  repeat (split; [assumption|]).
  rewrite Eb in *. destruct_ands. repeat (split; [assumption|]). split; [reflexivity|assumption].
Qed.

Lemma sr_clock jump off k s t : state_rel jump off k s t -> clock t = clock s.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

Lemma sr_ffi jump off k s t : state_rel jump off k s t -> ffi t = ffi s.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

Lemma sr_good jump off k s t : state_rel jump off k s t -> good_dimindex a.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

Lemma sr_use_stack jump off k s t : state_rel jump off k s t -> use_stack s = true.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

Lemma sr_err_lab jump off k s t :
  state_rel jump off k s t -> lookup stack_remove.stack_err_lab (code t) = SOME (stack_remove.halt_inst (n2w 2)).
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

Lemma sr_ss jump off k s t : state_rel jump off k s t -> stack_space s <= LENGTH (stack s).
Proof. intros H; unfold state_rel in H; cbv zeta in H; destruct_ands; assumption. Qed.

Lemma ev_halt_inst w (X : state a c ffi_t) :
  evaluate (stack_remove.halt_inst w, X) = (SOME (Halt (Word w)), empty_env (set_var 1 (Word w) X)).
Proof.
  unfold stack_remove.halt_inst. rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_const _ _ _))).
  rewrite ev_halt. unfold get_var. rewrite FLOOKUP_set_var_same. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_single_stack_alloc" *)
Theorem evaluate_single_stack_alloc : forall jump off k s t1 r s2 n,
  state_rel jump off k s t1 /\
  (r, s2) = (if stack_space s <? n then (SOME (Halt (Word (n2w 2))), empty_env s)
             else (NONE, set_stack_space (stack_space s - n) s)) /\
  n <> 0 /\ n <= stack_remove.max_stack_alloc ->
  exists ck t2,
    evaluate (stack_remove.single_stack_alloc jump k n, set_clock (clock t1 + ck) t1) = (r, t2) /\
    if stack_space s <? n then ffi t2 = ffi s2 else state_rel jump off k s2 t2.
Proof.
  intros jump off k s t1 r s2 n (H & Hr & Hn0 & Hn).
  destruct (state_rel_get_var_k _ _ _ _ _ H) as (c0 & Hk1 & Hc & Hl & Hk & _).
  pose proof (sr_good _ _ _ _ _ H) as Hg. pose proof (sr_ss _ _ _ _ _ H) as Hss.
  destruct (alloc_arith c0 (stack_space s) n (LENGTH (stack s)) Hg Hc Hl Hss Hn) as [_ Hcmp].
  set (cc := (c0 + bytes_in_word * n2w (stack_space s) - stack_remove.word_offset n)%w) in *.
  unfold get_var in Hk, Hk1.
  assert (Hsub : forall ck, inst (Arith (Binop asm.Sub k k (Imm (stack_remove.word_offset n))))
                   (set_clock (clock t1 + ck) t1) = SOME (set_var k (Word cc) (set_clock (clock t1 + ck) t1)))
    by (intros ck; apply inst_sub_imm; exact Hk).
  assert (Hk1' : forall ck, get_var (k + 1) (set_var k (Word cc) (set_clock (clock t1 + ck) t1)) = SOME (Word c0))
    by (intros ck; unfold get_var; rewrite FLOOKUP_set_var_other by lia; exact Hk1).
  assert (Hk' : forall ck, get_var k (set_var k (Word cc) (set_clock (clock t1 + ck) t1)) = SOME (Word cc))
    by (intros ck; unfold get_var; apply FLOOKUP_set_var_same).
  destruct (stack_space s <? n) eqn:Elt; injection Hr as -> ->.
  - apply N.ltb_lt in Elt. assert (Hlo : is_true (cc <+ c0)%w) by (apply Hcmp; exact Elt).
    destruct jump; unfold stack_remove.single_stack_alloc.
    + exists 1. eexists. split.
      * rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (Hsub 1))), ev_jumplower, Hk1', Hk'.
        cbn [asm.word_cmp]. rewrite Hlo, find_code_inl, code_set_var, code_set_clock, (sr_err_lab _ _ _ _ _ H),
          clock_set_var, clock_set_clock.
        assert (Hc1 : (clock t1 + 1 =? 0) = false) by (apply N.eqb_neq; rewrite N.add_1_r; apply N.neq_succ_0).
        rewrite Hc1.
        rewrite ev_halt_inst. cbn [bad_fun_return]. reflexivity.
      * cbn [ffi empty_env set_var set_stack set_regs dec_clock set_clock]. exact (sr_ffi _ _ _ _ _ H).
    + exists 0. eexists. split.
      * rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (Hsub 0))), ev_if, Hk'. cbn [get_var_imm].
        rewrite Hk1'. cbn [wordSem.word_cmp]. rewrite Hlo. rewrite ev_halt_inst. reflexivity.
      * cbn [ffi empty_env set_var set_stack set_regs dec_clock set_clock]. exact (sr_ffi _ _ _ _ _ H).
  - apply N.ltb_ge in Elt.
    assert (Hlo : (cc <+ c0)%w = false) by (apply Bool.not_true_iff_false; intros E; apply Hcmp in E; lia).
    assert (Ecc : cc = (c0 + bytes_in_word * n2w (stack_space s - n))%w).
    { subst cc. rewrite word_offset_eq. replace (stack_space s) with ((stack_space s - n) + n) at 1 by lia.
      rewrite <- word_add_n2w. word_ring. }
    assert (R : state_rel jump off k (set_stack_space (stack_space s - n) s)
                  (set_var k (Word cc) (set_clock (clock t1 + 0) t1))).
    { rewrite N.add_0_r, set_clock_same, Ecc. apply state_rel_set_k; [exact H|exact Hk1|lia]. }
    exists 0. destruct jump; unfold stack_remove.single_stack_alloc.
    + eexists. split; [|exact R].
      rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (Hsub 0))), ev_jumplower, Hk1', Hk'.
      cbn [asm.word_cmp]. rewrite Hlo. reflexivity.
    + eexists. split; [|exact R].
      rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (Hsub 0))), ev_if, Hk'. cbn [get_var_imm].
      rewrite Hk1'. cbn [wordSem.word_cmp]. rewrite Hlo, ev_skip. reflexivity.
Qed.

End Batch5.

Section Batch5b.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

Lemma ev_stackalloc_eq n (X : state a c ffi_t) :
  evaluate (StackAlloc n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if (stack_space X <? n)%N then (SOME (Halt (Word (n2w 2))), empty_env X) else
    (NONE, set_stack_space (stack_space X - n) X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackfree_eq n (X : state a c ffi_t) :
  evaluate (StackFree n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if (LENGTH (stack X) <? stack_space X + n)%N then (SOME Error, empty_env X) else
    (NONE, set_stack_space (stack_space X + n) X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma set_stack_space_twice x y s : set_stack_space x (set_stack_space y s) = set_stack_space x s.
Proof. reflexivity. Qed.

Lemma add_clock_seq (p1 p2 : prog a) (X Y Z : state a c ffi_t) ck ck' r :
  evaluate (p1, set_clock (clock X + ck) X) = (NONE, Y) ->
  evaluate (p2, set_clock (ck' + clock Y) Y) = (r, Z) ->
  evaluate (Seq p1 p2, set_clock (clock X + (ck + ck')) X) = (r, Z).
Proof.
  intros E1 E2.
  assert (Hn : (@NONE (result a)) <> SOME TimeOut) by discriminate.
  pose proof (evaluate_add_clock ck' p1 _ NONE Y (conj E1 Hn)) as E3.
  rewrite clock_set_clock, set_clock_set_clock, <- N.add_assoc in E3.
  rewrite (ev_seq_none _ _ _ _ E3), N.add_comm. exact E2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_stack_alloc" *)
Theorem evaluate_stack_alloc : forall off jump k n r s s2 t1,
  evaluate (StackAlloc n, s) = (r, s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 ->
  exists ck t2,
    evaluate (stack_remove.stack_alloc jump k n, set_clock (ck + clock t1) t1) = (r, t2) /\
    if classical_dec (forall w, r <> SOME (Halt w)) then state_rel jump off k s2 t2 else ffi t2 = ffi s2.
Proof.
  intros off jump k n. induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  intros r s s2 t1 (He & Hr & H).
  rewrite ev_stackalloc_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  rewrite stack_remove.stack_alloc_def.
  destruct (N.eqb_spec n 0) as [->|Hn0].
  - replace (stack_space s <? 0) with false in He by (symmetry; apply N.ltb_ge; lia).
    injection He as <- <-. rewrite N.sub_0_r, set_stack_space_same.
    exists 0, t1. rewrite N.add_0_l, set_clock_same, ev_skip. split; [reflexivity|].
    destruct (classical_dec _) as [_|Hn]; [exact H|exfalso; apply Hn; intros w; discriminate].
  - destruct (N.leb_spec n stack_remove.max_stack_alloc) as [Hle|Hgt].
    + destruct (evaluate_single_stack_alloc jump off k s t1 r s2 n (conj H (conj (eq_sym He) (conj Hn0 Hle))))
        as (ck & t2 & E & P).
      exists ck, t2. rewrite N.add_comm. split; [exact E|].
      destruct (stack_space s <? n); injection He as <- <-.
      * destruct (classical_dec _) as [Hw|_]; [exfalso; exact (Hw _ eq_refl)|exact P].
      * destruct (classical_dec _) as [_|Hn]; [exact P|exfalso; apply Hn; intros w; discriminate].
    + assert (Hm0 : stack_remove.max_stack_alloc <> 0) by (unfold stack_remove.max_stack_alloc; lia).
      destruct (stack_space s <? stack_remove.max_stack_alloc) eqn:Elt.
      * assert (Eq : ((SOME (Halt (Word (n2w 2))), empty_env s) : option (result a) * state a c ffi_t) =
                     (if stack_space s <? stack_remove.max_stack_alloc then (SOME (Halt (Word (n2w 2))), empty_env s)
                      else (NONE, set_stack_space (stack_space s - stack_remove.max_stack_alloc) s)))
          by (rewrite Elt; reflexivity).
        destruct (evaluate_single_stack_alloc jump off k s t1 _ _ stack_remove.max_stack_alloc
                    (conj H (conj Eq (conj Hm0 (N.le_refl _))))) as (ck & t2 & E & P).
        rewrite Elt in P.
        apply N.ltb_lt in Elt.
        replace (stack_space s <? n) with true in He by (symmetry; apply N.ltb_lt; lia).
        injection He as <- <-. exists ck, t2. split.
        -- rewrite N.add_comm. exact (ev_seq_some _ _ _ _ _ E).
        -- destruct (classical_dec _) as [Hw|_]; [exfalso; exact (Hw _ eq_refl)|exact P].
      * assert (Eq : ((NONE, set_stack_space (stack_space s - stack_remove.max_stack_alloc) s)
                       : option (result a) * state a c ffi_t) =
                     (if stack_space s <? stack_remove.max_stack_alloc then (SOME (Halt (Word (n2w 2))), empty_env s)
                      else (NONE, set_stack_space (stack_space s - stack_remove.max_stack_alloc) s)))
          by (rewrite Elt; reflexivity).
        destruct (evaluate_single_stack_alloc jump off k s t1 _ _ stack_remove.max_stack_alloc
                    (conj H (conj Eq (conj Hm0 (N.le_refl _))))) as (ck & t2 & E & P).
        rewrite Elt in P.
        apply N.ltb_ge in Elt.
        assert (He' : exists s2', evaluate (StackAlloc (n - stack_remove.max_stack_alloc),
                                set_stack_space (stack_space s - stack_remove.max_stack_alloc) s) = (r, s2') /\
                      ffi s2' = ffi s2 /\ ((forall w, r <> SOME (Halt w)) -> s2' = s2)).
        { rewrite ev_stackalloc_eq. cbn [use_stack stack_space set_stack_space].
          rewrite (sr_use_stack _ _ _ _ _ H). cbn [negb].
          destruct (stack_space s <? n) eqn:Eln; [apply N.ltb_lt in Eln|apply N.ltb_ge in Eln].
          - replace (stack_space s - stack_remove.max_stack_alloc <? n - stack_remove.max_stack_alloc)
              with true by (symmetry; apply N.ltb_lt; lia).
            injection He as <- <-. eexists; split; [reflexivity|split; [reflexivity|]].
            intros Hw; exfalso; exact (Hw _ eq_refl).
          - replace (stack_space s - stack_remove.max_stack_alloc <? n - stack_remove.max_stack_alloc)
              with false by (symmetry; apply N.ltb_ge; lia).
            injection He as <- <-. eexists; split; [reflexivity|].
            assert (Ess : stack_space s - stack_remove.max_stack_alloc - (n - stack_remove.max_stack_alloc) =
                          stack_space s - n) by lia.
            rewrite Ess. split; reflexivity. }
        destruct He' as (s2' & He' & Hf & Hs2).
        destruct (IH (n - stack_remove.max_stack_alloc) ltac:(lia) r _ s2' t2 (conj He' (conj Hr P)))
          as (ck' & t3 & E' & P').
        exists (ck + ck'), t3. split.
        -- rewrite N.add_comm. exact (add_clock_seq _ _ _ _ _ _ _ _ E E').
        -- destruct (classical_dec _) as [Hw|Hw]; [rewrite <- (Hs2 Hw); exact P'|rewrite <- Hf; exact P'].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_single_stack_free" *)
Theorem evaluate_single_stack_free : forall jump off k s t1 r s2 n,
  state_rel jump off k s t1 /\
  (r, s2) = (NONE, set_stack_space (stack_space s + n) s) /\
  ~ (LENGTH (stack s) < stack_space s + n) /\
  n <> 0 /\ n <= stack_remove.max_stack_alloc ->
  exists ck t2,
    evaluate (stack_remove.single_stack_free k n, set_clock (clock t1 + ck) t1) = (r, t2) /\
    state_rel jump off k s2 t2.
Proof.
  intros jump off k s t1 r s2 n (H & Hr & Hl & Hn0 & Hn). injection Hr as -> ->.
  destruct (state_rel_get_var_k _ _ _ _ _ H) as (c0 & Hk1 & Hc & Hlen & Hk & _).
  unfold get_var in Hk, Hk1.
  exists 0. eexists. split.
  - unfold stack_remove.single_stack_free. rewrite N.add_0_r, set_clock_same.
    apply ev_inst_some, inst_add_imm. exact Hk.
  - replace (c0 + bytes_in_word * n2w (stack_space s) + stack_remove.word_offset n)%w
      with (c0 + bytes_in_word * n2w (stack_space s + n))%w
      by (rewrite word_offset_eq, <- word_add_n2w; word_ring).
    apply state_rel_set_k; [exact H|exact Hk1|lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_stack_free" *)
Theorem evaluate_stack_free : forall jump off k n r s s2 t1,
  evaluate (StackFree n, s) = (r, s2) /\ r <> SOME Error /\
  state_rel jump off k s t1 ->
  exists ck t2,
    evaluate (stack_remove.stack_free k n, set_clock (ck + clock t1) t1) = (r, t2) /\
    state_rel jump off k s2 t2.
Proof.
  intros jump off k n. induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  intros r s s2 t1 (He & Hr & H).
  rewrite ev_stackfree_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (LENGTH (stack s) <? stack_space s + n) eqn:El; [injection He as <- <-; congruence|].
  apply N.ltb_ge in El. injection He as <- <-.
  rewrite stack_remove.stack_free_def.
  destruct (N.eqb_spec n 0) as [->|Hn0].
  - rewrite N.add_0_r, set_stack_space_same. exists 0, t1.
    rewrite N.add_0_l, set_clock_same, ev_skip. split; [reflexivity|exact H].
  - assert (El' : ~ (LENGTH (stack s) < stack_space s + n)) by lia.
    destruct (N.leb_spec n stack_remove.max_stack_alloc) as [Hle|Hgt].
    + destruct (evaluate_single_stack_free jump off k s t1 NONE _ n
                  (conj H (conj eq_refl (conj El' (conj Hn0 Hle))))) as (ck & t2 & E & P).
      exists ck, t2. rewrite N.add_comm. split; [exact E|exact P].
    + assert (Hm0 : stack_remove.max_stack_alloc <> 0) by (unfold stack_remove.max_stack_alloc; lia).
      assert (El2 : ~ (LENGTH (stack s) < stack_space s + stack_remove.max_stack_alloc)) by lia.
      destruct (evaluate_single_stack_free jump off k s t1 NONE _ stack_remove.max_stack_alloc
                  (conj H (conj eq_refl (conj El2 (conj Hm0 (N.le_refl _)))))) as (ck & t2 & E & P).
      assert (He' : evaluate (StackFree (n - stack_remove.max_stack_alloc),
                              set_stack_space (stack_space s + stack_remove.max_stack_alloc) s) =
                    (NONE, set_stack_space (stack_space s + n) s)).
      { rewrite ev_stackfree_eq. cbn [use_stack stack_space set_stack_space stack].
        rewrite (sr_use_stack _ _ _ _ _ H). cbn [negb].
        replace (LENGTH (stack s) <? stack_space s + stack_remove.max_stack_alloc + (n - stack_remove.max_stack_alloc))
          with false by (symmetry; apply N.ltb_ge; lia).
        f_equal. rewrite set_stack_space_twice. f_equal. lia. }
      destruct (IH (n - stack_remove.max_stack_alloc) ltac:(lia) NONE _ _ t2 (conj He' (conj Hr P)))
        as (ck' & t3 & E' & P').
      exists (ck + ck'), t3. split; [|exact P'].
      rewrite N.add_comm. exact (add_clock_seq _ _ _ _ _ _ _ _ E E').
Qed.

End Batch5b.


Ltac wring := word_Z; rewrite ?N2Z.inj_add, ?N2Z.inj_mul; cbn [Z.of_N]; apply zcong_eq; ring.

Section StoreHelpers.
Context {a : N}.

Lemma EL_map_N {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) : forall (l : list A) i,
  i < LENGTH l -> EL i (MAP f l) = f (EL i l).
Proof.
  induction l as [|x l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct (N.eq_dec i 0) as [->|Hn]; [reflexivity|].
  replace i with (SUC (i - 1)) by (lia). cbn [map]. rewrite !EL_SUC. cbn [TL].
  apply IH. rewrite LENGTH_cons_N in Hi. lia.
Qed.

Lemma INDEX_FIND_In {A} `{EqDecision A} `{Inhabited A} (x : A) : forall l i0, In x l ->
  exists i, INDEX_FIND i0 (fun n => bool_decide (n = x)) l = Some (i0 + i, x) /\
            i < LENGTH l /\ EL i l = x /\ (forall j, j < i -> EL j l <> x).
Proof.
  induction l as [|y l IH]; intros i0 Hin; [destruct Hin|].
  cbn [INDEX_FIND]. destruct (bool_decide (y = x)) eqn:E.
  - apply bool_decide_spec in E; subst y. exists 0. rewrite N.add_0_r. repeat split; [rewrite LENGTH_cons_N; lia|].
    intros j Hj; lia.
  - assert (Hy : y <> x) by (intros ->; rewrite (proj2 (bool_decide_spec (x = x)) eq_refl) in E; discriminate).
    destruct Hin as [->|Hin]; [contradiction|].
    destruct (IH (SUC i0) Hin) as (i & Ei & Hi & Hel & Hlt).
    exists (SUC i). split; [rewrite Ei; f_equal; f_equal; lia|].
    split; [rewrite LENGTH_cons_N; lia|]. split; [rewrite EL_SUC; exact Hel|].
    intros j Hj. destruct (N.eq_dec j 0) as [->|Hj0]; [exact Hy|].
    replace j with (SUC (j - 1)) by (lia). rewrite EL_SUC. apply Hlt. lia.
Qed.

Lemma store_list_distinct : ALL_DISTINCT stack_remove.store_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ALL_DISTINCT_EL {A} `{EqDecision A} `{Inhabited A} : forall (l : list A) i j,
  ALL_DISTINCT l = true -> i < LENGTH l -> j < LENGTH l -> EL i l = EL j l -> i = j.
Proof.
  induction l as [|x l IH]; intros i j Hd Hi Hj E; [cbn in Hi; lia|].
  cbn [ALL_DISTINCT] in Hd. apply andb_true_iff in Hd as [Hx Hd]. rewrite LENGTH_cons_N in Hi, Hj.
  assert (Hmem : forall k, k < LENGTH l -> EL k l <> x).
  { intros k Hk Ek. apply negb_true_iff in Hx. rewrite <- Ek in Hx.
    assert (Hin : In (EL k l) l) by (rewrite EL_nth by exact Hk; apply nth_In; rewrite LENGTH_length in Hk; lia).
    apply MEM_In in Hin. rewrite Hin in Hx; discriminate. }
  destruct (N.eq_dec i 0) as [->|Hi0]; destruct (N.eq_dec j 0) as [->|Hj0]; [reflexivity| | |].
  - replace j with (SUC (j - 1)) in E by (lia). rewrite EL_SUC in E. cbn [TL] in E.
    exfalso; apply (Hmem (j - 1)); [lia|symmetry; exact E].
  - replace i with (SUC (i - 1)) in E by (lia). rewrite EL_SUC in E. cbn [TL] in E.
    exfalso; apply (Hmem (i - 1)); [lia|exact E].
  - replace i with (SUC (i - 1)) in E by (lia). replace j with (SUC (j - 1)) in E by (lia).
    rewrite !EL_SUC in E. cbn [TL] in E. assert (i - 1 = j - 1) by (apply IH; auto; lia). lia.
Qed.

Lemma store_pos_MEM name : MEM name stack_remove.store_list = true ->
  exists i, stack_remove.store_pos name = i + 1 /\ i < LENGTH stack_remove.store_list /\
            EL i stack_remove.store_list = name.
Proof.
  intros H. apply MEM_In in H. destruct (INDEX_FIND_In name _ 0 H) as (i & Ei & Hi & Hel & _).
  exists i. unfold stack_remove.store_pos. rewrite Ei. auto.
Qed.

Lemma store_offset_pos name i : stack_remove.store_pos name = i + 1 ->
  (stack_remove.store_offset name : word a) = (word_2comp (bytes_in_word * n2w (i + 1)))%w.
Proof. intros E. unfold stack_remove.store_offset. rewrite E, word_offset_eq. wring. Qed.

Lemma word_list_rev_read {B} `{Inhabited B} : forall (xs : list B) (base : word a) p m d i,
  STAR (word_list_rev base xs) p (fun2set (m, d)) -> i < LENGTH xs ->
  m (base - bytes_in_word * n2w (i + 1))%w = EL i xs /\ (base - bytes_in_word * n2w (i + 1))%w IN d.
Proof.
  induction xs as [|x xs IH]; intros base p m d i Hs Hi; [cbn in Hi; lia|].
  rewrite LENGTH_cons_N in Hi. cbn [word_list_rev] in Hs. rewrite <- STAR_ASSOC in Hs.
  destruct (N.eq_dec i 0) as [->|Hi0].
  - replace (base - bytes_in_word * n2w (0 + 1))%w with (base - bytes_in_word)%w by wring.
    exact (sep_read _ _ _ _ _ Hs).
  - rewrite STAR_swap_l in Hs. destruct (IH _ _ _ _ (i - 1) Hs ltac:(lia)) as [E1 E2].
    replace (base - bytes_in_word * n2w (i + 1))%w
      with (base - bytes_in_word - bytes_in_word * n2w (i - 1 + 1))%w.
    + split; [|exact E2]. rewrite E1. replace i with (SUC (i - 1)) at 2 by (lia).
      rewrite EL_SUC. reflexivity.
    + replace (i + 1) with ((i - 1 + 1) + 1) by lia. rewrite <- (word_add_n2w (i - 1 + 1) 1). wring.
Qed.

Lemma word_list_rev_write {B} : forall (xs : list B) (base : word a) p m d i v,
  STAR (word_list_rev base xs) p (fun2set (m, d)) -> i < LENGTH xs ->
  STAR (word_list_rev base (LUPDATE v i xs)) p (fun2set ((((base - bytes_in_word * n2w (i + 1))%w) =+ v) m, d)).
Proof.
  induction xs as [|x xs IH]; intros base p m d i v Hs Hi; [cbn in Hi; lia|].
  rewrite LENGTH_cons_N in Hi. cbn [word_list_rev] in Hs. rewrite <- STAR_ASSOC in Hs.
  destruct (N.eq_dec i 0) as [->|Hi0].
  - cbn [LUPDATE N.eqb word_list_rev]. rewrite <- STAR_ASSOC.
    replace (base - bytes_in_word * n2w (0 + 1))%w with (base - bytes_in_word)%w by wring.
    exact (sep_write _ _ _ _ _ _ Hs).
  - replace (LUPDATE v i (x :: xs)) with (x :: LUPDATE v (i - 1) xs)
      by (cbn [LUPDATE]; destruct (N.eqb_spec i 0); [lia|]; f_equal; f_equal; lia).
    cbn [word_list_rev]. rewrite <- STAR_ASSOC, STAR_swap_l. rewrite STAR_swap_l in Hs.
    replace (base - bytes_in_word * n2w (i + 1))%w
      with (base - bytes_in_word - bytes_in_word * n2w (i - 1 + 1))%w.
    + apply IH; [exact Hs|lia].
    + replace (i + 1) with ((i - 1 + 1) + 1) by lia. rewrite <- (word_add_n2w (i - 1 + 1) 1). wring.
Qed.

Lemma map_update_LUPDATE {A B} `{EqDecision A} `{Inhabited A} (g g' : A -> B) x0 name : forall (l : list A) i,
  ALL_DISTINCT l = true -> i < LENGTH l -> EL i l = name ->
  g' name = x0 -> (forall n, n <> name -> g' n = g n) ->
  MAP g' l = LUPDATE x0 i (MAP g l).
Proof.
  induction l as [|y l IH]; intros i Hd Hi Hel Hn Ho; [cbn in Hi; lia|].
  cbn [ALL_DISTINCT] in Hd. apply andb_true_iff in Hd as [Hy Hd]. rewrite LENGTH_cons_N in Hi.
  cbn [map]. destruct (N.eq_dec i 0) as [->|Hi0].
  - cbn [LUPDATE N.eqb]. cbn [EL num_rec HD] in Hel. change (EL 0 (y :: l)) with y in Hel. subst y.
    f_equal; [exact Hn|]. apply map_ext_in. intros z Hz. apply Ho. intros ->.
    apply MEM_In in Hz. apply negb_true_iff in Hy. rewrite Hz in Hy; discriminate.
  - replace (LUPDATE x0 i (g y :: MAP g l)) with (g y :: LUPDATE x0 (i - 1) (MAP g l))
      by (cbn [LUPDATE]; destruct (N.eqb_spec i 0); [lia|]; f_equal; f_equal; lia).
    replace i with (SUC (i - 1)) in Hel by (lia). rewrite EL_SUC in Hel. cbn [TL] in Hel.
    f_equal.
    + apply Ho. intros ->. apply negb_true_iff in Hy.
      assert (Hin : In (EL (i - 1) l) l) by (rewrite EL_nth by lia; apply nth_In; rewrite LENGTH_length in Hi; lia).
      rewrite Hel in Hin. apply MEM_In in Hin. rewrite Hin in Hy; discriminate.
    + apply IH; auto. lia.
Qed.

End StoreHelpers.

Section Batch6.
Context {a : N} {cfg ffi_t : Type}.
Local Open Scope word_scope.

Lemma sr_mem_S (X S L : (word a * word_loc a -> Prop) -> Prop) : STAR (STAR X S) L = STAR S (STAR X L).
Proof. rewrite <- STAR_ASSOC, STAR_swap_l. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_lemma" *)
Local Theorem mem_load_lemma : forall name (s : state a cfg ffi_t) x (c : word a) (t1 : state a cfg ffi_t),
  MEM name stack_remove.store_list /\
  FLOOKUP (store s) name = SOME x /\
  STAR (STAR (STAR (STAR (memory (stackSem.memory s) (mdomain s))
        (word_list (the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a)
           (MAP Word (bitmaps s) ++ MAP Word (wordSem.buffer_buffer (data_buffer s)))))
        (word_list_exists ((the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a) +
             bytes_in_word * n2w (LENGTH (wordSem.buffer_buffer (data_buffer s)) + LENGTH (bitmaps s)))
           (wordSem.space_left (data_buffer s))))
        (word_store c (store s)))
      (word_list c (stack s))
      (fun2set (stackSem.memory t1, mdomain t1)) ->
  mem_load (c + stack_remove.store_offset name) t1 = SOME x.
Proof.
  intros name s x c t1 (Hm & Hx & Hs). rewrite sr_mem_S in Hs. unfold word_store in Hs.
  destruct (store_pos_MEM name Hm) as (i & Ep & Hi & Hel).
  rewrite (store_offset_pos name i Ep).
  assert (Hi' : (i < LENGTH (MAP (fun name => match FLOOKUP (store s) name with NONE => Word (n2w 0) | SOME x => x end)
                                  stack_remove.store_list))%N)
    by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact Hi).
  destruct (word_list_rev_read _ _ _ _ _ i Hs Hi') as [E1 E2].
  rewrite EL_map_N in E1 by exact Hi. rewrite Hel, Hx in E1.
  replace (c + - (bytes_in_word * n2w (i + 1)%N)) with (c - bytes_in_word * n2w (i + 1)%N) by wring.
  unfold mem_load. destruct (classical_dec _); [rewrite E1; reflexivity|contradiction].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_lemma2" *)
Local Theorem mem_load_lemma2 : forall name (s : state a cfg ffi_t) (c : word a) (t1 : state a cfg ffi_t),
  MEM name stack_remove.store_list /\
  STAR (STAR (STAR (STAR (memory (stackSem.memory s) (mdomain s))
        (word_list (the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a)
           (MAP Word (bitmaps s) ++ MAP Word (wordSem.buffer_buffer (data_buffer s)))))
        (word_list_exists ((the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a) +
             bytes_in_word * n2w (LENGTH (wordSem.buffer_buffer (data_buffer s)) + LENGTH (bitmaps s)))
           (wordSem.space_left (data_buffer s))))
        (word_store c (store s)))
      (word_list c (stack s))
      (fun2set (stackSem.memory t1, mdomain t1)) ->
  c + stack_remove.store_offset name IN mdomain t1.
Proof.
  intros name s c t1 (Hm & Hs). rewrite sr_mem_S in Hs. unfold word_store in Hs.
  destruct (store_pos_MEM name Hm) as (i & Ep & Hi & Hel).
  rewrite (store_offset_pos name i Ep).
  assert (Hi' : (i < LENGTH (MAP (fun name => match FLOOKUP (store s) name with NONE => Word (n2w 0) | SOME x => x end)
                                  stack_remove.store_list))%N)
    by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact Hi).
  destruct (word_list_rev_read _ _ _ _ _ i Hs Hi') as [_ E2].
  replace (c + - (bytes_in_word * n2w (i + 1)%N)) with (c - bytes_in_word * n2w (i + 1)%N) by wring.
  exact E2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "assoc_lem" *)
Local Theorem assoc_lem : forall {T} (A B C : (T -> Prop) -> Prop), STAR (STAR A B) C = STAR (STAR B C) A.
Proof. intros T A B C. rewrite <- STAR_ASSOC, STAR_COMM. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "store_write_lemma" *)
Local Theorem store_write_lemma : forall name (s : state a cfg ffi_t) (c : word a) m d x,
  MEM name stack_remove.store_list /\
  STAR (STAR (STAR (STAR (memory (stackSem.memory s) (mdomain s))
        (word_list (the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a)
           (MAP Word (bitmaps s) ++ MAP Word (wordSem.buffer_buffer (data_buffer s)))))
        (word_list_exists ((the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a) +
             bytes_in_word * n2w (LENGTH (wordSem.buffer_buffer (data_buffer s)) + LENGTH (bitmaps s)))
           (wordSem.space_left (data_buffer s))))
        (word_store c (store s)))
      (word_list c (stack s))
      (fun2set (m, d)) ->
  STAR (STAR (STAR (STAR (memory (stackSem.memory s) (mdomain s))
        (word_list (the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a)
           (MAP Word (bitmaps s) ++ MAP Word (wordSem.buffer_buffer (data_buffer s)))))
        (word_list_exists ((the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a) +
             bytes_in_word * n2w (LENGTH (wordSem.buffer_buffer (data_buffer s)) + LENGTH (bitmaps s)))
           (wordSem.space_left (data_buffer s))))
        (word_store c (store s |+ (name, x))))
      (word_list c (stack s))
      (fun2set ((c + stack_remove.store_offset name =+ x) m, d)).
Proof.
  intros name s c m d x (Hm & Hs). rewrite sr_mem_S in Hs |- *. unfold word_store in Hs |- *.
  destruct (store_pos_MEM name Hm) as (i & Ep & Hi & Hel).
  rewrite (store_offset_pos name i Ep).
  replace (c + - (bytes_in_word * n2w (i + 1)%N)) with (c - bytes_in_word * n2w (i + 1)%N) by wring.
  erewrite (map_update_LUPDATE _ _ x name); [|exact store_list_distinct|exact Hi|exact Hel| |].
  - apply word_list_rev_write; [exact Hs|]. rewrite LENGTH_length, length_map, <- LENGTH_length; exact Hi.
  - cbv beta. rewrite FLOOKUP_UPDATE. destruct (decide (name = name)); [reflexivity|congruence].
  - intros n Hn. cbv beta. rewrite FLOOKUP_UPDATE. destruct (decide (name = n)); [congruence|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_fun2set_SUBSET" *)
Theorem memory_fun2set_SUBSET : forall (m1 : word a -> word_loc a) d1 rest m2 d2,
  STAR (memory m1 d1) rest (fun2set (m2, d2)) -> d1 SUBSET d2.
Proof.
  intros m1 d1 rest m2 d2 H b Hb.
  exact (proj1 (memory_fun2set_IMP_read _ _ _ _ _ _ (conj H Hb))).
Qed.

End Batch6.


Section LoopHelpers.
Context {a : N} {cfg ffi_t : Type}.
Implicit Types X Y : state a cfg ffi_t.

Lemma ev_loop (c1 : prog a) X :
  evaluate (Loop c1, X) =
  let '(res, s1) := evaluate (c1, X) in
  if cont_loop res then
    (if (clock s1 =? 0) then (SOME TimeOut, empty_env s1) else evaluate (STOP (Loop c1), dec_clock s1))
  else (exit_loop res, s1).
Proof. rewrite evaluate_eqn; cbn [evaluate_body]; rewrite fix_clock_evaluate; reflexivity. Qed.

Lemma ev_break n X : evaluate (stackLang.Break n, X) = (SOME (Break n), X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma inst_load0 r ad (b : word a) v X :
  FLOOKUP (regs X) ad = SOME (Word b) -> mem_load b X = SOME v ->
  inst (Mem Load r (Addr ad (n2w 0))) X = SOME (set_var r v X).
Proof. intros H Hm. apply inst_load with b; [exact H|]. rewrite (proj1 WORD_ADD_0). exact Hm. Qed.

Lemma inst_store0 r ad (b : word a) v X :
  FLOOKUP (regs X) ad = SOME (Word b) -> FLOOKUP (regs X) r = SOME v -> b IN mdomain X ->
  inst (Mem Store r (Addr ad (n2w 0))) X = SOME (set_memory ((b =+ v) (stackSem.memory X)) X).
Proof.
  intros H Hr Hd. rewrite (inst_store r ad (n2w 0) b v X H Hr); rewrite (proj1 WORD_ADD_0); [reflexivity|exact Hd].
Qed.

Lemma bit0_test (w : word a) : fcp_index w 0 = negb (bool_decide ((w && n2w 1)%w = n2w 0)).
Proof.
  pose proof (word_bit_test 0 w) as H. rewrite word_bit_index in H. cbn [N.pow] in H.
  replace (0 <? dimindex a) with true in H by (symmetry; apply N.ltb_lt; pose proof (DIMINDEX_GT_0 a); lia).
  cbn [andb] in H. unfold is_true in H.
  destruct (bool_decide ((w && n2w 1)%w = n2w 0)) eqn:E; cbn [negb].
  - apply bool_decide_spec in E. destruct (fcp_index w 0); [|reflexivity]. exfalso; apply (proj1 H eq_refl), E.
  - apply bool_decide_false in E. apply H, E.
Qed.

Lemma word_sh_lsr1 (w : word a) : good_dimindex a -> wordLang.word_sh ast.Lsr w (w2n (n2w 1 : word a)) = Some (w >>> 1)%w.
Proof.
  intros Hg. rewrite word_1_n2w. unfold wordLang.word_sh.
  replace (dimindex a <=? 1) with false by (symmetry; apply N.leb_gt; destruct Hg as [E|E]; rewrite E; lia).
  reflexivity.
Qed.

Lemma word_list_read {B} `{Inhabited B} : forall (xs : list B) (base : word a) p m d i,
  STAR (word_list base xs) p (fun2set (m, d)) -> i < LENGTH xs ->
  m (base + bytes_in_word * n2w i)%w = EL i xs /\ (base + bytes_in_word * n2w i)%w IN d.
Proof.
  induction xs as [|x xs IH]; intros base p m d i Hs Hi; [cbn in Hi; lia|].
  rewrite LENGTH_cons_N in Hi. cbn [word_list] in Hs. rewrite <- STAR_ASSOC in Hs.
  destruct (N.eq_dec i 0) as [->|Hi0].
  - replace (base + bytes_in_word * n2w 0)%w with base by wring.
    exact (sep_read _ _ _ _ _ Hs).
  - rewrite STAR_swap_l in Hs. destruct (IH _ _ _ _ (i - 1) Hs ltac:(lia)) as [E1 E2].
    replace (base + bytes_in_word * n2w i)%w with (base + bytes_in_word + bytes_in_word * n2w (i - 1))%w.
    + split; [|exact E2]. rewrite E1. replace i with (SUC (i - 1)) at 2 by lia.
      rewrite EL_SUC. reflexivity.
    + replace i with (i - 1 + 1) at 2 by lia. rewrite <- (word_add_n2w (i - 1) 1). wring.
Qed.

Lemma state_ext_fw X Y :
  regs X = regs Y -> fp_regs X = fp_regs Y -> store X = store Y -> stack X = stack Y ->
  stack_space X = stack_space Y -> stackSem.memory X = stackSem.memory Y -> mdomain X = mdomain Y ->
  sh_mdomain X = sh_mdomain Y -> bitmaps X = bitmaps Y -> stackSem.compile X = stackSem.compile Y ->
  compile_oracle X = compile_oracle Y -> code_buffer X = code_buffer Y -> data_buffer X = data_buffer Y ->
  gc_fun X = gc_fun Y -> use_stack X = use_stack Y -> use_store X = use_store Y ->
  use_alloc X = use_alloc Y -> clock X = clock Y -> code X = code Y -> ffi X = ffi Y ->
  ffi_save_regs X = ffi_save_regs Y -> be X = be Y -> X = Y.
Proof. destruct X, Y; cbn; intros; subst; reflexivity. Qed.

Lemma set_regs_memory_same X : set_regs (regs X) (set_memory (stackSem.memory X) X) = X.
Proof. destruct X; reflexivity. Qed.

End LoopHelpers.

Ltac fmap_solve :=
  apply fmap_ext; let key := fresh "key" in intros key; rewrite ?FLOOKUP_UPDATE;
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); subst end;
  try congruence; try reflexivity; try lia.

Section CopyEach.
Context {a : N} {cfg ffi_t : Type}.
Local Open Scope word_scope.

Lemma distinct5 (t1 t2 : N) : ALL_DISTINCT [1; 2; 3; t1; t2] = true ->
  t1 <> 1 /\ t1 <> 2 /\ t1 <> 3 /\ t2 <> 1 /\ t2 <> 2 /\ t2 <> 3 /\ t1 <> t2.
Proof.
  intros H. cbn [ALL_DISTINCT MEM] in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_true_iff in H as [? H] end.
  repeat match goal with
         | Hx : negb (_ || _)%bool = true |- _ => apply negb_true_iff, orb_false_iff in Hx as [? ?]
         | Hx : negb (bool_decide _) = true |- _ => apply negb_true_iff, bool_decide_false in Hx
         | Hx : (_ || _)%bool = false |- _ => apply orb_false_iff in Hx as [? ?]
         | Hx : bool_decide _ = false |- _ => apply bool_decide_false in Hx
         end.
  repeat split; congruence.
Qed.

Lemma lsr1_lt (w : word a) : w <> n2w 0 -> (w2n (w >>> 1) < w2n w)%N.
Proof.
  intros H. rewrite w2n_lsr. cbn [N.pow]. assert (w2n w <> 0%N) by (intros E; apply H, w2n_eq_0, E).
  apply N.div_lt; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "copy_each_thm" *)
Theorem copy_each_thm : forall t1 t2 rest (pattern : word a) i (ad off : word a) bs d m dm i1 a1 m1 x
    (t : state a cfg ffi_t),
  copy_words_for_pattern pattern i ad off bs d m = SOME (i1, (a1, m1)) /\
  ALL_DISTINCT [1; 2; 3; t1; t2] /\ dm = mdomain t /\ good_dimindex a /\
  get_var 1 t = SOME (Word pattern) /\ d SUBSET dm /\
  get_var 2 t = SOME (Word ad) /\
  get_var 3 t = SOME (Word off) /\
  get_var t2 t = SOME (Word (x + bytes_in_word * n2w i)) /\
  STAR (STAR (word_list x (MAP Word bs)) rest) (memory m d) (fun2set (stackSem.memory t, dm)) ->
  exists ck y m2,
    evaluate (stack_remove.copy_each t1 t2, set_clock (clock t + ck) t) =
      (NONE, set_regs ((((if bool_decide (pattern = n2w 1) then regs t else regs t |+ (t1, Word y))
                          |+ (2, Word a1)) |+ (1, Word (n2w 1))) |+ (t2, Word (x + bytes_in_word * n2w i1)))
               (set_memory m2 t)) /\
    STAR (STAR (word_list x (MAP Word bs)) rest) (memory m1 d) (fun2set (m2, dm)).
Proof.
  intros t1 t2 rest pattern.
  induction pattern as [pattern IH] using (well_founded_induction
    (well_founded_ltof _ (fun w : word a => N.to_nat (w2n w)))).
  intros i ad off bs d m dm i1 a1 m1 x t (Hc & Hd & -> & Hg & H1 & Hsub & H2 & H3 & Ht2 & Hs).
  destruct (distinct5 t1 t2 Hd) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold get_var in H1, H2, H3, Ht2.
  rewrite copy_words_for_pattern_def in Hc.
  destruct (bool_decide (pattern = n2w 0)) eqn:E0; [discriminate Hc|]. apply bool_decide_false in E0.
  destruct (bool_decide (pattern = n2w 1)) eqn:E1.
  - (* the loop exits at once *)
    apply bool_decide_spec in E1. injection Hc as <- <- <-.
    exists 0, (n2w 0), (stackSem.memory t). split; [|exact Hs].
    unfold stack_remove.copy_each. rewrite N.add_0_r, set_clock_same, ev_loop, ev_if.
    unfold get_var; rewrite H1. cbn [get_var_imm wordSem.word_cmp]. subst pattern.
    rewrite (proj2 (bool_decide_spec (n2w 1 = n2w 1)) eq_refl). cbn [negb]. rewrite ev_break.
    cbn [cont_loop exit_loop]. rewrite N.eqb_refl.
    replace (((regs t |+ (2, Word ad)) |+ (1, Word (n2w 1))) |+ (t2, Word (x + bytes_in_word * n2w i)))
      with (regs t) by fmap_solve.
    rewrite set_regs_memory_same. reflexivity.
  - apply bool_decide_false in E1.
    destruct (⌜ad IN d⌝ && (i <? LENGTH bs))%bool eqn:Ec; [|discriminate Hc].
    apply andb_true_iff in Ec as [Ead Ei]. apply bool_decide_spec in Ead. apply N.ltb_lt in Ei.
    cbv zeta in Hc.
    set (w := EL i bs) in *. set (b := fcp_index pattern 0) in *.
    set (v := if b then w + off else w) in *.
    (* reading the pattern word *)
    assert (Hr : stackSem.memory t (x + bytes_in_word * n2w i) = Word w /\ (x + bytes_in_word * n2w i) IN mdomain t).
    { rewrite <- STAR_ASSOC in Hs. assert (Hl : (i < LENGTH (MAP Word bs))%N)
        by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact Ei).
      destruct (word_list_read _ _ _ _ _ i Hs Hl) as [Ea Eb]. split; [|exact Eb].
      rewrite Ea, EL_map_N by exact Ei. reflexivity. }
    destruct Hr as [Hrw Hrd].
    assert (Hadm : ad IN mdomain t) by (apply Hsub, Ead).
    (* the state after the loop body (clock adjusted later) *)
    set (R6 := ((((regs t |+ (t1, Word v)) |+ (t2, Word (x + bytes_in_word * n2w (i + 1)%N)))
                  |+ (1, Word (pattern >>> 1))) |+ (2, Word (ad + bytes_in_word)))).
    set (t8 := set_regs R6 (set_memory ((ad =+ Word v) (stackSem.memory t)) t)).
    assert (Hbody : forall C, evaluate (list_Seq [stackLang.load_inst t1 t2; stackLang.add_bytes_in_word_inst t2;
                         If Test 1 (Imm (n2w 1)) Skip (stackLang.add_inst t1 3); stackLang.right_shift_inst 1 1;
                         stackLang.store_inst t1 2; stackLang.add_bytes_in_word_inst 2], set_clock C t) =
                     (NONE, set_clock C t8)).
    { intros C. cbn [list_Seq].
      set (X0 := set_clock C t).
      assert (Hml : mem_load (x + bytes_in_word * n2w i) X0 = SOME (Word w))
        by (unfold mem_load; destruct (classical_dec _); [rewrite <- Hrw; reflexivity|contradiction]).
      rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_load0 t1 t2 _ (Word w) X0 Ht2 Hml))).
      set (X1 := set_var t1 (Word w) X0).
      assert (Ht2' : FLOOKUP (regs X1) t2 = SOME (Word (x + bytes_in_word * n2w i)))
        by (subst X1; rewrite FLOOKUP_set_var_other by congruence; exact Ht2).
      rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_add_imm t2 t2 bytes_in_word _ X1 Ht2'))).
      set (X2 := set_var t2 (Word (x + bytes_in_word * n2w i + bytes_in_word)) X1).
      assert (R2 : forall r, r <> t1 -> r <> t2 -> FLOOKUP (regs X2) r = FLOOKUP (regs t) r)
        by (intros r Hr1 Hr2; subst X2 X1 X0; rewrite !FLOOKUP_set_var_other by congruence; reflexivity).
      assert (EX3 : evaluate (If Test 1 (Imm (n2w 1)) Skip (stackLang.add_inst t1 3), X2) =
                    (NONE, set_var t1 (Word v) X2)).
      { rewrite ev_if. unfold get_var. rewrite (R2 1) by congruence. rewrite H1.
        cbn [get_var_imm wordSem.word_cmp]. subst v b. rewrite bit0_test.
        destruct (bool_decide ((pattern && n2w 1) = n2w 0)); cbn [negb].
        - rewrite ev_skip. f_equal. apply state_ext_fw; stk_fields; try reflexivity.
          subst X2 X1. stk_fields. fmap_solve.
        - apply ev_inst_some. apply inst_add_reg.
          + subst X2 X1. rewrite FLOOKUP_set_var_other by congruence. apply FLOOKUP_set_var_same.
          + rewrite (R2 3) by congruence. exact H3. }
      rewrite (ev_seq_none _ _ _ _ EX3). clear EX3.
      set (X3 := set_var t1 (Word v) X2).
      assert (H13 : FLOOKUP (regs X3) 1 = SOME (Word pattern))
        by (subst X3; rewrite FLOOKUP_set_var_other, (R2 1) by congruence; exact H1).
      rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_shift_imm ast.Lsr 1 1 (n2w 1) pattern (pattern >>> 1) X3
                 H13 (word_sh_lsr1 pattern Hg)))).
      set (X4 := set_var 1 (Word (pattern >>> 1)) X3).
      assert (H24 : FLOOKUP (regs X4) 2 = SOME (Word ad))
        by (subst X4 X3; rewrite !FLOOKUP_set_var_other, (R2 2) by congruence; exact H2).
      assert (Ht14 : FLOOKUP (regs X4) t1 = SOME (Word v))
        by (subst X4 X3; rewrite FLOOKUP_set_var_other by congruence; apply FLOOKUP_set_var_same).
      assert (Had4 : ad IN mdomain X4) by exact Hadm.
      rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_store0 t1 2 ad (Word v) X4 H24 Ht14 Had4))).
      set (X5 := set_memory ((ad =+ Word v) (stackSem.memory X4)) X4).
      assert (H25 : FLOOKUP (regs X5) 2 = SOME (Word ad)) by exact H24.
      rewrite (ev_inst_some _ _ _ (inst_add_imm 2 2 bytes_in_word ad X5 H25)).
      f_equal. subst t8 R6 X5 X4 X3 X2 X1 X0.
      apply state_ext_fw; stk_fields; try reflexivity.
      replace (x + bytes_in_word * n2w i + bytes_in_word) with (x + bytes_in_word * n2w (i + 1)%N)
        by (rewrite <- word_add_n2w; wring).
      fmap_solve. }
    assert (Hlt : ltof _ (fun w : word a => N.to_nat (w2n w)) (pattern >>> 1) pattern)
      by (unfold ltof; pose proof (lsr1_lt pattern E0); lia).
    assert (Hs' : STAR (STAR (word_list x (MAP Word bs)) rest) (memory ((ad =+ Word v) m) d)
                    (fun2set (stackSem.memory t8, mdomain t8))).
    { subst t8. stk_fields. rewrite STAR_COMM in Hs |- *. apply memory_write; auto. }
    assert (G1 : get_var 1 t8 = SOME (Word (pattern >>> 1))) by (subst t8 R6; unfold get_var; stk_fields; rewrite !FLOOKUP_UPDATE;
      repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    assert (G2 : get_var 2 t8 = SOME (Word (ad + bytes_in_word))) by (subst t8 R6; unfold get_var; stk_fields;
      rewrite !FLOOKUP_UPDATE; repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    assert (G3 : get_var 3 t8 = SOME (Word off)) by (subst t8 R6; unfold get_var; stk_fields;
      rewrite !FLOOKUP_UPDATE; repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    assert (Gt2 : get_var t2 t8 = SOME (Word (x + bytes_in_word * n2w (i + 1)%N))) by (subst t8 R6; unfold get_var; stk_fields;
      rewrite !FLOOKUP_UPDATE; repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    destruct (IH (pattern >>> 1) Hlt (i + 1)%N (ad + bytes_in_word) off bs d ((ad =+ Word v) m) (mdomain t8)
                i1 a1 m1 x t8 (conj Hc (conj Hd (conj eq_refl (conj Hg (conj G1 (conj Hsub (conj G2 (conj G3
                (conj Gt2 Hs')))))))))) as (ck' & y' & m2 & E' & S').
    exists (ck' + 1)%N, (if bool_decide (pattern >>> 1 = n2w 1) then v else y'), m2. split; [|exact S'].
    unfold stack_remove.copy_each in E' |- *. rewrite ev_loop, ev_if. unfold get_var. rewrite regs_set_clock, H1.
    cbn [get_var_imm wordSem.word_cmp]. rewrite (bd_false _ E1). cbn [negb].
    rewrite Hbody. cbn [cont_loop]. rewrite clock_set_clock.
    assert (Hc0 : (clock t + (ck' + 1) =? 0)%N = false) by (apply N.eqb_neq; lia). rewrite Hc0.
    unfold STOP. rewrite dec_clock_eq, clock_set_clock, set_clock_set_clock.
    replace (clock t + (ck' + 1) - 1)%N with (clock t8 + ck')%N by (subst t8; stk_fields; lia).
    rewrite E'. f_equal. subst t8 R6. apply state_ext_fw; stk_fields; try reflexivity.
    destruct (bool_decide (pattern >>> 1 = n2w 1)); fmap_solve.
Qed.

End CopyEach.

Section CopyLoop.
Context {a : N} {cfg ffi_t : Type}.
Local Open Scope word_scope.

Lemma msb_lt0 (w : word a) : (w < n2w 0) = word_msb w.
Proof.
  destruct (word_msb w) eqn:E.
  - apply (proj1 (word_msb_neg w)) in E. exact E.
  - apply Bool.not_true_iff_false. intros H. apply (proj2 (word_msb_neg w)) in H. congruence.
Qed.

Lemma copy_loop_unfold t1 t2 :
  @stack_remove.copy_loop a t1 t2 =
  Seq (stackLang.load_inst 1 t2) (Seq (stackLang.add_bytes_in_word_inst t2)
    (Seq (While Less 1 (Imm (n2w 0)) (list_Seq [stack_remove.copy_each t1 t2; stackLang.load_inst 1 t2;
                                                  stackLang.add_bytes_in_word_inst t2]))
         (stack_remove.copy_each t1 t2))).
Proof. reflexivity. Qed.

Lemma prefix_eval (t2 : N) (x : word a) i p (X : state a cfg ffi_t) (rest0 : prog a) :
  t2 <> 1 -> FLOOKUP (regs X) t2 = SOME (Word (x + bytes_in_word * n2w i)) ->
  mem_load (x + bytes_in_word * n2w i) X = SOME (Word p) ->
  evaluate (Seq (stackLang.load_inst 1 t2) (Seq (stackLang.add_bytes_in_word_inst t2) rest0), X) =
  evaluate (rest0, set_var t2 (Word (x + bytes_in_word * n2w (i + 1)%N)) (set_var 1 (Word p) X)).
Proof.
  intros Ht H Hm.
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_load0 1 t2 _ (Word p) X H Hm))).
  assert (H' : FLOOKUP (regs (set_var 1 (Word p) X)) t2 = SOME (Word (x + bytes_in_word * n2w i)))
    by (rewrite FLOOKUP_set_var_other by congruence; exact H).
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_add_imm t2 t2 bytes_in_word _ _ H'))).
  replace (x + bytes_in_word * n2w i + bytes_in_word) with (x + bytes_in_word * n2w (i + 1)%N)
    by (rewrite <- word_add_n2w; wring).
  reflexivity.
Qed.

Lemma prefix2 (t2 : N) (x : word a) i p (X : state a cfg ffi_t) :
  t2 <> 1 -> FLOOKUP (regs X) t2 = SOME (Word (x + bytes_in_word * n2w i)) ->
  mem_load (x + bytes_in_word * n2w i) X = SOME (Word p) ->
  evaluate (Seq (stackLang.load_inst 1 t2) (stackLang.add_bytes_in_word_inst t2), X) =
  (NONE, set_var t2 (Word (x + bytes_in_word * n2w (i + 1)%N)) (set_var 1 (Word p) X)).
Proof.
  intros Ht H Hm.
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_load0 1 t2 _ (Word p) X H Hm))).
  assert (H' : FLOOKUP (regs (set_var 1 (Word p) X)) t2 = SOME (Word (x + bytes_in_word * n2w i)))
    by (rewrite FLOOKUP_set_var_other by congruence; exact H).
  rewrite (ev_inst_some _ _ _ (inst_add_imm t2 t2 bytes_in_word _ _ H')).
  replace (x + bytes_in_word * n2w i + bytes_in_word) with (x + bytes_in_word * n2w (i + 1)%N)
    by (rewrite <- word_add_n2w; wring).
  reflexivity.
Qed.

Lemma ev_seq_cong (p1 p2 : prog a) (X Y : state a cfg ffi_t) :
  evaluate (p1, X) = evaluate (p1, Y) -> evaluate (Seq p1 p2, X) = evaluate (Seq p1 p2, Y).
Proof. intros H; rewrite !ev_seq, H; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "copy_loop_thm" *)
Theorem copy_loop_thm : forall t1 t2 rest i (ad off : word a) bs d m dm (i1 : N) a1 m1 x
    (t : state a cfg ffi_t),
  copy_words i ad off bs d m = SOME (a1, m1) /\
  ALL_DISTINCT [1; 2; 3; t1; t2] /\ dm = mdomain t /\ good_dimindex a /\
  d SUBSET dm /\
  get_var 2 t = SOME (Word ad) /\
  get_var 3 t = SOME (Word off) /\
  get_var t2 t = SOME (Word (x + bytes_in_word * n2w i)) /\
  STAR (STAR (word_list x (MAP Word bs)) rest) (memory m d) (fun2set (stackSem.memory t, dm)) ->
  exists ck (b : bool) y y2 m2,
    evaluate (stack_remove.copy_loop t1 t2, set_clock (clock t + ck) t) =
      (NONE, set_regs ((((if b then regs t else regs t |+ (t1, Word y))
                          |+ (2, Word a1)) |+ (1, Word (n2w 1))) |+ (t2, Word y2))
               (set_memory m2 t)) /\
    STAR (STAR (word_list x (MAP Word bs)) rest) (memory m1 d) (fun2set (m2, dm)).
Proof.
  intros t1 t2 rest i ad off bs. revert i ad.
  refine (well_founded_induction (well_founded_ltof _ (fun i => N.to_nat (LENGTH bs - i))) _ _).
  intros i IH ad d m dm i1 a1 m1 x t (Hc & Hd & -> & Hg & Hsub & H2 & H3 & Ht2 & Hs).
  destruct (distinct5 t1 t2 Hd) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold get_var in H2, H3, Ht2.
  rewrite copy_words_def in Hc. destruct (LENGTH bs <=? i)%N eqn:Elen; [discriminate Hc|].
  apply N.leb_gt in Elen. cbv zeta in Hc.
  set (pattern := EL i bs) in *.
  destruct (copy_words_for_pattern pattern (i + 1)%N ad off bs d m) as [[i1' [a1' m1']]|] eqn:Ecw;
    [|discriminate Hc].
  (* reading the pattern *)
  assert (Hr : stackSem.memory t (x + bytes_in_word * n2w i) = Word pattern /\
               (x + bytes_in_word * n2w i) IN mdomain t).
  { rewrite <- STAR_ASSOC in Hs. assert (Hl : (i < LENGTH (MAP Word bs))%N)
      by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact Elen).
    destruct (word_list_read _ _ _ _ _ i Hs Hl) as [Ea Eb]. split; [|exact Eb].
    rewrite Ea, EL_map_N by exact Elen. reflexivity. }
  destruct Hr as [Hrw Hrd].
  set (t' := set_regs ((regs t |+ (1, Word pattern)) |+ (t2, Word (x + bytes_in_word * n2w (i + 1)%N))) t).
  assert (Hpre : forall C, evaluate (stack_remove.copy_loop t1 t2, set_clock C t) =
                 evaluate (Seq (While Less 1 (Imm (n2w 0)) (list_Seq [stack_remove.copy_each t1 t2;
                   stackLang.load_inst 1 t2; stackLang.add_bytes_in_word_inst t2]))
                   (stack_remove.copy_each t1 t2), set_clock C t')).
  { intros C. rewrite copy_loop_unfold.
    assert (Hm : mem_load (x + bytes_in_word * n2w i) (set_clock C t) = SOME (Word pattern))
      by (unfold mem_load; destruct (classical_dec _); [rewrite <- Hrw; reflexivity|contradiction]).
    rewrite (prefix_eval t2 x i pattern (set_clock C t) _ D4 Ht2 Hm).
    f_equal. all: (f_equal; subst t'; apply state_ext_fw; stk_fields; reflexivity). }
  assert (G1 : get_var 1 t' = SOME (Word pattern))
    by (subst t'; unfold get_var; cbn [regs set_regs]; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
  assert (G2 : get_var 2 t' = SOME (Word ad))
    by (subst t'; unfold get_var; cbn [regs set_regs]; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
  assert (G3 : get_var 3 t' = SOME (Word off))
    by (subst t'; unfold get_var; cbn [regs set_regs]; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
  assert (Gt2 : get_var t2 t' = SOME (Word (x + bytes_in_word * n2w (i + 1)%N)))
    by (subst t'; unfold get_var; cbn [regs set_regs]; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
  destruct (copy_each_thm t1 t2 rest pattern (i + 1)%N ad off bs d m (mdomain t') i1' a1' m1' x t'
              (conj Ecw (conj Hd (conj eq_refl (conj Hg (conj G1 (conj Hsub (conj G2 (conj G3
              (conj Gt2 Hs)))))))))) as (cke & ye & m2e & Ee & Se).
  change (clock t') with (clock t) in Ee.
  assert (Hif : forall C, evaluate (If Less 1 (Imm (n2w 0)) (list_Seq [stack_remove.copy_each t1 t2;
                   stackLang.load_inst 1 t2; stackLang.add_bytes_in_word_inst t2]) (stackLang.Break 0),
                   set_clock C t') =
                 if word_msb pattern then evaluate (list_Seq [stack_remove.copy_each t1 t2;
                   stackLang.load_inst 1 t2; stackLang.add_bytes_in_word_inst t2], set_clock C t')
                 else (SOME (Break 0), set_clock C t')).
  { intros C. rewrite ev_if. rewrite get_var_set_clock, G1. cbn [get_var_imm wordSem.word_cmp].
    rewrite msb_lt0. destruct (word_msb pattern); [reflexivity|apply ev_break]. }
  destruct (word_msb pattern) eqn:Emsb.
  - (* the loop runs again *)
    pose proof (copy_words_for_pattern_LESS_EQ _ _ _ _ _ _ _ _ _ Ecw) as Hle.
    assert (Hlt : ltof _ (fun i => N.to_nat (LENGTH bs - i)) i1' i) by (unfold ltof; lia).
    set (t8 := set_regs ((((if bool_decide (pattern = n2w 1) then regs t' else regs t' |+ (t1, Word ye))
                          |+ (2, Word a1')) |+ (1, Word (n2w 1))) |+ (t2, Word (x + bytes_in_word * n2w i1')))
                  (set_memory m2e t')).
    assert (K2 : get_var 2 t8 = SOME (Word a1'))
      by (subst t8 t'; unfold get_var; cbn [regs set_regs set_memory];
          destruct (bool_decide (pattern = n2w 1)); rewrite !FLOOKUP_UPDATE;
          repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    assert (K3 : get_var 3 t8 = SOME (Word off))
      by (subst t8 t'; unfold get_var; cbn [regs set_regs set_memory];
          destruct (bool_decide (pattern = n2w 1)); rewrite !FLOOKUP_UPDATE;
          repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    assert (Kt2 : get_var t2 t8 = SOME (Word (x + bytes_in_word * n2w i1')))
      by (subst t8 t'; unfold get_var; cbn [regs set_regs set_memory];
          destruct (bool_decide (pattern = n2w 1)); rewrite !FLOOKUP_UPDATE;
          repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
    destruct (IH i1' Hlt a1' d m1' (mdomain t8) i1 a1 m1 x t8
                (conj Hc (conj Hd (conj eq_refl (conj Hg (conj Hsub (conj K2 (conj K3 (conj Kt2 Se)))))))))
      as (ckr & br & yr & y2r & m2r & Er & Sr).
    (* the next pattern *)
    rewrite copy_words_def in Hc. destruct (LENGTH bs <=? i1')%N eqn:Elen'; [discriminate Hc|].
    apply N.leb_gt in Elen'.
    set (p' := EL i1' bs) in *.
    assert (Hr' : m2e (x + bytes_in_word * n2w i1') = Word p').
    { rewrite <- STAR_ASSOC in Se. assert (Hl : (i1' < LENGTH (MAP Word bs))%N)
        by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact Elen').
      destruct (word_list_read _ _ _ _ _ i1' Se Hl) as [Ea _].
      rewrite Ea, EL_map_N by exact Elen'. reflexivity. }
    assert (Hrd' : (x + bytes_in_word * n2w i1') IN mdomain t).
    { rewrite <- STAR_ASSOC in Se. assert (Hl : (i1' < LENGTH (MAP Word bs))%N)
        by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact Elen').
      exact (proj2 (word_list_read _ _ _ _ _ i1' Se Hl)). }
    assert (Hm' : forall C, mem_load (x + bytes_in_word * n2w i1') (set_clock C t8) = SOME (Word p'))
      by (intros C; unfold mem_load; destruct (classical_dec _); [rewrite <- Hr'; reflexivity|contradiction]).
    set (W := (While Less 1 (Imm (n2w 0)) (list_Seq [stack_remove.copy_each t1 t2;
                stackLang.load_inst 1 t2; stackLang.add_bytes_in_word_inst t2]) : prog a)).
    rewrite copy_loop_unfold in Er. fold W in Er.
    rewrite (prefix_eval t2 x i1' p' (set_clock (clock t8 + ckr)%N t8) _ D4 Kt2 (Hm' _)) in Er.
    exists (cke + (ckr + 1))%N, (br && bool_decide (pattern = n2w 1))%bool, (if br then ye else yr), y2r, m2r.
    split; [|exact Sr].
    rewrite Hpre. fold W.
    replace (evaluate (Seq W (stack_remove.copy_each t1 t2), set_clock (clock t + (cke + (ckr + 1)))%N t'))
      with (evaluate (Seq W (stack_remove.copy_each t1 t2),
              set_var t2 (Word (x + bytes_in_word * n2w (i1' + 1)%N)) (set_var 1 (Word p') (set_clock (clock t8 + ckr)%N t8)))).
    + rewrite Er. f_equal. subst t8 t'. apply state_ext_fw; stk_fields; try reflexivity.
      destruct br, (bool_decide (pattern = n2w 1)); cbn [andb]; fmap_solve.
    + symmetry. apply ev_seq_cong. subst W. rewrite ev_loop, Hif. cbn [list_Seq].
      assert (Hn : (@NONE (result a)) <> SOME TimeOut) by discriminate.
      pose proof (evaluate_add_clock (ckr + 1) _ _ _ _ (conj Ee Hn)) as Ee'.
      rewrite clock_set_clock, set_clock_set_clock, <- N.add_assoc in Ee'.
      rewrite (ev_seq_none _ _ _ _ Ee').
      replace (set_clock (clock (set_regs ((((if bool_decide (pattern = n2w 1) then regs t' else regs t' |+ (t1, Word ye))
                          |+ (2, Word a1')) |+ (1, Word (n2w 1))) |+ (t2, Word (x + bytes_in_word * n2w i1')))
                  (set_memory m2e t')) + (ckr + 1))%N
                (set_regs ((((if bool_decide (pattern = n2w 1) then regs t' else regs t' |+ (t1, Word ye))
                          |+ (2, Word a1')) |+ (1, Word (n2w 1))) |+ (t2, Word (x + bytes_in_word * n2w i1')))
                  (set_memory m2e t'))) with (set_clock (clock t8 + (ckr + 1))%N t8) by reflexivity.
      rewrite (prefix2 t2 x i1' p' (set_clock (clock t8 + (ckr + 1))%N t8) D4 Kt2 (Hm' _)).
      cbn [cont_loop]. rewrite clock_set_var, clock_set_var, clock_set_clock.
      assert (Hc0 : (clock t8 + (ckr + 1) =? 0)%N = false) by (apply N.eqb_neq; lia). rewrite Hc0.
      unfold STOP. f_equal. f_equal. apply state_ext_fw; stk_fields; try reflexivity. lia.
  - injection Hc as <- <-.
    exists cke, (bool_decide (pattern = n2w 1)), ye, (x + bytes_in_word * n2w i1'), m2e. split; [|exact Se].
    rewrite Hpre, ev_seq, ev_loop, Hif. cbn [cont_loop exit_loop N.eqb]. rewrite Ee.
    f_equal. subst t'. apply state_ext_fw; stk_fields; try reflexivity.
    destruct (bool_decide (pattern = n2w 1)); fmap_solve.
Qed.

End CopyLoop.


Section CompCorrectDefs.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.

(** Galette-only: the conclusion of [comp_correct] for one program. *)
Definition cc_post jump off k (r : option (result a)) (s2 t2 : state a c ffi_t) : Prop :=
  match r with
  | SOME (Halt _) => ffi t2 = ffi s2
  | SOME TimeOut => ffi t2 = ffi s2
  | SOME (FinalFFI _) => ffi t2 = ffi s2
  | _ => state_rel jump off k s2 t2
  end.

Definition cc_concl jump off k (p : prog a) (r : option (result a)) (s2 t1 : state a c ffi_t) : Prop :=
  exists ck t2, evaluate (stack_remove.comp jump off k p, set_clock (ck + clock t1) t1) = (r, t2) /\
                cc_post jump off k r s2 t2.

Lemma cc_zero jump off k p r s2 t1 t2 :
  evaluate (stack_remove.comp jump off k p, t1) = (r, t2) -> cc_post jump off k r s2 t2 ->
  cc_concl jump off k p r s2 t1.
Proof. intros E P. exists 0, t2. rewrite N.add_0_l, set_clock_same. split; assumption. Qed.

(** State-relation accessors. *)
Lemma sr_use_store jump off k s t : state_rel jump off k s t -> use_store s = true.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.
Lemma sr_use_stack_t jump off k s t : state_rel jump off k s t -> use_stack t = false.
Proof. intros H; unfold state_rel in H; destruct_ands; apply not_true_is_false; assumption. Qed.
Lemma sr_use_store_t jump off k s t : state_rel jump off k s t -> use_store t = false.
Proof. intros H; unfold state_rel in H; destruct_ands; apply not_true_is_false; assumption. Qed.
Lemma sr_use_alloc_s jump off k s t : state_rel jump off k s t -> use_alloc s = false.
Proof. intros H; unfold state_rel in H; destruct_ands; apply not_true_is_false; assumption. Qed.
Lemma sr_use_alloc_t jump off k s t : state_rel jump off k s t -> use_alloc t = false.
Proof. intros H; unfold state_rel in H; destruct_ands; apply not_true_is_false; assumption. Qed.
Lemma sr_code_buffer jump off k s t : state_rel jump off k s t -> code_buffer t = code_buffer s.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.
Lemma sr_sh_mdomain jump off k s t : state_rel jump off k s t -> sh_mdomain t = sh_mdomain s.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.
Lemma sr_ffi_save_regs jump off k s t : state_rel jump off k s t -> ffi_save_regs t = ffi_save_regs s.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.
Lemma sr_k2 jump off k s t : state_rel jump off k s t -> FLOOKUP (regs t) (k + 2) = FLOOKUP (store s) CurrHeap.
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.
Lemma sr_code_rel jump off k s t : state_rel jump off k s t -> code_rel jump off k (code s) (code t).
Proof. intros H; unfold state_rel in H; destruct_ands; assumption. Qed.

Lemma state_rel_empty_env_ffi jump off k s t :
  state_rel jump off k s t -> ffi (empty_env t) = ffi (empty_env s).
Proof. intros H; exact (sr_ffi _ _ _ _ _ H). Qed.

Lemma state_rel_set_code_buffer jump off k s t cb :
  state_rel jump off k s t -> state_rel jump off k (set_code_buffer cb s) (set_code_buffer cb t).
Proof. intros H. unfold state_rel in *; cbv zeta in *; stk_fields. destruct_ands. tauto. Qed.

Lemma state_rel_set_ffi jump off k s t f :
  state_rel jump off k s t -> state_rel jump off k (set_ffi f s) (set_ffi f t).
Proof. intros H. unfold state_rel in *; cbv zeta in *; stk_fields. destruct_ands. tauto. Qed.

Lemma state_rel_dec_clock jump off k s t :
  state_rel jump off k s t -> state_rel jump off k (dec_clock s) (dec_clock t).
Proof. exact (state_rel_IMP jump off k s t). Qed.

End CompCorrectDefs.

Ltac sr_bool :=
  repeat match goal with
  | Hx : (_ && _)%bool = true |- _ => apply andb_true_iff in Hx as [? ?]
  | Hx : is_true (_ && _)%bool |- _ => apply andb_true_iff in Hx as [? ?]
  | Hx : (_ <? _)%N = true |- _ => apply N.ltb_lt in Hx
  | Hx : is_true (_ <? _)%N |- _ => apply N.ltb_lt in Hx
  | Hx : negb _ = true |- _ => apply negb_true_iff in Hx
  | Hx : is_true (negb _) |- _ => apply negb_true_iff in Hx
  | Hx : bool_decide _ = false |- _ => apply bool_decide_false in Hx
  end.

Section SimpleCases.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma cc_skip s1 r s2 t1 :
  evaluate (Skip, s1) = (r, s2) -> state_rel jump off k s1 t1 -> cc_concl jump off k Skip r s2 t1.
Proof.
  intros He H. rewrite ev_skip in He. injection He as <- <-.
  apply (cc_zero _ _ _ _ _ _ _ t1); [apply ev_skip|exact H].
Qed.

Lemma cc_halt v s1 r s2 t1 :
  evaluate (stackLang.Halt v, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (stackLang.Halt v : prog a) k = true -> cc_concl jump off k (stackLang.Halt v) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_halt in He. rewrite <- (sr_get_var _ _ _ _ _ _ H Hb) in He.
  destruct (get_var v t1) as [w|] eqn:Ew; injection He as <- <-; [|congruence].
  apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)); [cbn [stack_remove.comp]; rewrite ev_halt, Ew; reflexivity|].
  exact (sr_ffi _ _ _ _ _ H).
Qed.

Lemma ev_alloc_eq n (X : state a c ffi_t) :
  evaluate (Alloc n, X) =
  if negb (use_alloc X) then (SOME Error, X) else
  match get_var n X with SOME (Word w) => alloc w X | _ => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_alloc n s1 r s2 t1 :
  evaluate (Alloc n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  cc_concl jump off k (Alloc n) r s2 t1.
Proof.
  intros He Hr H. rewrite ev_alloc_eq, (sr_use_alloc_s _ _ _ _ _ H) in He. injection He as <- _. congruence.
Qed.

Lemma cc_inst i s1 r s2 t1 :
  evaluate (Inst i, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Inst i) k = true -> cc_concl jump off k (Inst i) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. rewrite ev_inst in He.
  destruct (inst i s1) as [s'|] eqn:Ei; injection He as <- <-; [|congruence].
  destruct (state_rel_inst jump off k s1 t1 i s' (conj H (conj Hb Ei))) as (t' & Et & R).
  apply (cc_zero _ _ _ _ _ _ _ t'); [cbn [stack_remove.comp]; rewrite ev_inst, Et; reflexivity|exact R].
Qed.

Lemma ev_get_eq v name (X : state a c ffi_t) :
  evaluate (Get v name, X) =
  if negb (use_store X) then (SOME Error, X) else
  match FLOOKUP (store X) name with SOME x => (NONE, set_var v x X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_get v name s1 r s2 t1 :
  evaluate (Get v name, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Get v name : prog a) k = true -> cc_concl jump off k (Get v name) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_get_eq, (sr_use_store _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (FLOOKUP (store s1) name) as [x|] eqn:Ex; injection He as <- <-; [|congruence].
  apply (cc_zero _ _ _ _ _ _ _ (set_var v x t1)); [|apply state_rel_set_var; split; [exact H|exact Hb]].
  cbn [stack_remove.comp]. destruct (decide (name = CurrHeap)) as [->|Hn].
  - apply ev_inst_some, inst_move. rewrite (sr_k2 _ _ _ _ _ H). exact Ex.
  - destruct (state_rel_get_var_k _ _ _ _ _ H) as (c0 & Hk1 & _ & _ & _ & Hm).
    destruct (decide (name = CurrHeap)) as [|_]; [contradiction|].
    apply ev_inst_some. apply (inst_load v (k + 1) (stack_remove.store_offset name) c0); [exact Hk1|].
    exact (mem_load_lemma name s1 x c0 t1 (conj (name_cases name Hn) (conj Ex Hm))).
Qed.

End SimpleCases.

Section SimpleCases2.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma sr_mem_form (M : (word a * word_loc a -> Prop) -> Prop) (bp : word a) (bms buf : list (word a)) sl S L :
  STAR (STAR (STAR (STAR M (word_list bp (MAP Word (bms ++ buf))))
      (word_list_exists (bp + bytes_in_word * n2w (LENGTH (bms ++ buf)))%w sl)) S) L =
  STAR (STAR (STAR (STAR M (word_list bp (MAP Word bms ++ MAP Word buf)))
      (word_list_exists (bp + bytes_in_word * n2w (LENGTH buf + LENGTH bms))%w sl)) S) L.
Proof. rewrite map_app, LENGTH_app_N, (N.add_comm (LENGTH bms)). reflexivity. Qed.

Lemma state_rel_set_CurrHeap s t w :
  state_rel jump off k s t -> state_rel jump off k (set_store CurrHeap w s) (set_var (k + 2) w t).
Proof.
  intros H. unfold state_rel, set_store, set_var in *; cbv zeta in *; stk_fields.
  rewrite !(FLOOKUP_UPDATE (regs t)), !(FLOOKUP_UPDATE (store s)).
  destruct (decide (k + 2 = k + 2)) as [_|]; [|congruence].
  destruct (decide (k + 2 = k + 1)) as [|_]; [lia|].
  destruct (decide (k + 2 = k)) as [|_]; [lia|].
  destruct (decide (CurrHeap = CurrHeap)) as [_|]; [|congruence].
  destruct (decide (CurrHeap = BitmapBase)) as [|_]; [discriminate|].
  destruct_ands. repeat (split; [assumption|]).
  split; [intros n Hn; rewrite FLOOKUP_UPDATE; destruct (decide (k + 2 = n)); [lia|auto]|].
  repeat (split; [try assumption; try reflexivity|]).
  destruct (FLOOKUP (regs t) (k + 1)) as [[base|]|]; try contradiction.
  destruct_ands. repeat (split; [assumption|]). rewrite !word_store_CurrHeap. assumption.
Qed.

Lemma ev_set_eq name v (X : state a c ffi_t) :
  evaluate (Set_ name v, X) =
  if negb (use_store X) then (SOME Error, X) else
  match get_var v X with SOME w => (NONE, set_store name w X) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_set name v s1 r s2 t1 :
  evaluate (Set_ name v, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Set_ name v : prog a) k = true -> cc_concl jump off k (Set_ name v) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb Hbm].
  apply N.ltb_lt in Hb. apply negb_true_iff, bool_decide_false in Hbm.
  rewrite ev_set_eq, (sr_use_store _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (get_var v s1) as [w|] eqn:Ew; injection He as <- <-; [|congruence].
  cbn [stack_remove.comp]. destruct (decide (name = CurrHeap)) as [->|Hn].
  - apply (cc_zero _ _ _ _ _ _ _ (set_var (k + 2) w t1)); [|apply state_rel_set_CurrHeap; exact H].
    apply ev_inst_some, inst_move. rewrite <- (sr_get_var _ _ _ _ _ _ H Hb) in Ew. exact Ew.
  - pose proof (name_cases name Hn) as Hmem.
    destruct (state_rel_get_var_k _ _ _ _ _ H) as (c0 & Hk1 & _ & _ & _ & Hm).
    pose proof (mem_load_lemma2 name s1 c0 t1 (conj Hmem Hm)) as Hd.
    set (ad := (c0 + stack_remove.store_offset name)%w) in *.
    apply (cc_zero _ _ _ _ _ _ _ (set_memory ((ad =+ w) (stackSem.memory t1)) t1)).
    + cbn [stack_remove.comp]. destruct (decide (name = CurrHeap)) as [|_]; [contradiction|].
      apply ev_inst_some. apply inst_store; [exact Hk1| |exact Hd].
      rewrite <- (sr_get_var _ _ _ _ _ _ H Hb) in Ew. exact Ew.
    + cbn [cc_post]. unfold state_rel, set_store in *; cbv zeta in *; stk_fields.
      rewrite !(FLOOKUP_UPDATE (store s1)).
      destruct (decide (name = CurrHeap)) as [|_]; [contradiction|].
      destruct (decide (name = BitmapBase)) as [|_]; [contradiction|].
      destruct_ands. repeat (split; [assumption|]).
      destruct (FLOOKUP (regs t1) (k + 1)) as [[base|]|] eqn:Eb; try contradiction.
      unfold get_var in Hk1. rewrite Eb in Hk1. injection Hk1 as <-.
      destruct_ands. repeat (split; [assumption|]).
      rewrite sr_mem_form in *. subst ad.
      apply (store_write_lemma name s1 base). split; [exact Hmem|assumption].
Qed.

Lemma ev_opcurrheap_eq op v src (X : state a c ffi_t) :
  evaluate (OpCurrHeap op v src, X) =
  if negb (use_store X) then (SOME Error, X) else
  match word_exp X (wordLang.Op op [wordLang.Var src; wordLang.Lookup CurrHeap]) with
  | SOME w => (NONE, set_var v (Word w) X)
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_opcurrheap op v src s1 r s2 t1 :
  evaluate (OpCurrHeap op v src, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (OpCurrHeap op v src : prog a) k = true -> cc_concl jump off k (OpCurrHeap op v src) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_opcurrheap_eq, (sr_use_store _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (word_exp s1 (wordLang.Op op [wordLang.Var src; wordLang.Lookup CurrHeap])) as [w|] eqn:Ew;
    injection He as <- <-; [|congruence].
  apply (cc_zero _ _ _ _ _ _ _ (set_var v (Word w) t1)); [|apply state_rel_set_var; split; [exact H|exact H0]].
  cbn [stack_remove.comp]. apply ev_inst_some. cbn [inst].
  assert (Hne : bool_decide (@Reg a (k + 2) = Reg src) = false)
    by (apply bd_false; intros E; injection E as E; lia).
  rewrite Hne, Bool.andb_false_r. unfold assign.
  replace (word_exp t1 (wordLang.Op op [wordLang.Var src; wordLang.Var (k + 2)])) with (SOME w); [reflexivity|].
  rewrite <- Ew. cbn [word_exp MAP]. rewrite (state_rel_regs _ _ _ _ _ _ H H1), (sr_k2 _ _ _ _ _ H). reflexivity.
Qed.

Lemma ev_tick_eq (X : state a c ffi_t) :
  evaluate (Tick, X) = if (clock X =? 0) then (SOME TimeOut, empty_env X) else (NONE, dec_clock X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_tick s1 r s2 t1 :
  evaluate (Tick, s1) = (r, s2) -> state_rel jump off k s1 t1 -> cc_concl jump off k Tick r s2 t1.
Proof.
  intros He H. rewrite ev_tick_eq in He. pose proof (sr_clock _ _ _ _ _ H) as Hc.
  destruct (clock s1 =? 0) eqn:Ec; injection He as <- <-.
  - apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)); [cbn [stack_remove.comp]; rewrite ev_tick_eq, Hc, Ec; reflexivity|].
    exact (sr_ffi _ _ _ _ _ H).
  - apply (cc_zero _ _ _ _ _ _ _ (dec_clock t1)); [cbn [stack_remove.comp]; rewrite ev_tick_eq, Hc, Ec; reflexivity|].
    apply state_rel_dec_clock, H.
Qed.

Lemma ev_return_eq n (X : state a c ffi_t) :
  evaluate (Return n, X) =
  match get_var n X with SOME (Loc l1 l2) => (SOME (Result (Loc l1 l2)), X) | _ => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_raise_eq n (X : state a c ffi_t) :
  evaluate (Raise n, X) =
  match get_var n X with SOME (Loc l1 l2) => (SOME (Exception (Loc l1 l2)), X) | _ => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_return n s1 r s2 t1 :
  evaluate (Return n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Return n : prog a) k = true -> cc_concl jump off k (Return n) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_return_eq, <- (sr_get_var _ _ _ _ _ _ H Hb) in He.
  destruct (get_var n t1) as [[|l1 l2]|] eqn:Eg; injection He as <- <-; try congruence.
  apply (cc_zero _ _ _ _ _ _ _ t1); [cbn [stack_remove.comp]; rewrite ev_return_eq, Eg; reflexivity|exact H].
Qed.

Lemma cc_raise n s1 r s2 t1 :
  evaluate (Raise n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Raise n : prog a) k = true -> cc_concl jump off k (Raise n) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_raise_eq, <- (sr_get_var _ _ _ _ _ _ H Hb) in He.
  destruct (get_var n t1) as [[|l1 l2]|] eqn:Eg; injection He as <- <-; try congruence.
  apply (cc_zero _ _ _ _ _ _ _ t1); [cbn [stack_remove.comp]; rewrite ev_raise_eq, Eg; reflexivity|exact H].
Qed.

Lemma cc_break n s1 r s2 t1 :
  evaluate (stackLang.Break n, s1) = (r, s2) -> state_rel jump off k s1 t1 ->
  cc_concl jump off k (stackLang.Break n) r s2 t1.
Proof.
  intros He H. rewrite ev_break in He. injection He as <- <-.
  apply (cc_zero _ _ _ _ _ _ _ t1); [apply ev_break|exact H].
Qed.

Lemma ev_continue n (X : state a c ffi_t) : evaluate (stackLang.Continue n, X) = (SOME (Continue n), X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_continue n s1 r s2 t1 :
  evaluate (stackLang.Continue n, s1) = (r, s2) -> state_rel jump off k s1 t1 ->
  cc_concl jump off k (stackLang.Continue n) r s2 t1.
Proof.
  intros He H. rewrite ev_continue in He. injection He as <- <-.
  apply (cc_zero _ _ _ _ _ _ _ t1); [apply ev_continue|exact H].
Qed.

Lemma ev_cbw_eq r1 r2 (X : state a c ffi_t) :
  evaluate (CodeBufferWrite r1 r2, X) =
  match get_var r1 X, get_var r2 X with
  | SOME (Word w1), SOME (Word w2) =>
      match wordSem.buffer_write (code_buffer X) w1 (w2w w2) with
      | SOME new_cb => (NONE, set_code_buffer new_cb X)
      | _ => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_cbw r1 r2 s1 r s2 t1 :
  evaluate (CodeBufferWrite r1 r2, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (CodeBufferWrite r1 r2 : prog a) k = true -> cc_concl jump off k (CodeBufferWrite r1 r2) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_cbw_eq, <- (sr_get_var _ _ _ _ _ _ H H0), <- (sr_get_var _ _ _ _ _ _ H H1),
    <- (sr_code_buffer _ _ _ _ _ H) in He.
  destruct (get_var r1 t1) as [[w1|]|] eqn:E1; try (injection He as <- <-; congruence).
  destruct (get_var r2 t1) as [[w2|]|] eqn:E2; try (injection He as <- <-; congruence).
  destruct (wordSem.buffer_write (code_buffer t1) w1 (w2w w2)) as [cb|] eqn:Eb; injection He as <- <-; [|congruence].
  apply (cc_zero _ _ _ _ _ _ _ (set_code_buffer cb t1)).
  - cbn [stack_remove.comp]. rewrite ev_cbw_eq, E1, E2, Eb. reflexivity.
  - rewrite (sr_code_buffer _ _ _ _ _ H) in Eb. cbn [cc_post].
    replace (set_code_buffer cb s1) with (set_code_buffer cb s1) by reflexivity.
    apply state_rel_set_code_buffer, H.
Qed.

Lemma ev_locvalue_eq r l1 l2 (X : state a c ffi_t) :
  evaluate (LocValue r l1 l2, X) =
  if classical_dec (loc_check (code X) (l1, l2)) then (NONE, set_var r (Loc l1 l2) X) else (SOME Error, X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_locvalue rg l1 l2 s1 r s2 t1 :
  evaluate (LocValue rg l1 l2, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (LocValue rg l1 l2 : prog a) k = true -> cc_concl jump off k (LocValue rg l1 l2) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_locvalue_eq in He. destruct (classical_dec _) as [Hl|]; injection He as <- <-; [|congruence].
  pose proof (code_rel_loc_check _ _ _ _ _ _ _ (conj (sr_code_rel _ _ _ _ _ H) Hl)) as Hl'.
  apply (cc_zero _ _ _ _ _ _ _ (set_var rg (Loc l1 l2) t1)).
  - cbn [stack_remove.comp]. rewrite ev_locvalue_eq. destruct (classical_dec _); [reflexivity|contradiction].
  - apply state_rel_set_var; split; [exact H|exact Hb].
Qed.

Lemma cc_stackalloc n s1 r s2 t1 :
  evaluate (StackAlloc n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  cc_concl jump off k (StackAlloc n) r s2 t1.
Proof.
  intros He Hr H.
  destruct (evaluate_stack_alloc off jump k n r s1 s2 t1 (conj He (conj Hr H))) as (ck & t2 & E & P).
  exists ck, t2. split; [exact E|].
  rewrite ev_stackalloc_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (stack_space s1 <? n); injection He as <- <-.
  - destruct (classical_dec _) as [Hw|_]; [exfalso; exact (Hw _ eq_refl)|exact P].
  - destruct (classical_dec _) as [_|Hn]; [exact P|exfalso; apply Hn; intros w; discriminate].
Qed.

Lemma cc_stackfree n s1 r s2 t1 :
  evaluate (StackFree n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  cc_concl jump off k (StackFree n) r s2 t1.
Proof.
  intros He Hr H.
  destruct (evaluate_stack_free jump off k n r s1 s2 t1 (conj He (conj Hr H))) as (ck & t2 & E & P).
  exists ck, t2. split; [exact E|].
  rewrite ev_stackfree_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (LENGTH (stack s1) <? stack_space s1 + n); injection He as <- <-; [congruence|exact P].
Qed.

End SimpleCases2.


(** Galette-only: AC reasoning on separating conjunctions. *)
Ltac star_front x :=
  repeat first [ rewrite (STAR_swap_l _ x _) | rewrite (STAR_COMM _ x) ].

Ltac star_ac_loop :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- ?R = STAR ?x ?r1 => star_front x; apply (f_equal (STAR x)); star_ac_loop
  end.

Ltac star_ac := repeat rewrite <- STAR_ASSOC; star_ac_loop.

Section StackCases.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma set_var_twice r v1 v2 (X : state a c ffi_t) : set_var r v2 (set_var r v1 X) = set_var r v2 X.
Proof. unfold set_var; cbn [regs set_regs]. rewrite regs_update_twice. reflexivity. Qed.

Lemma set_regs_upd_twice r v1 v2 (X : state a c ffi_t) :
  set_var r v2 (set_regs (regs X |+ (r, v1)) X) = set_var r v2 X.
Proof. unfold set_var; cbn [regs set_regs]. rewrite regs_update_twice. reflexivity. Qed.

(** Reading the stack through [state_rel]. *)
Lemma sr_stack_read s t idx :
  state_rel jump off k s t -> idx < LENGTH (stack s) ->
  exists base, FLOOKUP (regs t) (k + 1) = SOME (Word base) /\
    FLOOKUP (regs t) k = SOME (Word (base + bytes_in_word * n2w (stack_space s))%w) /\
    stackSem.memory t (base + bytes_in_word * n2w idx)%w = EL idx (stack s) /\
    (base + bytes_in_word * n2w idx)%w IN mdomain t.
Proof.
  intros H Hi. destruct (state_rel_get_var_k _ _ _ _ _ H) as (c0 & Hk1 & _ & _ & Hk & Hm).
  exists c0. split; [exact Hk1|]. split; [exact Hk|].
  rewrite STAR_COMM in Hm. exact (word_list_read _ _ _ _ _ idx Hm Hi).
Qed.

Lemma ev_stackload_eq r n (X : state a c ffi_t) :
  evaluate (StackLoad r n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if (stack_space X + n <? LENGTH (stack X))%N
  then (NONE, set_var r (EL (stack_space X + n) (stack X)) X)
  else (SOME Error, empty_env X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma mem_load_of (X : state a c ffi_t) ad v : stackSem.memory X ad = v -> ad IN mdomain X -> mem_load ad X = SOME v.
Proof. intros E D. unfold mem_load. destruct (classical_dec _); [rewrite E; reflexivity|contradiction]. Qed.

Lemma cc_stackload rg n s1 r s2 t1 :
  evaluate (StackLoad rg n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StackLoad rg n : prog a) k = true -> cc_concl jump off k (StackLoad rg n) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_stackload_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (stack_space s1 + n <? LENGTH (stack s1)) eqn:El; injection He as <- <-; [|congruence].
  apply N.ltb_lt in El.
  destruct (sr_stack_read _ _ _ H El) as (base & Hk1 & Hk & Hm & Hd).
  apply (cc_zero _ _ _ _ _ _ _ (set_var rg (EL (stack_space s1 + n) (stack s1)) t1));
    [|apply state_rel_set_var; split; [exact H|exact Hb]].
  assert (Ea : ((base + bytes_in_word * n2w (stack_space s1)) + stack_remove.word_offset n)%w =
               (base + bytes_in_word * n2w (stack_space s1 + n))%w)
    by (rewrite word_offset_eq, <- word_add_n2w; wring).
  cbn [stack_remove.comp]. cbv zeta.
  destruct (offset_ok 0 off (stack_remove.word_offset n)).
  - apply ev_inst_some. apply (inst_load _ _ _ _ _ _ Hk). rewrite Ea. apply mem_load_of; assumption.
  - unfold stack_remove.stack_load.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_move rg k _ t1 Hk))).
    set (X1 := set_var rg (Word (base + bytes_in_word * n2w (stack_space s1))%w) t1).
    rewrite (ev_seq_none _ _ _ _ (evaluate_upshift rg n X1 _ (FLOOKUP_set_var_same _ _ _))).
    set (X2 := set_regs (regs X1 |+ (rg, Word (base + bytes_in_word * n2w (stack_space s1) +
                                               stack_remove.word_offset n)%w)) X1).
    assert (F2 : FLOOKUP (regs X2) rg = SOME (Word (base + bytes_in_word * n2w (stack_space s1) +
                                                    stack_remove.word_offset n)%w))
      by (subst X2; cbn [regs set_regs]; rewrite FLOOKUP_UPDATE; destruct (decide (rg = rg)); [reflexivity|congruence]).
    assert (M2 : mem_load (base + bytes_in_word * n2w (stack_space s1) + stack_remove.word_offset n)%w X2 =
                 SOME (EL (stack_space s1 + n) (stack s1)))
      by (rewrite Ea; apply mem_load_of; assumption).
    rewrite (ev_inst_some _ _ _ (inst_load0 rg rg _ _ X2 F2 M2)).
    subst X2 X1. rewrite set_regs_upd_twice, set_var_twice. reflexivity.
Qed.

End StackCases.

Section StackCases2.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma aligned_addr (w base : word a) ss :
  good_dimindex a -> ((w >>> word_shift a) << word_shift a)%w = w ->
  (w + (base + bytes_in_word * n2w ss))%w = (base + bytes_in_word * n2w (ss + w2n (w >>> word_shift a)%w))%w.
Proof.
  intros Hg Ha. rewrite <- Ha at 1. rewrite (lsl_word_shift _ Hg).
  rewrite <- word_add_n2w, <- (n2w_w2n (w >>> word_shift a)%w) at 1. wring.
Qed.

Lemma ev_stackloadany_eq r rn (X : state a c ffi_t) :
  evaluate (StackLoadAny r rn, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match get_var rn X with
  | SOME (Word w) =>
      let i := (stack_space X + w2n (w >>> word_shift a)%w)%N in
      if andb (i <? LENGTH (stack X))%N (bool_decide ((w >>> word_shift a) << word_shift a = w)%w)
      then (NONE, set_var r (EL i (stack X)) X)
      else (SOME Error, empty_env X)
  | _ => (SOME Error, empty_env X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_stackloadany rg rn s1 r s2 t1 :
  evaluate (StackLoadAny rg rn, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StackLoadAny rg rn : prog a) k = true -> cc_concl jump off k (StackLoadAny rg rn) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
  apply N.ltb_lt in Hb1, Hb2.
  rewrite ev_stackloadany_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (get_var rn s1) as [[w|]|] eqn:Ew; try (injection He as <- <-; congruence). cbv zeta in He.
  destruct (stack_space s1 + w2n (w >>> word_shift a)%w <? LENGTH (stack s1)) eqn:El;
    [|injection He as <- <-; congruence].
  destruct (bool_decide ((w >>> word_shift a) << word_shift a = w)%w) eqn:Ea;
    [|injection He as <- <-; congruence].
  cbn [andb] in He. injection He as <- <-. apply N.ltb_lt in El. apply bool_decide_spec in Ea.
  destruct (sr_stack_read jump off k _ _ _ H El) as (base & Hk1 & Hk & Hm & Hd).
  apply (cc_zero _ _ _ _ _ _ _ (set_var rg (EL (stack_space s1 + w2n (w >>> word_shift a)%w) (stack s1)) t1));
    [|apply state_rel_set_var; split; [exact H|exact Hb1]].
  cbn [stack_remove.comp].
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb2) in Ew. unfold get_var in Ew.
  assert (F1 : FLOOKUP (regs (set_var rg (Word w) t1)) rg = SOME (Word w)) by apply FLOOKUP_set_var_same.
  assert (F2 : FLOOKUP (regs (set_var rg (Word w) t1)) k = SOME (Word (base + bytes_in_word * n2w (stack_space s1))%w))
    by (rewrite FLOOKUP_set_var_other by lia; exact Hk).
  assert (EAB : evaluate (Seq (stackLang.move rg rn) (stackLang.add_inst rg k), t1) =
                (NONE, set_var rg (Word (w + (base + bytes_in_word * n2w (stack_space s1)))%w) (set_var rg (Word w) t1))).
  { rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_move rg rn _ t1 Ew))).
    exact (ev_inst_some _ _ _ (inst_add_reg rg rg k _ _ _ F1 F2)). }
  rewrite (ev_seq_none _ _ _ _ EAB).
  rewrite (aligned_addr _ _ _ (sr_good _ _ _ _ _ H) Ea).
  assert (M3 : mem_load (base + bytes_in_word * n2w (stack_space s1 + w2n (w >>> word_shift a)%w))%w
                 (set_var rg (Word (base + bytes_in_word * n2w (stack_space s1 + w2n (w >>> word_shift a)%w))%w)
                   (set_var rg (Word w) t1)) = SOME (EL (stack_space s1 + w2n (w >>> word_shift a)%w) (stack s1)))
    by (apply mem_load_of; assumption).
  rewrite (ev_inst_some _ _ _ (inst_load0 rg rg _ _ _ (FLOOKUP_set_var_same _ _ _) M3)).
  rewrite !set_var_twice. reflexivity.
Qed.

Lemma ev_stackstore_eq r n (X : state a c ffi_t) :
  evaluate (StackStore r n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if (LENGTH (stack X) <=? stack_space X + n)%N then (SOME Error, empty_env X) else
  match get_var r X with
  | NONE => (SOME Error, empty_env X)
  | SOME v => (NONE, set_stack (LUPDATE v (stack_space X + n) (stack X)) X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_stackstore rg n s1 r s2 t1 :
  evaluate (StackStore rg n, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StackStore rg n : prog a) k = true -> cc_concl jump off k (StackStore rg n) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_stackstore_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (LENGTH (stack s1) <=? stack_space s1 + n) eqn:El; [injection He as <- <-; congruence|].
  apply N.leb_gt in El.
  destruct (get_var rg s1) as [v|] eqn:Ev; injection He as <- <-; [|congruence].
  destruct (sr_stack_read jump off k _ _ _ H El) as (base & Hk1 & Hk & Hm & Hd).
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb) in Ev. unfold get_var in Ev.
  set (ad := (base + bytes_in_word * n2w (stack_space s1 + n))%w) in *.
  assert (Ea : ((base + bytes_in_word * n2w (stack_space s1)) + stack_remove.word_offset n)%w = ad)
    by (subst ad; rewrite word_offset_eq, <- word_add_n2w; wring).
  assert (R : state_rel jump off k (set_stack (LUPDATE v (stack_space s1 + n) (stack s1)) s1)
                (set_memory ((ad =+ v) (stackSem.memory t1)) t1)).
  { rewrite N.add_comm.
    apply (state_rel_stack_store jump off k s1 t1 (stack s1) (base + bytes_in_word * n2w (stack_space s1))%w n ad v).
    split; [exact H|]. split; [reflexivity|]. split; [exact Hk|]. split; [lia|].
    rewrite word_offset_eq in Ea. exact Ea. }
  apply (cc_zero _ _ _ _ _ _ _ (set_memory ((ad =+ v) (stackSem.memory t1)) t1)); [|exact R].
  cbn [stack_remove.comp]. cbv zeta.
  destruct (offset_ok 0 off (stack_remove.word_offset n)).
  - apply ev_inst_some. rewrite <- Ea. apply (inst_store _ _ _ _ _ _ Hk Ev). rewrite Ea. exact Hd.
  - unfold stack_remove.stack_store.
    rewrite (ev_seq_none _ _ _ _ (evaluate_upshift k n t1 _ Hk)).
    set (X1 := set_regs (regs t1 |+ (k, Word (base + bytes_in_word * n2w (stack_space s1) + stack_remove.word_offset n)%w)) t1).
    assert (F1 : FLOOKUP (regs X1) k = SOME (Word ad))
      by (subst X1; cbn [regs set_regs]; rewrite FLOOKUP_UPDATE, Ea; destruct (decide (k = k)); [reflexivity|congruence]).
    assert (F2 : FLOOKUP (regs X1) rg = SOME v)
      by (subst X1; cbn [regs set_regs]; rewrite FLOOKUP_UPDATE; destruct (decide (k = rg)); [lia|exact Ev]).
    assert (D1 : ad IN mdomain X1) by exact Hd.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_store0 rg k ad v X1 F1 F2 D1))).
    rewrite (evaluate_downshift k n (set_memory ((ad =+ v) (stackSem.memory X1)) X1) ad F1).
    f_equal. subst X1. apply state_ext_fw; stk_fields; try reflexivity.
    apply fmap_ext; intros key. rewrite !FLOOKUP_UPDATE. destruct (decide (k = key)) as [<-|]; [|reflexivity].
    rewrite Hk. f_equal. f_equal. rewrite <- Ea. wring.
Qed.

End StackCases2.

Section StackCases3.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma ev_stackstoreany_eq r rn (X : state a c ffi_t) :
  evaluate (StackStoreAny r rn, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match get_var r X, get_var rn X with
  | SOME v, SOME (Word w) =>
      let i := (stack_space X + w2n (w >>> word_shift a)%w)%N in
      if andb (i <? LENGTH (stack X))%N (bool_decide ((w >>> word_shift a) << word_shift a = w)%w)
      then (NONE, set_stack (LUPDATE v i (stack X)) X)
      else (SOME Error, empty_env X)
  | _, _ => (SOME Error, empty_env X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_stackstoreany rg rn s1 r s2 t1 :
  evaluate (StackStoreAny rg rn, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StackStoreAny rg rn : prog a) k = true -> cc_concl jump off k (StackStoreAny rg rn) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
  apply N.ltb_lt in Hb1, Hb2.
  rewrite ev_stackstoreany_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (get_var rg s1) as [v|] eqn:Ev; [|injection He as <- <-; congruence].
  destruct (get_var rn s1) as [[w|]|] eqn:Ew; try (injection He as <- <-; congruence). cbv zeta in He.
  destruct (stack_space s1 + w2n (w >>> word_shift a)%w <? LENGTH (stack s1)) eqn:El;
    [|injection He as <- <-; congruence].
  destruct (bool_decide ((w >>> word_shift a) << word_shift a = w)%w) eqn:Ea;
    [|injection He as <- <-; congruence].
  cbn [andb] in He. injection He as <- <-. apply N.ltb_lt in El. apply bool_decide_spec in Ea.
  destruct (sr_stack_read jump off k _ _ _ H El) as (base & Hk1 & Hk & Hm & Hd).
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb1) in Ev. rewrite <- (sr_get_var _ _ _ _ _ _ H Hb2) in Ew.
  unfold get_var in Ev, Ew.
  set (idx := (stack_space s1 + w2n (w >>> word_shift a)%w)%N) in *.
  set (ad := (base + bytes_in_word * n2w idx)%w) in *.
  assert (Ead : ((base + bytes_in_word * n2w (stack_space s1)) + w)%w = ad)
    by (subst ad idx; rewrite WORD_ADD_COMM; exact (aligned_addr _ _ _ (sr_good _ _ _ _ _ H) Ea)).
  assert (R : state_rel jump off k (set_stack (LUPDATE v idx (stack s1)) s1)
                (set_memory ((ad =+ v) (stackSem.memory t1)) t1)).
  { subst idx. rewrite N.add_comm.
    apply (state_rel_stack_store jump off k s1 t1 (stack s1) (base + bytes_in_word * n2w (stack_space s1))%w
             (w2n (w >>> word_shift a)%w) ad v).
    split; [exact H|]. split; [reflexivity|]. split; [exact Hk|]. split; [lia|].
    subst ad. rewrite <- word_add_n2w. wring. }
  apply (cc_zero _ _ _ _ _ _ _ (set_memory ((ad =+ v) (stackSem.memory t1)) t1)); [|exact R].
  cbn [stack_remove.comp].
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_add_reg k k rn _ _ t1 Hk Ew))).
  set (X1 := set_var k (Word (base + bytes_in_word * n2w (stack_space s1) + w)%w) t1).
  assert (F1 : FLOOKUP (regs X1) k = SOME (Word ad)) by (subst X1; rewrite FLOOKUP_set_var_same, Ead; reflexivity).
  assert (F2 : FLOOKUP (regs X1) rg = SOME v) by (subst X1; rewrite FLOOKUP_set_var_other by lia; exact Ev).
  assert (D1 : ad IN mdomain X1) by exact Hd.
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_store0 rg k ad v X1 F1 F2 D1))).
  set (X2 := set_memory ((ad =+ v) (stackSem.memory X1)) X1).
  assert (F3 : FLOOKUP (regs X2) rn = SOME (Word w)) by (subst X2 X1; cbn [regs set_memory];
    rewrite FLOOKUP_set_var_other by lia; exact Ew).
  rewrite (ev_inst_some _ _ _ (inst_sub_reg k k rn ad w X2 F1 F3)).
  f_equal. subst X2 X1. apply state_ext_fw; stk_fields; try reflexivity.
  apply fmap_ext; intros key. rewrite !FLOOKUP_UPDATE. destruct (decide (k = key)) as [<-|]; [|reflexivity].
  rewrite Hk. f_equal. f_equal. rewrite <- Ead. wring.
Qed.

Lemma ev_stackgetsize_eq r (X : state a c ffi_t) :
  evaluate (StackGetSize r, X) =
  if negb (use_stack X) then (SOME Error, X) else (NONE, set_var r (Word (n2w (stack_space X))) X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma word_shift_lt (Hg : good_dimindex a) : w2n (n2w (word_shift a) : word a) = word_shift a /\ word_shift a < dimindex a.
Proof.
  unfold word_shift. destruct Hg as [E|E]; rewrite E; cbn [N.eqb]; rewrite w2n_n2w, dimword_pow, E; cbn; lia.
Qed.

Lemma word_sh_ws sh (w : word a) (Hg : good_dimindex a) :
  sh <> ast.Ror -> sh <> ast.Asr ->
  wordLang.word_sh sh w (w2n (n2w (word_shift a) : word a)) =
  Some (match sh with ast.Lsl => (w << word_shift a)%w | _ => (w >>> word_shift a)%w end).
Proof.
  intros H1 H2. destruct (word_shift_lt Hg) as [E L]. rewrite E. unfold wordLang.word_sh.
  replace (dimindex a <=? word_shift a) with false by (symmetry; apply N.leb_gt; exact L).
  rewrite Bool.andb_false_r. destruct sh; congruence.
Qed.

Lemma cc_stackgetsize rg s1 r s2 t1 :
  evaluate (StackGetSize rg, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StackGetSize rg : prog a) k = true -> cc_concl jump off k (StackGetSize rg) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_stackgetsize_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He. injection He as <- <-.
  apply (cc_zero _ _ _ _ _ _ _ (set_var rg (Word (n2w (stack_space s1))) t1));
    [|apply state_rel_set_var; split; [exact H|exact Hb]].
  destruct (state_rel_get_var_k _ _ _ _ _ H) as (base & Hk1 & Hc & Hl & Hk & _).
  unfold get_var in Hk1, Hk. pose proof (sr_good _ _ _ _ _ H) as Hg.
  pose proof (sr_ss _ _ _ _ _ H) as Hss.
  cbn [stack_remove.comp].
  assert (F1 : FLOOKUP (regs (set_var rg (Word (base + bytes_in_word * n2w (stack_space s1))%w) t1)) rg =
               SOME (Word (base + bytes_in_word * n2w (stack_space s1))%w)) by apply FLOOKUP_set_var_same.
  assert (F2 : FLOOKUP (regs (set_var rg (Word (base + bytes_in_word * n2w (stack_space s1))%w) t1)) (k + 1) =
               SOME (Word base)) by (rewrite FLOOKUP_set_var_other by lia; exact Hk1).
  assert (EAB : evaluate (Seq (stackLang.move rg k) (stackLang.sub_inst rg (k + 1)), t1) =
                (NONE, set_var rg (Word (base + bytes_in_word * n2w (stack_space s1) - base)%w)
                         (set_var rg (Word (base + bytes_in_word * n2w (stack_space s1))%w) t1))).
  { rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_move rg k _ t1 Hk))).
    exact (ev_inst_some _ _ _ (inst_sub_reg rg rg (k + 1) _ _ _ F1 F2)). }
  rewrite (ev_seq_none _ _ _ _ EAB).
  replace (base + bytes_in_word * n2w (stack_space s1) - base)%w with (bytes_in_word * n2w (stack_space s1) : word a)%w
    by wring.
  assert (Hsh : ((bytes_in_word * n2w (stack_space s1) : word a) >>> word_shift a)%w = n2w (stack_space s1)).
  { apply bytes_in_word_word_shift. split; [exact Hg|].
    rewrite w2n_n2w. destruct (good_dimindex_d Hg) as [Hd _]. rewrite Hd in Hl |- *.
    pose proof (N.Div0.mod_le (stack_space s1) (dimword a)).
    assert (dimindex a DIV 8 * (stack_space s1 MOD dimword a) <= dimindex a DIV 8 * LENGTH (stack s1))
      by (apply N.mul_le_mono_l; lia). lia. }
  rewrite (ev_inst_some _ _ _ (inst_shift_imm ast.Lsr rg rg (n2w (word_shift a)) _ _ _
             (FLOOKUP_set_var_same _ _ _) (word_sh_ws ast.Lsr _ Hg ltac:(discriminate) ltac:(discriminate)))).
  cbn beta iota. rewrite Hsh, !set_var_twice. reflexivity.
Qed.

Lemma ev_stacksetsize_eq r (X : state a c ffi_t) :
  evaluate (StackSetSize r, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match get_var r X with
  | SOME (Word w) =>
      if (LENGTH (stack X) <=? w2n w)%N then (SOME Error, empty_env X)
      else (NONE, set_var r (Word (w << word_shift a)%w) (set_stack_space (w2n w) X))
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_stacksetsize rg s1 r s2 t1 :
  evaluate (StackSetSize rg, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StackSetSize rg : prog a) k = true -> cc_concl jump off k (StackSetSize rg) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb; sr_bool.
  rewrite ev_stacksetsize_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (get_var rg s1) as [[w|]|] eqn:Ew; try (injection He as <- <-; congruence).
  destruct (LENGTH (stack s1) <=? w2n w) eqn:El; injection He as <- <-; [congruence|]. apply N.leb_gt in El.
  destruct (state_rel_get_var_k _ _ _ _ _ H) as (base & Hk1 & Hc & Hl & Hk & _).
  unfold get_var in Hk1, Hk. pose proof (sr_good _ _ _ _ _ H) as Hg.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb) in Ew. unfold get_var in Ew.
  assert (Hlsl : (w << word_shift a)%w = (bytes_in_word * n2w (w2n w))%w)
    by (rewrite (lsl_word_shift _ Hg), n2w_w2n; wring).
  set (t' := set_var rg (Word (w << word_shift a)%w) (set_var k (Word (base + bytes_in_word * n2w (w2n w))%w) t1)).
  apply (cc_zero _ _ _ _ _ _ _ t').
  - cbn [stack_remove.comp].
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_shift_imm ast.Lsl rg rg (n2w (word_shift a)) _ _ _
               Ew (word_sh_ws ast.Lsl _ Hg ltac:(discriminate) ltac:(discriminate))))).
    cbn beta iota.
    set (X1 := set_var rg (Word (w << word_shift a)%w) t1).
    assert (F1 : FLOOKUP (regs X1) (k + 1) = SOME (Word base)) by (subst X1; rewrite FLOOKUP_set_var_other by lia; exact Hk1).
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_move k (k + 1) _ X1 F1))).
    assert (F2 : FLOOKUP (regs (set_var k (Word base) X1)) k = SOME (Word base)) by apply FLOOKUP_set_var_same.
    assert (F3 : FLOOKUP (regs (set_var k (Word base) X1)) rg = SOME (Word (w << word_shift a)%w))
      by (rewrite FLOOKUP_set_var_other by lia; subst X1; apply FLOOKUP_set_var_same).
    rewrite (ev_inst_some _ _ _ (inst_add_reg k k rg _ _ _ F2 F3)).
    f_equal. subst t' X1. rewrite set_var_twice, Hlsl.
    apply state_ext_fw; stk_fields; try reflexivity. fmap_solve.
  - cbn [cc_post]. subst t'. apply state_rel_set_var. split; [|exact Hb].
    apply state_rel_set_k; [exact H|exact Hk1|lia].
Qed.

End StackCases3.

Section StackCases4.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma EL_app_l_N {A} `{Inhabited A} : forall (l1 l2 : list A) i, i < LENGTH l1 -> EL i (l1 ++ l2) = EL i l1.
Proof.
  induction l1 as [|x l1 IH]; intros l2 i Hi; [cbn in Hi; lia|].
  destruct (N.eq_dec i 0) as [->|Hi0]; [reflexivity|].
  replace i with (SUC (i - 1)) by lia. cbn [app]. rewrite !EL_SUC. cbn [TL].
  apply IH. rewrite LENGTH_cons_N in Hi. lia.
Qed.

Lemma sr_mem_W1 (M W1 W2 S L : (word a * word_loc a -> Prop) -> Prop) :
  STAR (STAR (STAR (STAR M W1) W2) S) L = STAR W1 (STAR M (STAR W2 (STAR S L))).
Proof. star_ac. Qed.

Lemma ev_bitmapload_eq r v (X : state a c ffi_t) :
  evaluate (BitmapLoad r v, X) =
  if orb (negb (use_stack X)) (r =? v)%N then (SOME Error, X) else
  match get_var v X with
  | SOME (Word w) =>
      if (LENGTH (bitmaps X) <=? w2n w)%N then (SOME Error, X)
      else (NONE, set_var r (Word (EL (w2n w) (bitmaps X))) X)
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma sr_bitmapbase s t : state_rel jump off k s t ->
  exists ww, FLOOKUP (store s) BitmapBase = SOME (Word ww).
Proof.
  intros H; unfold state_rel in H; destruct_ands.
  match goal with Hx : is_true (is_SOME_Word _) |- _ => revert Hx end.
  unfold is_SOME_Word. destruct (FLOOKUP (store s) BitmapBase) as [[ww|]|]; intros Hx; try discriminate. eauto.
Qed.

Lemma cc_bitmapload rg v s1 r s2 t1 :
  evaluate (BitmapLoad rg v, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (BitmapLoad rg v : prog a) k = true -> cc_concl jump off k (BitmapLoad rg v) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
  apply N.ltb_lt in Hb1, Hb2.
  rewrite ev_bitmapload_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb orb] in He.
  destruct (rg =? v) eqn:Erv; [injection He as <- <-; congruence|]. apply N.eqb_neq in Erv.
  destruct (get_var v s1) as [[w|]|] eqn:Ew; try (injection He as <- <-; congruence).
  destruct (LENGTH (bitmaps s1) <=? w2n w) eqn:El; injection He as <- <-; [congruence|]. apply N.leb_gt in El.
  destruct (sr_bitmapbase _ _ H) as (ww & Eww).
  destruct (state_rel_get_var_k _ _ _ _ _ H) as (base & Hk1 & _ & _ & _ & Hm).
  unfold get_var in Hk1. pose proof (sr_good _ _ _ _ _ H) as Hg.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb2) in Ew. unfold get_var in Ew.
  apply (cc_zero _ _ _ _ _ _ _ (set_var rg (Word (EL (w2n w) (bitmaps s1))) t1));
    [|apply state_rel_set_var; split; [exact H|exact Hb1]].
  cbn [stack_remove.comp list_Seq].
  assert (Hmem : MEM BitmapBase stack_remove.store_list = true) by reflexivity.
  pose proof (mem_load_lemma BitmapBase s1 (Word ww) base t1 (conj Hmem (conj Eww Hm))) as Hld.
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_load rg (k + 1) _ base _ t1 Hk1 Hld))).
  set (X1 := set_var rg (Word ww) t1).
  assert (F1 : FLOOKUP (regs X1) rg = SOME (Word ww)) by apply FLOOKUP_set_var_same.
  assert (F2 : FLOOKUP (regs X1) v = SOME (Word w)) by (subst X1; rewrite FLOOKUP_set_var_other by lia; exact Ew).
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_add_reg rg rg v _ _ X1 F1 F2))).
  rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_shift_imm ast.Lsl rg rg (n2w (word_shift a)) _ _ _
             (FLOOKUP_set_var_same _ _ _) (word_sh_ws ast.Lsl _ Hg ltac:(discriminate) ltac:(discriminate))))).
  cbn beta iota.
  rewrite Eww in Hm. cbn [the_SOME_Word] in Hm. rewrite sr_mem_W1 in Hm.
  assert (Hl : (w2n w < LENGTH (MAP Word (bitmaps s1) ++ MAP Word (wordSem.buffer_buffer (data_buffer s1))))%N)
    by (rewrite LENGTH_app_N, !LENGTH_length, !length_map, <- !LENGTH_length; lia).
  destruct (word_list_read _ _ _ _ _ (w2n w) Hm Hl) as [Er Ed].
  rewrite EL_app_l_N in Er by (rewrite LENGTH_length, length_map, <- LENGTH_length; exact El).
  rewrite EL_map_N in Er by exact El.
  assert (Ea : ((ww + w) << word_shift a)%w = ((ww << word_shift a) + bytes_in_word * n2w (w2n w))%w)
    by (rewrite WORD_ADD_LSL, (lsl_word_shift w Hg), n2w_w2n; wring).
  assert (M4 : mem_load ((ww + w) << word_shift a)%w
                 (set_var rg (Word ((ww + w) << word_shift a)%w) (set_var rg (Word (ww + w)%w) X1)) =
               SOME (Word (EL (w2n w) (bitmaps s1))))
    by (rewrite Ea; apply mem_load_of; assumption).
  rewrite (ev_inst_some _ _ _ (inst_load0 rg rg _ _ _ (FLOOKUP_set_var_same _ _ _) M4)).
  subst X1. rewrite !set_var_twice. reflexivity.
Qed.

End StackCases4.

Section DBW.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma ev_dbw_eq r1 r2 (X : state a c ffi_t) :
  evaluate (DataBufferWrite r1 r2, X) =
  if negb (use_stack X) then (SOME Error, X) else
  match get_var r1 X, get_var r2 X with
  | SOME (Word w1), SOME (Word w2) =>
      match wordSem.buffer_write (data_buffer X) w1 w2 with
      | SOME new_db => (NONE, set_data_buffer new_db X)
      | _ => (SOME Error, X)
      end
  | _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma STAR_emp_r' (p : (word a * word_loc a -> Prop) -> Prop) : STAR p emp = p.
Proof. rewrite STAR_COMM. apply STAR_emp_l. Qed.

Lemma dbw_rearr (M W O E S L : (word a * word_loc a -> Prop) -> Prop) :
  STAR (STAR (STAR (STAR M W) (STAR O E)) S) L = STAR O (STAR M (STAR W (STAR E (STAR S L)))).
Proof. star_ac. Qed.

Lemma dbw_rearr2 (M W O E S L : (word a * word_loc a -> Prop) -> Prop) :
  STAR (STAR (STAR (STAR M (STAR W O)) E) S) L = STAR O (STAR M (STAR W (STAR E (STAR S L)))).
Proof. star_ac. Qed.

Lemma cc_dbw r1 r2 s1 r s2 t1 :
  evaluate (DataBufferWrite r1 r2, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (DataBufferWrite r1 r2 : prog a) k = true -> cc_concl jump off k (DataBufferWrite r1 r2) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
  apply N.ltb_lt in Hb1, Hb2.
  rewrite ev_dbw_eq, (sr_use_stack _ _ _ _ _ H) in He. cbn [negb] in He.
  destruct (get_var r1 s1) as [[w1|]|] eqn:E1; try (injection He as <- <-; congruence).
  destruct (get_var r2 s1) as [[w2|]|] eqn:E2; try (injection He as <- <-; congruence).
  destruct (wordSem.buffer_write (data_buffer s1) w1 w2) as [db|] eqn:Eb; injection He as <- <-; [|congruence].
  unfold wordSem.buffer_write in Eb.
  destruct (bool_decide _) eqn:Ep; [|discriminate Eb]. destruct (0 <? wordSem.space_left (data_buffer s1)) eqn:Esl;
    [|discriminate Eb]. cbn [andb] in Eb. injection Eb as <-.
  apply bool_decide_spec in Ep. apply N.ltb_lt in Esl.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb1) in E1. rewrite <- (sr_get_var _ _ _ _ _ _ H Hb2) in E2.
  unfold get_var in E1, E2.
  (* unpack the state relation *)
  pose proof H as H'. unfold state_rel in H'; cbv zeta in H'; destruct_ands.
  destruct (FLOOKUP (regs t1) (k + 1)) as [[base|]|] eqn:Ebase; try contradiction. destruct_ands.
  set (bp := (the_SOME_Word (FLOOKUP (store s1) BitmapBase) << word_shift a)%w) in *.
  set (all := bitmaps s1 ++ wordSem.buffer_buffer (data_buffer s1)) in *.
  set (sl := wordSem.space_left (data_buffer s1)) in *.
  assert (Ew1 : w1 = (bp + bytes_in_word * n2w (LENGTH all))%w).
  { rewrite <- Ep. fold (bytes_in_word : word a).
    match goal with Hp : wordSem.position (data_buffer s1) = _ |- _ => rewrite Hp end.
    subst all. rewrite LENGTH_app_N, <- word_add_n2w. wring. }
  rewrite Ew1 in E1. clear Ep Ew1.
  set (A := (bp + bytes_in_word * n2w (LENGTH all))%w) in *.
  match goal with Hm : STAR _ (word_list base (stack s1)) (fun2set _) |- _ => rename Hm into Hmem end.
  replace sl with (SUC (sl - 1)) in Hmem by lia.
  rewrite (proj2 (word_list_exists_thm A (sl - 1))) in Hmem.
  rewrite (STAR_COMM (STAR (memory _ _) _) (SEP_EXISTS _)), !STAR_SEP_EXISTS_l in Hmem.
  apply SEP_EXISTS_THM in Hmem as [x Hmem].
  rewrite (STAR_COMM (STAR (one (A, x)) _) _), dbw_rearr in Hmem.
  destruct (sep_read _ _ _ _ _ Hmem) as [_ HA].
  pose proof (sep_write _ _ _ (Word w2) _ _ Hmem) as Hw.
  apply (cc_zero _ _ _ _ _ _ _ (set_memory ((A =+ Word w2) (stackSem.memory t1)) t1)).
  - cbn [stack_remove.comp]. apply ev_inst_some. apply inst_store0; assumption.
  - cbn [cc_post]. unfold state_rel; cbv zeta; stk_fields.
    repeat (split; [assumption|]). rewrite Ebase.
    repeat (split; [assumption|]).
    cbn [wordSem.buffer_buffer wordSem.space_left wordSem.position]. fold bp.
    rewrite !app_assoc. fold all. rewrite map_app, (word_list_APPEND (MAP Word all) (MAP Word [w2]) bp).
    cbn [map word_list]. rewrite STAR_emp_r'. rewrite LENGTH_length, length_map, <- LENGTH_length. fold A.
    replace (bp + bytes_in_word * n2w (LENGTH (all ++ [w2])))%w with (A + bytes_in_word)%w
      by (subst A; rewrite LENGTH_app_N; change (LENGTH [w2]) with 1; rewrite <- word_add_n2w; wring).
    rewrite dbw_rearr2. exact Hw.
Qed.

End DBW.


Section FFICase.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma ev_ffi_eq ffi_index ptr len ptr2 len2 ret (X : state a c ffi_t) :
  evaluate (FFI ffi_index ptr len ptr2 len2 ret, X) =
  match get_var len X, get_var ptr X, get_var len2 X, get_var ptr2 X with
  | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
      match read_bytearray w2 (w2n w) (wordSem.mem_load_byte_aux (stackSem.memory X) (mdomain X) (be X)),
            read_bytearray w4 (w2n w3) (wordSem.mem_load_byte_aux (stackSem.memory X) (mdomain X) (be X)) with
      | SOME bytes, SOME bytes2 =>
          match call_FFI (ffi X) (ExtCall ffi_index) bytes bytes2 with
          | FFI_final outcome => (SOME (FinalFFI outcome), X)
          | FFI_return new_ffi new_bytes =>
              let new_m := wordSem.write_bytearray w4 new_bytes (stackSem.memory X) (mdomain X) (be X) in
              (NONE, set_ffi new_ffi (set_fp_regs FEMPTY
                       (set_regs (DRESTRICT (regs X) (ffi_save_regs X)) (set_memory new_m X))))
          end
      | _, _ => (SOME Error, X)
      end
  | _, _, _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_ffi ffi_index ptr len ptr2 len2 ret s1 r s2 t1 :
  evaluate (FFI ffi_index ptr len ptr2 len2 ret, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (FFI ffi_index ptr len ptr2 len2 ret : prog a) k = true ->
  cc_concl jump off k (FFI ffi_index ptr len ptr2 len2 ret) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb.
  apply andb_true_iff in Hb as [Hb Hret]. apply andb_true_iff in Hb as [Hb Hl2].
  apply andb_true_iff in Hb as [Hb Hp2]. apply andb_true_iff in Hb as [Hp Hl].
  apply N.ltb_lt in Hp, Hl, Hp2, Hl2.
  rewrite ev_ffi_eq in He.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hl), <- (sr_get_var _ _ _ _ _ _ H Hp),
    <- (sr_get_var _ _ _ _ _ _ H Hl2), <- (sr_get_var _ _ _ _ _ _ H Hp2) in He.
  destruct (get_var len t1) as [[w|]|] eqn:E1; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (get_var ptr t1) as [[w2|]|] eqn:E2; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (get_var len2 t1) as [[w3|]|] eqn:E3; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (get_var ptr2 t1) as [[w4|]|] eqn:E4; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (read_bytearray w2 (w2n w) (wordSem.mem_load_byte_aux (stackSem.memory s1) (mdomain s1) (be s1)))
    as [bytes|] eqn:R1; cbv beta iota in He; [|injection He as <- <-; congruence].
  destruct (read_bytearray w4 (w2n w3) (wordSem.mem_load_byte_aux (stackSem.memory s1) (mdomain s1) (be s1)))
    as [bytes2|] eqn:R2; cbv beta iota in He; [|injection He as <- <-; congruence].
  pose proof (read_bytearray_IMP_read_bytearray _ _ _ _ _ _ _ _ (conj H R1)) as R1'.
  pose proof (read_bytearray_IMP_read_bytearray _ _ _ _ _ _ _ _ (conj H R2)) as R2'.
  destruct (call_FFI (ffi s1) (ExtCall ffi_index) bytes bytes2) as [nf nb|outcome] eqn:Ec;
    injection He as <- <-.
  - cbv zeta.
    apply (cc_zero _ _ _ _ _ _ _ (set_ffi nf (set_fp_regs FEMPTY (set_regs (DRESTRICT (regs t1) (ffi_save_regs t1))
             (set_memory (wordSem.write_bytearray w4 nb (stackSem.memory t1) (mdomain t1) (be t1)) t1))))).
    + cbn [stack_remove.comp]. rewrite ev_ffi_eq, E1, E2, E3, E4, R1', R2', (sr_ffi _ _ _ _ _ H), Ec. reflexivity.
    + cbn [cc_post]. pose proof (call_FFI_LENGTH _ _ _ _ _ _ Ec) as Hlen.
      pose proof (read_bytearray_LENGTH _ _ _ _ R2) as Hlen2.
      unfold state_rel in *; cbv zeta in *; stk_fields. destruct_ands.
      rewrite !FLOOKUP_DRESTRICT.
      assert (Hs : forall x, x IN (k INSERT (k + 1 INSERT (k + 2 INSERT {}))) -> x IN ffi_save_regs t1) by assumption.
      destruct (classical_dec (k + 2 IN ffi_save_regs t1)) as [_|Hn]; [|exfalso; apply Hn, Hs; right; right; left; reflexivity].
      destruct (classical_dec (k + 1 IN ffi_save_regs t1)) as [_|Hn]; [|exfalso; apply Hn, Hs; right; left; reflexivity].
      destruct (classical_dec (k IN ffi_save_regs t1)) as [_|Hn]; [|exfalso; apply Hn, Hs; left; reflexivity].
      repeat (split; [first [assumption|reflexivity]|]).
      split; [intros n Hn; rewrite !FLOOKUP_DRESTRICT;
              match goal with Hf : ffi_save_regs t1 = ffi_save_regs s1 |- _ => rewrite Hf end;
              destruct (classical_dec _); [auto|reflexivity]|].
      repeat (split; [first [assumption|reflexivity]|]).
      destruct (FLOOKUP (regs t1) (k + 1)) as [[base|]|]; try contradiction. destruct_ands.
      repeat (split; [first [assumption|reflexivity]|]).
      rewrite sr_mem_assoc in *.
      match goal with Hbe : be t1 = be s1 |- _ => rewrite Hbe end.
      apply (write_bytearray_lemma nb w4 (stackSem.memory s1) (mdomain s1) (be s1) bytes2).
      split; [assumption|]. rewrite Hlen, Hlen2. exact R2.
  - apply (cc_zero _ _ _ _ _ _ _ t1).
    + cbn [stack_remove.comp]. rewrite ev_ffi_eq, E1, E2, E3, E4, R1', R2', (sr_ffi _ _ _ _ _ H), Ec. reflexivity.
    + exact (sr_ffi _ _ _ _ _ H).
Qed.

End FFICase.

Section ShMemCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma sh_mem_op_rel op r (ad : word a) s t res s' :
  state_rel jump off k s t -> r < k -> sh_mem_op op r ad s = (res, s') -> res <> SOME Error ->
  exists t', sh_mem_op op r ad t = (res, t') /\ ffi t' = ffi s' /\ (res = NONE -> state_rel jump off k s' t').
Proof.
  intros H Hr E Hn. pose proof (sr_ffi _ _ _ _ _ H) as Hf. pose proof (sr_sh_mdomain _ _ _ _ _ H) as Hd.
  pose proof (sr_get_var _ _ _ _ _ _ H Hr) as Hg.
  destruct op; cbn [sh_mem_op] in E |- *;
    unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte, sh_mem_load16, sh_mem_store16,
      sh_mem_load32, sh_mem_store32 in E |- *;
    rewrite ?Hg, ?Hd, ?Hf;
    repeat match type of E with
    | context [match ?x with _ => _ end] => let Ex := fresh "Ex" in destruct x eqn:Ex; cbv beta iota in E
    | context [if ?x then _ else _] => let Ex := fresh "Ex" in destruct x eqn:Ex; cbv beta iota in E
    end;
    injection E as <- <-; try congruence;
    eexists; (split; [reflexivity|]); (split; [cbn [ffi set_ffi set_regs]; first [reflexivity|exact Hf]|]);
    intros Hres;
    first [ discriminate Hres
          | apply state_rel_set_ffi, H
          | apply state_rel_set_ffi; change (set_regs (regs s |+ (r, ?v)) s) with (set_var r v s);
            change (set_regs (regs t |+ (r, ?v)) t) with (set_var r v t);
            apply state_rel_set_var; split; [exact H|exact Hr] ].
Qed.

Lemma ev_shmemop_eq op r ad w (X : state a c ffi_t) :
  evaluate (ShMemOp op r (Addr ad w), X) =
  match word_exp X (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]) with
  | SOME ad' => if (clock X =? 0) then (SOME TimeOut, empty_env X) else sh_mem_op op r ad' (dec_clock X)
  | _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_shmemop op rg ad w s1 r s2 t1 :
  evaluate (ShMemOp op rg (Addr ad w), s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (ShMemOp op rg (Addr ad w) : prog a) k = true -> cc_concl jump off k (ShMemOp op rg (Addr ad w)) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply N.ltb_lt in Hb1, Hb2.
  rewrite ev_shmemop_eq in He. rewrite <- (sr_exp_addr _ _ _ _ _ _ _ H Hb2) in He.
  destruct (word_exp t1 (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w])) as [ad'|] eqn:Ea;
    [|injection He as <- <-; congruence].
  rewrite <- (sr_clock _ _ _ _ _ H) in He.
  destruct (clock t1 =? 0) eqn:Ec.
  - injection He as <- <-. apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)).
    + cbn [stack_remove.comp]. rewrite ev_shmemop_eq, Ea, Ec. reflexivity.
    + exact (sr_ffi _ _ _ _ _ H).
  - destruct (sh_mem_op_rel op rg ad' _ _ r s2 (state_rel_dec_clock _ _ _ _ _ H) Hb1 He Hr) as (t' & Et & Hf & Hs).
    apply (cc_zero _ _ _ _ _ _ _ t').
    + cbn [stack_remove.comp]. rewrite ev_shmemop_eq, Ea, Ec. exact Et.
    + destruct r as [[]|]; cbn [cc_post]; try exact Hf; try (exfalso; apply Hr; reflexivity); try (apply Hs; reflexivity).
      all: exfalso; revert He; unfold sh_mem_op, sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
             sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32; destruct op;
           repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; cbv beta iota;
           intros E; injection E; intros; discriminate.
Qed.

End ShMemCase.

Section StoreConstsCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma state_rel_regmem s t (Rs Rt : fmap N (word_loc a)) ms mt :
  state_rel jump off k s t ->
  (forall n, n < k -> FLOOKUP Rt n = FLOOKUP Rs n) ->
  FLOOKUP Rt k = FLOOKUP (regs t) k -> FLOOKUP Rt (k + 1) = FLOOKUP (regs t) (k + 1) ->
  FLOOKUP Rt (k + 2) = FLOOKUP (regs t) (k + 2) ->
  (forall base, FLOOKUP (regs t) (k + 1) = SOME (Word base) ->
     STAR (STAR (STAR (STAR (memory ms (mdomain s))
        (word_list (the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a)%w
           (MAP Word (bitmaps s ++ wordSem.buffer_buffer (data_buffer s)))))
        (word_list_exists ((the_SOME_Word (FLOOKUP (store s) BitmapBase) << word_shift a) +
             bytes_in_word * n2w (LENGTH (bitmaps s ++ wordSem.buffer_buffer (data_buffer s))))%w
           (wordSem.space_left (data_buffer s))))
        (word_store base (store s)))
      (word_list base (stack s))
      (fun2set (mt, mdomain t))) ->
  state_rel jump off k (set_regs Rs (set_memory ms s)) (set_regs Rt (set_memory mt t)).
Proof.
  intros H Hn Hk Hk1 Hk2 Hm. pose proof (Hm) as Hm'.
  unfold state_rel in *; cbv zeta in *; stk_fields. rewrite Hk, Hk1, Hk2.
  destruct_ands. repeat (split; [assumption|]).
  destruct (FLOOKUP (regs t) (k + 1)) as [[base|]|]; try contradiction. destruct_ands.
  repeat (split; [assumption|]). apply Hm'. reflexivity.
Qed.

Lemma ev_storeconsts_eq r1 r2 stub (X : state a c ffi_t) :
  evaluate (StoreConsts r1 r2 stub, X) =
  if negb (use_store X) then (SOME Error, X) else
  if andb (negb (use_alloc X)) (IS_SOME stub) then (SOME Error, X) else
  if negb (check_store_consts_opt r1 r2 stub (code X)) then (SOME Error, X) else
    store_const_sem r1 r2 X.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma distinct6 (r1 r2 : N) : ALL_DISTINCT [0; 1; 2; 3; r1; r2] = true ->
  ALL_DISTINCT [1; 2; 3; r1; r2] = true /\ r1 <> 0 /\ r2 <> 0.
Proof.
  intros H. cbn [ALL_DISTINCT] in H. apply andb_true_iff in H as [H0 H].
  split; [exact H|]. cbn [MEM] in H0. apply negb_true_iff in H0.
  repeat (apply orb_false_iff in H0 as [? H0]). sr_bool. split; congruence.
Qed.

Lemma sc_rearr (M Wb Wbuf E S L : (word a * word_loc a -> Prop) -> Prop) :
  STAR (STAR (STAR (STAR M (STAR Wb Wbuf)) E) S) L = STAR (STAR Wb (STAR Wbuf (STAR E (STAR S L)))) M.
Proof. star_ac. Qed.

Lemma cc_storeconsts r1 r2 stub s1 r s2 t1 :
  evaluate (StoreConsts r1 r2 stub, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (StoreConsts r1 r2 stub : prog a) k = true -> cc_concl jump off k (StoreConsts r1 r2 stub) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb Hb2].
  apply andb_true_iff in Hb as [Hb3 Hb1]. apply N.ltb_lt in Hb3, Hb1, Hb2.
  rewrite ev_storeconsts_eq, (sr_use_store _ _ _ _ _ H), (sr_use_alloc_s _ _ _ _ _ H) in He. cbn [negb andb] in He.
  destruct stub as [st|]; cbn [IS_SOME check_store_consts_opt negb] in He; [injection He as <- <-; congruence|].
  unfold store_const_sem in He. rewrite (sr_use_alloc_s _ _ _ _ _ H) in He.
  destruct (ALL_DISTINCT [0; 1; 2; 3; r1; r2]) eqn:Ed; cbn [negb] in He; [|injection He as <- <-; congruence].
  destruct (distinct6 r1 r2 Ed) as (Hd5 & Hr10 & Hr20).
  destruct (distinct5 r1 r2 Hd5) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  destruct (get_var 1 s1) as [[i|]|] eqn:E1; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (get_var 2 s1) as [[ad|]|] eqn:E2; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (get_var 3 s1) as [[off0|]|] eqn:E3; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (copy_words (w2n i) ad off0 (bitmaps s1) (mdomain s1) (stackSem.memory s1)) as [[ad' m]|] eqn:Ecw;
    cbv beta iota in He; [|injection He as <- <-; congruence].
  injection He as <- <-. cbn [I].
  assert (H1k : 1 < k) by lia. assert (H2k : 2 < k) by lia.
  rewrite <- (sr_get_var _ _ _ _ _ _ H H1k) in E1. rewrite <- (sr_get_var _ _ _ _ _ _ H H2k) in E2.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb3) in E3. unfold get_var in E1, E2, E3.
  destruct (sr_bitmapbase jump off k _ _ H) as (ww & Eww).
  pose proof H as H'. unfold state_rel in H'; cbv zeta in H'; destruct_ands.
  destruct (FLOOKUP (regs t1) (k + 1)) as [[base|]|] eqn:Ebase; try contradiction. destruct_ands.
  match goal with Hm : STAR _ (word_list base (stack s1)) (fun2set _) |- _ => rename Hm into Hmem end.
  pose proof (sr_good _ _ _ _ _ H) as Hg.
  set (bp := (ww << word_shift a)%w).
  assert (Ebp : the_SOME_Word (FLOOKUP (store s1) BitmapBase) = ww) by (rewrite Eww; reflexivity).
  (* the prefix *)
  set (X := set_var r2 (Word ((ww + i) << word_shift a)%w) (set_var r2 (Word (ww + i)%w) (set_var r2 (Word ww) t1))).
  assert (Hpre : forall C, evaluate (stack_remove.comp jump off k (StoreConsts r1 r2 NONE), set_clock C t1) =
                 evaluate (Seq (stack_remove.copy_loop r1 r2) (Seq (stackLang.move r1 1) (stackLang.move r2 1)),
                           set_clock C X)).
  { intros C. cbn [stack_remove.comp list_Seq].
    assert (Hmem' : MEM BitmapBase stack_remove.store_list = true) by reflexivity.
    pose proof (state_rel_get_var_k _ _ _ _ _ H) as (c0 & Hk1 & _ & _ & _ & Hm).
    unfold get_var in Hk1. rewrite Ebase in Hk1. injection Hk1 as <-.
    pose proof (mem_load_lemma BitmapBase s1 (Word ww) base (set_clock C t1) (conj Hmem' (conj Eww Hm))) as Hld.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_load r2 (k + 1) _ base _ (set_clock C t1) Ebase Hld))).
    assert (F1 : FLOOKUP (regs (set_var r2 (Word ww) (set_clock C t1))) r2 = SOME (Word ww)) by apply FLOOKUP_set_var_same.
    assert (F2 : FLOOKUP (regs (set_var r2 (Word ww) (set_clock C t1))) 1 = SOME (Word i))
      by (rewrite FLOOKUP_set_var_other by congruence; exact E1).
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_add_reg r2 r2 1 _ _ _ F1 F2))).
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_shift_imm ast.Lsl r2 r2 (n2w (word_shift a)) _ _ _
               (FLOOKUP_set_var_same _ _ _) (word_sh_ws ast.Lsl _ Hg ltac:(discriminate) ltac:(discriminate))))).
    cbn beta iota. f_equal. all: (f_equal; subst X; apply state_ext_fw; stk_fields; reflexivity). }
  (* the copy loop *)
  assert (Ea : ((ww + i) << word_shift a)%w = (bp + bytes_in_word * n2w (w2n i))%w)
    by (subst bp; rewrite WORD_ADD_LSL, (lsl_word_shift i Hg), n2w_w2n; wring).
  assert (G2 : get_var 2 X = SOME (Word ad)) by (subst X; unfold get_var; rewrite !FLOOKUP_set_var_other by congruence; exact E2).
  assert (G3 : get_var 3 X = SOME (Word off0)) by (subst X; unfold get_var; rewrite !FLOOKUP_set_var_other by congruence; exact E3).
  assert (Gr2 : get_var r2 X = SOME (Word (bp + bytes_in_word * n2w (w2n i))%w))
    by (subst X; unfold get_var; rewrite FLOOKUP_set_var_same, Ea; reflexivity).
  rewrite Ebp in Hmem. fold bp in Hmem.
  rewrite map_app, (word_list_APPEND (MAP Word (bitmaps s1)) (MAP Word (wordSem.buffer_buffer (data_buffer s1))) bp),
    sc_rearr in Hmem.
  assert (Hsub : mdomain s1 SUBSET mdomain X).
  { eapply (memory_fun2set_SUBSET (stackSem.memory s1) _ _ (stackSem.memory t1)). rewrite STAR_COMM. exact Hmem. }
  destruct (copy_loop_thm r1 r2 _ (w2n i) ad off0 (bitmaps s1) (mdomain s1) (stackSem.memory s1) (mdomain X) 0 ad' m bp X
              (conj Ecw (conj Hd5 (conj eq_refl (conj Hg (conj Hsub (conj G2 (conj G3 (conj Gr2 Hmem)))))))))
    as (ck & b & y & y2 & m2 & Ecl & Scl).
  set (R := (((if b then regs X else regs X |+ (r1, Word y)) |+ (2, Word ad')) |+ (1, Word (n2w 1))) |+ (r2, Word y2)).
  set (Y := set_regs R (set_memory m2 X)).
  assert (FY1 : FLOOKUP (regs Y) 1 = SOME (Word (n2w 1)))
    by (subst Y R; cbn [regs set_regs]; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence).
  assert (FY1' : FLOOKUP (regs (set_var r1 (Word (n2w 1)) Y)) 1 = SOME (Word (n2w 1)))
    by (rewrite FLOOKUP_set_var_other by congruence; exact FY1).
  exists ck, (set_var r2 (Word (n2w 1)) (set_var r1 (Word (n2w 1)) Y)). split.
  - rewrite Hpre. replace (ck + clock t1) with (clock X + ck) by (subst X; stk_fields; lia).
    rewrite (ev_seq_none _ _ _ _ Ecl). fold R Y.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_move r1 1 _ Y FY1))).
    exact (ev_inst_some _ _ _ (inst_move r2 1 _ _ FY1')).
  - cbn [cc_post].
    set (Rs := ((((regs s1 |+ (2, Word ad')) |+ (1, Word (n2w 1))) |+ (r2, Word (n2w 1))) |+ (r1, Word (n2w 1)))).
    set (Rt := (R |+ (r1, Word (n2w 1))) |+ (r2, Word (n2w 1))).
    replace (set_var r1 (Word (n2w 1)) (set_var r2 (Word (n2w 1)) (set_var 1 (Word (n2w 1))
               (set_var 2 (Word ad') (set_memory m s1))))) with (set_regs Rs (set_memory m s1))
      by (subst Rs; apply state_ext_fw; stk_fields; reflexivity).
    replace (set_var r2 (Word (n2w 1)) (set_var r1 (Word (n2w 1)) Y)) with (set_regs Rt (set_memory m2 t1))
      by (subst Rt Y R X; apply state_ext_fw; stk_fields; reflexivity).
    apply state_rel_regmem; [exact H| | | | |].
    + intros n Hn. subst Rt Rs R X. cbn [regs set_var set_regs].
      destruct b; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end;
        try congruence; try lia; exact (state_rel_regs _ _ _ _ _ _ H Hn).
    + subst Rt R X. cbn [regs set_var set_regs]. destruct b; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end;
        try congruence; try lia.
    + subst Rt R X. cbn [regs set_var set_regs]. destruct b; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end;
        try congruence; try lia.
    + subst Rt R X. cbn [regs set_var set_regs]. destruct b; rewrite !FLOOKUP_UPDATE;
        repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end;
        try congruence; try lia.
    + intros base' Eb'. rewrite Ebase in Eb'. injection Eb' as <-.
      rewrite Ebp. fold bp. rewrite map_app,
        (word_list_APPEND (MAP Word (bitmaps s1)) (MAP Word (wordSem.buffer_buffer (data_buffer s1))) bp), sc_rearr.
      exact Scl.
Qed.

End StoreConstsCase.

Section InstallCase.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma ALOOKUP_prog_comp (l : list (N * prog a)) n :
  ALOOKUP (MAP (stack_remove.prog_comp jump off k) l) n = option_map (stack_remove.comp jump off k) (ALOOKUP l n).
Proof.
  induction l as [|[x p] l IH]; [reflexivity|]. cbn [map stack_remove.prog_comp ALOOKUP].
  destruct (decide (x = n)); [reflexivity|exact IH].
Qed.

Lemma MAP_FST_prog_comp (l : list (N * prog a)) :
  MAP fst (MAP (stack_remove.prog_comp jump off k) l) = MAP fst l.
Proof. induction l as [|[x p] l IH]; [reflexivity|]. cbn [map stack_remove.prog_comp fst]. f_equal; exact IH. Qed.

Lemma code_rel_union (c1 c2 : spt (prog a)) (progs : list (N * prog a)) :
  code_rel jump off k c1 c2 ->
  (forall i p, MEM (i, p) progs -> reg_bound p k /\ stack_num_stubs <= i + 1) ->
  code_rel jump off k (sptree.union c1 (sptree.fromAList progs))
    (sptree.union c2 (sptree.fromAList (MAP (stack_remove.prog_comp jump off k) progs))).
Proof.
  intros [Hc Hd] Hm. split.
  - intros n p Hl. rewrite sptree.lookup_union in Hl |- *. destruct (lookup n c1) as [p1|] eqn:E1.
    + injection Hl as <-. destruct (Hc _ _ E1) as [Hb Hl2]. rewrite Hl2. auto.
    + rewrite sptree.lookup_fromAList in Hl. pose proof (ALOOKUP_In _ _ _ Hl) as Hin.
      destruct (Hm n p (proj2 (MEM_In _ _) Hin)) as [Hb Hs]. split; [exact Hb|].
      assert (E2 : lookup n c2 = NONE).
      { apply sptree.lookup_NONE_domain. rewrite Hd. intros [Hx|Hx].
        - apply sptree.lookup_NONE_domain in E1. exact (E1 Hx).
        - unfold stack_num_stubs in Hs. unfold pred_set.INSERT, pred_set.IN, pred_set.EMPTY in Hx. lia. }
      rewrite E2, sptree.lookup_fromAList, ALOOKUP_prog_comp, Hl. reflexivity.
  - rewrite !sptree.domain_union, !sptree.domain_fromAList, Hd, MAP_FST_prog_comp.
    apply set_ext; intros x; unfold pred_set.UNION, pred_set.INSERT, pred_set.IN; tauto.
Qed.

Lemma ev_install_eq ptr len dptr dlen ret (X : state a c ffi_t) :
  evaluate (Install ptr len dptr dlen ret, X) =
  match get_var ptr X, get_var len X, get_var dptr X, get_var dlen X with
  | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
      let '(cfg, (progs, bm)) := compile_oracle X 0 in
      match wordSem.buffer_flush (code_buffer X) w1 w2,
            (if use_stack X then wordSem.buffer_flush (data_buffer X) w3 w4 else SOME (bm, data_buffer X)) with
      | SOME (bytes, cb), SOME (data, db) =>
          let new_oracle := shift_seq 1 (compile_oracle X) in
          match stackSem.compile X cfg progs, progs with
          | SOME (bytes', cfg'), (k0, prog0) :: _ =>
              if andb (andb (bool_decide (bytes = bytes')) (bool_decide (data = bm)))
                      ⌜FST (new_oracle 0) = cfg'⌝ then
                (NONE, set_compile_oracle new_oracle
                  (set_fp_regs FEMPTY
                    (set_regs (DRESTRICT (regs X) (ffi_save_regs X) |+ (ptr, Loc k0 0))
                      (set_code (sptree.union (code X) (sptree.fromAList progs))
                        (set_data_buffer db
                          (set_code_buffer cb
                            (set_bitmaps (bitmaps X ++ bm) X)))))))
              else (SOME Error, X)
          | _, _ => (SOME Error, X)
          end
      | _, _ => (SOME Error, X)
      end
  | _, _, _, _ => (SOME Error, X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_install ptr len dptr dlen ret s1 r s2 t1 :
  evaluate (Install ptr len dptr dlen ret, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Install ptr len dptr dlen ret : prog a) k = true ->
  cc_concl jump off k (Install ptr len dptr dlen ret) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb.
  apply andb_true_iff in Hb as [Hb Hret]. apply andb_true_iff in Hb as [Hb Hdl].
  apply andb_true_iff in Hb as [Hb Hdp]. apply andb_true_iff in Hb as [Hp Hl].
  apply N.ltb_lt in Hp, Hl, Hdp, Hdl.
  rewrite ev_install_eq in He.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hp), <- (sr_get_var _ _ _ _ _ _ H Hl),
    <- (sr_get_var _ _ _ _ _ _ H Hdp), <- (sr_get_var _ _ _ _ _ _ H Hdl) in He.
  destruct (get_var ptr t1) as [[w1|]|] eqn:E1; cbv beta iota zeta in He; try (injection He as <- <-; congruence).
  destruct (get_var len t1) as [[w2|]|] eqn:E2; cbv beta iota zeta in He; try (injection He as <- <-; congruence).
  destruct (get_var dptr t1) as [[w3|]|] eqn:E3; cbv beta iota zeta in He; try (injection He as <- <-; congruence).
  destruct (get_var dlen t1) as [[w4|]|] eqn:E4; cbv beta iota zeta in He; try (injection He as <- <-; congruence).
  pose proof H as H'. unfold state_rel in H'; cbv zeta in H'; destruct_ands.
  rename H15 into Horacle_t, H16 into Hmemo, H14 into Hcomp.
  destruct (compile_oracle s1 0) as [cfg [progs bm]] eqn:Eo.
  rewrite (sr_use_stack _ _ _ _ _ H) in He.
  rewrite <- (sr_code_buffer _ _ _ _ _ H) in He.
  destruct (wordSem.buffer_flush (code_buffer t1) w1 w2) as [[bytes cb]|] eqn:Ecb; cbv beta iota zeta in He;
    [|injection He as <- <-; congruence].
  destruct (wordSem.buffer_flush (data_buffer s1) w3 w4) as [[data db]|] eqn:Edb; cbv beta iota zeta in He;
    [|injection He as <- <-; congruence].
  rewrite Hcomp in He. cbv beta in He.
  destruct (stackSem.compile t1 cfg (MAP (stack_remove.prog_comp jump off k) progs)) as [[bytes' cfg']|] eqn:Ec;
    cbv beta iota zeta in He; [|injection He as <- <-; congruence].
  destruct progs as [|[k0 prog0] rest]; cbv beta iota zeta in He; [injection He as <- <-; congruence|].
  destruct (bool_decide (bytes = bytes')) eqn:Eb1; cbn [andb] in He; [|injection He as <- <-; congruence].
  destruct (bool_decide (data = bm)) eqn:Eb2; cbn [andb] in He; [|injection He as <- <-; congruence].
  destruct (⌜FST (shift_seq 1 (compile_oracle s1) 0) = cfg'⌝) eqn:Eb3; cbn [andb] in He;
    [|injection He as <- <-; congruence].
  injection He as <- <-. apply bool_decide_spec in Eb2. subst data.
  set (progs' := MAP (stack_remove.prog_comp jump off k) ((k0, prog0) :: rest)).
  set (t' := set_compile_oracle (shift_seq 1 (compile_oracle t1))
               (set_fp_regs FEMPTY (set_regs (DRESTRICT (regs t1) (ffi_save_regs t1) |+ (ptr, Loc k0 0))
                 (set_code (sptree.union (code t1) (sptree.fromAList progs'))
                   (set_data_buffer (data_buffer t1) (set_code_buffer cb
                     (set_bitmaps (bitmaps t1 ++ bm) t1))))))).
  apply (cc_zero _ _ _ _ _ _ _ t').
  - cbn [stack_remove.comp]. rewrite ev_install_eq, E1, E2, E3, E4. cbv beta iota.
    rewrite Horacle_t, Eo. cbn [PAIR_MAP I fst snd]. rewrite Ecb, (sr_use_stack_t _ _ _ _ _ H).
    cbv beta iota zeta. rewrite Ec. cbn [map stack_remove.prog_comp].
    rewrite Eb1, (proj2 (bool_decide_spec (bm = bm)) eq_refl). cbn [andb].
    match goal with |- context [⌜FST (shift_seq 1 ?o 0) = cfg'⌝] =>
      replace (⌜FST (shift_seq 1 o 0) = cfg'⌝) with true end.
    all: try (rewrite <- Horacle_t; reflexivity).
    all: symmetry; apply bool_decide_spec; apply bool_decide_spec in Eb3; unfold shift_seq in *;
      unfold compose; destruct (compile_oracle s1 (0 + 1)) as [x [y z]]; exact Eb3.
  - cbn [cc_post]. subst t' progs'.
    unfold wordSem.buffer_flush in Edb.
    destruct (bool_decide (wordSem.position (data_buffer s1) = w3)) eqn:Ed1; cbn [andb] in Edb; cbv beta iota in Edb; [|discriminate Edb].
    destruct (bool_decide ((wordSem.position (data_buffer s1) + n2w (dimindex a DIV 8) *
                 n2w (LENGTH (wordSem.buffer_buffer (data_buffer s1))))%w = w4)) eqn:Ed2;
      cbv beta iota in Edb; [|discriminate Edb].
    injection Edb as <- <-. apply bool_decide_spec in Ed2.
    assert (CR : code_rel jump off k (sptree.union (code s1) (sptree.fromAList ((k0, prog0) :: rest)))
                   (sptree.union (code t1) (sptree.fromAList (MAP (stack_remove.prog_comp jump off k) ((k0, prog0) :: rest))))).
    { apply code_rel_union; [exact (sr_code_rel _ _ _ _ _ H)|]. intros i p Hm. apply (Hmemo 0). rewrite Eo. exact Hm. }
    unfold state_rel in *; cbv zeta in *; stk_fields.
    rewrite !FLOOKUP_UPDATE, !FLOOKUP_DRESTRICT.
    destruct (decide (ptr = k + 2)) as [|_]; [lia|]. destruct (decide (ptr = k + 1)) as [|_]; [lia|].
    destruct (decide (ptr = k)) as [|_]; [lia|].
    assert (Hs : forall x, x IN (k INSERT (k + 1 INSERT (k + 2 INSERT {}))) -> x IN ffi_save_regs t1) by assumption.
    destruct (classical_dec (k + 2 IN ffi_save_regs t1)) as [_|Hn]; [|exfalso; apply Hn, Hs; right; right; left; reflexivity].
    destruct (classical_dec (k + 1 IN ffi_save_regs t1)) as [_|Hn]; [|exfalso; apply Hn, Hs; right; left; reflexivity].
    destruct (classical_dec (k IN ffi_save_regs t1)) as [_|Hn]; [|exfalso; apply Hn, Hs; left; reflexivity].
    repeat (split; [first [assumption|reflexivity]|]).
    split; [rewrite Horacle_t; reflexivity|].
    split; [intros n i p Hm; apply (Hmemo (n + 1)); unfold shift_seq in Hm; exact Hm|].
    split; [assumption|].
    split.
    { intros n Hn. rewrite !FLOOKUP_UPDATE, !FLOOKUP_DRESTRICT. destruct (decide (ptr = n)); [reflexivity|].
      rewrite H10. destruct (classical_dec _); [auto|reflexivity]. }
    split.
    { exact CR. }
    split; [rewrite sptree.lookup_union; match goal with Hl : lookup stack_remove.stack_err_lab (code t1) = _ |- _ =>
              rewrite Hl end; reflexivity|].
    repeat (split; [assumption|]).
    split.
    { rewrite <- Ed2. match goal with Hp : wordSem.position (data_buffer s1) = _ |- _ => rewrite Hp end.
      fold (bytes_in_word : word a). rewrite LENGTH_app_N, <- word_add_n2w. cbn [wordSem.position]. wring. }
    destruct (FLOOKUP (regs t1) (k + 1)) as [[base|]|]; try contradiction. destruct_ands.
    repeat (split; [assumption|]).
    rewrite app_nil_r. assumption.
Qed.

End InstallCase.


Section RecCases.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Definition IHT (x : prog a * state a c ffi_t) : Prop :=
  forall y, eval_lt y x -> forall r s2 t1, evaluate y = (r, s2) -> r <> SOME Error ->
    state_rel jump off k (snd y) t1 -> reg_bound (fst y) k = true -> cc_concl jump off k (fst y) r s2 t1.

Lemma add_clock_none (p : prog a) (X Y : state a c ffi_t) ck ck' :
  evaluate (p, set_clock (ck + clock X) X) = (NONE, Y) ->
  evaluate (p, set_clock (ck + ck' + clock X) X) = (NONE, set_clock (clock Y + ck') Y).
Proof.
  intros E. assert (Hn : (@NONE (result a)) <> SOME TimeOut) by discriminate.
  pose proof (evaluate_add_clock ck' _ _ _ _ (conj E Hn)) as E'.
  rewrite clock_set_clock, set_clock_set_clock in E'. rewrite <- E'. f_equal. f_equal. f_equal. lia.
Qed.

Lemma add_clock_some (p : prog a) (X Y : state a c ffi_t) ck ck' res :
  evaluate (p, set_clock (ck + clock X) X) = (res, Y) -> res <> SOME TimeOut ->
  evaluate (p, set_clock (ck + ck' + clock X) X) = (res, set_clock (clock Y + ck') Y).
Proof.
  intros E Hn.
  pose proof (evaluate_add_clock ck' _ _ _ _ (conj E Hn)) as E'.
  rewrite clock_set_clock, set_clock_set_clock in E'. rewrite <- E'. f_equal. f_equal. f_equal. lia.
Qed.

Lemma cc_seq p1 p2 s1 r s2 t1 (IH : IHT (Seq p1 p2, s1)) :
  evaluate (Seq p1 p2, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Seq p1 p2) k = true -> cc_concl jump off k (Seq p1 p2) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
  rewrite ev_seq in He. destruct (evaluate (p1, s1)) as [res s'] eqn:E1.
  assert (Hres : res <> SOME Error) by (destruct res; [injection He as -> _; exact Hr|discriminate]).
  assert (Hlt1 : eval_lt (p1, s1) (Seq p1 p2, s1)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
  destruct (IH (p1, s1) Hlt1 res s' t1 E1 Hres H Hb1) as (ck & t2 & E2 & P2). cbn [fst] in E2.
  destruct res as [x|].
  - injection He as <- <-. exists ck, t2. split; [cbn [stack_remove.comp]; apply ev_seq_some; exact E2|exact P2].
  - cbn [cc_post] in P2. pose proof (evaluate_clock _ _ _ _ E1) as Hc.
    assert (Hlt2 : eval_lt (p2, s') (Seq p1 p2, s1)).
    { destruct (N.eq_dec (clock s') (clock s1)) as [Ec|Ec]; [right; cbn [fst snd psize]; split; [exact Ec|lia]|left; cbn [snd]; lia]. }
    destruct (IH (p2, s') Hlt2 r s2 t2 He Hr P2 Hb2) as (ck' & t3 & E3 & P3).
    exists (ck + ck'), t3. split; [|exact P3]. cbn [stack_remove.comp].
    rewrite (ev_seq_none _ _ _ _ (add_clock_none _ _ _ ck ck' E2)). rewrite N.add_comm. exact E3.
Qed.

Lemma cc_if cmp0 rg ri p1 p2 s1 r s2 t1 (IH : IHT (If cmp0 rg ri p1 p2, s1)) :
  evaluate (If cmp0 rg ri p1 p2, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (If cmp0 rg ri p1 p2) k = true -> cc_concl jump off k (If cmp0 rg ri p1 p2) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb.
  apply andb_true_iff in Hb as [Hb Hb2]. apply andb_true_iff in Hb as [Hb Hb1].
  apply andb_true_iff in Hb as [Hrg Hri]. apply N.ltb_lt in Hrg.
  assert (Gi : forall C, get_var_imm ri (set_clock C t1) = get_var_imm ri s1).
  { intros C. destruct ri as [n|w]; cbn [get_var_imm]; [|reflexivity].
    rewrite get_var_set_clock. apply N.ltb_lt in Hri. exact (sr_get_var _ _ _ _ _ _ H Hri). }
  assert (Gr : forall C, get_var rg (set_clock C t1) = get_var rg s1)
    by (intros C; rewrite get_var_set_clock; exact (sr_get_var _ _ _ _ _ _ H Hrg)).
  rewrite ev_if in He.
  destruct (get_var rg s1) as [x|] eqn:Ex; [|injection He as <- <-; congruence].
  destruct (get_var_imm ri s1) as [y|] eqn:Ey; [|injection He as <- <-; congruence].
  destruct (wordSem.word_cmp cmp0 x y) as [[|]|] eqn:Ec; [| |injection He as <- <-; congruence].
  - assert (Hlt : eval_lt (p1, s1) (If cmp0 rg ri p1 p2, s1)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
    destruct (IH (p1, s1) Hlt r s2 t1 He Hr H Hb1) as (ck & t2 & E2 & P2). exists ck, t2. split; [|exact P2].
    cbn [stack_remove.comp]. rewrite ev_if, Gr, Gi, Ec. exact E2.
  - assert (Hlt : eval_lt (p2, s1) (If cmp0 rg ri p1 p2, s1)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
    destruct (IH (p2, s1) Hlt r s2 t1 He Hr H Hb2) as (ck & t2 & E2 & P2). exists ck, t2. split; [|exact P2].
    cbn [stack_remove.comp]. rewrite ev_if, Gr, Gi, Ec. exact E2.
Qed.

Lemma cc_post_exit_loop res s' t2 :
  cont_loop res = false -> res <> SOME Error -> cc_post jump off k res s' t2 -> cc_post jump off k (exit_loop res) s' t2.
Proof.
  intros Hc Hn P. destruct res as [[x|x|n|n|w| |f|]|]; cbn [exit_loop cont_loop cc_post] in *; try exact P;
    try discriminate Hc; destruct (n =? 0); exact P.
Qed.

Lemma dec_clock_add (X : state a c ffi_t) ck : clock X <> 0 ->
  dec_clock (set_clock (ck + clock X) X) = set_clock (ck + clock (dec_clock X)) (dec_clock X).
Proof. intros H. unfold dec_clock. rewrite !clock_set_clock, !set_clock_set_clock. f_equal. lia. Qed.

Lemma dec_clock_add2 (X : state a c ffi_t) ck : clock X <> 0 ->
  dec_clock (set_clock (clock X + ck) X) = set_clock (ck + clock (dec_clock X)) (dec_clock X).
Proof. intros H. unfold dec_clock. rewrite !clock_set_clock, !set_clock_set_clock. f_equal. lia. Qed.

Lemma cc_loop p1 s1 r s2 t1 (IH : IHT (Loop p1, s1)) :
  evaluate (Loop p1, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Loop p1) k = true -> cc_concl jump off k (Loop p1) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb.
  rewrite ev_loop in He. destruct (evaluate (p1, s1)) as [res s'] eqn:E1.
  assert (Hres : res <> SOME Error)
    by (intros ->; cbn [cont_loop exit_loop] in He; injection He as <- _; congruence).
  assert (Hlt1 : eval_lt (p1, s1) (Loop p1, s1)) by (right; cbn [fst snd psize]; split; [reflexivity|lia]).
  destruct (IH (p1, s1) Hlt1 res s' t1 E1 Hres H Hb) as (ck & t2 & E2 & P2). cbn [fst] in E2.
  destruct (cont_loop res) eqn:Ecl.
  - assert (Rel : state_rel jump off k s' t2)
      by (destruct res as [[]|]; cbn [cont_loop] in Ecl; try discriminate Ecl; exact P2).
    pose proof (sr_clock _ _ _ _ _ Rel) as Hct.
    assert (Hnt : res <> SOME TimeOut) by (intros ->; discriminate Ecl).
    destruct (clock s' =? 0) eqn:Ez.
    + injection He as <- <-. exists ck, (empty_env t2). split.
      * cbn [stack_remove.comp]. rewrite ev_loop, E2, Ecl, Hct, Ez. reflexivity.
      * exact (sr_ffi _ _ _ _ _ Rel).
    + apply N.eqb_neq in Ez. unfold STOP in He. pose proof (evaluate_clock _ _ _ _ E1) as Hc.
      assert (Hlt2 : eval_lt (Loop p1, dec_clock s') (Loop p1, s1))
        by (left; cbn [snd]; unfold dec_clock; rewrite clock_set_clock; lia).
      destruct (IH (Loop p1, dec_clock s') Hlt2 r s2 (dec_clock t2) He Hr (state_rel_dec_clock _ _ _ _ _ Rel) Hb)
        as (ck' & t3 & E3 & P3).
      exists (ck + ck'), t3. split; [|exact P3]. cbn [stack_remove.comp] in E3 |- *.
      rewrite ev_loop, (add_clock_some _ _ _ ck ck' _ E2 Hnt), Ecl, clock_set_clock.
      replace (clock t2 + ck' =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      unfold STOP. rewrite dec_clock_add2 by lia. exact E3.
  - injection He as <- <-. exists ck, t2. split.
    + cbn [stack_remove.comp]. rewrite ev_loop, E2, Ecl. reflexivity.
    + apply cc_post_exit_loop; assumption.
Qed.

Lemma cc_post_bad_fun res s' t2 :
  bad_fun_return res = false -> cc_post jump off k res s' t2 -> cc_post jump off k res s' t2.
Proof. intros _ P; exact P. Qed.

Lemma cc_jumplower r1 r2 dest s1 r s2 t1 (IH : IHT (JumpLower r1 r2 dest, s1)) :
  evaluate (JumpLower r1 r2 dest, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (JumpLower r1 r2 dest : prog a) k = true -> cc_concl jump off k (JumpLower r1 r2 dest) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply N.ltb_lt in Hb1, Hb2.
  rewrite ev_jumplower in He.
  rewrite <- (sr_get_var _ _ _ _ _ _ H Hb1), <- (sr_get_var _ _ _ _ _ _ H Hb2) in He.
  destruct (get_var r1 t1) as [[x|]|] eqn:E1; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (get_var r2 t1) as [[y|]|] eqn:E2; cbv beta iota in He; try (injection He as <- <-; congruence).
  destruct (word_cmp Lower x y) eqn:Ecmp.
  - destruct (find_code (inl dest) (regs s1) (code s1)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
    destruct (find_code_lemma jump off k s1 t1 (inl dest) prog0 (conj H (conj Logic.I Ef)))
      as [Ef' Hbp].
    pose proof (sr_clock _ _ _ _ _ H) as Hct.
    destruct (clock s1 =? 0) eqn:Ez.
    + injection He as <- <-. apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)).
      * cbn [stack_remove.comp]. rewrite ev_jumplower, E1, E2. cbv beta iota. rewrite Ecmp, Ef', Hct, Ez. reflexivity.
      * exact (sr_ffi _ _ _ _ _ H).
    + apply N.eqb_neq in Ez.
      destruct (evaluate (prog0, dec_clock s1)) as [res s'] eqn:Ev.
      destruct (bad_fun_return res) eqn:Ebad; injection He as <- <-; [congruence|].
      assert (Hlt : eval_lt (prog0, dec_clock s1) (JumpLower r1 r2 dest, s1))
        by (left; cbn [snd]; unfold dec_clock; rewrite clock_set_clock; lia).
      destruct (IH (prog0, dec_clock s1) Hlt res s' (dec_clock t1) Ev Hr (state_rel_dec_clock _ _ _ _ _ H) Hbp)
        as (ck & t2 & E3 & P3). cbn [fst] in E3.
      exists ck, t2. split; [|exact P3]. cbn [stack_remove.comp].
      rewrite ev_jumplower. rewrite !get_var_set_clock, E1, E2. cbv beta iota. rewrite Ecmp.
      rewrite regs_set_clock, code_set_clock, Ef', clock_set_clock.
      replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite dec_clock_add by lia. rewrite E3, Ebad. reflexivity.
  - injection He as <- <-. apply (cc_zero _ _ _ _ _ _ _ t1); [|exact H].
    cbn [stack_remove.comp]. rewrite ev_jumplower, E1, E2. cbv beta iota. rewrite Ecmp. reflexivity.
Qed.

End RecCases.

Section RecCases2.
Context {a : N} {c ffi_t : Type}.
Implicit Types s t : state a c ffi_t.
Variables (jump : bool) (off : word a * word a) (k : N).

Lemma ev_rawcall_eq dest (X : state a c ffi_t) :
  evaluate (RawCall dest, X) =
  match lookup dest (code X) with
  | NONE => (SOME Error, X)
  | SOME prog0 =>
      match dest_Seq prog0 with
      | SOME (_, body) =>
          if (clock X =? 0) then (SOME TimeOut, empty_env X) else
            match evaluate (body, dec_clock X) with
            | (res, s) => if bad_fun_return res then (SOME Error, s) else (res, s)
            end
      | _ => (SOME Error, X)
      end
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma cc_rawcall dest s1 r s2 t1 (IH : IHT jump off k (RawCall dest, s1)) :
  evaluate (RawCall dest, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  cc_concl jump off k (RawCall dest) r s2 t1.
Proof.
  intros He Hr H. rewrite ev_rawcall_eq in He.
  destruct (lookup dest (code s1)) as [prog0|] eqn:El; [|injection He as <- <-; congruence].
  destruct (proj1 (sr_code_rel _ _ _ _ _ H) _ _ El) as [Hbp El'].
  destruct (dest_Seq prog0) as [[x body]|] eqn:Eds; [|injection He as <- <-; congruence].
  assert (Ep : prog0 = Seq x body) by (destruct prog0; try discriminate Eds; injection Eds as -> ->; reflexivity).
  subst prog0.
  cbn [reg_bound] in Hbp. apply andb_true_iff in Hbp as [_ Hbb].
  pose proof (sr_clock _ _ _ _ _ H) as Hct.
  destruct (clock s1 =? 0) eqn:Ez.
  - injection He as <- <-. apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)).
    + cbn [stack_remove.comp]. rewrite ev_rawcall_eq, El'. cbn [stack_remove.comp dest_Seq]. rewrite Hct, Ez. reflexivity.
    + exact (sr_ffi _ _ _ _ _ H).
  - apply N.eqb_neq in Ez.
    destruct (evaluate (body, dec_clock s1)) as [res s'] eqn:Ev.
    destruct (bad_fun_return res) eqn:Ebad; injection He as <- <-; [congruence|].
    assert (Hlt : eval_lt (body, dec_clock s1) (RawCall dest, s1))
      by (left; cbn [snd]; unfold dec_clock; rewrite clock_set_clock; lia).
    destruct (IH (body, dec_clock s1) Hlt res s' (dec_clock t1) Ev Hr (state_rel_dec_clock _ _ _ _ _ H) Hbb)
      as (ck & t2 & E3 & P3). cbn [fst] in E3.
    exists ck, t2. split; [|exact P3]. cbn [stack_remove.comp].
    rewrite ev_rawcall_eq, code_set_clock, El'. cbn [stack_remove.comp dest_Seq]. rewrite clock_set_clock.
    replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite dec_clock_add by lia. rewrite E3, Ebad. reflexivity.
Qed.

Definition ev_call_eq := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (@evaluate_def a c ffi_t))))))))))))))))))).

Lemma call_state (t1 : state a c ffi_t) lr v ck0 :
  clock t1 <> 0 ->
  dec_clock (set_var lr v (set_clock (ck0 + clock t1) t1)) =
  set_clock (ck0 + clock (dec_clock (set_var lr v t1))) (dec_clock (set_var lr v t1)).
Proof. intros H. rewrite set_var_set_clock. change (clock t1) with (clock (set_var lr v t1)) at 1. apply dec_clock_add. exact H. Qed.

Ltac call_prefix Ef' :=
  cbn [stack_remove.comp]; rewrite ev_call_eq; cbv beta iota;
  rewrite regs_set_clock, code_set_clock, Ef'; cbv beta iota;
  rewrite clock_set_clock.

Lemma cc_call ret dest h s1 r s2 t1 (IH : IHT jump off k (Call ret dest h, s1)) :
  evaluate (Call ret dest h, s1) = (r, s2) -> r <> SOME Error -> state_rel jump off k s1 t1 ->
  reg_bound (Call ret dest h) k = true -> cc_concl jump off k (Call ret dest h) r s2 t1.
Proof.
  intros He Hr H Hb. cbn [reg_bound] in Hb. apply andb_true_iff in Hb as [Hd Hrb].
  assert (Hdest : match dest with inl _ => True | inr i => i < k end)
    by (destruct dest; [exact Logic.I|apply N.ltb_lt; exact Hd]).
  rewrite ev_call_eq in He. pose proof (sr_clock _ _ _ _ _ H) as Hct.
  destruct ret as [[rh [lr [l1 l2]]]|].
  2: {
    destruct (find_code dest (regs s1) (code s1)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
    destruct (find_code_lemma jump off k s1 t1 dest prog0 (conj H (conj Hdest Ef)))
      as [Ef' Hbp].
    destruct (negb (bool_decide (h = NONE))) eqn:Eh; [injection He as <- <-; congruence|].
    destruct (clock s1 =? 0) eqn:Ez.
    - injection He as <- <-. apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)).
      + cbn [stack_remove.comp]. rewrite ev_call_eq. cbv beta iota. rewrite Ef'.
        destruct h as [[hh [k1 k2]]|]; [|]; cbn [stack_remove.comp] in *.
        all: rewrite ?Eh; cbv beta iota; rewrite ?Hct, ?Ez; try reflexivity.
        all: exfalso; apply negb_false_iff, bool_decide_spec in Eh; discriminate Eh.
      + exact (sr_ffi _ _ _ _ _ H).
    - apply N.eqb_neq in Ez.
      destruct (evaluate (prog0, dec_clock s1)) as [res s'] eqn:Ev.
      destruct (bad_fun_return res) eqn:Ebad; injection He as <- <-; [congruence|].
      assert (Hlt : eval_lt (prog0, dec_clock s1) (Call NONE dest h, s1))
        by (left; cbn [snd]; unfold dec_clock; rewrite clock_set_clock; lia).
      destruct (IH (prog0, dec_clock s1) Hlt res s' (dec_clock t1) Ev Hr (state_rel_dec_clock _ _ _ _ _ H) Hbp)
        as (ck & t2 & E3 & P3). cbn [fst] in E3.
      exists ck, t2. split; [|exact P3].
      apply negb_false_iff, bool_decide_spec in Eh. subst h.
      cbn [stack_remove.comp]. rewrite ev_call_eq. cbv beta iota.
      rewrite regs_set_clock, code_set_clock, Ef'. cbv beta iota.
      rewrite (proj2 (negb_false_iff _) (proj2 (bool_decide_spec _) eq_refl)).
      rewrite clock_set_clock.
      replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite dec_clock_add by lia. rewrite E3, Ebad. reflexivity. }
  apply andb_true_iff in Hrb as [Hrb Hhb]. apply andb_true_iff in Hrb as [Hrh Hlr]. apply N.ltb_lt in Hlr.
  destruct (find_code dest (regs s1 \\ lr) (code s1)) as [prog0|] eqn:Ef; [|injection He as <- <-; congruence].
  destruct (find_code_lemma2 jump off k s1 t1 dest prog0 lr (conj H (conj Hdest Ef)))
    as [Ef' Hbp].
  destruct (clock s1 =? 0) eqn:Ez.
  { injection He as <- <-. apply (cc_zero _ _ _ _ _ _ _ (empty_env t1)).
    - cbn [stack_remove.comp]. rewrite ev_call_eq. cbv beta iota. rewrite Ef'. cbv beta iota. rewrite Hct, Ez. reflexivity.
    - exact (sr_ffi _ _ _ _ _ H). }
  apply N.eqb_neq in Ez.
  set (Ys := dec_clock (set_var lr (Loc l1 l2) s1)) in He |- *.
  set (Yt := dec_clock (set_var lr (Loc l1 l2) t1)).
  assert (HY : state_rel jump off k Ys Yt)
    by (apply state_rel_dec_clock, state_rel_set_var; split; [exact H|exact Hlr]).
  destruct (evaluate (prog0, Ys)) as [res s'] eqn:Ev.
  assert (Hres : res <> SOME Error) by (intros ->; cbv beta iota in He; injection He as <- _; congruence).
  assert (HcY : clock Ys < clock s1) by (subst Ys; unfold dec_clock; rewrite clock_set_clock; cbn [clock set_var set_regs]; lia).
  assert (Hlt : eval_lt (prog0, Ys) (Call (SOME (rh, (lr, (l1, l2)))) dest h, s1)) by (left; exact HcY).
  destruct (IH (prog0, Ys) Hlt res s' Yt Ev Hres HY Hbp) as (ck & t2 & E2 & P2). cbn [fst] in E2.
  pose proof (evaluate_clock _ _ _ _ Ev) as Hcs'.
  assert (Pre : forall ck0, dec_clock (set_var lr (Loc l1 l2) (set_clock (ck0 + clock t1) t1)) =
                            set_clock (ck0 + clock Yt) Yt) by (intros ck0; subst Yt; apply call_state; lia).
  destruct res as [[x|x|n|n|w| |f|]|]; cbv beta iota in He.
  - (* Result *)
    destruct (bool_decide (x = Loc l1 l2)) eqn:Ex; cbn [negb] in He; [|injection He as <- <-; congruence].
    cbn [cc_post] in P2.
    assert (Hlt2 : eval_lt (rh, s') (Call (SOME (rh, (lr, (l1, l2)))) dest h, s1)) by (left; cbn [snd]; lia).
    destruct (IH (rh, s') Hlt2 r s2 t2 He Hr P2 Hrh) as (ck' & t3 & E3 & P3).
    exists (ck + ck'), t3. split; [|exact P3].
    call_prefix Ef'. replace (ck + ck' + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite Pre, (add_clock_some _ _ _ ck ck' _ E2 ltac:(discriminate)). cbv beta iota.
    rewrite Ex. cbn [negb]. rewrite N.add_comm. exact E3.
  - (* Exception *)
    destruct h as [[hh [k1 k2]]|].
    + destruct (bool_decide (x = Loc k1 k2)) eqn:Ex; cbn [negb] in He; [|injection He as <- <-; congruence].
      cbn [cc_post] in P2. cbn [reg_bound] in Hhb.
      assert (Hlt2 : eval_lt (hh, s') (Call (SOME (rh, (lr, (l1, l2)))) dest (SOME (hh, (k1, k2))), s1))
        by (left; cbn [snd]; lia).
      destruct (IH (hh, s') Hlt2 r s2 t2 He Hr P2 Hhb) as (ck' & t3 & E3 & P3).
      exists (ck + ck'), t3. split; [|exact P3].
      call_prefix Ef'. replace (ck + ck' + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite Pre, (add_clock_some _ _ _ ck ck' _ E2 ltac:(discriminate)). cbv beta iota.
      rewrite Ex. cbn [negb]. rewrite N.add_comm. exact E3.
    + injection He as <- <-. exists ck, t2. split; [|exact P2].
      call_prefix Ef'. replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      rewrite Pre, E2. reflexivity.
  - injection He as <- <-; congruence.
  - injection He as <- <-; congruence.
  - injection He as <- <-. exists ck, t2. split; [|exact P2].
    call_prefix Ef'. replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite Pre, E2. reflexivity.
  - injection He as <- <-. exists ck, t2. split; [|exact P2].
    call_prefix Ef'. replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite Pre, E2. reflexivity.
  - injection He as <- <-. exists ck, t2. split; [|exact P2].
    call_prefix Ef'. replace (ck + clock t1 =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    rewrite Pre, E2. reflexivity.
  - congruence.
  - injection He as <- <-; congruence.
Qed.

End RecCases2.

Section Main.
Context {a : N} {c ffi_t : Type}.

Lemma comp_correct_gen jump off k : forall (x : prog a * state a c ffi_t) r s2 t1,
  evaluate x = (r, s2) -> r <> SOME Error -> state_rel jump off k (snd x) t1 ->
  reg_bound (fst x) k = true -> cc_concl jump off k (fst x) r s2 t1.
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s2 t1 He Hr H Hb; cbn [fst snd] in *.
  assert (IH' : IHT jump off k (p, s)) by exact IH. clear IH.
  destruct p.
  - eapply cc_skip; eassumption.
  - eapply cc_inst; eassumption.
  - eapply cc_get; eassumption.
  - eapply cc_set; eassumption.
  - eapply cc_opcurrheap; eassumption.
  - eapply cc_call; eassumption.
  - eapply cc_seq; eassumption.
  - eapply cc_if; eassumption.
  - eapply cc_loop; eassumption.
  - eapply cc_jumplower; eassumption.
  - eapply cc_alloc; eassumption.
  - eapply cc_storeconsts; eassumption.
  - eapply cc_raise; eassumption.
  - eapply cc_return; eassumption.
  - eapply cc_break; eassumption.
  - eapply cc_continue; eassumption.
  - eapply cc_ffi; eassumption.
  - eapply cc_tick; eassumption.
  - eapply cc_locvalue; eassumption.
  - eapply cc_install; eassumption.
  - destruct a0. eapply cc_shmemop; eassumption.
  - eapply cc_cbw; eassumption.
  - eapply cc_dbw; eassumption.
  - eapply cc_rawcall; eassumption.
  - eapply cc_stackalloc; eassumption.
  - eapply cc_stackfree; eassumption.
  - eapply cc_stackstore; eassumption.
  - eapply cc_stackstoreany; eassumption.
  - eapply cc_stackload; eassumption.
  - eapply cc_stackloadany; eassumption.
  - eapply cc_stackgetsize; eassumption.
  - eapply cc_stacksetsize; eassumption.
  - eapply cc_bitmapload; eassumption.
  - eapply cc_halt; eassumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct" *)
Local Theorem comp_correct : forall (p : prog a) (s1 : state a c ffi_t) r s2 t1 k off jump,
  evaluate (p, s1) = (r, s2) /\ r <> SOME Error /\ state_rel jump off k s1 t1 /\ reg_bound p k ->
  exists ck t2,
    evaluate (stack_remove.comp jump off k p, set_clock (ck + clock t1) t1) = (r, t2) /\
    match r with
    | SOME (Halt _) => ffi t2 = ffi s2
    | SOME TimeOut => ffi t2 = ffi s2
    | SOME (FinalFFI _) => ffi t2 = ffi s2
    | _ => state_rel jump off k s2 t2
    end.
Proof.
  intros p s1 r s2 t1 k off jump (He & Hr & H & Hb).
  exact (comp_correct_gen jump off k (p, s1) r s2 t1 He Hr H Hb).
Qed.

End Main.

Section CompileSemantics.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "compile_semantics" *)
Theorem compile_semantics : forall jump off k (s1 s2 : state a c ffi_t) start,
  state_rel jump off k s1 s2 /\ semantics start s1 <> Fail ->
  semantics start s2 = semantics start s1.
Proof.
  intros jump off k s1 s2 start [H HF].
  apply semantics_sim; [exact HF|].
  intros k0 r st1 E Hr.
  pose proof (state_rel_with_clock jump off k s1 s2 k0 H) as Hk.
  assert (Hb : reg_bound (@Call a NONE (inl start) NONE) k = true) by reflexivity.
  destruct (comp_correct (Call NONE (inl start) NONE) (set_clock k0 s1) r st1 (set_clock k0 s2) k off jump
              (conj E (conj Hr (conj Hk Hb)))) as (ck & t2 & E2 & P2).
  exists ck, t2. split.
  - cbn [stack_remove.comp] in E2. rewrite clock_set_clock, set_clock_set_clock, N.add_comm in E2. exact E2.
  - destruct r as [[]|]; try exact P2; exact (sr_ffi _ _ _ _ _ P2).
Qed.

End CompileSemantics.

(** ** Initialisation code *)

Section InitDefs.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_val_def" *)
Definition mem_val (regs0 : fmap N (word_loc a)) (x : word a + N) : word_loc a :=
  match x with inl w => Word w | inr n => FAPPLY regs0 n end.

(** HOL [read_mem] recurses on [SUC n]; [read_mem_def] gives HOL's equations. *)
Definition read_mem (ad : word a) (m : word a -> word_loc a) (n : N) : list (word_loc a) :=
  num_rec (fun _ => []) (fun _ r ad => m ad :: r (ad + bytes_in_word)) n ad.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "read_mem_def" *)
Theorem read_mem_def : forall (ad : word a) m n,
  read_mem ad m 0 = [] /\ read_mem ad m (SUC n) = m ad :: read_mem (ad + bytes_in_word) m n.
Proof. intros; split; [reflexivity|]. unfold read_mem; rewrite num_rec_SUC; reflexivity. Qed.

(** HOL [addresses] recurses on [SUC n]; [addresses_def] gives HOL's equations. *)
Definition addresses (ad : word a) (n : N) : word a -> Prop :=
  num_rec (fun _ => EMPTY) (fun _ r ad => ad INSERT r (ad + bytes_in_word)) n ad.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "addresses_def" *)
Theorem addresses_def : forall (ad : word a) n,
  addresses ad 0 = EMPTY /\ addresses ad (SUC n) = ad INSERT addresses (ad + bytes_in_word) n.
Proof. intros; split; [reflexivity|]. unfold addresses; rewrite num_rec_SUC; reflexivity. Qed.

(** HOL's record update is written out with [mk_state]. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_reduce_def" *)
Definition init_reduce (gen_gc jump : bool) (off : word a * word a) (k : N) (code0 : spt (prog a))
    (bitmaps0 : list (word a)) (data_sp : N) (coracle : N -> c * (list (N * prog a) * list (word a)))
    (s : state a c ffi_t) : state a c ffi_t :=
  let heap_ptr := wordSem.theWord (FAPPLY (regs s) (k + 2)%N) in
  let bitmap_ptr := wordSem.theWord (FAPPLY (regs s) 3) << word_shift a in
  let stack_ptr := wordSem.theWord (FAPPLY (regs s) k) in
  let base_ptr := wordSem.theWord (FAPPLY (regs s) (k + 1)%N) in
  let heap_sp := (w2n (base_ptr - heap_ptr) DIV (dimindex a DIV 8) - LENGTH stack_remove.store_list)%N in
  let stack_sp := (w2n (stack_ptr - base_ptr) DIV (dimindex a DIV 8))%N in
  mk_state (regs s) (fp_regs s)
    (FEMPTY |++ MAP (fun n => match stack_remove.store_init gen_gc k n with
                              | inl w => (n, Word w)
                              | inr i => (n, FAPPLY (regs s) i)
                              end) (CurrHeap :: stack_remove.store_list))
    (read_mem base_ptr (stackSem.memory s) (stack_sp + 1))
    stack_sp (stackSem.memory s) (addresses heap_ptr heap_sp) (sh_mdomain s) bitmaps0
    (fun c0 p => stackSem.compile s c0 (MAP (stack_remove.prog_comp jump off k) p)) coracle
    (code_buffer s)
    (wordSem.mk_buffer (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0)) [] data_sp)
    (gc_fun s) true true false (clock s) code0 (ffi s) (ffi_save_regs s) (be s).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_heap_limit_ok_def" *)
Definition stack_heap_limit_ok (t : state a c ffi_t) (lims : N * N) : Prop :=
  let '(stack_lim, heap_lim) := lims in
  FLOOKUP (store t) HeapLength = SOME (Word (n2w heap_lim * bytes_in_word)) /\
  (heap_lim * (dimindex a DIV 8) < dimword a)%N /\
  stack_lim = LENGTH (stack t).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_prop_def" *)
Definition init_prop (gen_gc : bool) (max_heap data_sp : N) (stack_heap_lim : N * N) (s : state a c ffi_t) : Prop :=
  exists curr other bitmap_base len,
    FLOOKUP (store s) CurrHeap = SOME (Word curr) /\
    FLOOKUP (store s) NextFree = SOME (Word curr) /\
    FLOOKUP (store s) TriggerGC = SOME (Word (if gen_gc then curr else other)) /\
    FLOOKUP (store s) EndOfHeap = SOME (Word other) /\
    FLOOKUP (store s) OtherHeap = SOME (Word other) /\
    FLOOKUP (store s) BitmapBase = SOME (Word bitmap_base) /\
    FLOOKUP (store s) HeapLength = SOME (Word (n2w len * bytes_in_word)) /\
    FLOOKUP (store s) ProgStart = SOME (Word (n2w 0)) /\
    FLOOKUP (store s) AllocSize = SOME (Word (n2w 0)) /\
    FLOOKUP (store s) Globals = SOME (Word (n2w 0)) /\
    FLOOKUP (store s) GlobReal = SOME (Word curr) /\
    FLOOKUP (store s) Handler = SOME (Word (n2w 0)) /\
    FLOOKUP (store s) GenStart = SOME (Word (n2w 0)) /\
    FLOOKUP (store s) CodeBuffer = SOME (Word (wordSem.position (code_buffer s))) /\
    FLOOKUP (store s) CodeBufferEnd =
      SOME (Word (wordSem.position (code_buffer s) + n2w (wordSem.space_left (code_buffer s)))) /\
    FLOOKUP (store s) BitmapBuffer = SOME (Word (wordSem.position (data_buffer s))) /\
    FLOOKUP (store s) BitmapBufferEnd =
      SOME (Word (wordSem.position (data_buffer s) +
                  bytes_in_word * n2w (wordSem.space_left (data_buffer s)))) /\
    stack_heap_limit_ok s stack_heap_lim /\
    wordSem.buffer_buffer (code_buffer s) = [] /\ wordSem.buffer_buffer (data_buffer s) = [] /\
    use_stack s /\ use_store s /\
    FLOOKUP (regs s) 0 = SOME (Loc 1 0) /\
    (LENGTH (bitmaps s) + data_sp + 1 < dimword a)%N /\
    (LENGTH (stack s) < dimword a)%N /\
    other = curr + bytes_in_word * n2w len /\
    byte_aligned curr /\
    LAST (stack s) = Word (n2w 0) /\
    LENGTH (stack s) = SUC (stack_space s) /\
    (LENGTH (stack s) * (dimindex a DIV 8) < dimword a)%N /\
    (len + len <= max_heap)%N /\
    STAR (word_list_exists curr len) (word_list_exists other len) (fun2set (stackSem.memory s, mdomain s)).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_code_pre_def" *)
Definition init_code_pre (k : N) (bitmaps0 : list (word a)) (data_sp : N) (s : state a c ffi_t) : Prop :=
  exists ptr2 ptr3 ptr4 bitmap_ptr,
    good_dimindex a /\ (8 <= k)%N /\ 1 IN domain (code s) /\
    (k INSERT ((k + 1)%N INSERT ((k + 2)%N INSERT EMPTY))) SUBSET ffi_save_regs s /\
    ~ use_stack s /\ ~ use_store s /\ ~ use_alloc s /\
    FLOOKUP (regs s) 2 = SOME (Word ptr2) /\
    FLOOKUP (regs s) 3 = SOME (Word ptr3) /\
    FLOOKUP (regs s) 4 = SOME (Word ptr4) /\
    stackSem.memory s ptr2 = Word bitmap_ptr /\
    stackSem.memory s (ptr2 + bytes_in_word) =
      Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0)) /\
    stackSem.memory s (ptr2 + n2w 2 * bytes_in_word) =
      Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0) + bytes_in_word * n2w data_sp) /\
    stackSem.memory s (ptr2 + n2w 3 * bytes_in_word) = Word (wordSem.position (code_buffer s)) /\
    stackSem.memory s (ptr2 + n2w 4 * bytes_in_word) =
      Word (wordSem.position (code_buffer s) + n2w (wordSem.space_left (code_buffer s))) /\
    ptr2 <=+ ptr4 /\ n2w 1024 * bytes_in_word <=+ ptr4 - ptr2 /\
    byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
    wordSem.buffer_buffer (code_buffer s) = [] /\
    STAR (STAR (word_list bitmap_ptr (MAP Word bitmaps0))
               (word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0)) data_sp))
         (word_list_exists ptr2 (w2n (ptr4 - ptr2) DIV w2n (bytes_in_word : word a)))
      (fun2set (stackSem.memory s, mdomain s)).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_stack_heap_limit''_def" *)
Definition get_stack_heap_limit'' (h2 h3 h4 : N) : N * N :=
  ((h4 - h3 - LENGTH stack_remove.store_list)%N, ((h3 - h2) DIV 2)%N).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_stack_heap_limit'_def" *)
Definition get_stack_heap_limit' (max_heap : N) (p2 p3 p4 : word a) : N * N :=
  let ptr2 := w2n p2 in
  let ptr3 := w2n p3 in
  let ptr4 := w2n p4 in
  let d := (dimindex a DIV 8)%N in
  let max_heap_w : word a :=
    if (max_heap * w2n (bytes_in_word : word a) <? dimword a)%N then bytes_in_word * n2w max_heap
    else - n2w 1 in
  let reg3 : word a :=
    n2w ptr2 +
    ((- n2w 1 * n2w ptr2 +
      (if max_heap_w <+ - n2w 1 * n2w ptr2 + n2w ptr3 then max_heap_w + n2w ptr2 else n2w ptr3))
       >>> (word_shift a + 1) << (word_shift a + 1)) in
  get_stack_heap_limit'' (ptr2 DIV d) (w2n reg3 DIV d) (ptr4 DIV d).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_stack_heap_limit_def" *)
Definition get_stack_heap_limit (max_heap : N) (ptrs : word a * (word a * word a)) : N * N :=
  let '(ptr2, (ptr3, ptr4)) := ptrs in
  let middle := ptr2 + (- n2w 1 * ptr2 + ptr4) >>> (word_shift a + 1) << word_shift a in
  let adj_ptr2 := ptr2 + bytes_in_word * n2w stack_remove.max_stack_alloc in
  let adj_ptr4 := ptr4 - bytes_in_word * n2w stack_remove.max_stack_alloc in
  let adj_ptr3 := if andb (adj_ptr2 <=+ ptr3) (ptr3 <=+ adj_ptr4) then ptr3 else middle in
  get_stack_heap_limit' max_heap ptr2 adj_ptr3 ptr4.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "read_pointers_def" *)
Definition read_pointers (s : state a c ffi_t) : word a * (word a * word a) :=
  (wordSem.theWord (THE (FLOOKUP (regs s) 2)),
   (wordSem.theWord (THE (FLOOKUP (regs s) 3)),
    wordSem.theWord (THE (FLOOKUP (regs s) 4)))).

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_opt_def" *)
Definition make_init_opt (gen_gc : bool) (max_heap : N) (bitmaps0 : list (word a)) (data_sp : N)
    (coracle : N -> c * (list (N * prog a) * list (word a))) (jump : bool) (off : word a * word a) (k : N)
    (code0 : spt (prog a)) (s : state a c ffi_t) : option (state a c ffi_t) :=
  match evaluate (stack_remove.init_code gen_gc max_heap k, s) with
  | (SOME _, t) => NONE
  | (NONE, t) =>
      if classical_dec (init_prop gen_gc max_heap data_sp (get_stack_heap_limit max_heap (read_pointers s))
                          (init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle t))
      then SOME (init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle t) else NONE
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_pre_def" *)
Definition init_pre (gen_gc : bool) (max_heap : N) (bitmaps0 : list (word a)) (data_sp k start : N)
    (s : state a c ffi_t) : Prop :=
  lookup 0 (code s) = SOME (Seq (stack_remove.init_code gen_gc max_heap k) (Call NONE (inl start) NONE)) /\
  init_code_pre k bitmaps0 data_sp s /\ (stack_remove.max_stack_alloc <= max_heap)%N.

(** HOL's record update is written out with [mk_state]. *)
(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_def" *)
Definition make_init_any (gen_gc : bool) (max_heap : N) (bitmaps0 : list (word a)) (data_sp : N)
    (coracle : N -> c * (list (N * prog a) * list (word a))) (jump : bool) (off : word a * word a) (k : N)
    (code0 : spt (prog a)) (s : state a c ffi_t) : state a c ffi_t :=
  match make_init_opt gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s with
  | SOME t => t
  | NONE =>
      mk_state (FEMPTY |+ (0%N, Loc 1 0)) FEMPTY
        (FEMPTY |++ MAP (fun x => (x, Word (n2w 0))) (CurrHeap :: stack_remove.store_list))
        [Word (n2w 0)] 0 (stackSem.memory s) EMPTY (sh_mdomain s) [n2w 4]
        (fun c0 p => stackSem.compile s c0 (MAP (stack_remove.prog_comp jump off k) p)) coracle
        (wordSem.mk_buffer (n2w 0) [] 0) (wordSem.mk_buffer (n2w 0) [] 0)
        (gc_fun s) true true false (clock s) code0 (ffi s) (ffi_save_regs s) (be s)
  end.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "discharge_these_def" *)
Definition discharge_these (jump : bool) (off : word a * word a) (gen_gc : bool) (max_heap k start : N)
    (coracle : N -> c * (list (N * prog a) * list (word a))) (code0 : list (N * prog a)) (s2 : state a c ffi_t) : Prop :=
  EVERY (fun '(n, p) => andb (reg_bound p k) (stack_num_stubs <=? n + 1)%N) code0 /\
  (forall n i p, MEM (i, p) (FST (SND (coracle n))) -> reg_bound p k /\ (stack_num_stubs <= i + 1)%N) /\
  compile_oracle s2 = (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) ∘ coracle /\
  code s2 = fromAList (stack_remove.compile jump off gen_gc max_heap k start code0) /\
  (8 <= k)%N /\ 1 IN domain (code s2) /\
  (k INSERT ((k + 1)%N INSERT ((k + 2)%N INSERT EMPTY))) SUBSET ffi_save_regs s2 /\ ~ use_stack s2 /\
  ~ use_store s2 /\ ~ use_alloc s2 /\ (stack_remove.max_stack_alloc <= max_heap)%N.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "propagate_these_def" *)
Definition propagate_these (s : state a c ffi_t) (bitmaps0 : list (word a)) (data_sp : N) : Prop :=
  good_dimindex a /\
  exists ptr2 ptr3 ptr4 bitmap_ptr,
    FLOOKUP (regs s) 2 = SOME (Word ptr2) /\
    FLOOKUP (regs s) 3 = SOME (Word ptr3) /\
    FLOOKUP (regs s) 4 = SOME (Word ptr4) /\
    stackSem.memory s ptr2 = Word bitmap_ptr /\
    stackSem.memory s (ptr2 + bytes_in_word) =
      Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0)) /\
    stackSem.memory s (ptr2 + n2w 2 * bytes_in_word) =
      Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0) + bytes_in_word * n2w data_sp) /\
    stackSem.memory s (ptr2 + n2w 3 * bytes_in_word) = Word (wordSem.position (code_buffer s)) /\
    stackSem.memory s (ptr2 + n2w 4 * bytes_in_word) =
      Word (wordSem.position (code_buffer s) + n2w (wordSem.space_left (code_buffer s))) /\
    wordSem.buffer_buffer (code_buffer s) = [] /\
    ptr2 <=+ ptr4 /\
    byte_aligned ptr2 /\ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
    n2w 1024 * bytes_in_word <=+ ptr4 - ptr2 /\
    STAR (STAR (word_list bitmap_ptr (MAP Word bitmaps0))
               (word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps0)) data_sp))
         (word_list_exists ptr2 (w2n (- n2w 1 * ptr2 + ptr4) DIV w2n (bytes_in_word : word a)))
      (fun2set (stackSem.memory s, mdomain s)).

End InitDefs.


Section InitLemmas1.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "LENGTH_read_mem" *)
Theorem LENGTH_read_mem : forall n (ad : word a) m, LENGTH (read_mem ad m n) = n.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad m; [reflexivity|].
  rewrite (proj2 (read_mem_def ad m n)), LENGTH_cons_N, IH. reflexivity.
Qed.

Lemma bw_d (Hg : good_dimindex a) : (bytes_in_word : word a) = n2w (dimindex a DIV 8).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "IN_addresses" *)
Local Theorem IN_addresses : forall n (ad x : word a),
  x IN addresses ad n <-> exists i, i < n /\ x = (ad + n2w i * bytes_in_word)%w.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad x.
  - rewrite (proj1 (addresses_def ad 0)). split; [intros []|intros (i & Hi & _); lia].
  - rewrite (proj2 (addresses_def ad n)), IN_INSERT, IH. split.
    + intros [->|(i & Hi & ->)].
      * exists 0; split; [lia|wring].
      * exists (i + 1); split; [lia|]. rewrite <- word_add_n2w. wring.
    + intros (i & Hi & ->). destruct (N.eq_dec i 0) as [->|Hi0]; [left; wring|].
      right; exists (i - 1); split; [lia|]. replace i with (i - 1 + 1) at 1 by lia.
      rewrite <- word_add_n2w. wring.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "addresses_thm" *)
Theorem addresses_thm : forall n (ad : word a),
  addresses ad n = (fun x => exists i, x = (ad + n2w i * bytes_in_word)%w /\ i < n).
Proof.
  intros n ad. apply set_ext; intros x. change (addresses ad n x) with (x IN addresses ad n).
  rewrite IN_addresses. split; intros (i & H1 & H2); exists i; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "MOD_EQ_IMP_MULT" *)
Local Theorem MOD_EQ_IMP_MULT : forall n d, n MOD d = 0 /\ d <> 0 -> exists k, n = d * k.
Proof. intros n d [H Hd]. exists (n / d). pose proof (N.div_mod n d Hd). lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "star_move_lemma" *)
Local Theorem star_move_lemma : forall {T} (p0 p1 p1' p2 p3 p4 : (T -> Prop) -> Prop),
  STAR (STAR (STAR (STAR (STAR p0 p1) p1') p2) p3) p4 = STAR p2 (STAR (STAR p1 p1') (STAR p3 (STAR p4 p0))).
Proof. intros. star_ac. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "MOD_LESS_EQ_MOD_IMP" *)
Local Theorem MOD_LESS_EQ_MOD_IMP : forall m k n, m MOD k <= n /\ m < k -> m <= n.
Proof. intros m k n [H1 H2]. rewrite N.mod_small in H1 by exact H2. exact H1. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "MAP_mem_val_MAP_INL" *)
Local Theorem MAP_mem_val_MAP_INL : forall (ws : list (word a)) f, MAP (mem_val f) (MAP inl ws) = MAP Word ws.
Proof. induction ws as [|w ws IH]; intros f; [reflexivity|]. cbn [map]. rewrite IH. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_EQ_rev" *)
Theorem word_list_EQ_rev : forall {B} (xs : list B) (ad : word a),
  word_list ad xs = word_list_rev (ad + n2w (LENGTH xs) * bytes_in_word)%w (REVERSE xs).
Proof.
  intros B xs; induction xs as [|x xs IH] using rev_ind; intros ad; [reflexivity|].
  rewrite word_list_APPEND, IH, rev_app_distr. cbn [rev app word_list word_list_rev].
  rewrite LENGTH_app_N. change (LENGTH [x]) with 1.
  replace (ad + n2w (LENGTH xs + 1) * bytes_in_word - bytes_in_word)%w
    with (ad + n2w (LENGTH xs) * bytes_in_word)%w by (rewrite <- word_add_n2w; wring).
  replace (ad + bytes_in_word * n2w (LENGTH xs))%w with (ad + n2w (LENGTH xs) * bytes_in_word)%w by wring.
  rewrite (STAR_COMM (one _) emp), STAR_emp_l, STAR_COMM. reflexivity.
Qed.

Lemma LENGTH_REVERSE_N {B} (l : list B) : LENGTH (REVERSE l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_rev. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_and_rev_join_lemma" *)
Local Theorem word_list_and_rev_join_lemma : forall {B} (b ad : word a) (xs ys : list B) p q ss (b1 : Prop),
  b = (ad + n2w (LENGTH xs + LENGTH ys) * bytes_in_word)%w /\
  STAR (STAR p (word_list ad (xs ++ REVERSE ys))) q ss /\ b1 ->
  STAR (STAR (STAR p (word_list ad xs)) (word_list_rev b ys)) q ss /\ b1.
Proof.
  intros B b ad xs ys p q ss b1 (-> & H & Hb). split; [|exact Hb].
  rewrite word_list_APPEND, (word_list_EQ_rev (REVERSE ys)), rev_involutive, LENGTH_REVERSE_N in H.
  replace (ad + bytes_in_word * n2w (LENGTH xs) + n2w (LENGTH ys) * bytes_in_word)%w
    with (ad + n2w (LENGTH xs + LENGTH ys) * bytes_in_word)%w in H by (rewrite <- word_add_n2w; wring).
  rewrite STAR_ASSOC in H. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_IMP_read_mem" *)
Local Theorem word_list_IMP_read_mem : forall (m : word a -> word_loc a) dm xs (ad : word a) p,
  STAR p (word_list ad xs) (fun2set (m, dm)) -> read_mem ad m (LENGTH xs) = xs.
Proof.
  intros m dm xs; induction xs as [|x xs IH]; intros ad p H; [reflexivity|].
  rewrite LENGTH_cons_N, (proj2 (read_mem_def ad m (LENGTH xs))).
  cbn [word_list] in H. rewrite STAR_swap_l in H. destruct (sep_read _ _ _ _ _ H) as [E _].
  rewrite E. f_equal. apply (IH _ (STAR (one (ad, x)) p)). rewrite <- STAR_ASSOC. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "INSERT_DELETE_EQ_DELETE" *)
Local Theorem INSERT_DELETE_EQ_DELETE : forall {T} (x : T) s, (x INSERT s) DELETE x = s DELETE x.
Proof. intros. sets. Qed.

Lemma n2w_mul_d_ne0 (Hg : good_dimindex a) i :
  0 < i -> i * (dimindex a DIV 8) < dimword a -> (n2w (i * (dimindex a DIV 8)) : word a) <> n2w 0.
Proof.
  intros H0 Hl E. apply (f_equal w2n) in E. rewrite !w2n_n2w, (N.mod_small (i * _)) in E by exact Hl.
  rewrite N.Div0.mod_0_l in E. destruct (good_dimindex_d Hg) as [_ Hd]. nia.
Qed.

Lemma addresses_not_in (ad : word a) n :
  good_dimindex a -> (dimindex a DIV 8) * (n + 1) < dimword a -> ~ (ad IN addresses (ad + bytes_in_word)%w n).
Proof.
  intros Hg Hb Hin. apply IN_addresses in Hin as (i & Hi & E).
  apply (n2w_mul_d_ne0 Hg (i + 1)); [lia|nia|].
  rewrite <- word_mul_n2w. fold (bytes_in_word : word a).
  apply (f_equal (fun w => (w - ad)%w)) in E.
  replace (ad - ad)%w with (n2w 0 : word a) in E by wring. rewrite E. rewrite <- word_add_n2w. wring.
Qed.

End InitLemmas1.

Section InitLemmas2.
Context {a : N} {c ffi_t : Type}.

Lemma fun2set_EMPTY_eq (m : word a -> word_loc a) : fun2set (m, EMPTY) = EMPTY.
Proof. apply fun2set_EMPTY. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_addresses" *)
Local Theorem memory_addresses : forall n (ad : word a) (m : word a -> word_loc a),
  n * (dimindex a DIV 8) < dimword a /\ good_dimindex a ->
  memory m (addresses ad n) = word_list ad (read_mem ad m n).
Proof.
  intros n; induction n as [|n IH] using N.peano_ind; intros ad m [Hb Hg].
  - rewrite (proj1 (addresses_def ad 0)), (proj1 (read_mem_def ad m 0)). cbn [word_list].
    unfold memory. rewrite fun2set_EMPTY_eq. reflexivity.
  - rewrite (proj2 (addresses_def ad n)), (proj2 (read_mem_def ad m n)). cbn [word_list].
    rewrite <- IH by (split; [nia|exact Hg]).
    assert (Hn : ~ (ad IN addresses (ad + bytes_in_word)%w n)) by (apply addresses_not_in; [exact Hg|nia]).
    apply functional_extensionality; intros s; apply propositional_extensionality.
    unfold memory. rewrite one_STAR. split.
    + intros ->. split; [apply IN_fun2set; split; [reflexivity|left; reflexivity]|].
      rewrite fun2set_DELETE. f_equal. f_equal. apply set_ext; intros x. unfold pred_set.DELETE, pred_set.DIFF,
        pred_set.INSERT, pred_set.IN, pred_set.EMPTY. split; [intros [[->|Hx] Hn2]; [exfalso; apply Hn2; left; reflexivity|exact Hx]|].
      intros Hx; split; [right; exact Hx|intros [E|[]]; subst x; exact (Hn Hx)].
    + intros [Hin Hd]. apply set_ext; intros [b z].
      split.
      * intros Hs. destruct (classic ((b, z) = (ad, m ad))) as [E|Ne].
        -- injection E as -> ->. apply IN_fun2set; split; [reflexivity|left; reflexivity].
        -- assert (Hx : (b, z) IN (s DELETE (ad, m ad))) by (apply IN_DELETE; split; assumption).
           rewrite Hd in Hx. apply IN_fun2set in Hx as [Ez Hb2]. apply IN_fun2set; split; [exact Ez|right; exact Hb2].
      * intros Hf. apply IN_fun2set in Hf as [Ez [Eb|Hb2]].
        -- subst b z. exact Hin.
        -- assert (Hx : (b, z) IN fun2set (m, addresses (ad + bytes_in_word)%w n)) by (apply IN_fun2set; split; assumption).
           rewrite <- Hd in Hx. apply IN_DELETE in Hx as [Hx _]. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_exists_addresses" *)
Theorem word_list_exists_addresses : forall (m1 : word a -> word_loc a) n (ad : word a),
  (dimindex a DIV 8) * n < dimword a /\ good_dimindex a ->
  word_list_exists ad n (fun2set (m1, addresses ad n)).
Proof.
  intros m1 n; induction n as [|n IH] using N.peano_ind; intros ad [Hb Hg].
  - rewrite (proj1 (word_list_exists_thm ad 0)), (proj1 (addresses_def ad 0)), fun2set_EMPTY_eq. reflexivity.
  - rewrite (proj2 (word_list_exists_thm ad n)), (proj2 (addresses_def ad n)).
    apply SEP_EXISTS_THM. exists (m1 ad). apply one_fun2set. split; [reflexivity|]. split; [left; reflexivity|].
    assert (Hn : ~ (ad IN addresses (ad + bytes_in_word)%w n)) by (apply addresses_not_in; [exact Hg|nia]).
    replace ((ad INSERT addresses (ad + bytes_in_word)%w n) DELETE ad) with (addresses (ad + bytes_in_word)%w n).
    + apply IH. split; [nia|exact Hg].
    + apply set_ext; intros x.
      unfold pred_set.DELETE, pred_set.DIFF, pred_set.INSERT, pred_set.IN, pred_set.EMPTY in *. split.
      * intros Hx; split; [right; exact Hx|intros [E|[]]; subst x; exact (Hn Hx)].
      * intros [[E|Hx] Hne]; [subst x; exfalso; apply Hne; left; reflexivity|exact Hx].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_reduce_stack_space" *)
Local Theorem init_reduce_stack_space : forall gen_gc jump off k code0 bitmaps0 data_sp coracle (s8 : state a c ffi_t),
  stack_space (init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle s8) <=
  LENGTH (stack (init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle s8)).
Proof. intros. unfold init_reduce. cbv zeta. cbn [stack stack_space]. rewrite LENGTH_read_mem. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "byte_aligned_bytes_in_word_MULT" *)
Local Theorem byte_aligned_bytes_in_word_MULT : forall w : word a,
  good_dimindex a -> byte_aligned (bytes_in_word * w)%w.
Proof.
  intros w Hg. unfold byte_aligned, bytes_in_word. destruct Hg as [E|E]; rewrite E.
  - change (LOG2 (32 DIV 8)) with 2. replace (n2w (32 DIV 8) : word a) with (n2w 1 << 2 : word a)%w.
    + apply aligned_mul_shift_1.
    + rewrite WORD_MUL_LSL, word_mul_n2w. reflexivity.
  - change (LOG2 (64 DIV 8)) with 3. replace (n2w (64 DIV 8) : word a) with (n2w 1 << 3 : word a)%w.
    + apply aligned_mul_shift_1.
    + rewrite WORD_MUL_LSL, word_mul_n2w. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "sub_rewrite" *)
Local Theorem sub_rewrite : forall ptr ptr', ptr <= ptr' ->
  (- n2w 1 * n2w ptr + n2w ptr' : word a)%w = n2w (ptr' - ptr).
Proof. intros ptr ptr' H. word_Z. rewrite N2Z.inj_sub by exact H. apply zcong_eq. ring. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "div_rewrite" *)
Local Theorem div_rewrite : forall n x, n <= x /\ 1 < n -> x / n <> 0.
Proof. intros n x [H1 H2] E. apply N.div_small_iff in E; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "push_if" *)
Theorem push_if : forall {A B} (b : bool) (f g : A -> B) x y,
  (if b then f x else f y) = f (if b then x else y) /\ (if b then f x else g x) = (if b then f else g) x.
Proof. intros; destruct b; split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "fmap_simp_lemma1" *)
Local Theorem fmap_simp_lemma1 : forall {V} (g : fmap N V) x y z,
  ((g |+ (0, x)) |+ (5, y)) |+ (0, z) = (g |+ (0, z)) |+ (5, y).
Proof. intros. apply fmap_ext; intros key. rewrite !FLOOKUP_UPDATE.
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)) end; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_inj" *)
Theorem word_list_inj : forall {B} (xs : list B) (ad : word a) u u',
  word_list ad xs u /\ word_list ad xs u' -> u = u'.
Proof.
  intros B xs; induction xs as [|x xs IH]; intros ad u u' [H1 H2].
  - cbn [word_list] in *. unfold emp in *. congruence.
  - cbn [word_list] in *. apply one_STAR in H1 as [Hi1 H1]. apply one_STAR in H2 as [Hi2 H2].
    pose proof (IH _ _ _ (conj H1 H2)) as E.
    apply set_ext; intros y. destruct (classic (y = (ad, x))) as [->|Ne]; [split; intros; assumption|].
    split; intros Hy.
    + assert (Hy' : y IN (u DELETE (ad, x))) by (apply IN_DELETE; split; assumption).
      rewrite E in Hy'. apply IN_DELETE in Hy' as [Hy' _]. exact Hy'.
    + assert (Hy' : y IN (u' DELETE (ad, x))) by (apply IN_DELETE; split; assumption).
      rewrite <- E in Hy'. apply IN_DELETE in Hy' as [Hy' _]. exact Hy'.
Qed.

End InitLemmas2.

Section InitLemmas3.
Context {a : N} {c ffi_t : Type}.

Lemma d_divides_dimword (Hg : good_dimindex a) : (dimindex a DIV 8) * (dimword a / (dimindex a DIV 8)) = dimword a.
Proof. rewrite dimword_pow. destruct Hg as [E|E]; rewrite E; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_wrap" *)
Theorem word_list_wrap : forall {B} (ls : list B) (ad : word a),
  good_dimindex a /\ dimword a / (dimindex a DIV 8) < LENGTH ls ->
  exists x xs y ys b, word_list ad ls = STAR (word_list ad (x :: xs)) (word_list b (y :: ys)) /\ b = ad.
Proof.
  intros B ls ad [Hg Hl]. set (r := dimword a / (dimindex a DIV 8)) in *.
  assert (Hr0 : 0 < r) by (subst r; rewrite dimword_pow; destruct Hg as [E|E]; rewrite E; cbn; lia).
  rewrite <- (firstn_skipn (N.to_nat r) ls).
  assert (Ht : LENGTH (firstn (N.to_nat r) ls) = r)
    by (rewrite LENGTH_length, length_firstn; rewrite LENGTH_length in Hl; lia).
  destruct (firstn (N.to_nat r) ls) as [|x xs] eqn:Et; [cbn in Ht; lia|].
  destruct (skipn (N.to_nat r) ls) as [|y ys] eqn:Ed.
  { exfalso. pose proof (firstn_skipn (N.to_nat r) ls) as E. rewrite Et, Ed, app_nil_r in E.
    rewrite <- E, Ht in Hl. lia. }
  exists x, xs, y, ys, ad. split; [|reflexivity].
  rewrite word_list_APPEND, Ht. f_equal. f_equal.
  unfold bytes_in_word. rewrite word_mul_n2w. unfold r. rewrite d_divides_dimword by exact Hg. rewrite n2w_dimword. wring.
Qed.

Lemma w2n_add_bw (ad : word a) L (Hg : good_dimindex a) :
  w2n ad + (L + 1) * w2n (bytes_in_word : word a) < dimword a ->
  w2n (ad + bytes_in_word)%w = w2n ad + w2n (bytes_in_word : word a).
Proof. intros H. unfold word_add. rewrite w2n_n2w, N.mod_small; [reflexivity|nia]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_set" *)
Theorem word_list_set : forall {B} `{Inhabited B} (xs : list B) (ad : word a),
  good_dimindex a /\ w2n ad + LENGTH xs * w2n (bytes_in_word : word a) < dimword a ->
  word_list ad xs (set (GENLIST (fun i => ((ad + n2w i * bytes_in_word)%w, EL i xs)) (LENGTH xs))).
Proof.
  intros B HB xs; induction xs as [|x xs IH]; intros ad [Hg Hb].
  - reflexivity.
  - rewrite LENGTH_cons_N in Hb |- *. cbn [word_list]. apply one_STAR.
    destruct (good_dimindex_d Hg) as [Hd Hd0]. split.
    + apply IN_set, In_GENLIST_iff. exists 0. split; [lia|]. f_equal. wring.
    + replace (set (GENLIST (fun i => ((ad + n2w i * bytes_in_word)%w, EL i (x :: xs))) (N.succ (LENGTH xs)))
               DELETE (ad, x))
        with (set (GENLIST (fun i => ((ad + bytes_in_word + n2w i * bytes_in_word)%w, EL i xs)) (LENGTH xs))).
      * apply IH. split; [exact Hg|]. rewrite (w2n_add_bw _ (LENGTH xs) Hg) by nia. nia.
      * apply set_ext; intros y. change ((y IN set (GENLIST (fun i => ((ad + bytes_in_word + n2w i * bytes_in_word)%w, EL i xs)) (LENGTH xs))) <->
          (y IN (set (GENLIST (fun i => ((ad + n2w i * bytes_in_word)%w, EL i (x :: xs))) (N.succ (LENGTH xs))) DELETE (ad, x)))).
        rewrite IN_DELETE, !IN_set, !In_GENLIST_iff. split.
        -- intros (i & Hi & ->). split.
           ++ exists (i + 1). split; [lia|]. f_equal.
              ** rewrite <- word_add_n2w. wring.
              ** replace (i + 1) with (SUC i) by lia. rewrite EL_SUC. reflexivity.
           ++ intros E. injection E as E _. apply (n2w_mul_d_ne0 Hg (i + 1)); [lia|nia|].
              rewrite <- word_mul_n2w. fold (bytes_in_word : word a).
              apply (f_equal (fun w => (w - ad)%w)) in E.
              replace (ad - ad)%w with (n2w 0 : word a) in E by wring. rewrite <- E, <- word_add_n2w. wring.
        -- intros [(i & Hi & ->) Hne]. destruct (N.eq_dec i 0) as [->|Hi0].
           ++ exfalso; apply Hne. f_equal. wring.
           ++ exists (i - 1). split; [lia|]. f_equal.
              ** replace i with (i - 1 + 1) at 1 by lia. rewrite <- word_add_n2w. wring.
              ** replace i with (SUC (i - 1)) at 1 by lia. rewrite EL_SUC. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_seteq" *)
Theorem word_list_seteq : forall {B} `{Inhabited B} (xs : list B) (ad : word a),
  good_dimindex a /\ w2n ad + LENGTH xs * w2n (bytes_in_word : word a) < dimword a ->
  word_list ad xs = (fun s => s = set (GENLIST (fun i => ((ad + n2w i * bytes_in_word)%w, EL i xs)) (LENGTH xs))).
Proof.
  intros B HB xs ad H. pose proof (word_list_set xs ad H) as Hs.
  apply functional_extensionality; intros s; apply propositional_extensionality. split.
  - intros Hw. exact (word_list_inj xs ad _ _ (conj Hw Hs)).
  - intros ->. exact Hs.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_EL_in_memory" *)
Theorem word_list_EL_in_memory : forall {B} `{Inhabited B} (xs : list B) (ad : word a) r1 r2 m dm i,
  good_dimindex a /\ w2n ad + LENGTH xs * w2n (bytes_in_word : word a) < dimword a /\
  STAR (STAR r1 (word_list ad xs)) r2 (fun2set (m, dm)) /\ i < LENGTH xs ->
  m (ad + n2w i * bytes_in_word)%w = EL i xs.
Proof.
  intros B HB xs ad r1 r2 m dm i (Hg & Hb & H & Hi).
  assert (H' : STAR (word_list ad xs) (STAR r1 r2) (fun2set (m, dm))).
  { revert H. replace (STAR (STAR r1 (word_list ad xs)) r2) with (STAR (word_list ad xs) (STAR r1 r2)); [auto|]. star_ac. }
  destruct (word_list_read xs ad _ m dm i H' Hi) as [E _].
  rewrite <- E. f_equal. wring.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_in_memory" *)
Theorem word_list_in_memory : forall (xs : list (word_loc a)) (ad : word a) r1 r2 m dm,
  STAR (STAR r1 (word_list ad xs)) r2 (fun2set (m, dm)) /\ good_dimindex a /\
  w2n ad + LENGTH xs * w2n (bytes_in_word : word a) < dimword a ->
  memory m (addresses ad (LENGTH xs)) = word_list ad xs.
Proof.
  intros xs ad r1 r2 m dm (H & Hg & Hb).
  destruct (good_dimindex_d Hg) as [Hd _].
  rewrite memory_addresses by (split; [rewrite Hd in Hb; nia|exact Hg]).
  f_equal. apply (word_list_IMP_read_mem m dm xs ad (STAR r1 r2)).
  revert H. replace (STAR (STAR r1 (word_list ad xs)) r2) with (STAR (STAR r1 r2) (word_list ad xs)); [auto|]. star_ac.
Qed.

End InitLemmas3.

Section StoreListCode.
Context {a : N} {c ffi_t : Type}.

Lemma mem_val_upd_other (R : fmap N (word_loc a)) r v xs :
  (forall n, In (inr n) xs -> n <> r) ->
  MAP (mem_val (R |+ (r, v))) xs = MAP (mem_val R) xs.
Proof.
  intros H. apply map_ext_in. intros [w|n] Hin; [reflexivity|]. cbn [mem_val].
  unfold FAPPLY. rewrite FLOOKUP_UPDATE. destruct (decide (r = n)) as [->|]; [|reflexivity].
  exfalso; exact (H n Hin eq_refl).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "store_list_code_thm" *)
Theorem store_list_code_thm : forall a0 t (xs : list (word a + N)) (s : state a c ffi_t) (w : word a) frame ys m dm,
  STAR (word_list w ys) frame (fun2set (m, dm)) /\
  m = stackSem.memory s /\ dm = mdomain s /\
  LENGTH ys = LENGTH xs /\ a0 <> t /\
  get_var a0 s = SOME (Word w) /\ t IN FDOM (regs s) /\
  EVERY (fun x => ⌜forall n, inr n = x -> n <> a0 /\ n <> t /\ n IN FDOM (regs s)⌝) xs ->
  exists r1 m1,
    STAR (word_list w (MAP (mem_val (regs s)) xs)) frame (fun2set (m1, mdomain s)) /\
    evaluate (stack_remove.store_list_code a0 t xs, s) =
      (NONE, set_regs (regs s |++ [(a0, Word (w + bytes_in_word * n2w (LENGTH xs))%w); (t, r1)])
               (set_memory m1 s)).
Proof.
  intros a0 t xs; induction xs as [|x xs IH];
    intros s w frame ys m dm (Hs & -> & -> & Hl & Hat & Ha & Ht & Hev).
  - destruct ys; [|rewrite LENGTH_cons_N in Hl; cbn in Hl; lia].
    exists (FAPPLY (regs s) t), (stackSem.memory s). split; [exact Hs|].
    cbn [stack_remove.store_list_code]. rewrite ev_skip. f_equal.
    apply state_ext_fw; stk_fields; try reflexivity. cbn [FUPDATE_LIST FOLDL].
    apply fmap_ext; intros key. rewrite !FLOOKUP_UPDATE.
    destruct (decide (t = key)) as [<-|]; [|destruct (decide (a0 = key)) as [<-|]; [|reflexivity]].
    + unfold FAPPLY. unfold FDOM, pred_set.IN in Ht. destruct (FLOOKUP (regs s) t); [reflexivity|congruence].
    + unfold get_var in Ha. rewrite Ha. f_equal. f_equal. cbn [LENGTH]. wring.
  - destruct ys as [|y ys]; [rewrite LENGTH_cons_N in Hl; cbn in Hl; lia|].
    rewrite !LENGTH_cons_N in Hl.
    cbn [EVERY] in Hev. apply andb_true_iff in Hev as [Hx Hev]. apply bool_decide_spec in Hx.
    cbn [word_list] in Hs. rewrite <- STAR_ASSOC in Hs.
    destruct (sep_read _ _ _ _ _ Hs) as [_ Hwd].
    unfold get_var in Ha.
    assert (Hev' : forall n, In (inr n) xs -> n <> a0 /\ n <> t /\ n IN FDOM (regs s)).
    { intros n Hn. unfold is_true in Hev. rewrite EVERY_Forall, Forall_forall in Hev.
      specialize (Hev _ Hn). apply bool_decide_spec in Hev. exact (Hev n eq_refl). }
    (* the value stored and the state after the first block *)
    set (v := mem_val (regs s) x).
    assert (Hblock : exists R1, evaluate (stack_remove.store_list_code a0 t (x :: xs), s) =
              evaluate (stack_remove.store_list_code a0 t xs,
                set_var a0 (Word (w + bytes_in_word)%w)
                  (set_memory ((w =+ v) (stackSem.memory s)) (set_regs R1 s))) /\
              FLOOKUP R1 a0 = FLOOKUP (regs s) a0 /\ (forall n, n <> t -> FLOOKUP R1 n = FLOOKUP (regs s) n) /\
              t IN FDOM R1).
    { destruct x as [w'|i].
      - exists (regs s |+ (t, Word w')). cbn [stack_remove.store_list_code list_Seq].
        assert (F1 : FLOOKUP (regs (set_var t (Word w') s)) a0 = SOME (Word w))
          by (rewrite FLOOKUP_set_var_other by congruence; exact Ha).
        assert (F2 : FLOOKUP (regs (set_var t (Word w') s)) t = SOME (Word w')) by apply FLOOKUP_set_var_same.
        assert (D2 : w IN mdomain (set_var t (Word w') s)) by exact Hwd.
        assert (E3 : evaluate (Seq (stackLang.const_inst t w') (Seq (stackLang.store_inst t a0)
                       (stackLang.add_bytes_in_word_inst a0)), s) =
                     (NONE, set_var a0 (Word (w + bytes_in_word)%w)
                        (set_memory ((w =+ Word w') (stackSem.memory s)) (set_regs (regs s |+ (t, Word w')) s)))).
        { rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_const _ _ _))).
          rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_store0 t a0 w (Word w') _ F1 F2 D2))).
          apply ev_inst_some. apply inst_add_imm. exact F1. }
        split; [rewrite (ev_seq_none _ _ _ _ E3); reflexivity|].
        split; [rewrite FLOOKUP_UPDATE; destruct (decide (t = a0)); [congruence|reflexivity]|].
        split; [intros n Hn; rewrite FLOOKUP_UPDATE; destruct (decide (t = n)); [congruence|reflexivity]|].
        unfold FDOM, pred_set.IN. rewrite FLOOKUP_UPDATE. destruct (decide (t = t)); [discriminate|congruence].
      - exists (regs s). cbn [stack_remove.store_list_code list_Seq].
        destruct (Hx i eq_refl) as (Hia & Hit & Hif).
        assert (F2 : FLOOKUP (regs s) i = SOME v).
        { subst v. cbn [mem_val]. unfold FAPPLY. unfold FDOM, pred_set.IN in Hif.
          destruct (FLOOKUP (regs s) i); [reflexivity|congruence]. }
        assert (E3 : evaluate (Seq (stackLang.store_inst i a0) (stackLang.add_bytes_in_word_inst a0), s) =
                     (NONE, set_var a0 (Word (w + bytes_in_word)%w)
                        (set_memory ((w =+ v) (stackSem.memory s)) (set_regs (regs s) s)))).
        { rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_store0 i a0 w v _ Ha F2 Hwd))).
          apply ev_inst_some. apply inst_add_imm. exact Ha. }
        split; [rewrite (ev_seq_none _ _ _ _ E3); reflexivity|].
        split; [reflexivity|]. split; [intros; reflexivity|exact Ht]. }
    destruct Hblock as (R1 & Eb & HR1a & HR1 & HR1t).
    set (s4 := set_var a0 (Word (w + bytes_in_word)%w) (set_memory ((w =+ v) (stackSem.memory s)) (set_regs R1 s))).
    pose proof (sep_write _ _ _ v _ _ Hs) as Hs'.
    assert (Hs4 : STAR (word_list (w + bytes_in_word)%w ys) (STAR frame (one (w, v)))
                    (fun2set (stackSem.memory s4, mdomain s4))).
    { subst s4. stk_fields. replace (STAR (word_list (w + bytes_in_word)%w ys) (STAR frame (one (w, v))))
        with (STAR (one (w, v)) (STAR (word_list (w + bytes_in_word)%w ys) frame)) by star_ac. exact Hs'. }
    assert (Ha4 : get_var a0 s4 = SOME (Word (w + bytes_in_word)%w)) by (subst s4; unfold get_var; apply FLOOKUP_set_var_same).
    assert (Ht4 : t IN FDOM (regs s4)).
    { subst s4. unfold FDOM, pred_set.IN in *. cbn [regs set_var set_regs set_memory].
      rewrite FLOOKUP_UPDATE. destruct (decide (a0 = t)); [discriminate|exact HR1t]. }
    assert (Hev4 : EVERY (fun x => ⌜forall n, inr n = x -> n <> a0 /\ n <> t /\ n IN FDOM (regs s4)⌝) xs).
    { unfold is_true. rewrite EVERY_Forall, Forall_forall. intros z Hz. apply bool_decide_spec.
      intros n En. subst z. destruct (Hev' n Hz) as (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
      subst s4. unfold FDOM, pred_set.IN in *. cbn [regs set_var set_regs set_memory].
      rewrite FLOOKUP_UPDATE. destruct (decide (a0 = n)); [discriminate|]. rewrite HR1 by exact H2. exact H3. }
    assert (Hl' : LENGTH ys = LENGTH xs) by lia.
    destruct (IH s4 (w + bytes_in_word)%w (STAR frame (one (w, v))) ys _ _
                (conj Hs4 (conj eq_refl (conj eq_refl (conj Hl' (conj Hat (conj Ha4 (conj Ht4 Hev4))))))))
      as (r1 & m1 & Hm1 & Ev).
    exists r1, m1. split.
    + replace (MAP (mem_val (regs s)) (x :: xs)) with (v :: MAP (mem_val (regs s4)) xs).
      * cbn [word_list]. revert Hm1. replace (STAR (word_list (w + bytes_in_word)%w (MAP (mem_val (regs s4)) xs))
                                               (STAR frame (one (w, v))))
          with (STAR (STAR (one (w, v)) (word_list (w + bytes_in_word)%w (MAP (mem_val (regs s4)) xs))) frame) by star_ac.
        auto.
      * cbn [map]. f_equal. subst s4. cbn [regs set_var set_regs set_memory].
        rewrite mem_val_upd_other by (intros n Hn; exact (proj1 (Hev' n Hn))).
        apply map_ext_in. intros [w0|n] Hin; [reflexivity|]. cbn [mem_val]. unfold FAPPLY.
        rewrite HR1 by exact (proj1 (proj2 (Hev' n Hin))). reflexivity.
    + rewrite Eb. fold s4. rewrite Ev. f_equal. subst s4.
      apply state_ext_fw; stk_fields; try reflexivity.
      cbn [FUPDATE_LIST FOLDL]. apply fmap_ext; intros key. rewrite !FLOOKUP_UPDATE.
      destruct (decide (t = key)) as [<-|]; [reflexivity|].
      destruct (decide (a0 = key)) as [<-|].
      * f_equal. f_equal. rewrite LENGTH_cons_N. rewrite <- N.add_1_l, <- word_add_n2w. wring.
      * apply HR1. congruence.
Qed.

End StoreListCode.

Section InitMisc.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "clock_neutral_store_list_code" *)
Theorem clock_neutral_store_list_code : forall (xs : list (word a + N)) n k,
  clock_neutral (stack_remove.store_list_code n k xs).
Proof.
  unfold is_true. induction xs as [|[w|i] xs IH]; intros n k; [reflexivity| |];
    cbn [stack_remove.store_list_code list_Seq clock_neutral andb]; apply IH.
Qed.

Lemma clock_neutral_init_code gen_gc max_heap k : clock_neutral (@stack_remove.init_code a gen_gc max_heap k) = true.
Proof.
  unfold stack_remove.init_code, stack_remove.init_memory. cbv zeta.
  cbn [list_Seq clock_neutral andb]. rewrite Bool.andb_true_r. apply clock_neutral_store_list_code.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_init_code_clock" *)
Local Theorem evaluate_init_code_clock : forall gen_gc max_heap k (s : state a c ffi_t) res t c0,
  evaluate (stack_remove.init_code gen_gc max_heap k, s) = (res, t) ->
  evaluate (stack_remove.init_code gen_gc max_heap k, set_clock c0 s) = (res, set_clock c0 t).
Proof.
  intros gen_gc max_heap k s res t c0 H.
  apply evaluate_clock_neutral. split; [exact H|apply clock_neutral_init_code].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_init_code_ffi" *)
Theorem evaluate_init_code_ffi : forall gen_gc max_heap k (s : state a c ffi_t) res t c0,
  evaluate (stack_remove.init_code gen_gc max_heap k, s) = (res, t) ->
  evaluate (stack_remove.init_code gen_gc max_heap k, set_ffi c0 s) = (res, set_ffi c0 t).
Proof.
  intros gen_gc max_heap k s res t c0 H.
  apply evaluate_ffi_neutral. split; [exact H|apply clock_neutral_init_code].
Qed.

Lemma ALOOKUP_init_stubs gen_gc max_heap k start n :
  3 <= n -> ALOOKUP (@stack_remove.init_stubs a gen_gc max_heap k start) n = NONE.
Proof.
  intros H. unfold stack_remove.init_stubs. cbn [ALOOKUP].
  destruct (decide (0 = n)); [lia|]. destruct (decide (1 = n)); [lia|]. destruct (decide (2 = n)); [lia|].
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "IMP_code_rel" *)
Local Theorem IMP_code_rel : forall jump off k gen_gc max_heap start (code1 : list (N * prog a)) code2,
  EVERY (fun '(n, p) => andb (reg_bound p k) (stack_num_stubs <=? n + 1)) code1 /\
  code2 = fromAList (stack_remove.compile jump off gen_gc max_heap k start code1) ->
  code_rel jump off k (fromAList code1) code2.
Proof.
  intros jump off k gen_gc max_heap start code1 code2 [Hev ->]. split.
  - intros n p Hl. rewrite sptree.lookup_fromAList in Hl |- *.
    pose proof (ALOOKUP_In _ _ _ Hl) as Hin.
    unfold is_true in Hev. rewrite EVERY_Forall, Forall_forall in Hev.
    specialize (Hev _ Hin). cbv beta iota in Hev. apply andb_true_iff in Hev as [Hb Hs].
    apply N.leb_le in Hs. unfold stack_num_stubs in Hs.
    split; [exact Hb|]. unfold stack_remove.compile. rewrite ALOOKUP_APPEND, ALOOKUP_init_stubs by lia.
    rewrite ALOOKUP_prog_comp, Hl. reflexivity.
  - rewrite !sptree.domain_fromAList. unfold stack_remove.compile.
    rewrite map_app, MAP_FST_prog_comp. apply set_ext; intros x.
    unfold pred_set.UNION, pred_set.INSERT, pred_set.IN, pred_set.EMPTY.
    unfold stack_remove.init_stubs. cbn [map fst app MEM].
    unfold is_true. rewrite !orb_true_iff, !bool_decide_spec. tauto.
Qed.

End InitMisc.

Section MakeInitAny.
Context {a : N} {c ffi_t : Type}.

Lemma set_ffi_same (s : state a c ffi_t) : set_ffi (ffi s) s = s.
Proof. destruct s; reflexivity. Qed.

Ltac mia_cases :=
  unfold make_init_any, make_init_opt;
  match goal with |- context [evaluate (?p, ?s)] =>
    let E := fresh "E" in destruct (evaluate (p, s)) as [[?|] ?] eqn:E end;
  [|destruct (classical_dec _)].

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_ffi" *)
Theorem make_init_any_ffi : forall gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  ffi (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s) = ffi s.
Proof.
  intros. unfold make_init_any, make_init_opt.
  destruct (evaluate (stack_remove.init_code gen_gc max_heap k, s)) as [[r|] t] eqn:E; [reflexivity|].
  destruct (classical_dec _); [|reflexivity].
  unfold init_reduce. cbv zeta. cbn [ffi].
  pose proof (evaluate_init_code_ffi gen_gc max_heap k s NONE t (ffi s) E) as E2.
  rewrite set_ffi_same, E in E2. injection E2 as E2. rewrite E2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_bitmaps" *)
Theorem make_init_any_bitmaps : forall gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  bitmaps (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s) =
  if IS_SOME (make_init_opt gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s) then bitmaps0
  else [n2w 4].
Proof. intros. mia_cases; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_use_stack" *)
Theorem make_init_any_use_stack : forall gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  use_stack (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s).
Proof. intros. mia_cases; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_use_store" *)
Theorem make_init_any_use_store : forall gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  use_store (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s).
Proof. intros. mia_cases; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_use_alloc" *)
Theorem make_init_any_use_alloc : forall gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  ~ use_alloc (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s).
Proof. intros. mia_cases; discriminate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_code" *)
Theorem make_init_any_code : forall gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  code (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s) = code0.
Proof. intros. mia_cases; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_stack_limit" *)
Theorem make_init_any_stack_limit : forall gen_gc max_heap (bitmaps0 : list (word a)) data_sp coracle jump off k code0
    (s : state a c ffi_t),
  LENGTH (stack (make_init_any gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s)) *
    (dimindex a DIV 8) < dimword a.
Proof.
  intros. mia_cases.
  - cbn [stack]. change (LENGTH [Word (n2w 0 : word a)]) with 1. rewrite dimword_pow.
    pose proof (DIMINDEX_GT_0 a). assert (dimindex a < 2 ** dimindex a) by (apply N.pow_gt_lin_r; lia).
    pose proof (N.Div0.div_le_upper_bound (dimindex a) 8 (dimindex a) ltac:(lia)). lia.
  - match goal with Hp : init_prop _ _ _ _ _ |- _ => destruct Hp as (? & ? & ? & ? & Hp) end.
    destruct_ands. assumption.
  - cbn [stack]. change (LENGTH [Word (n2w 0 : word a)]) with 1. rewrite dimword_pow.
    pose proof (DIMINDEX_GT_0 a). assert (dimindex a < 2 ** dimindex a) by (apply N.pow_gt_lin_r; lia).
    pose proof (N.Div0.div_le_upper_bound (dimindex a) 8 (dimindex a) ltac:(lia)). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_any_compile_oracle" *)
Theorem make_init_any_compile_oracle : forall ggc max_heap bitmaps0 data_sp coracle jump off k code0 (s : state a c ffi_t),
  compile_oracle (make_init_any ggc max_heap bitmaps0 data_sp coracle jump off k code0 s) = coracle.
Proof. intros. mia_cases; reflexivity. Qed.

End MakeInitAny.


Section Exec.
Context {a : N} {c ffi_t : Type}.
Implicit Types X : state a c ffi_t.

Lemma word_sh_lsr_small (w : word a) v : v < dimindex a -> wordLang.word_sh ast.Lsr w (w2n (n2w v : word a)) = Some (w >>> v)%w.
Proof.
  intros H. rewrite w2n_n2w, N.mod_small by (rewrite dimword_pow; apply N.lt_trans with (dimindex a); [exact H|apply N.pow_gt_lin_r; lia]).
  unfold wordLang.word_sh. replace (dimindex a <=? v) with false by (symmetry; apply N.leb_gt; exact H).
  rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma word_sh_lsl_small (w : word a) v : v < dimindex a -> wordLang.word_sh ast.Lsl w (w2n (n2w v : word a)) = Some (w << v)%w.
Proof.
  intros H. rewrite w2n_n2w, N.mod_small by (rewrite dimword_pow; apply N.lt_trans with (dimindex a); [exact H|apply N.pow_gt_lin_r; lia]).
  unfold wordLang.word_sh. replace (dimindex a <=? v) with false by (symmetry; apply N.leb_gt; exact H).
  rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma set_var_same_val r v X : FLOOKUP (regs X) r = SOME v -> set_var r v X = X.
Proof.
  intros H. apply state_ext_fw; stk_fields; try reflexivity.
  apply fmap_ext; intros key. rewrite FLOOKUP_UPDATE. destruct (decide (r = key)) as [<-|]; [|reflexivity].
  symmetry; exact H.
Qed.

Lemma ev_if_lower r1 r2 (x y : word a) (c1 c2 : prog a) X :
  FLOOKUP (regs X) r1 = SOME (Word x) -> FLOOKUP (regs X) r2 = SOME (Word y) ->
  evaluate (If Lower r1 (Reg r2) c1 c2, X) = if (x <+ y)%w then evaluate (c1, X) else evaluate (c2, X).
Proof.
  intros H1 H2. rewrite ev_if. unfold get_var. cbn [get_var_imm]. unfold get_var. rewrite H1, H2.
  cbn [wordSem.word_cmp]. destruct ((x <+ y)%w); reflexivity.
Qed.

Lemma ev_seq_eq_none (p1 p2 : prog a) X Y : evaluate (p1, X) = (NONE, Y) -> evaluate (Seq p1 p2, X) = evaluate (p2, Y).
Proof. apply ev_seq_none. Qed.

End Exec.

Ltac flook :=
  repeat first [ rewrite FLOOKUP_set_var_same | rewrite FLOOKUP_set_var_other by lia ];
  first [ reflexivity | eassumption ].

Ltac sh_small := first [ apply word_sh_lsr_small | apply word_sh_lsl_small ]; lia.

Ltac inst_solve :=
  match goal with
  | |- inst (asm.Const _ _) _ = _ => eapply inst_const
  | |- inst (Arith (Binop asm.Or _ _ (Reg _))) _ = _ => eapply inst_move; flook
  | |- inst (Arith (Binop asm.Sub _ _ (Reg _))) _ = _ => eapply inst_sub_reg; flook
  | |- inst (Arith (Binop asm.Add _ _ (Reg _))) _ = _ => eapply inst_add_reg; flook
  | |- inst (Arith (Binop asm.Add _ _ (Imm _))) _ = _ => eapply inst_add_imm; flook
  | |- inst (Arith (Shift _ _ _ (Imm _))) _ = _ => eapply inst_shift_imm; [flook|sh_small]
  end.

Ltac step1 :=
  match goal with
  | |- evaluate (Seq (Inst _) _, _) = _ => etransitivity; [apply ev_seq_none, ev_inst_some; inst_solve|]
  | |- evaluate (Inst _, _) = _ => etransitivity; [apply ev_inst_some; inst_solve|]
  end.

Section ChunkA.
Context {a : N} {c ffi_t : Type}.
Implicit Types X : state a c ffi_t.
Local Open Scope word_scope.

Lemma chunkA X rest (w2 w3 w4 : word a) :
  good_dimindex a ->
  FLOOKUP (regs X) 2 = SOME (Word w2) -> FLOOKUP (regs X) 3 = SOME (Word w3) ->
  FLOOKUP (regs X) 4 = SOME (Word w4) ->
  let middle := (w4 - w2) >>> (1 + word_shift a)%N << word_shift a + w2 in
  let adj2 := w2 + n2w stack_remove.max_stack_alloc * bytes_in_word in
  let adj4 := w4 - n2w stack_remove.max_stack_alloc * bytes_in_word in
  let adj3 := if w3 <+ adj2 then middle else if adj4 <+ w3 then middle else w3 in
  evaluate (Seq (stackLang.move 0 4) (Seq (stackLang.sub_inst 0 2) (Seq (stackLang.right_shift_inst 0 (1 + word_shift a))
    (Seq (stackLang.left_shift_inst 0 (word_shift a)) (Seq (stackLang.add_inst 0 2)
    (Seq (stackLang.const_inst 5 (n2w stack_remove.max_stack_alloc * bytes_in_word))
    (Seq (stackLang.add_inst 2 5) (Seq (stackLang.sub_inst 4 5)
    (Seq (If Lower 3 (Reg 2) (stackLang.move 3 0) (If Lower 4 (Reg 3) (stackLang.move 3 0) Skip)) rest)))))))), X) =
  evaluate (rest, set_regs (((((regs X |+ (0%N, Word middle)) |+ (5%N, Word (n2w stack_remove.max_stack_alloc * bytes_in_word)))
                                |+ (2%N, Word adj2)) |+ (4%N, Word adj4)) |+ (3%N, Word adj3)) X).
Proof.
  intros Hg H2 H3 H4 middle adj2 adj4 adj3.
  pose proof (word_shift_lt Hg) as [_ Hws].
  assert (Hws1 : (1 + word_shift a < dimindex a)%N) by (unfold word_shift in *; destruct Hg as [E|E]; rewrite E in *; cbn in *; lia).
  do 8 step1.
  match goal with |- evaluate (Seq ?ifp rest, ?X8) = _ =>
    assert (EI : evaluate (ifp, X8) = (NONE, set_var 3 (Word adj3) X8));
    [|rewrite (ev_seq_eq_none _ _ _ _ EI)] end.
  { rewrite (ev_if_lower 3 2 w3 adj2) by flook. subst adj3. destruct (w3 <+ adj2) eqn:E1.
    - apply ev_inst_some. eapply inst_move. flook.
    - rewrite (ev_if_lower 4 3 adj4 w3) by flook. destruct (adj4 <+ w3) eqn:E2.
      + apply ev_inst_some. eapply inst_move. flook.
      + rewrite ev_skip. f_equal. symmetry. apply set_var_same_val. flook. }
  apply (f_equal (fun Y => evaluate (rest, Y))). apply state_ext_fw; stk_fields; try reflexivity. fmap_solve.
Qed.

End ChunkA.

Section ChunkB.
Context {a : N} {c ffi_t : Type}.
Implicit Types X : state a c ffi_t.
Local Open Scope word_scope.

Lemma chunkB X rest (a2 a3 a4 m mhw : word a) :
  FLOOKUP (regs X) 2 = SOME (Word a2) -> FLOOKUP (regs X) 3 = SOME (Word a3) ->
  FLOOKUP (regs X) 4 = SOME (Word a4) ->
  let w2' := a2 - m in
  let x0 := a3 - w2' in
  let r3' := if mhw <+ x0 then w2' + mhw else a3 in
  evaluate (Seq (stackLang.const_inst 0 m) (Seq (stackLang.sub_inst 2 0) (Seq (stackLang.add_inst 4 0)
    (Seq (stackLang.move 0 3) (Seq (stackLang.sub_inst 0 2) (Seq (stackLang.const_inst 5 mhw)
    (Seq (If Lower 5 (Reg 0) (Seq (stackLang.move 3 2) (stackLang.add_inst 3 5)) Skip) rest)))))), X) =
  evaluate (rest, set_regs (((((regs X |+ (0%N, Word x0)) |+ (2%N, Word w2')) |+ (4%N, Word (a4 + m)))
                               |+ (5%N, Word mhw)) |+ (3%N, Word r3')) X).
Proof.
  intros H2 H3 H4 w2' x0 r3'.
  do 6 step1.
  match goal with |- evaluate (Seq ?ifp rest, ?X8) = _ =>
    assert (EI : evaluate (ifp, X8) = (NONE, set_var 3 (Word r3') X8));
    [ rewrite (ev_if_lower 5 0 mhw x0) by flook; subst r3'; destruct (mhw <+ x0) eqn:E1;
      [ assert (F2 : FLOOKUP (regs X8) 2 = SOME (Word w2')) by flook;
        rewrite (ev_seq_none _ _ X8 (set_var 3 (Word w2') X8)) by (apply ev_inst_some, inst_move, F2);
        assert (F3 : FLOOKUP (regs (set_var 3 (Word w2') X8)) 3 = SOME (Word w2')) by flook;
        assert (F5 : FLOOKUP (regs (set_var 3 (Word w2') X8)) 5 = SOME (Word mhw)) by flook;
        rewrite (ev_inst_some _ _ _ (inst_add_reg 3 3 5 w2' mhw _ F3 F5));
        rewrite set_var_twice; reflexivity
      | rewrite ev_skip; f_equal; symmetry; apply set_var_same_val; flook ]
    | rewrite (ev_seq_eq_none _ _ _ _ EI) ] end.
  apply (f_equal (fun Y => evaluate (rest, Y))). apply state_ext_fw; stk_fields; try reflexivity. fmap_solve.
Qed.

End ChunkB.

Section ChunkC.
Context {a : N} {c ffi_t : Type}.
Implicit Types X : state a c ffi_t.
Local Open Scope word_scope.

Lemma chunkC X rest k (b2 b3 b4 : word a) :
  good_dimindex a -> (8 <= k)%N ->
  FLOOKUP (regs X) 2 = SOME (Word b2) -> FLOOKUP (regs X) 3 = SOME (Word b3) ->
  FLOOKUP (regs X) 4 = SOME (Word b4) ->
  let R3 := (b3 - b2) >>> (word_shift a + 1)%N << (word_shift a + 1)%N + b2 in
  let half := (R3 - b2) >>> 1 in
  evaluate (Seq (stackLang.sub_inst 3 2) (Seq (stackLang.right_shift_inst 3 (word_shift a + 1))
    (Seq (stackLang.left_shift_inst 3 (word_shift a + 1)) (Seq (stackLang.add_inst 3 2)
    (Seq (stackLang.move 5 3) (Seq (stackLang.sub_inst 5 2) (Seq (stackLang.right_shift_inst 5 1)
    (Seq (stackLang.move (k + 2) 2) (Seq (stackLang.add_inst 2 5) (Seq (stackLang.move k 4)
    (Seq (stackLang.move (k + 1) 3) rest)))))))))), X) =
  evaluate (rest, set_regs ((((((regs X |+ (3%N, Word R3)) |+ (5%N, Word half)) |+ ((k + 2)%N, Word b2))
                               |+ (2%N, Word (b2 + half))) |+ (k, Word b4)) |+ ((k + 1)%N, Word R3)) X).
Proof.
  intros Hg Hk H2 H3 H4 R3 half.
  pose proof (word_shift_lt Hg) as [_ Hws].
  assert (Hws1 : (word_shift a + 1 < dimindex a)%N) by (unfold word_shift in *; destruct Hg as [E|E]; rewrite E in *; cbn in *; lia).
  assert (H1d : (1 < dimindex a)%N) by lia.
  do 11 step1.
  apply (f_equal (fun Y => evaluate (rest, Y))). apply state_ext_fw; stk_fields; try reflexivity. fmap_solve.
Qed.

End ChunkC.

Section ChunkD.
Context {a : N} {c ffi_t : Type}.
Implicit Types X : state a c ffi_t.
Local Open Scope word_scope.

Lemma chunkD X rest k (p2 bmp v4 v6 v7 v1 : word a) :
  good_dimindex a -> (8 <= k)%N ->
  FLOOKUP (regs X) (k + 2)%N = SOME (Word p2) ->
  stackSem.memory X p2 = Word bmp -> p2 IN mdomain X ->
  stackSem.memory X (p2 + bytes_in_word) = Word v4 -> (p2 + bytes_in_word) IN mdomain X ->
  stackSem.memory X (p2 + bytes_in_word + bytes_in_word) = Word v6 ->
  (p2 + bytes_in_word + bytes_in_word) IN mdomain X ->
  stackSem.memory X (p2 + bytes_in_word + bytes_in_word + bytes_in_word) = Word v7 ->
  (p2 + bytes_in_word + bytes_in_word + bytes_in_word) IN mdomain X ->
  stackSem.memory X (p2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word) = Word v1 ->
  (p2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word) IN mdomain X ->
  evaluate (Seq (stackLang.load_inst 3 (k + 2)) (Seq (stackLang.right_shift_inst 3 (word_shift a))
    (Seq (stackLang.move 0 (k + 2)) (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 4 0)
    (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 6 0)
    (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 7 0)
    (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 1 0) rest)))))))))), X) =
  evaluate (rest, set_regs ((((((regs X |+ (3%N, Word (bmp >>> word_shift a)))
                                 |+ (0%N, Word (p2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word)))
                                |+ (4%N, Word v4)) |+ (6%N, Word v6)) |+ (7%N, Word v7)) |+ (1%N, Word v1)) X).
Proof.
  intros Hg Hk H2 M0 D0 M1 D1 M2 D2 M3 D3 M4 D4.
  pose proof (word_shift_lt Hg) as [_ Hws].
  etransitivity; [apply ev_seq_none, ev_inst_some; eapply inst_load0; [flook|apply mem_load_of; [exact M0|exact D0]]|].
  do 3 step1.
  etransitivity; [apply ev_seq_none, ev_inst_some; eapply inst_load0; [flook|apply mem_load_of; [exact M1|exact D1]]|].
  step1.
  etransitivity; [apply ev_seq_none, ev_inst_some; eapply inst_load0; [flook|apply mem_load_of; [exact M2|exact D2]]|].
  step1.
  etransitivity; [apply ev_seq_none, ev_inst_some; eapply inst_load0; [flook|apply mem_load_of; [exact M3|exact D3]]|].
  step1.
  etransitivity; [apply ev_seq_none, ev_inst_some; eapply inst_load0; [flook|apply mem_load_of; [exact M4|exact D4]]|].
  apply (f_equal (fun Y => evaluate (rest, Y))). apply state_ext_fw; stk_fields; try reflexivity. fmap_solve.
Qed.

End ChunkD.



Section Arith.
Context {a : N}.
Local Open Scope word_scope.

Lemma w2n_n2w_lt x : (x < dimword a)%N -> w2n (n2w x : word a) = x.
Proof. intros H; rewrite w2n_n2w; apply N.mod_small, H. Qed.

Lemma pow_ws (Hg : good_dimindex a) : (2 ^ word_shift a = dimindex a DIV 8)%N.
Proof. unfold word_shift. destruct Hg as [E|E]; rewrite E; reflexivity. Qed.

Lemma lsr_n2w (x m : N) : (x < dimword a)%N -> ((n2w x : word a) >>> m) = n2w (x / 2 ^ m).
Proof. intros H. rewrite word_lsr_n2w_div, w2n_n2w_lt by exact H. reflexivity. Qed.

Lemma lsl_n2w (x m : N) : (m < dimindex a)%N -> ((n2w x : word a) << m) = n2w (x * 2 ^ m).
Proof. intros H. rewrite word_lsl_n2w. replace (dimindex a - 1 <? m)%N with false by (symmetry; apply N.ltb_ge; lia). reflexivity. Qed.

Lemma n2w_add_N (x y : N) : (n2w x : word a) + n2w y = n2w (x + y).
Proof. apply word_add_n2w. Qed.

Lemma n2w_sub_N (x y : N) : (y <= x)%N -> (n2w x : word a) - n2w y = n2w (x - y).
Proof. intros H. word_Z. rewrite N2Z.inj_sub by exact H. apply zcong_eq; ring. Qed.

Lemma byte_aligned_mod (w : word a) (Hg : good_dimindex a) :
  byte_aligned w -> (w2n w mod (dimindex a DIV 8) = 0)%N.
Proof.
  intros H. unfold byte_aligned in H. apply aligned_w2n in H.
  destruct Hg as [E|E]; rewrite E in *; exact H.
Qed.

End Arith.

Section Arith2.
Context {a : N}.
Local Open Scope word_scope.

Lemma dimword_ge (Hg : good_dimindex a) : (2 ^ 32 <= dimword a)%N.
Proof. rewrite dimword_pow. destruct Hg as [E|E]; rewrite E; [lia|]. apply N.pow_le_mono_r; lia. Qed.

Lemma init_arith (w2 w3 w4 : word a) max_heap :
  good_dimindex a -> byte_aligned w2 -> byte_aligned w4 -> w2 <=+ w4 ->
  n2w 1024 * bytes_in_word <=+ w4 - w2 -> (stack_remove.max_stack_alloc <= max_heap)%N ->
  let d := (dimindex a DIV 8)%N in
  let middle := (w4 - w2) >>> (1 + word_shift a)%N << word_shift a + w2 in
  let adj2 := w2 + n2w stack_remove.max_stack_alloc * bytes_in_word in
  let adj4 := w4 - n2w stack_remove.max_stack_alloc * bytes_in_word in
  let adj3 := if w3 <+ adj2 then middle else if adj4 <+ w3 then middle else w3 in
  let w2' := adj2 - n2w stack_remove.max_stack_alloc * bytes_in_word in
  let x0 := adj3 - w2' in
  let mhw := if (max_heap * w2n (bytes_in_word : word a) <? dimword a)%N
             then n2w max_heap * bytes_in_word else n2w 0 - n2w 1 in
  let r3' := if mhw <+ x0 then w2' + mhw else adj3 in
  let R3 := (r3' - w2') >>> (word_shift a + 1)%N << (word_shift a + 1)%N + w2' in
  let half := (R3 - w2') >>> 1 in
  exists hl rest,
    w2' = w2 /\
    R3 = n2w (w2n w2 + 2 * hl * d) /\ half = n2w (hl * d) /\
    (w2n w2 + (2 * hl + 48 + rest) * d = w2n w4)%N /\ (207 <= rest)%N /\ (127 <= hl)%N /\
    (2 * hl <= max_heap)%N /\
    get_stack_heap_limit max_heap (w2, (w3, w4)) = (rest, hl).
Proof.
  intros Hg Ha2 Ha4 Hle HL Hmh d middle adj2 adj4 adj3 w2' x0 mhw r3' R3 half.
  pose proof (byte_aligned_mod _ Hg Ha2) as HP2. pose proof (byte_aligned_mod _ Hg Ha4) as HP4.
  pose proof (dimword_ge Hg) as HD. pose proof (pow_ws Hg) as Hpw.
  assert (Hdv : d = 4 \/ d = 8) by (subst d; destruct Hg as [E|E]; rewrite E; [left|right]; reflexivity).
  assert (Hbw : (bytes_in_word : word a) = n2w d) by reflexivity.
  assert (Hd0 : d <> 0%N) by (clear - Hdv; lia).
  assert (Hws : (word_shift a + 1 < dimindex a)%N) by (unfold word_shift; destruct Hg as [E|E]; rewrite E; cbn; lia).
  set (P2 := w2n w2) in *. set (P3 := w2n w3) in *. set (P4 := w2n w4) in *.
  assert (HP2l : (P2 < dimword a)%N) by apply w2n_lt. assert (HP3l : (P3 < dimword a)%N) by apply w2n_lt.
  assert (HP4l : (P4 < dimword a)%N) by apply w2n_lt.
  assert (E2 : w2 = n2w P2) by (symmetry; apply n2w_w2n). assert (E3 : w3 = n2w P3) by (symmetry; apply n2w_w2n).
  assert (E4 : w4 = n2w P4) by (symmetry; apply n2w_w2n).
  apply WORD_LS in Hle. fold P2 P4 in Hle.
  assert (Hsub : w4 - w2 = n2w (P4 - P2)) by (rewrite E2, E4 at 1; apply n2w_sub_N; lia).
  apply WORD_LS in HL. rewrite Hsub, w2n_n2w_lt in HL by lia.
  rewrite Hbw, word_mul_n2w, w2n_n2w_lt in HL by (destruct Hdv as [-> | ->]; lia).
  set (L := (P4 - P2)%N) in *. assert (HLd : L = (P4 - P2)%N) by reflexivity. clearbody L.
  (* middle *)
  assert (Emid : middle = n2w (L / (2 * d) * d + P2)).
  { subst middle. rewrite Hsub, lsr_n2w by lia. rewrite lsl_n2w by (unfold word_shift; destruct Hg as [E|E]; rewrite E; cbn; lia).
    rewrite Hpw, E2, n2w_add_N. replace (2 ^ (1 + word_shift a))%N with (2 * d)%N; [reflexivity|].
    rewrite N.pow_add_r, Hpw. reflexivity. }
  remember (L / (2 * d) * d + P2)%N as Mid eqn:HMideq.
  assert (HMid : (P2 + 255 * d <= Mid <= P4 - 255 * d)%N).
  { subst Mid. assert (H2d : (2 * d <> 0)%N) by lia.
    pose proof (N.div_mod L (2 * d) H2d) as Hdm. pose proof (N.mod_lt L (2 * d) H2d) as Hml.
    set (q := (L / (2 * d))%N) in *. set (r := (L mod (2 * d))%N) in *. clearbody q r.
    destruct Hdv as [Ed|Ed]; rewrite Ed in *; lia. }
  clear HMideq.
  assert (Emid' : w2 + (- n2w 1 * w2 + w4) >>> (word_shift a + 1) << word_shift a = n2w Mid).
  { rewrite <- Emid. subst middle. replace (- n2w 1 * w2 + w4) with (w4 - w2) by wring.
    rewrite (N.add_comm (word_shift a) 1). wring. }
  assert (Eadj2 : adj2 = n2w (P2 + 255 * d)) by (subst adj2; rewrite E2, Hbw, word_mul_n2w, n2w_add_N; try (f_equal; unfold stack_remove.max_stack_alloc; lia)).
  assert (Eadj4 : adj4 = n2w (P4 - 255 * d)).
  { subst adj4. rewrite E4, Hbw, word_mul_n2w, n2w_sub_N by (unfold stack_remove.max_stack_alloc; lia).
    try (f_equal; unfold stack_remove.max_stack_alloc; lia). }
  remember (if (P3 <? P2 + 255 * d)%N then Mid else if (P4 - 255 * d <? P3)%N then Mid else P3) as A3 eqn:HA3eq.
  assert (Eadj3 : adj3 = n2w A3).
  { subst adj3 A3. rewrite Eadj2, Eadj4.
    rewrite !word_lo_w2n, !w2n_n2w_lt by lia. change (w2n w3) with P3.
    destruct (P3 <? P2 + 255 * d)%N; [exact Emid|]. destruct (P4 - 255 * d <? P3)%N; [exact Emid|exact E3]. }
  assert (HA3 : (P2 + 255 * d <= A3 <= P4 - 255 * d)%N).
  { subst A3. destruct (N.ltb_spec P3 (P2 + 255 * d)); [exact HMid|]. destruct (N.ltb_spec (P4 - 255 * d) P3); [exact HMid|lia]. }
  assert (Eadj3' : (if andb (adj2 <=+ w3) (w3 <=+ adj4) then w3 else n2w Mid) = n2w A3).
  { rewrite <- Eadj3. subst adj3. rewrite Eadj2, Eadj4. rewrite !word_lo_w2n, !word_ls_w2n, !w2n_n2w_lt by lia.
    change (w2n w3) with P3. rewrite <- Emid.
    destruct (N.ltb_spec P3 (P2 + 255 * d)); [destruct (N.leb_spec (P2 + 255 * d) P3); [lia|reflexivity]|].
    destruct (N.leb_spec (P2 + 255 * d) P3); [|lia]. cbn [andb].
    destruct (N.ltb_spec (P4 - 255 * d) P3); destruct (N.leb_spec P3 (P4 - 255 * d)); try lia; reflexivity. }
  clear HA3eq.
  assert (Ew2' : w2' = w2) by (subst w2' adj2; wring).
  assert (Ex0 : x0 = n2w (A3 - P2)) by (subst x0; rewrite Ew2', Eadj3, E2 at 1; apply n2w_sub_N; lia).
  remember (if (max_heap * d <? dimword a)%N then (max_heap * d)%N else (dimword a - 1)%N) as MH eqn:HMHeq.
  assert (Emhw : mhw = n2w MH).
  { subst mhw MH. assert (Hw : w2n (bytes_in_word : word a) = d) by (rewrite Hbw; apply w2n_n2w_lt; destruct Hdv as [-> | ->]; lia).
    rewrite Hw. destruct (max_heap * d <? dimword a)%N; [rewrite Hbw, word_mul_n2w; reflexivity|].
    apply word_eq_w2n. rewrite w2n_sub, !w2n_n2w, N.Div0.mod_0_l, (N.mod_small 1) by lia.
    rewrite N.add_0_l. reflexivity. }
  assert (HMH : (255 * d <= MH < dimword a)%N).
  { subst MH. destruct (N.ltb_spec (max_heap * d) (dimword a)).
    - unfold stack_remove.max_stack_alloc in Hmh. split; [|assumption]. apply N.mul_le_mono_r. exact Hmh.
    - destruct Hdv as [-> | ->]; lia. }
  assert (Hw : w2n (bytes_in_word : word a) = d) by (rewrite Hbw; apply w2n_n2w_lt; destruct Hdv as [-> | ->]; lia).
  assert (Emhw' : (if (max_heap * w2n (bytes_in_word : word a) <? dimword a)%N
                   then bytes_in_word * n2w max_heap else - n2w 1) = (n2w MH : word a)).
  { rewrite <- Emhw. subst mhw. destruct (max_heap * w2n (bytes_in_word : word a) <? dimword a)%N; wring. }
  assert (HMHle : (max_heap * d < dimword a -> MH = max_heap * d)%N)
    by (intros Hlt; subst MH; apply N.ltb_lt in Hlt; rewrite Hlt; reflexivity).
  assert (HMHge : (dimword a <= max_heap * d -> MH = dimword a - 1)%N)
    by (intros Hge; subst MH; apply N.ltb_ge in Hge; rewrite Hge; reflexivity).
  clear HMHeq.
  remember (if (MH <? A3 - P2)%N then MH else (A3 - P2)%N) as Y eqn:HYeq.
  assert (Er3 : r3' - w2' = n2w Y).
  { subst r3'. rewrite Emhw, Ex0, word_lo_w2n, !w2n_n2w_lt by lia. rewrite Ew2'.
    subst Y. destruct (MH <? A3 - P2)%N.
    - wring.
    - rewrite Eadj3, E2. apply n2w_sub_N. lia. }
  assert (EY : (- n2w 1 * n2w P2 + (if (n2w MH : word a) <+ - n2w 1 * n2w P2 + n2w A3 then n2w MH + n2w P2 else n2w A3)
                : word a) = (n2w Y : word a)).
  { replace (- n2w 1 * n2w P2 + n2w A3 : word a) with (n2w (A3 - P2) : word a)
      by (rewrite <- n2w_sub_N by lia; wring).
    rewrite word_lo_w2n, !w2n_n2w_lt by lia. subst Y. destruct (MH <? A3 - P2)%N.
    - wring.
    - rewrite <- n2w_sub_N by lia. wring. }
  assert (HY : (255 * d <= Y <= L - 255 * d /\ Y <= MH)%N)
    by (subst Y; destruct (N.ltb_spec MH (A3 - P2)); lia).
  clear HYeq.
  assert (H2d : (2 * d <> 0)%N) by lia.
  remember (Y / (2 * d))%N as hl eqn:Hhleq.
  assert (HYdm : (Y = 2 * d * hl + Y mod (2 * d))%N) by (subst hl; apply N.div_mod; exact H2d).
  pose proof (N.mod_lt Y (2 * d) H2d) as HYml.
  remember (Y mod (2 * d))%N as ry eqn:Hryeq. clear Hryeq Hhleq.
  assert (H2hl : (2 * hl * d <= Y)%N) by (clear - HYdm; nia).
  assert (HYD : (Y < dimword a)%N) by (clear - HY HLd HP4l Hle; lia).
  assert (Hq : (Y / (d * 2) = hl)%N).
  { rewrite HYdm. replace (2 * d * hl + ry)%N with (hl * (d * 2) + ry)%N by ring.
    rewrite N.div_add_l by (clear - Hd0; lia). rewrite (N.div_small ry) by (clear - HYml; lia). ring. }
  assert (ER3 : R3 = n2w (P2 + 2 * hl * d)).
  { subst R3. rewrite Er3, lsr_n2w by exact HYD. rewrite lsl_n2w by exact Hws. rewrite Ew2', E2 at 1.
    rewrite N.pow_add_r, Hpw. change (2 ^ 1)%N with 2%N.
    replace (dimindex a DIV 8)%N with d by reflexivity. rewrite Hq, n2w_add_N. f_equal. ring. }
  assert (Ehalf : half = n2w (hl * d)).
  { subst half. rewrite ER3, Ew2', E2 at 1. rewrite n2w_sub_N by (clear; lia).
    replace (P2 + 2 * hl * d - P2)%N with (hl * d * 2)%N by (clear; lia).
    rewrite lsr_n2w by (clear - H2hl HYD; lia).
    f_equal. change (2 ^ 1)%N with 2%N. apply N.div_mul. clear; lia. }
  (* the alignment of [L] *)
  assert (HLd' : (L mod d = 0)%N).
  { subst L. apply N.Div0.mod_divides in HP2 as [q2 Hq2]. apply N.Div0.mod_divides in HP4 as [q4 Hq4].
    rewrite Hq2, Hq4, <- N.mul_sub_distr_l. rewrite N.mul_comm. apply N.Div0.mod_mul. }
  assert (HLdiv : (L = d * (L / d))%N).
  { pose proof (N.div_mod L d Hd0) as Hdm. rewrite HLd', N.add_0_r in Hdm. exact Hdm. }
  remember (L / d)%N as Ld eqn:HLdeq. clear HLdeq.
  assert (Eg : get_stack_heap_limit max_heap (w2, (w3, w4)) = (Ld - 2 * hl - 48, hl)%N).
  { unfold get_stack_heap_limit, get_stack_heap_limit', get_stack_heap_limit''.
    rewrite Emid'.
    replace (w2 + bytes_in_word * n2w stack_remove.max_stack_alloc) with adj2 by (subst adj2; wring).
    replace (w4 - bytes_in_word * n2w stack_remove.max_stack_alloc) with adj4 by (subst adj4; wring).
    rewrite Eadj3', (w2n_n2w_lt A3) by (clear - HA3 HP4l; lia).
    rewrite Emhw'. change (w2n w2) with P2. rewrite EY.
    assert (Er : (n2w P2 + n2w Y >>> (word_shift a + 1) << (word_shift a + 1) : word a) = R3).
    { rewrite <- E2. subst R3. rewrite <- Er3, Ew2'. apply WORD_ADD_COMM. }
    rewrite Er, ER3, (w2n_n2w_lt (P2 + 2 * hl * d)) by (clear - H2hl HY HLd HP4l Hle; lia).
    change (w2n w4) with P4.
    apply N.Div0.mod_divides in HP2 as [q2 Hq2]. rewrite Hq2.
    change (dimindex a DIV 8)%N with d. change (LENGTH stack_remove.store_list) with 48%N.
    replace (P4 / d)%N with (q2 + Ld)%N.
    - replace ((d * q2 + 2 * hl * d) / d)%N with (q2 + 2 * hl)%N.
      + rewrite (N.mul_comm d q2), N.div_mul by exact Hd0. f_equal; [clear; lia|].
        replace (q2 + 2 * hl - q2)%N with (hl * 2)%N by (clear; lia).
        apply N.div_mul. clear; lia.
      + replace (d * q2 + 2 * hl * d)%N with ((q2 + 2 * hl) * d)%N by (clear; lia).
        rewrite N.div_mul by exact Hd0. reflexivity.
    - replace P4 with ((q2 + Ld) * d)%N by (clear - HLdiv HLd Hle Hq2; nia). rewrite N.div_mul by exact Hd0. reflexivity. }
  exists hl, (Ld - 2 * hl - 48)%N.
  split; [exact Ew2'|]. split; [exact ER3|]. split; [exact Ehalf|].
  assert (Hrest : (2 * hl + 255 <= Ld)%N).
  { clear - HLdiv HY H2hl Hdv. destruct Hdv as [Ed|Ed]; rewrite Ed in *; lia. }
  assert (Hhl : (127 <= hl)%N) by (clear - HY HYdm HYml Hdv; destruct Hdv as [Ed|Ed]; rewrite Ed in *; lia).
  split.
  { clear - HLdiv HLd Hrest Hle Hdv. destruct Hdv as [Ed|Ed]; rewrite Ed in *; lia. }
  split; [clear - Hrest; lia|]. split; [exact Hhl|].
  split; [|exact Eg].
  destruct (N.ltb_spec (max_heap * d) (dimword a)) as [Hlt|Hge].
  - rewrite (HMHle Hlt) in HY. clear - HY HYdm HYml Hdv.
    destruct Hdv as [Ed|Ed]; rewrite Ed in *; lia.
  - rewrite (HMHge Hge) in HY. clear - HY HYdm HYml Hdv Hge HD.
    destruct Hdv as [Ed|Ed]; rewrite Ed in *; lia.
Qed.

End Arith2.



Section InitCode.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

Lemma init_code_unfold gen_gc max_heap k :
  @stack_remove.init_code a gen_gc max_heap k =
  Seq (stackLang.move 0 4) (Seq (stackLang.sub_inst 0 2) (Seq (stackLang.right_shift_inst 0 (1 + word_shift a))
    (Seq (stackLang.left_shift_inst 0 (word_shift a)) (Seq (stackLang.add_inst 0 2)
    (Seq (stackLang.const_inst 5 (n2w stack_remove.max_stack_alloc * bytes_in_word))
    (Seq (stackLang.add_inst 2 5) (Seq (stackLang.sub_inst 4 5)
    (Seq (If Lower 3 (Reg 2) (stackLang.move 3 0) (If Lower 4 (Reg 3) (stackLang.move 3 0) Skip))
  (Seq (stackLang.const_inst 0 (n2w stack_remove.max_stack_alloc * bytes_in_word)) (Seq (stackLang.sub_inst 2 0)
    (Seq (stackLang.add_inst 4 0) (Seq (stackLang.move 0 3) (Seq (stackLang.sub_inst 0 2)
    (Seq (stackLang.const_inst 5 (if (max_heap * w2n (bytes_in_word : word a) <? dimword a)%N
                                   then n2w max_heap * bytes_in_word else n2w 0 - n2w 1))
    (Seq (If Lower 5 (Reg 0) (Seq (stackLang.move 3 2) (stackLang.add_inst 3 5)) Skip)
  (Seq (stackLang.sub_inst 3 2) (Seq (stackLang.right_shift_inst 3 (word_shift a + 1))
    (Seq (stackLang.left_shift_inst 3 (word_shift a + 1)) (Seq (stackLang.add_inst 3 2)
    (Seq (stackLang.move 5 3) (Seq (stackLang.sub_inst 5 2) (Seq (stackLang.right_shift_inst 5 1)
    (Seq (stackLang.move (k + 2) 2) (Seq (stackLang.add_inst 2 5) (Seq (stackLang.move k 4)
    (Seq (stackLang.move (k + 1) 3)
  (Seq (stackLang.load_inst 3 (k + 2)) (Seq (stackLang.right_shift_inst 3 (word_shift a))
    (Seq (stackLang.move 0 (k + 2)) (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 4 0)
    (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 6 0)
    (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 7 0)
    (Seq (stackLang.add_bytes_in_word_inst 0) (Seq (stackLang.load_inst 1 0)
  (Seq (Seq (stackLang.const_inst 0 bytes_in_word) (Seq (stackLang.sub_inst k 0) (Seq (stackLang.const_inst 0 (n2w 0))
         (Seq (stackLang.store_inst 0 k)
           (stack_remove.store_list_code (k + 1) 0 (MAP (stack_remove.store_init gen_gc k) (REVERSE stack_remove.store_list)))))))
       (LocValue 0 1 0))))))))))))))))))))))))))))))))))))))).
Proof. reflexivity. Qed.

End InitCode.

Ltac flook2 :=
  rewrite ?FLOOKUP_UPDATE;
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try (exfalso; lia) end;
  first [ reflexivity | eassumption ].

Section InitCodeThm.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

Lemma set_regs_twice R R' (X : state a c ffi_t) : set_regs R (set_regs R' X) = set_regs R X.
Proof. reflexivity. Qed.
Lemma regs_set_regs R (X : state a c ffi_t) : regs (set_regs R X) = R.
Proof. reflexivity. Qed.
Lemma memory_set_regs R (X : state a c ffi_t) : stackSem.memory (set_regs R X) = stackSem.memory X.
Proof. reflexivity. Qed.
Lemma mdomain_set_regs R (X : state a c ffi_t) : mdomain (set_regs R X) = mdomain X.
Proof. reflexivity. Qed.

Lemma d_lt_dimword (Hg : good_dimindex a) : (dimindex a DIV 8 < dimword a)%N.
Proof. rewrite dimword_pow. destruct Hg as [E|E]; rewrite E; reflexivity. Qed.

Lemma init_code_prefix k (s : state a c ffi_t) max_heap (gen_gc : bool) ptr2 ptr3 ptr4 bmp v4 v6 v7 v1 :
  good_dimindex a -> (8 <= k)%N ->
  FLOOKUP (regs s) 2 = SOME (Word ptr2) -> FLOOKUP (regs s) 3 = SOME (Word ptr3) ->
  FLOOKUP (regs s) 4 = SOME (Word ptr4) ->
  stackSem.memory s ptr2 = Word bmp -> ptr2 IN mdomain s ->
  stackSem.memory s (ptr2 + bytes_in_word) = Word v4 -> (ptr2 + bytes_in_word) IN mdomain s ->
  stackSem.memory s (ptr2 + bytes_in_word + bytes_in_word) = Word v6 ->
  (ptr2 + bytes_in_word + bytes_in_word) IN mdomain s ->
  stackSem.memory s (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word) = Word v7 ->
  (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word) IN mdomain s ->
  stackSem.memory s (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word) = Word v1 ->
  (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word) IN mdomain s ->
  byte_aligned ptr2 -> byte_aligned ptr4 -> ptr2 <=+ ptr4 -> n2w 1024 * bytes_in_word <=+ ptr4 - ptr2 ->
  (stack_remove.max_stack_alloc <= max_heap)%N ->
  exists hl rest RD,
    evaluate (stack_remove.init_code gen_gc max_heap k, s) =
      evaluate (Seq (stack_remove.init_memory k (MAP (stack_remove.store_init gen_gc k) (REVERSE stack_remove.store_list)))
                    (LocValue 0 1 0), set_regs RD s) /\
    FLOOKUP RD 1 = SOME (Word v1) /\ FLOOKUP RD 2 = SOME (Word (ptr2 + n2w (hl * (dimindex a DIV 8))%N)) /\
    FLOOKUP RD 3 = SOME (Word (bmp >>> word_shift a)) /\ FLOOKUP RD 4 = SOME (Word v4) /\
    FLOOKUP RD 5 = SOME (Word (n2w (hl * (dimindex a DIV 8))%N)) /\ FLOOKUP RD 6 = SOME (Word v6) /\
    FLOOKUP RD 7 = SOME (Word v7) /\ FLOOKUP RD k = SOME (Word ptr4) /\
    FLOOKUP RD (k + 1)%N = SOME (Word (n2w (w2n ptr2 + 2 * hl * (dimindex a DIV 8))%N)) /\
    FLOOKUP RD (k + 2)%N = SOME (Word ptr2) /\
    (w2n ptr2 + (2 * hl + 48 + rest) * (dimindex a DIV 8) = w2n ptr4)%N /\ (207 <= rest)%N /\ (127 <= hl)%N /\
    (2 * hl <= max_heap)%N /\ get_stack_heap_limit max_heap (ptr2, (ptr3, ptr4)) = (rest, hl) /\
    (ptr2 + n2w stack_remove.max_stack_alloc * bytes_in_word <=+ ptr3 ->
     ptr3 <=+ ptr4 - n2w stack_remove.max_stack_alloc * bytes_in_word ->
     (w2n (- n2w 1 * ptr2 + ptr3) <= max_heap * w2n (bytes_in_word : word a))%N ->
     (w2n (bytes_in_word : word a) * max_heap < dimword a)%N ->
     n2w (w2n ptr2 + 2 * hl * (dimindex a DIV 8))%N =
       (ptr3 + - n2w 1 * ptr2) >>> (word_shift a + 1) << (word_shift a + 1) + ptr2).
Proof.
  intros Hg Hk8 R2 R3 R4 M0 D0 M1 D1 M2 D2 M3 D3 M4 D4 Ha2 Ha4 Hle HL Hmh.
  pose proof (init_arith ptr2 ptr3 ptr4 max_heap Hg Ha2 Ha4 Hle HL Hmh) as Harith. cbv zeta in Harith.
  destruct Harith as (hl & rest & Ew2' & ER3 & Ehalf & Hsz & Hrest & Hhl & Hmh2 & Eg).
  rewrite Ew2' in ER3, Ehalf.
  exists hl, rest. eexists. split.
  { rewrite init_code_unfold.
    rewrite (chunkA s _ ptr2 ptr3 ptr4 Hg R2 R3 R4).
    erewrite chunkB by (rewrite regs_set_regs; flook2).
    rewrite set_regs_twice, regs_set_regs.
    erewrite chunkC by (first [exact Hg|exact Hk8|rewrite regs_set_regs; flook2]).
    rewrite set_regs_twice, regs_set_regs.
    rewrite Ew2'.
    rewrite (chunkD _ _ k ptr2 bmp v4 v6 v7 v1 Hg Hk8) by (rewrite ?regs_set_regs, ?memory_set_regs, ?mdomain_set_regs; flook2).
    rewrite set_regs_twice, regs_set_regs.
    rewrite Ehalf, ER3. reflexivity. }
  split; [flook2|]. split; [flook2|]. split; [flook2|]. split; [flook2|]. split; [flook2|].
  split; [flook2|]. split; [flook2|].
  split; [rewrite ?FLOOKUP_UPDATE;
          repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try (exfalso; lia) end;
          do 2 f_equal; wring|].
  split; [flook2|]. split; [flook2|].
  do 4 (split; [assumption|]). split; [exact Eg|].
  intros C1 C2 C3 C4. rewrite <- ER3.
  assert (Hc1 : (ptr3 <+ ptr2 + n2w stack_remove.max_stack_alloc * bytes_in_word) = false).
  { destruct (ptr3 <+ _) eqn:E; [|reflexivity]. exfalso. exact (proj2 (WORD_NOT_LOWER _ _) C1 E). }
  assert (Hc2 : (ptr4 - n2w stack_remove.max_stack_alloc * bytes_in_word <+ ptr3) = false).
  { destruct (_ <+ ptr3) eqn:E; [|reflexivity]. exfalso. exact (proj2 (WORD_NOT_LOWER _ _) C2 E). }
  assert (Hc3 : (max_heap * w2n (bytes_in_word : word a) <? dimword a)%N = true)
    by (apply N.ltb_lt; rewrite N.mul_comm; exact C4).
  rewrite Hc1, Hc2, Hc3.
  assert (Hc4 : (n2w max_heap * bytes_in_word <+ ptr3 - ptr2) = false).
  { destruct (n2w max_heap * bytes_in_word <+ ptr3 - ptr2) eqn:E; [|reflexivity]. exfalso. apply WORD_LO in E.
    replace (ptr3 - ptr2) with (- n2w 1 * ptr2 + ptr3) in E by wring.
    rewrite (bw_d Hg), word_mul_n2w, w2n_n2w_lt in E.
    - rewrite (bw_d Hg), w2n_n2w_lt in C3 by exact (d_lt_dimword Hg).
      lia.
    - rewrite (bw_d Hg), w2n_n2w_lt in C4 by exact (d_lt_dimword Hg).
      lia. }
  rewrite Hc4. f_equal. f_equal. f_equal. wring.
Qed.


Lemma store_init_cases (gen_gc : bool) k n :
  (exists w, @stack_remove.store_init a gen_gc k n = inl w) \/
  (exists i, @stack_remove.store_init a gen_gc k n = inr i /\ ((1 <= i <= 7)%N \/ i = (k + 2)%N)).
Proof.
  unfold stack_remove.store_init, UPDATE_LIST.
  destruct n; cbn; try (left; eexists; reflexivity); right; eexists; (split; [reflexivity|]);
    try (destruct gen_gc); lia.
Qed.

Lemma In_store_init_inr (gen_gc : bool) k i :
  In (inr i) (MAP (@stack_remove.store_init a gen_gc k) (REVERSE stack_remove.store_list)) ->
  (1 <= i <= 7)%N \/ i = (k + 2)%N.
Proof.
  intros Hin. unfold MAP in Hin. apply in_map_iff in Hin as (n & En & _).
  destruct (store_init_cases gen_gc k n) as [(w & Ew)|(j & Ej & Hj)]; rewrite Ew in En || rewrite Ej in En;
    [discriminate|injection En as ->; exact Hj].
Qed.

Lemma LENGTH_store_list : LENGTH stack_remove.store_list = 48.
Proof. reflexivity. Qed.

Lemma init_memory_run k (gen_gc : bool) (X : state a c ffi_t) (w4 base : word a) v ys frame :
  (8 <= k)%N -> FLOOKUP (regs X) k = SOME (Word w4) -> FLOOKUP (regs X) (k + 1)%N = SOME (Word base) ->
  (forall i, (1 <= i <= 7)%N \/ i = (k + 2)%N -> i IN FDOM (regs X)) ->
  1 IN domain (code X) ->
  STAR (word_list base ys) (STAR (one (w4 - bytes_in_word, v)) frame) (fun2set (stackSem.memory X, mdomain X)) ->
  LENGTH ys = 48 ->
  exists RF m1,
    STAR (word_list base (MAP (mem_val (regs X)) (MAP (stack_remove.store_init gen_gc k) (REVERSE stack_remove.store_list))))
         (STAR (one (w4 - bytes_in_word, Word (n2w 0))) frame) (fun2set (m1, mdomain X)) /\
    evaluate (Seq (stack_remove.init_memory k (MAP (stack_remove.store_init gen_gc k) (REVERSE stack_remove.store_list)))
                  (LocValue 0 1 0), X) = (NONE, set_regs RF (set_memory m1 X)) /\
    FLOOKUP RF 0 = SOME (Loc 1 0) /\ FLOOKUP RF k = SOME (Word (w4 - bytes_in_word)) /\
    FLOOKUP RF (k + 1)%N = SOME (Word (base + bytes_in_word * n2w 48)) /\
    (forall i, i <> 0%N -> i <> k -> i <> (k + 1)%N -> FLOOKUP RF i = FLOOKUP (regs X) i).
Proof.
  intros Hk8 Rk Rk1 Hfd H1 Hm Hl.
  set (xs := MAP (stack_remove.store_init gen_gc k) (REVERSE stack_remove.store_list)).
  set (X1 := set_var k (Word (w4 - bytes_in_word)) (set_var 0 (Word bytes_in_word) X)).
  set (X2 := set_var 0 (Word (n2w 0)) X1).
  assert (Hd : (w4 - bytes_in_word) IN mdomain X).
  { rewrite STAR_swap_l in Hm. exact (proj2 (sep_read _ _ _ _ _ Hm)). }
  set (X3 := set_memory (((w4 - bytes_in_word) =+ Word (n2w 0)) (stackSem.memory X2)) X2).
  assert (F3 : FLOOKUP (regs X2) k = SOME (Word (w4 - bytes_in_word))) by (subst X2 X1; flook).
  assert (F4 : FLOOKUP (regs X2) 0 = SOME (Word (n2w 0))) by (subst X2; flook).
  assert (Hm3 : STAR (word_list base ys) (STAR (one (w4 - bytes_in_word, Word (n2w 0))) frame)
                  (fun2set (stackSem.memory X3, mdomain X3))).
  { rewrite STAR_swap_l in Hm |- *. exact (sep_write _ _ _ (Word (n2w 0)) _ _ Hm). }
  assert (HL : LENGTH ys = LENGTH xs) by (rewrite Hl; reflexivity).
  assert (Hne : (k + 1)%N <> 0%N) by lia.
  assert (Hga : get_var (k + 1) X3 = SOME (Word base)).
  { unfold get_var. subst X3 X2 X1. cbn [regs set_memory]. flook. }
  assert (Hft : 0 IN FDOM (regs X3)).
  { unfold FDOM, pred_set.IN. change (regs X3) with (regs X2). rewrite F4. discriminate. }
  assert (Hrx3 : regs X3 = ((regs X |+ (0%N, Word bytes_in_word)) |+ (k, Word (w4 - bytes_in_word))) |+ (0%N, Word (n2w 0)))
    by reflexivity.
  assert (Hev : EVERY (fun x => ⌜forall n, inr n = x -> n <> (k + 1)%N /\ n <> 0%N /\ n IN FDOM (regs X3)⌝) xs).
  { unfold is_true. rewrite EVERY_Forall, Forall_forall. intros z Hz. apply bool_decide_spec.
    intros n En. subst z. pose proof (In_store_init_inr gen_gc k n Hz) as Hn.
    split; [lia|split; [lia|]]. rewrite Hrx3. unfold FDOM, pred_set.IN. rewrite !FLOOKUP_UPDATE.
    destruct (decide (0%N = n)); [lia|]. destruct (decide (k = n)); [lia|]. exact (Hfd n Hn). }
  destruct (store_list_code_thm (k + 1) 0 xs X3 base _ ys _ _
              (conj Hm3 (conj eq_refl (conj eq_refl (conj HL (conj Hne (conj Hga (conj Hft Hev))))))))
    as (r1 & m1 & Hm1 & Ev).
  set (R4 := regs X3 |++ [((k + 1)%N, Word (base + bytes_in_word * n2w (LENGTH xs))); (0%N, r1)]).
  assert (Eim : evaluate (stack_remove.init_memory k xs, X) = (NONE, set_regs R4 (set_memory m1 X3))).
  { unfold stack_remove.init_memory. cbn [list_Seq].
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_const _ _ _))).
    assert (F1 : FLOOKUP (regs (set_var 0 (Word bytes_in_word) X)) k = SOME (Word w4)) by flook.
    assert (F2 : FLOOKUP (regs (set_var 0 (Word bytes_in_word) X)) 0 = SOME (Word bytes_in_word)) by flook.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_sub_reg k k 0 _ _ _ F1 F2))). fold X1.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_const _ _ _))). fold X2.
    rewrite (ev_seq_none _ _ _ _ (ev_inst_some _ _ _ (inst_store0 0 k _ _ _ F3 F4 Hd))). fold X3.
    exact Ev. }
  exists (R4 |+ (0%N, Loc 1 0)), m1. split.
  { rewrite Hrx3 in Hm1. rewrite !mem_val_upd_other in Hm1
      by (intros n Hn; pose proof (In_store_init_inr gen_gc k n Hn); lia). exact Hm1. }
  split.
  { rewrite (ev_seq_none _ _ _ _ Eim), ev_locvalue_eq.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|].
    exfalso. apply Hn. left. split; [reflexivity|exact H1]. }
  subst R4. cbn [FUPDATE_LIST FOLDL]. rewrite Hrx3.
  split; [rewrite !FLOOKUP_UPDATE; destruct (decide _); [reflexivity|congruence]|].
  split; [rewrite !FLOOKUP_UPDATE;
          repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try (exfalso; lia) end;
          reflexivity|].
  split; [rewrite !FLOOKUP_UPDATE;
          repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try (exfalso; lia) end;
          reflexivity|].
  intros i Hi0 Hik Hik1. rewrite !FLOOKUP_UPDATE.
  repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try (exfalso; lia) end;
  reflexivity.
Qed.


Lemma WLE_elim {B} `{Inhabited B} (ad : word a) n q (s : word a * B -> Prop) :
  STAR (word_list_exists ad n) q s -> exists xs : list B, LENGTH xs = n /\ STAR (word_list ad xs) q s.
Proof.
  intros Hs. apply STAR_alt in Hs as (u & Hu & Hp & Hq). unfold word_list_exists in Hp.
  apply SEP_EXISTS_THM in Hp as [xs Hxs]. apply (proj2 (cond_STAR _ _ _)) in Hxs as [Hl Hw].
  exists xs. split; [exact Hl|]. apply STAR_alt. exists u. auto.
Qed.

Lemma word_list_IN {B} (xs : list B) : forall (ad : word a) q m dm i,
  STAR (word_list ad xs) q (fun2set (m, dm)) -> (i < LENGTH xs)%N -> (ad + n2w i * bytes_in_word) IN dm.
Proof.
  induction xs as [|x xs IH]; intros ad q m dm i H Hi; [change (@LENGTH B []) with 0%N in Hi; lia|].
  cbn [word_list] in H. rewrite <- STAR_ASSOC in H.
  destruct (N.eq_dec i 0) as [->|Hi0].
  - replace (ad + n2w 0 * bytes_in_word) with ad by wring. exact (proj2 (sep_read _ _ _ _ _ H)).
  - rewrite STAR_swap_l in H. rewrite LENGTH_cons_N in Hi.
    replace (ad + n2w i * bytes_in_word) with ((ad + bytes_in_word) + n2w (i - 1) * bytes_in_word).
    + assert (Hi' : (i - 1 < LENGTH xs)%N) by (change (SUC (LENGTH xs)) with (N.succ (LENGTH xs)) in Hi; lia).
      exact (IH _ _ _ _ _ H Hi').
    + replace i with ((i - 1) + 1)%N at 2 by lia. rewrite <- word_add_n2w. wring.
Qed.

Lemma FAPPLY_SOME {V} `{Inhabited V} (R : fmap N V) i v : FLOOKUP R i = SOME v -> FAPPLY R i = v.
Proof. intros Hs. unfold FAPPLY. rewrite Hs. reflexivity. Qed.

Lemma FLOOKUP_FUPDATE_LIST_MAP_notin {K V} `{EqDecision K} (g : K -> V) (l : list K) :
  forall f0 x, ~ In x l -> FLOOKUP (f0 |++ MAP (fun n => (n, g n)) l) x = FLOOKUP f0 x.
Proof.
  induction l as [|y l IH]; intros f0 x Hn; [reflexivity|].
  cbn [MAP map FUPDATE_LIST FOLDL] in *. change (FOLDL FUPDATE (f0 |+ (y, g y)) (map (fun n => (n, g n)) l))
    with ((f0 |+ (y, g y)) |++ MAP (fun n => (n, g n)) l).
  rewrite IH by (intros Hi; apply Hn; right; exact Hi). rewrite FLOOKUP_UPDATE.
  destruct (decide (y = x)) as [->|]; [exfalso; apply Hn; left; reflexivity|reflexivity].
Qed.

Lemma FLOOKUP_FUPDATE_LIST_MAP {K V} `{EqDecision K} (g : K -> V) (l : list K) :
  forall f0 x, In x l -> FLOOKUP (f0 |++ MAP (fun n => (n, g n)) l) x = SOME (g x).
Proof.
  induction l as [|y l IH]; intros f0 x Hn; [destruct Hn|].
  cbn [MAP map FUPDATE_LIST FOLDL] in *. change (FOLDL FUPDATE (f0 |+ (y, g y)) (map (fun n => (n, g n)) l))
    with ((f0 |+ (y, g y)) |++ MAP (fun n => (n, g n)) l).
  destruct (in_dec (fun u v => decide (u = v)) x l) as [Hi|Hi]; [exact (IH _ _ Hi)|].
  rewrite FLOOKUP_FUPDATE_LIST_MAP_notin by exact Hi. rewrite FLOOKUP_UPDATE.
  destruct Hn as [->|Hn]; [|contradiction]. destruct (decide (x = x)); [reflexivity|congruence].
Qed.

Lemma lsr_lsl_aligned (w : word a) : good_dimindex a -> byte_aligned w -> (w >>> word_shift a) << word_shift a = w.
Proof.
  intros Hg Ha. pose proof (byte_aligned_mod _ Hg Ha) as Hm.
  rewrite <- (n2w_w2n w) at 1. rewrite lsr_n2w by apply w2n_lt.
  rewrite lsl_n2w by (unfold word_shift; destruct Hg as [E|E]; rewrite E; reflexivity).
  rewrite (pow_ws Hg). rewrite N.mul_comm, <- N.Lcm0.divide_div_mul_exact.
  - rewrite N.mul_comm, N.div_mul by (destruct (good_dimindex_d Hg); lia). apply n2w_w2n.
  - apply N.Lcm0.mod_divide. exact Hm.
Qed.

Lemma one_one_false {B} (ad : word a) (x y : B) p m dm :
  STAR (one (ad, x)) (STAR (one (ad, y)) p) (fun2set (m, dm)) -> False.
Proof.
  intros H. apply one_fun2set in H as (_ & _ & H). apply one_fun2set in H as (_ & Hd & _).
  apply IN_DELETE in Hd as [_ Hd]. apply Hd. reflexivity.
Qed.

Lemma word_list_len_bound {B} (ls : list B) (ad : word a) q m dm :
  good_dimindex a -> STAR (word_list ad ls) q (fun2set (m, dm)) -> (LENGTH ls <= dimword a / (dimindex a DIV 8))%N.
Proof.
  intros Hg H. destruct (N.le_gt_cases (LENGTH ls) (dimword a / (dimindex a DIV 8))) as [Hl|Hl]; [exact Hl|].
  exfalso. destruct (word_list_wrap ls ad (conj Hg Hl)) as (x & xs & y & ys & b & E & ->).
  rewrite E in H. cbn [word_list] in H.
  apply (one_one_false ad x y (STAR (STAR (word_list (ad + bytes_in_word) xs) (word_list (ad + bytes_in_word) ys)) q) m dm).
  revert H. match goal with |- ?A _ -> ?B _ => replace A with B by star_ac end. auto.
Qed.

Lemma word_list_in_memory' (xs : list (word_loc a)) (ad : word a) r m dm :
  STAR (word_list ad xs) r (fun2set (m, dm)) -> good_dimindex a ->
  (w2n ad + LENGTH xs * w2n (bytes_in_word : word a) < dimword a)%N ->
  memory m (addresses ad (LENGTH xs)) = word_list ad xs.
Proof.
  intros H Hg Hb. apply (word_list_in_memory xs ad emp r m dm). split; [|split; [exact Hg|exact Hb]].
  rewrite STAR_emp_l. exact H.
Qed.

Lemma rev_map_map_rev {A B C} (f : B -> C) (g : A -> B) (l : list A) :
  REVERSE (MAP f (MAP g (REVERSE l))) = MAP (fun x => f (g x)) l.
Proof. rewrite map_map, map_rev, rev_involutive. reflexivity. Qed.

Lemma LENGTH_map_N {A B} (f : A -> B) (l : list A) : LENGTH (MAP f l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_map. reflexivity. Qed.

Lemma LAST_snoc {B} `{Inhabited B} (l : list B) (x : B) : LAST (l ++ [x]) = x.
Proof. induction l as [|y l IH]; [reflexivity|]. destruct l as [|z l]; [reflexivity|]. exact IH. Qed.


End InitCodeThm.

Ltac wring2 := word_Z; repeat first [rewrite N2Z.inj_add | rewrite N2Z.inj_mul]; cbn [Z.of_N]; apply zcong_eq; ring.

Ltac star_front_in x H :=
  repeat rewrite <- STAR_ASSOC in H;
  repeat first [ rewrite (STAR_swap_l _ x _) in H | rewrite (STAR_COMM _ x) in H ].

Ltac st_look HST x v G :=
  rewrite HST by (repeat first [left; reflexivity|right]);
  change (stack_remove.store_init _ _ x) with v; cbn [mem_val]; rewrite (FAPPLY_SOME _ _ _ G).

Section InitCodeMain.
Context {a : N} {c ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_code_thm" *)
Theorem init_code_thm : forall gen_gc max_heap k bitmaps0 data_sp (s : state a c ffi_t) jump off code0 coracle,
  init_code_pre k bitmaps0 data_sp s /\ code_rel jump off k code0 (code s) /\
  compile_oracle s = (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) ∘ coracle /\
  (forall n i p, MEM (i, p) (FST (SND (coracle n))) -> reg_bound p k /\ (stack_num_stubs <= i + 1)%N) /\
  lookup stack_remove.stack_err_lab (code s) = SOME (stack_remove.halt_inst (n2w 2)) /\
  (stack_remove.max_stack_alloc <= max_heap)%N ->
  match evaluate (stack_remove.init_code gen_gc max_heap k, s) with
  | (SOME res, t) => False
  | (NONE, t) =>
      (exists w2 w3 w4 : word a,
         FLOOKUP (regs s) 2 = SOME (Word w2) /\ byte_aligned w2 /\
         FLOOKUP (regs t) (k + 2)%N = SOME (Word w2) /\
         FLOOKUP (regs s) 4 = SOME (Word w4) /\ byte_aligned w4 /\ w2 <+ w4 /\
         FLOOKUP (regs t) k = SOME (Word (w4 - bytes_in_word)) /\
         (w2 + n2w stack_remove.max_stack_alloc * bytes_in_word <=+ w3 /\
          w3 <=+ w4 - n2w stack_remove.max_stack_alloc * bytes_in_word /\
          (w2n (- n2w 1 * w2 + w3) <= max_heap * w2n (bytes_in_word : word a))%N /\
          (w2n (bytes_in_word : word a) * max_heap < dimword a)%N ->
          FLOOKUP (regs t) (k + 1)%N =
            SOME (Word (((w3 + - n2w 1 * w2) >>> (word_shift a + 1) << (word_shift a + 1)) + w2 +
                        bytes_in_word * n2w (LENGTH stack_remove.store_list)))) /\
         FLOOKUP (regs s) 3 = SOME (Word w3)) /\
      state_rel jump off k (init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle t) t /\
      ffi t = ffi s /\
      init_prop gen_gc max_heap data_sp (get_stack_heap_limit max_heap (read_pointers s))
        (init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle t) /\
      mdomain s = mdomain t /\
      sh_mdomain s = sh_mdomain t /\
      (let t0 := init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle t in
       fun2set (stackSem.memory s, mdomain t0) = fun2set (stackSem.memory t, mdomain t0))
  end.
Proof.
  intros gen_gc max_heap k bitmaps0 data_sp s jump off code0 coracle (Hpre & Hcr & Hco & Horc & Herr & Hmh).
  destruct Hpre as (ptr2 & ptr3 & ptr4 & bmp & Hg & Hk8 & H1c & Hfsr & Hus & Hust & Hua & R2 & R3 & R4 &
                    M0 & M1 & M2 & M3 & M4 & Hle & HL & Ha2 & Ha4 & Hab & Hcbb & Hmem).
  pose proof (init_arith ptr2 ptr3 ptr4 max_heap Hg Ha2 Ha4 Hle HL Hmh) as Harith. cbv zeta in Harith.
  destruct Harith as (hl & rest & _ & _ & _ & Hsz & Hrest & Hhl & Hmh2 & Eg).
  destruct (good_dimindex_d Hg) as [Hbwd Hd0].
  pose proof (bw_d Hg) as Ebw.
  remember (dimindex a DIV 8)%N as d eqn:Ed.
  assert (Hdv : d = 4%N \/ d = 8%N) by (subst d; destruct Hg as [E|E]; rewrite E; [left|right]; reflexivity).
  pose proof (dimword_ge Hg) as HDW.
  pose proof (w2n_lt ptr4) as HP4. pose proof (w2n_lt ptr2) as HP2.
  assert (Hs24 : ptr4 - ptr2 = n2w (w2n ptr4 - w2n ptr2)).
  { apply WORD_LS in Hle. rewrite <- n2w_sub_N by exact Hle. rewrite !n2w_w2n. reflexivity. }
  assert (EN : (w2n (ptr4 - ptr2) DIV w2n (bytes_in_word : word a) = 2 * hl + (48 + rest))%N).
  { rewrite Hs24, w2n_n2w_lt by lia. rewrite Hbwd. rewrite <- Hsz.
    replace (w2n ptr2 + (2 * hl + 48 + rest) * d - w2n ptr2)%N with ((2 * hl + (48 + rest)) * d)%N by lia.
    apply N.div_mul. lia. }
  rewrite EN, !word_list_exists_ADD in Hmem.
  assert (exists R1, rest = (R1 + 1)%N) as [R1 ->] by (exists (rest - 1)%N; lia).
  rewrite word_list_exists_ADD in Hmem.
  match type of Hmem with context [word_list_exists ?ad (2 * hl)%N] =>
    star_front_in (word_list_exists (B := word_loc a) ad (2 * hl)%N) Hmem end.
  apply WLE_elim in Hmem as (heap & Hlh & Hmem).
  match type of Hmem with context [word_list_exists ?ad 48%N] =>
    star_front_in (word_list_exists (B := word_loc a) ad 48%N) Hmem end.
  apply WLE_elim in Hmem as (sl & Hls & Hmem).
  match type of Hmem with context [word_list_exists ?ad R1] =>
    star_front_in (word_list_exists (B := word_loc a) ad R1) Hmem end.
  apply WLE_elim in Hmem as (rest1 & Hlr & Hmem).
  match type of Hmem with context [word_list_exists ?ad 1%N] =>
    star_front_in (word_list_exists (B := word_loc a) ad 1%N) Hmem end.
  apply WLE_elim in Hmem as (lst & Hll & Hmem).
  destruct lst as [|rl [|? ?]]; [discriminate|
    |rewrite !LENGTH_cons_N in Hll; change (SUC (SUC (LENGTH l))) with (N.succ (N.succ (LENGTH l))) in Hll; lia].
  cbn [word_list] in Hmem. rewrite (STAR_COMM _ emp), STAR_emp_l in Hmem.
  set (S0 := ptr2 + bytes_in_word * n2w (2 * hl)) in Hmem.
  set (K0 := S0 + bytes_in_word * n2w 48) in Hmem.
  assert (EL0 : K0 + bytes_in_word * n2w R1 = ptr4 - bytes_in_word).
  { subst K0 S0. rewrite <- (n2w_w2n ptr2) at 1. rewrite <- (n2w_w2n ptr4), <- Hsz. rewrite Ebw. wring2. }
  assert (ES0 : S0 = n2w (w2n ptr2 + 2 * hl * d)).
  { subst S0. rewrite <- (n2w_w2n ptr2) at 1. rewrite Ebw. wring2. }
  rewrite EL0 in Hmem.
  assert (Hmhp : STAR (word_list ptr2 heap) (STAR (one (ptr4 - bytes_in_word, rl)) (STAR (word_list K0 rest1)
                  (STAR (word_list S0 sl) (STAR (word_list bmp (MAP Word bitmaps0))
                     (word_list_exists (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) data_sp)))))
                  (fun2set (stackSem.memory s, mdomain s))).
  { revert Hmem. match goal with |- ?A _ -> ?B _ => replace A with B by star_ac end. auto. }
  assert (Hdi : forall i, (i < 5)%N -> (ptr2 + n2w i * bytes_in_word) IN mdomain s).
  { intros i Hi. apply (word_list_IN heap ptr2 _ _ _ i Hmhp). lia. }
  assert (D0 : ptr2 IN mdomain s).
  { replace ptr2 with (ptr2 + n2w 0 * bytes_in_word) at 1 by wring. apply Hdi; lia. }
  assert (D1 : (ptr2 + bytes_in_word) IN mdomain s).
  { replace (ptr2 + bytes_in_word) with (ptr2 + n2w 1 * bytes_in_word) by wring. apply Hdi; lia. }
  assert (D2 : (ptr2 + bytes_in_word + bytes_in_word) IN mdomain s).
  { replace (ptr2 + bytes_in_word + bytes_in_word) with (ptr2 + n2w 2 * bytes_in_word) by wring. apply Hdi; lia. }
  assert (D3 : (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word) IN mdomain s).
  { replace (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word) with (ptr2 + n2w 3 * bytes_in_word) by wring.
    apply Hdi; lia. }
  assert (D4 : (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word) IN mdomain s).
  { replace (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word)
      with (ptr2 + n2w 4 * bytes_in_word) by wring. apply Hdi; lia. }
  replace (ptr2 + n2w 2 * bytes_in_word) with (ptr2 + bytes_in_word + bytes_in_word) in M2 by wring.
  replace (ptr2 + n2w 3 * bytes_in_word) with (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word) in M3 by wring.
  replace (ptr2 + n2w 4 * bytes_in_word) with (ptr2 + bytes_in_word + bytes_in_word + bytes_in_word + bytes_in_word)
    in M4 by wring.
  destruct (init_code_prefix k s max_heap gen_gc ptr2 ptr3 ptr4 bmp _ _ _ _ Hg Hk8 R2 R3 R4 M0 D0 M1 D1 M2 D2 M3 D3 M4 D4
              Ha2 Ha4 Hle HL Hmh)
    as (hl' & rest' & RD & Eev & F1 & F2 & F3 & F4 & F5 & F6 & F7 & Fk & Fk1 & Fk2 & _ & _ & _ & _ & Eg' & Hrange).
  rewrite Eg in Eg'. injection Eg' as E1 E2. subst rest' hl'.
  rewrite <- Ed in Fk1, Hrange, F2, F5. rewrite <- ES0 in Fk1, Hrange.
  assert (Hfd : forall i, (1 <= i <= 7)%N \/ i = (k + 2)%N -> i IN FDOM (regs (set_regs RD s))).
  { intros i Hi. rewrite regs_set_regs. unfold FDOM, pred_set.IN.
    destruct Hi as [Hi| ->]; [|rewrite Fk2; discriminate].
    assert (Hi' : i = 1%N \/ i = 2%N \/ i = 3%N \/ i = 4%N \/ i = 5%N \/ i = 6%N \/ i = 7%N) by lia.
    destruct Hi' as [ -> |[ -> |[ -> |[ -> |[ -> |[ -> | -> ]]]]]];
      first [rewrite F1|rewrite F2|rewrite F3|rewrite F4|rewrite F5|rewrite F6|rewrite F7]; discriminate. }
  assert (Hm5 : STAR (word_list S0 sl) (STAR (one (ptr4 - bytes_in_word, rl))
                  (STAR (word_list ptr2 heap) (STAR (word_list K0 rest1) (STAR (word_list bmp (MAP Word bitmaps0))
                     (word_list_exists (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) data_sp)))))
                  (fun2set (stackSem.memory (set_regs RD s), mdomain (set_regs RD s)))).
  { rewrite memory_set_regs, mdomain_set_regs. revert Hmem.
    match goal with |- ?A _ -> ?B _ => replace A with B by star_ac end. auto. }
  destruct (init_memory_run k gen_gc (set_regs RD s) ptr4 S0 rl sl _ Hk8 Fk Fk1 Hfd H1c Hm5 Hls)
    as (RF & m1 & Hm1 & Ev & G0 & Gk & Gk1 & Gother).
  rewrite Eev, Ev. cbv iota.
  rewrite regs_set_regs in Gother.
  assert (Hne : forall i, ((1 <= i <= 7)%N \/ i = (k + 2)%N) -> FLOOKUP RF i = FLOOKUP RD i)
    by (intros i Hi; apply Gother; lia).
  assert (Hthe : forall i w, FLOOKUP RF i = SOME (Word w) -> wordSem.theWord (FAPPLY RF i) = w)
    by (intros i w Hi; rewrite (FAPPLY_SOME _ _ _ Hi); reflexivity).
  assert (Gk2 : FLOOKUP RF (k + 2)%N = SOME (Word ptr2)) by (rewrite Hne by lia; exact Fk2).
  assert (G3 : FLOOKUP RF 3 = SOME (Word (bmp >>> word_shift a))) by (rewrite Hne by lia; exact F3).
  assert (Ehs : (w2n (S0 + bytes_in_word * n2w 48 - ptr2) DIV d - LENGTH stack_remove.store_list = 2 * hl)%N).
  { replace (S0 + bytes_in_word * n2w 48 - ptr2) with (n2w ((2 * hl + 48) * d) : word a)
      by (subst S0; rewrite Ebw; wring2).
    rewrite w2n_n2w_lt by lia. rewrite N.div_mul by lia. rewrite LENGTH_store_list. lia. }
  assert (Ess : (w2n (ptr4 - bytes_in_word - (S0 + bytes_in_word * n2w 48)) DIV d = R1)%N).
  { replace (ptr4 - bytes_in_word - (S0 + bytes_in_word * n2w 48)) with (n2w (R1 * d) : word a).
    - rewrite w2n_n2w_lt by lia. rewrite N.div_mul by lia. reflexivity.
    - rewrite <- EL0. subst K0. rewrite Ebw. wring2. }
  assert (Et0 : init_reduce gen_gc jump off k code0 bitmaps0 data_sp coracle (set_regs RF (set_memory m1 (set_regs RD s))) =
                mk_state RF (fp_regs s)
                  (FEMPTY |++ MAP (fun n => match stack_remove.store_init gen_gc k n with
                                            | inl w => (n, Word w)
                                            | inr i => (n, FAPPLY RF i)
                                            end) (CurrHeap :: stack_remove.store_list))
                  (read_mem (S0 + bytes_in_word * n2w 48) m1 (R1 + 1)) R1 m1
                  (addresses ptr2 (2 * hl)) (sh_mdomain s) bitmaps0
                  (fun c0 p => stackSem.compile s c0 (MAP (stack_remove.prog_comp jump off k) p)) coracle
                  (code_buffer s) (wordSem.mk_buffer (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) [] data_sp)
                  (gc_fun s) true true false (clock s) code0 (ffi s) (ffi_save_regs s) (be s)).
  { unfold init_reduce. rewrite regs_set_regs.
    rewrite (Hthe _ _ Gk2), (Hthe _ _ G3), (Hthe _ _ Gk), (Hthe _ _ Gk1).
    rewrite (lsr_lsl_aligned bmp Hg Hab). rewrite <- Ed. rewrite Ehs, Ess. reflexivity. }
  assert (Emapf : (fun n => match stack_remove.store_init gen_gc k n with
                            | inl w => (n, Word w)
                            | inr i => (n, FAPPLY RF i)
                            end) = (fun n => (n, mem_val RF (stack_remove.store_init gen_gc k n)))).
  { apply functional_extensionality; intros n. destruct (stack_remove.store_init gen_gc k n); reflexivity. }
  rewrite Emapf in Et0.
  set (STORE := FEMPTY |++ MAP (fun n => (n, mem_val RF (stack_remove.store_init gen_gc k n)))
                                (CurrHeap :: stack_remove.store_list)) in Et0.
  assert (HST : forall x, In x (CurrHeap :: stack_remove.store_list) ->
                  FLOOKUP STORE x = SOME (mem_val RF (stack_remove.store_init gen_gc k x)))
    by (intros x Hx; exact (FLOOKUP_FUPDATE_LIST_MAP (fun n => mem_val RF (stack_remove.store_init gen_gc k n)) _ _ _ Hx)).
  assert (EK0w : (w2n (S0 + bytes_in_word * n2w 48) = w2n ptr2 + (2 * hl + 48) * d)%N).
  { replace (S0 + bytes_in_word * n2w 48) with (n2w (w2n ptr2 + (2 * hl + 48) * d) : word a).
    - apply w2n_n2w_lt. lia.
    - subst S0. rewrite <- (n2w_w2n ptr2) at 2. rewrite Ebw. wring2. }
  subst K0.
rewrite regs_set_regs, mdomain_set_regs in Hm1.
  assert (Emem : memory m1 (addresses ptr2 (2 * hl)) = word_list ptr2 heap).
  { rewrite <- Hlh. pose proof Hm1 as Hc. star_front_in (word_list ptr2 heap) Hc.
    apply (word_list_in_memory' _ _ _ _ _ Hc Hg). rewrite Hlh, Hbwd. lia. }
  assert (EWL : word_list (S0 + bytes_in_word * n2w 48) (rest1 ++ [Word (n2w 0)]) =
                STAR (word_list (S0 + bytes_in_word * n2w 48) rest1) (one (ptr4 - bytes_in_word, Word (n2w 0)))).
  { rewrite word_list_APPEND. cbn [word_list]. rewrite Hlr, EL0, (STAR_COMM _ emp), STAR_emp_l. reflexivity. }
  assert (Hm2 : STAR (STAR (word_list S0 (MAP (mem_val RD) (MAP (stack_remove.store_init gen_gc k)
                        (REVERSE stack_remove.store_list))))
                   (STAR (word_list ptr2 heap) (STAR (word_list bmp (MAP Word bitmaps0))
                      (word_list_exists (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) data_sp))))
                  (word_list (S0 + bytes_in_word * n2w 48) (rest1 ++ [Word (n2w 0)]))
                  (fun2set (m1, mdomain s))).
  { rewrite EWL. revert Hm1. match goal with |- ?A _ -> ?B _ => replace A with B by star_ac end. auto. }
  assert (ERM : read_mem (S0 + bytes_in_word * n2w 48) m1 (R1 + 1) = rest1 ++ [Word (n2w 0)]).
  { replace (R1 + 1)%N with (LENGTH (rest1 ++ [Word (n2w 0)])) by (rewrite LENGTH_app_N, Hlr; reflexivity).
    exact (word_list_IMP_read_mem _ _ _ _ _ Hm2). }
  assert (Ewst : word_store (S0 + bytes_in_word * n2w 48) STORE =
                 word_list S0 (MAP (mem_val RD) (MAP (stack_remove.store_init gen_gc k) (REVERSE stack_remove.store_list)))).
  { unfold word_store. rewrite word_list_EQ_rev. f_equal.
    - match goal with |- context [LENGTH ?l] => replace (LENGTH l) with 48%N by reflexivity end. wring.
    - rewrite rev_map_map_rev. apply map_ext_in. intros n Hn.
      rewrite HST by (right; exact Hn).
      destruct (@store_init_cases a gen_gc k n) as [(w & Ew)|(i & Ei & Hi)]; rewrite ?Ew, ?Ei; [reflexivity|].
      cbn [mem_val]. unfold FAPPLY. rewrite Hne by exact Hi. reflexivity. }
  rewrite Et0.
  split.
  { exists ptr2, ptr3, ptr4. rewrite regs_set_regs.
    refine (conj R2 (conj Ha2 (conj Gk2 (conj R4 (conj Ha4 (conj _ (conj Gk (conj _ R3)))))))).
    - apply WORD_LO. lia.
    - intros (C1 & C2 & C3 & C4). rewrite Gk1, LENGTH_store_list, (Hrange C1 C2 C3 C4). reflexivity. }
  split.
  { unfold state_rel.
    cbn [use_stack use_store use_alloc be gc_fun clock ffi ffi_save_regs fp_regs code_buffer sh_mdomain
         stackSem.compile compile_oracle regs code store stack stack_space bitmaps data_buffer
         stackSem.memory mdomain set_regs set_memory].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hus|]. split; [exact Hust|]. split; [exact Hua|]. split; [discriminate|].
    do 8 (split; [reflexivity|]).
    split; [reflexivity|]. split; [rewrite Hco; reflexivity|].
    split; [exact Horc|]. split; [exact Hg|]. split; [intros; reflexivity|].
    split; [exact Hcr|]. split; [exact Herr|].
    split.
    { rewrite Gk2, HST by (left; reflexivity).
      change (stack_remove.store_init gen_gc k CurrHeap) with (@inr (word a) N (k + 2)%N).
      cbn [mem_val]. rewrite (FAPPLY_SOME _ _ _ Gk2). reflexivity. }
    split; [exact Hfsr|].
    assert (EBB : FLOOKUP STORE BitmapBase = SOME (Word (bmp >>> word_shift a))).
    { rewrite HST by (repeat first [left; reflexivity|right]).
      change (stack_remove.store_init gen_gc k BitmapBase) with (@inr (word a) N 3%N).
      cbn [mem_val]. rewrite (FAPPLY_SOME _ _ _ G3). reflexivity. }
    rewrite EBB. split; [reflexivity|].
    split; [rewrite LENGTH_read_mem; lia|].
    cbv zeta. cbn [the_SOME_Word wordSem.position]. rewrite (lsr_lsl_aligned bmp Hg Hab).
    split; [reflexivity|].
    rewrite Gk1. rewrite <- Ed.
    split; [rewrite EK0w; unfold stack_remove.max_stack_alloc; lia|].
    split; [rewrite EK0w, LENGTH_read_mem, Hbwd; lia|].
    split; [rewrite Gk; do 2 f_equal; symmetry; exact EL0|].
    rewrite app_nil_r.
    rewrite Emem, ERM, Ewst, EWL.
    revert Hm1. match goal with |- ?A _ -> ?B _ => replace B with A by star_ac end. auto. }
  split; [reflexivity|].
  assert (G1 : FLOOKUP RF 1 = SOME (Word (wordSem.position (code_buffer s) + n2w (wordSem.space_left (code_buffer s)))))
    by (rewrite Hne by lia; exact F1).
  assert (G2 : FLOOKUP RF 2 = SOME (Word (ptr2 + n2w (hl * d)))) by (rewrite Hne by lia; exact F2).
  assert (G4 : FLOOKUP RF 4 = SOME (Word (bmp + bytes_in_word * n2w (LENGTH bitmaps0)))) by (rewrite Hne by lia; exact F4).
  assert (G5 : FLOOKUP RF 5 = SOME (Word (n2w (hl * d)))) by (rewrite Hne by lia; exact F5).
  assert (G6 : FLOOKUP RF 6 = SOME (Word (bmp + bytes_in_word * n2w (LENGTH bitmaps0) + bytes_in_word * n2w data_sp)))
    by (rewrite Hne by lia; exact F6).
  assert (G7 : FLOOKUP RF 7 = SOME (Word (wordSem.position (code_buffer s)))) by (rewrite Hne by lia; exact F7).
  split.
  { unfold init_prop.
    exists ptr2, (ptr2 + n2w (hl * d)), (bmp >>> word_shift a), hl.
    cbn [store regs stack stack_space bitmaps data_buffer code_buffer use_stack use_store stackSem.memory mdomain
         wordSem.position wordSem.space_left wordSem.buffer_buffer].
    split; [st_look HST CurrHeap (@inr (word a) N (k + 2)%N) Gk2; reflexivity|].
    split; [st_look HST NextFree (@inr (word a) N (k + 2)%N) Gk2; reflexivity|].
    split.
    { rewrite HST by (repeat first [left; reflexivity|right]).
      change (stack_remove.store_init gen_gc k TriggerGC) with (@inr (word a) N (if gen_gc then (k + 2)%N else 2%N)).
      destruct gen_gc; cbn [mem_val]; [rewrite (FAPPLY_SOME _ _ _ Gk2)|rewrite (FAPPLY_SOME _ _ _ G2)]; reflexivity. }
    split; [st_look HST EndOfHeap (@inr (word a) N 2%N) G2; reflexivity|].
    split; [st_look HST OtherHeap (@inr (word a) N 2%N) G2; reflexivity|].
    split; [st_look HST BitmapBase (@inr (word a) N 3%N) G3; reflexivity|].
    split; [st_look HST HeapLength (@inr (word a) N 5%N) G5; rewrite Ebw, word_mul_n2w; reflexivity|].
    do 3 (split; [rewrite HST by (repeat first [left; reflexivity|right]); reflexivity|]).
    split; [st_look HST GlobReal (@inr (word a) N (k + 2)%N) Gk2; reflexivity|].
    do 2 (split; [rewrite HST by (repeat first [left; reflexivity|right]); reflexivity|]).
    split; [st_look HST CodeBuffer (@inr (word a) N 7%N) G7; reflexivity|].
    split; [st_look HST CodeBufferEnd (@inr (word a) N 1%N) G1; reflexivity|].
    split; [st_look HST BitmapBuffer (@inr (word a) N 4%N) G4; reflexivity|].
    split; [st_look HST BitmapBufferEnd (@inr (word a) N 6%N) G6; reflexivity|].
    split.
    { unfold read_pointers. rewrite R2, R3, R4. cbn [THE wordSem.theWord]. rewrite Eg.
      unfold stack_heap_limit_ok. cbn [store stack].
      split; [st_look HST HeapLength (@inr (word a) N 5%N) G5; rewrite Ebw, word_mul_n2w; reflexivity|].
      split; [rewrite <- Ed; lia|]. rewrite LENGTH_read_mem. reflexivity. }
    split; [exact Hcbb|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact G0|].
    split.
    { pose proof Hm1 as Hc.
      star_front_in (word_list_exists (B := word_loc a) (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) data_sp) Hc.
      apply WLE_elim in Hc as (dl & Hdl & Hc).
      star_front_in (word_list (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) dl) Hc.
      star_front_in (word_list bmp (MAP Word bitmaps0)) Hc.
      rewrite STAR_ASSOC in Hc.
      replace (bmp + bytes_in_word * n2w (LENGTH bitmaps0)) with (bmp + bytes_in_word * n2w (LENGTH (MAP Word bitmaps0))) in Hc
        by (rewrite LENGTH_map_N; reflexivity).
      rewrite <- word_list_APPEND in Hc.
      pose proof (word_list_len_bound _ _ _ _ _ Hg Hc) as Hb.
      rewrite LENGTH_app_N, LENGTH_map_N, Hdl, <- Ed in Hb.
      pose proof (N.Div0.mul_div_le (dimword a) d) as Hmd.
      destruct Hdv as [-> | ->]; lia. }
    split; [rewrite LENGTH_read_mem; lia|].
    split; [rewrite Ebw; wring|].
    split; [exact Ha2|].
    split; [rewrite ERM; apply LAST_snoc|].
    split; [rewrite LENGTH_read_mem; change (SUC R1) with (N.succ R1); lia|].
    split; [rewrite LENGTH_read_mem, <- Ed; lia|].
    split; [lia|].
    replace (ptr2 + n2w (hl * d)) with (ptr2 + bytes_in_word * n2w hl) by (rewrite Ebw; wring).
    rewrite <- word_list_exists_ADD. replace (hl + hl)%N with (2 * hl)%N by lia.
    apply word_list_exists_addresses. split; [rewrite <- Ed; lia|exact Hg]. }
  split; [reflexivity|]. split; [reflexivity|].
  cbv zeta. cbn [mdomain stackSem.memory set_regs set_memory].
  assert (Emems : memory (stackSem.memory s) (addresses ptr2 (2 * hl)) = word_list ptr2 heap).
  { rewrite <- Hlh. apply (word_list_in_memory' _ _ _ _ _ Hmhp Hg). rewrite Hlh, Hbwd. lia. }
  rewrite <- Emem in Emems. unfold memory in Emems.
  apply (f_equal (fun P => P (fun2set (stackSem.memory s, addresses ptr2 (2 * hl))))) in Emems.
  cbv beta in Emems. rewrite <- Emems. reflexivity.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "evaluate_init_code" *)
Theorem evaluate_init_code : forall gen_gc max_heap bitmaps0 data_sp k start (s : state a c ffi_t) jump off coracle code0,
  init_pre gen_gc max_heap bitmaps0 data_sp k start s /\
  compile_oracle s = (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) ∘ coracle /\
  (forall n i p, MEM (i, p) (FST (SND (coracle n))) -> reg_bound p k /\ (stack_num_stubs <= i + 1)%N) /\
  lookup stack_remove.stack_err_lab (code s) = SOME (stack_remove.halt_inst (n2w 2)) /\
  code_rel jump off k code0 (code s) ->
  match evaluate (stack_remove.init_code gen_gc max_heap k, s) with
  | (NONE, t) => exists r, make_init_opt gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s = SOME r /\
                           state_rel jump off k r t /\ ffi t = ffi s
  | _ => False
  end.
Proof.
  intros gen_gc max_heap bitmaps0 data_sp k start s jump off coracle code0 ((_ & Hpre & Hmh) & Hco & Horc & Herr & Hcr).
  pose proof (init_code_thm gen_gc max_heap k bitmaps0 data_sp s jump off code0 coracle
                (conj Hpre (conj Hcr (conj Hco (conj Horc (conj Herr Hmh)))))) as H.
  unfold make_init_opt.
  destruct (evaluate (stack_remove.init_code gen_gc max_heap k, s)) as [[r|] t]; [contradiction|].
  destruct H as (_ & Hsr & Hffi & Hip & _).
  destruct (classical_dec _) as [_|Hn]; [|contradiction].
  eexists; split; [reflexivity|]. split; assumption.
Qed.

Lemma if_dec_eq {A} (P Q : Prop) (x y1 y2 : A) :
  (P <-> Q) -> (~ P -> ~ Q -> y1 = y2) ->
  (if classical_dec P then x else y1) = (if classical_dec Q then x else y2).
Proof.
  intros E H. destruct (classical_dec P) as [p|np]; destruct (classical_dec Q) as [q|nq]; try reflexivity.
  - exfalso; exact (nq (proj1 E p)).
  - exfalso; exact (np (proj2 E q)).
  - exact (H np nq).
Qed.

Lemma semantics_shift0 start (s t : state a c ffi_t) :
  (forall k, evaluate (@Call a NONE (inl 0%N) NONE, set_clock (k + 1) s) =
             evaluate (@Call a NONE (inl start) NONE, set_clock k t)) ->
  FST (evaluate (@Call a NONE (inl 0%N) NONE, set_clock 0 s)) = SOME TimeOut ->
  ffi (SND (evaluate (@Call a NONE (inl 0%N) NONE, set_clock 0 s))) =
    ffi (SND (evaluate (@Call a NONE (inl start) NONE, set_clock 0 t))) ->
  semantics 0 s = semantics start t.
Proof.
  intros Hk H0 Hf. unfold semantics. cbv zeta.
  set (P0 := @Call a NONE (inl 0%N) NONE) in *. set (Ps := @Call a NONE (inl start) NONE) in *.
  assert (Hsh : forall k, k <> 0%N -> evaluate (P0, set_clock k s) = evaluate (Ps, set_clock (k - 1) t)).
  { intros k Hk0. replace k with ((k - 1) + 1)%N at 1 by lia. apply Hk. }
  apply if_dec_eq.
  - split; intros [k Hb].
    + destruct (N.eq_dec k 0) as [->|Hk0].
      * rewrite H0 in Hb. destruct Hb as [Hb _]. exfalso; exact (Hb eq_refl).
      * exists (k - 1)%N. rewrite <- (Hsh k Hk0). exact Hb.
    + exists (k + 1)%N. rewrite Hk. exact Hb.
  - intros _ _.
    match goal with |- match some ?F with _ => _ end = match some ?G with _ => _ end =>
      assert (EFG : F = G) end.
    { apply functional_extensionality; intros res; apply propositional_extensionality.
      split; intros (k & t1 & r & o & E & M & R).
      - destruct (N.eq_dec k 0) as [->|Hk0].
        + rewrite E in H0. cbn [FST] in H0. injection H0 as ->. contradiction.
        + exists (k - 1)%N, t1, r, o. rewrite <- (Hsh k Hk0). auto.
      - exists (k + 1)%N, t1, r, o. rewrite Hk. auto. }
    rewrite EFG. destruct (some _); [reflexivity|].
    apply (f_equal Diverge). apply f_equal.
    apply functional_extensionality; intros y; apply propositional_extensionality.
    unfold IMAGE. split; intros (k & -> & _).
    + destruct (N.eq_dec k 0) as [->|Hk0].
      * exists 0%N. split; [rewrite Hf; reflexivity|exact Logic.I].
      * exists (k - 1)%N. split; [rewrite (Hsh k Hk0); reflexivity|exact Logic.I].
    + exists (k + 1)%N. split; [rewrite Hk; reflexivity|exact Logic.I].
Qed.

Lemma bad_fun_return_call (X : state a c ffi_t) dest :
  bad_fun_return (FST (evaluate (@Call a NONE dest NONE, X))) = false.
Proof.
  rewrite ev_call_eq. destruct (find_code _ _ _); [|reflexivity].
  cbn [negb]. rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl). cbn [negb].
  destruct (clock X =? 0)%N; [reflexivity|].
  destruct (evaluate _) as [res s'] eqn:E. destruct (bad_fun_return res) eqn:Eb; [reflexivity|exact Eb].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "init_semantics" *)
Theorem init_semantics : forall gen_gc max_heap bitmaps0 data_sp k start (s : state a c ffi_t) jump off code0 coracle,
  lookup stack_remove.stack_err_lab (code s) = SOME (stack_remove.halt_inst (n2w 2)) /\
  code_rel jump off k code0 (code s) /\
  init_pre gen_gc max_heap bitmaps0 data_sp k start s /\
  compile_oracle s = (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) ∘ coracle /\
  (forall n i p, MEM (i, p) (FST (SND (coracle n))) -> reg_bound p k /\ (stack_num_stubs <= i + 1)%N) ->
  match evaluate (stack_remove.init_code gen_gc max_heap k, s) with
  | (NONE, t) => semantics 0 s = semantics start t /\
                 exists r, make_init_opt gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s = SOME r /\
                           state_rel jump off k r t
  | _ => False
  end.
Proof.
  intros gen_gc max_heap bitmaps0 data_sp k start s jump off code0 coracle (Herr & Hcr & Hip & Hco & Horc).
  pose proof (evaluate_init_code gen_gc max_heap bitmaps0 data_sp k start s jump off coracle code0
                (conj Hip (conj Hco (conj Horc (conj Herr Hcr))))) as H.
  destruct (evaluate (stack_remove.init_code gen_gc max_heap k, s)) as [[r|] t] eqn:Ei; [contradiction|].
  destruct H as (r & Hr & Hsr & Hffi). split; [|exists r; split; assumption].
  destruct Hip as (Hl0 & _ & _).
  apply semantics_shift0.
  - intros ck. rewrite ev_call_eq. cbn [find_code]. change (code (set_clock (ck + 1) s)) with (code s). rewrite Hl0.
    cbn [negb]. rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl). cbn [negb].
    change (clock (set_clock (ck + 1) s)) with (ck + 1)%N.
    replace ((ck + 1) =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (dec_clock (set_clock (ck + 1) s)) with (set_clock ck s)
      by (unfold dec_clock; change (clock (set_clock (ck + 1) s)) with (ck + 1)%N;
          rewrite N.add_sub; reflexivity).
    rewrite (ev_seq_none _ _ _ _ (evaluate_init_code_clock gen_gc max_heap k s NONE t ck Ei)).
    pose proof (bad_fun_return_call (set_clock ck t) (inl start)) as Hb.
    destruct (evaluate (@Call a NONE (inl start) NONE, set_clock ck t)) as [res2 t2].
    cbn [FST] in Hb. rewrite Hb. reflexivity.
  - rewrite ev_call_eq. cbn [find_code]. change (code (set_clock 0 s)) with (code s). rewrite Hl0.
    cbn [negb]. rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl). reflexivity.
  - rewrite ev_call_eq. cbn [find_code]. change (code (set_clock 0 s)) with (code s). rewrite Hl0.
    cbn [negb]. rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl). cbn [negb FST SND].
    change (clock (set_clock 0 s) =? 0)%N with true.
    rewrite ev_call_eq. change (code (set_clock 0 t)) with (code t).
    transitivity (ffi s); [reflexivity|]. rewrite <- Hffi.
    destruct (find_code _ _ (code t)); [|reflexivity].
    cbn [negb]. rewrite (proj2 (bool_decide_spec (@NONE (prog a * (N * N)) = NONE)) eq_refl). cbn [negb].
    change (clock (set_clock 0 t) =? 0)%N with true. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_opt_SOME_semantics" *)
Theorem make_init_opt_SOME_semantics : forall gen_gc max_heap bitmaps0 data_sp k start (s2 : state a c ffi_t) jump off coracle code0,
  init_pre gen_gc max_heap bitmaps0 data_sp k start s2 /\
  compile_oracle s2 = (I ## (MAP (stack_remove.prog_comp jump off k) ## I)) ∘ coracle /\
  (forall n i p, MEM (i, p) (FST (SND (coracle n))) -> reg_bound p k /\ (stack_num_stubs <= i + 1)%N) /\
  code_rel jump off k code0 (code s2) /\
  lookup stack_remove.stack_err_lab (code s2) = SOME (stack_remove.halt_inst (n2w 2)) ->
  exists s1, make_init_opt gen_gc max_heap bitmaps0 data_sp coracle jump off k code0 s2 = SOME s1 /\
             (semantics start s1 <> Fail -> semantics 0 s2 = semantics start s1).
Proof.
  intros gen_gc max_heap bitmaps0 data_sp k start s2 jump off coracle code0 (Hip & Hco & Horc & Hcr & Herr).
  pose proof (init_semantics gen_gc max_heap bitmaps0 data_sp k start s2 jump off code0 coracle
                (conj Herr (conj Hcr (conj Hip (conj Hco Horc))))) as H.
  destruct (evaluate (stack_remove.init_code gen_gc max_heap k, s2)) as [[r|] t]; [contradiction|].
  destruct H as (Hsem & s1 & Hs1 & Hsr). exists s1. split; [exact Hs1|].
  intros HF. rewrite Hsem. exact (compile_semantics jump off k s1 t start (conj Hsr HF)).
Qed.


(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "make_init_semantics" *)
Theorem make_init_semantics : forall jump off gen_gc max_heap k start coracle code0 (s2 : state a c ffi_t) bitmaps0 data_sp,
  discharge_these jump off gen_gc max_heap k start coracle code0 s2 /\
  propagate_these s2 bitmaps0 data_sp ->
  exists s1, make_init_opt gen_gc max_heap bitmaps0 data_sp coracle jump off k (fromAList code0) s2 = SOME s1 /\
             (semantics start s1 <> Fail -> semantics 0 s2 = semantics start s1).
Proof.
  intros jump off gen_gc max_heap k start coracle code0 s2 bitmaps0 data_sp
    ((Hev & Horc & Hco & Hcode & Hk8 & H1 & Hfsr & Hus & Hust & Hua & Hmh) & Hg &
     ptr2 & ptr3 & ptr4 & bmp & R2 & R3 & R4 & M0 & M1 & M2 & M3 & M4 & Hcbb & Hle & Ha2 & Ha4 & Hab & HL & Hmem).
  apply make_init_opt_SOME_semantics.
  split.
  { split; [rewrite Hcode, sptree.lookup_fromAList; reflexivity|].
    split; [|exact Hmh].
    exists ptr2, ptr3, ptr4, bmp.
    do 21 (split; [assumption|]).
    replace (ptr4 - ptr2) with (- n2w 1 * ptr2 + ptr4) by wring. exact Hmem. }
  split; [exact Hco|]. split; [exact Horc|].
  split; [exact (IMP_code_rel jump off k gen_gc max_heap start code0 (code s2) (conj Hev Hcode))|].
  rewrite Hcode, sptree.lookup_fromAList. reflexivity.
Qed.

End InitCodeMain.

(** ** Syntactic properties: [stack_asm_name] *)

Section AsmName.
Context {a : N}.

Ltac sr_bnorm :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H : is_true (_ && _) |- _ => apply andb_true_iff in H as [? ?]
  end.


Lemma reg_name_mono (c : asm_config a) r r' : reg_name r c = true -> r' <= r -> reg_name r' c = true.
Proof. unfold reg_name; intros H Hle; apply N.ltb_lt in H; apply N.ltb_lt; lia. Qed.

Lemma good_dimindex_ge (Hg : good_dimindex a) : 32 <= dimindex a.
Proof. destruct Hg as [H|H]; rewrite H; lia. Qed.

Lemma n2w_small_ne0 (Hg : good_dimindex a) x : 0 < x -> x < 32 -> (n2w x : word a) <> n2w 0.
Proof.
  intros H0 H32 E. apply (f_equal w2n) in E. rewrite !w2n_n2w in E.
  pose proof (good_dimindex_ge Hg) as Hd. unfold dimword in E.
  assert (32 < 2 ** dimindex a) by (apply N.lt_le_trans with (2 ** 32); [reflexivity|apply N.pow_le_mono_r; lia]).
  rewrite (N.mod_small x), (N.mod_small 0) in E by lia. lia.
Qed.

Lemma w2n_n2w_small (Hg : good_dimindex a) x : x < 32 -> w2n (n2w x : word a) = x.
Proof.
  intros H. rewrite w2n_n2w. pose proof (good_dimindex_ge Hg) as Hd. unfold dimword.
  apply N.mod_small. apply N.lt_le_trans with (2 ** 32); [|apply N.pow_le_mono_r; lia].
  apply N.lt_trans with 32; [exact H|reflexivity].
Qed.

Lemma word_shift_small : word_shift a <= 3 /\ 0 < word_shift a.
Proof. unfold word_shift; destruct (dimindex a =? 32); lia. Qed.

Ltac sr_leaf c k Hg Hv Hk Hk2 Hk0 :=
  first
    [ reflexivity | assumption
    | apply (reg_name_mono c (k + 2)); [exact Hk2|lia]
    | apply (reg_name_mono c k); [exact Hk|lia]
    | (destruct (Hv 1 ltac:(unfold stack_remove.max_stack_alloc; lia)) as [_ Hb];
       rewrite N.mul_1_l in Hb; exact Hb)
    | (apply N.ltb_lt; rewrite w2n_n2w_small by first [exact Hg|(pose proof word_shift_small; lia)];
       pose proof (good_dimindex_ge Hg); pose proof word_shift_small; lia)
    | (apply Bool.implb_true_iff; intros Hx; apply bool_decide_spec in Hx; exfalso;
       revert Hx; apply n2w_small_ne0; [exact Hg|..]; pose proof word_shift_small; lia)
    | (apply Bool.implb_true_iff; intros _; apply bool_decide_spec; reflexivity)
    | (destruct (two_reg_arith c); cbn [implb]; [|reflexivity];
       first [ apply orb_true_iff; left; apply bool_decide_spec; reflexivity
             | apply orb_true_iff; right; apply andb_true_iff; split; apply bool_decide_spec; reflexivity
             | assumption
             | apply bool_decide_spec; reflexivity ]) ].


Section FuelNames.
Variables (c : asm_config a) (Hv : forall n, n <= stack_remove.max_stack_alloc ->
     valid_imm c (inl asm.Sub) (n2w (n * (dimindex a DIV 8))) = true /\
     valid_imm c (inl asm.Add) (n2w (n * (dimindex a DIV 8))) = true).

Lemma valid_word_offset_add n : n <= stack_remove.max_stack_alloc ->
  valid_imm c (inl asm.Add) (stack_remove.word_offset n) = true.
Proof. intros H; unfold stack_remove.word_offset; rewrite N.mul_comm; exact (proj2 (Hv n H)). Qed.

Lemma valid_word_offset_sub n : n <= stack_remove.max_stack_alloc ->
  valid_imm c (inl asm.Sub) (stack_remove.word_offset n) = true.
Proof. intros H; unfold stack_remove.word_offset; rewrite N.mul_comm; exact (proj1 (Hv n H)). Qed.

Ltac fuel_leaf :=
  cbn [stack_asm_name inst_name arith_name reg_imm_name stack_remove.single_stack_free
       stack_remove.single_stack_alloc stack_remove.halt_inst];
  repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end);
  first [ reflexivity | assumption
        | apply valid_word_offset_add; unfold stack_remove.max_stack_alloc in *; lia
        | apply valid_word_offset_sub; unfold stack_remove.max_stack_alloc in *; lia
        | destruct (two_reg_arith c); cbn [implb]; [|reflexivity];
          apply orb_true_iff; left; apply bool_decide_spec; reflexivity ].

Lemma asm_name_upshift_f r (Hr : reg_name r c = true) :
  forall f n, stack_asm_name c (@stack_remove.upshift_f a f r n) = true.
Proof.
  induction f as [|f IH]; intros n; cbn [stack_remove.upshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc) eqn:E; [apply N.leb_le in E|apply N.leb_gt in E].
  - fuel_leaf.
  - cbn [stack_asm_name]; apply andb_true_iff; split; [|apply IH]. fuel_leaf.
Qed.

Lemma asm_name_downshift_f r (Hr : reg_name r c = true) :
  forall f n, stack_asm_name c (@stack_remove.downshift_f a f r n) = true.
Proof.
  induction f as [|f IH]; intros n; cbn [stack_remove.downshift_f]; [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc) eqn:E; [apply N.leb_le in E|apply N.leb_gt in E].
  - fuel_leaf.
  - cbn [stack_asm_name]; apply andb_true_iff; split; [|apply IH]. fuel_leaf.
Qed.

Lemma asm_name_stack_free_f k (Hk : reg_name k c = true) :
  forall f n, stack_asm_name c (@stack_remove.stack_free_f a f k n) = true.
Proof.
  induction f as [|f IH]; intros n; cbn [stack_remove.stack_free_f]; [reflexivity|].
  destruct (n =? 0); [reflexivity|].
  destruct (n <=? stack_remove.max_stack_alloc) eqn:E; [apply N.leb_le in E|apply N.leb_gt in E].
  - fuel_leaf.
  - cbn [stack_asm_name]; apply andb_true_iff; split; [|apply IH]. fuel_leaf.
Qed.

Lemma asm_name_stack_alloc_f jump k (Hk : reg_name k c = true) (H1 : reg_name 1 c = true) :
  forall f n, stack_asm_name c (@stack_remove.stack_alloc_f a f jump k n) = true.
Proof.
  induction f as [|f IH]; intros n; cbn [stack_remove.stack_alloc_f]; [reflexivity|].
  destruct (n =? 0) eqn:E0; [reflexivity|]. apply N.eqb_neq in E0.
  destruct (n <=? stack_remove.max_stack_alloc) eqn:E; [apply N.leb_le in E|apply N.leb_gt in E].
  - destruct jump; cbn [stack_remove.single_stack_alloc stack_asm_name stack_remove.halt_inst];
      repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end); fuel_leaf.
  - cbn [stack_asm_name]; apply andb_true_iff; split; [|apply IH].
    destruct jump; cbn [stack_remove.single_stack_alloc stack_asm_name stack_remove.halt_inst];
      repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end); fuel_leaf.
Qed.

End FuelNames.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_remove_comp_stack_asm_name" *)
Theorem stack_remove_comp_stack_asm_name : forall (c : asm_config a) jump off k (p : prog a),
  stack_asm_name c p /\ stack_asm_remove c p /\
  addr_offset_ok c (n2w 0) /\
  good_dimindex a /\
  (forall n, n <= stack_remove.max_stack_alloc ->
     valid_imm c (inl asm.Sub) (n2w (n * (dimindex a DIV 8))) /\
     valid_imm c (inl asm.Add) (n2w (n * (dimindex a DIV 8)))) /\
  (forall s, addr_offset_ok c (stack_remove.store_offset s)) /\
  reg_name (k + 2) c /\ reg_name (k + 1) c /\ reg_name k c /\ k <> 0 /\
  off = addr_offset c ->
  stack_asm_name c (stack_remove.comp jump off k p).
Proof.
  intros c jump off k p.
  induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp] using prog_nested_ind;
    intros (H1 & H2 & H0 & Hg & Hv & Hs & Hk2 & Hk1 & Hk & Hk0 & ->); unfold is_true in *.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|exact H1].
    destruct h as [[p2 [k1 k2]]|]; cbn [stack_remove.comp stack_asm_name stack_asm_remove] in H1, H2 |- *;
      sr_bnorm; repeat (apply andb_true_iff; split); try assumption; try reflexivity;
      first [apply (Hr p1 _ eq_refl)|apply (Hh p2 _ eq_refl)]; repeat (first [exact Hv|exact Hs|assumption|reflexivity|split]).
  - cbn [stack_remove.comp stack_asm_name stack_asm_remove] in H1, H2 |- *; sr_bnorm.
    apply andb_true_iff; split; [apply IH1|apply IH2]; repeat (first [exact Hv|exact Hs|assumption|reflexivity|split]).
  - cbn [stack_remove.comp stack_asm_name stack_asm_remove] in H1, H2 |- *; sr_bnorm.
    apply andb_true_iff; split; [apply IH1|apply IH2]; repeat (first [exact Hv|exact Hs|assumption|reflexivity|split]).
  - cbn [stack_remove.comp stack_asm_name stack_asm_remove] in H1, H2 |- *; apply IH; repeat (first [exact Hv|exact Hs|assumption|reflexivity|split]).
  - destruct p; try contradiction; cbn [stack_remove.comp]; try exact H1.
    all: repeat (match goal with |- context [if ?b then _ else _] => destruct b eqn:? end);
         unfold stack_remove.stack_store, stack_remove.stack_load, stack_remove.copy_loop,
                stack_remove.copy_each; cbn [list_Seq stack_asm_name stack_asm_remove inst_name arith_name addr_name reg_imm_name]
           in H1, H2 |- *; sr_bnorm.
    all: repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end).
    all: try sr_leaf c k Hg Hv Hk Hk2 Hk0.
    all: try (match goal with |- (if ?m then _ else _) = true =>
                replace m with true by reflexivity; first [apply Hs|exact H0] end).
    all: try (match goal with H : implb (two_reg_arith ?cc) ?x = true |- implb (two_reg_arith ?cc) (?x || _) = true =>
                destruct (two_reg_arith cc); cbn [implb] in H |- *; [rewrite H; reflexivity|reflexivity] end).
    all: try (unfold stack_remove.upshift; apply asm_name_upshift_f; [exact Hv|assumption]).
    all: try (unfold stack_remove.downshift; apply asm_name_downshift_f; [exact Hv|assumption]).
    all: try (unfold stack_remove.stack_free; apply asm_name_stack_free_f; [exact Hv|assumption]).
    all: try (unfold stack_remove.stack_alloc; apply asm_name_stack_alloc_f; [exact Hv|assumption|
                apply (reg_name_mono c k); [exact Hk|lia]]).
Qed.


Lemma UPDATE_LIST_P {A B} `{EqDecision A} (P : B -> Prop) : forall (l : list (A * B)) (f : A -> B) x,
  (forall z, P (f z)) -> (forall z y, In (z, y) l -> P y) -> P (UPDATE_LIST f l x).
Proof.
  induction l as [|[z y] l IH]; intros f x Hf Hl; [apply Hf|].
  unfold UPDATE_LIST in *; cbn [FOLDL]. apply IH.
  - intros w. unfold combin.C, pair.UNCURRY; cbn. rewrite APPLY_UPDATE_THM.
    destruct (decide (z = w)); [apply (Hl z y); left; reflexivity|apply Hf].
  - intros w v Hin; apply (Hl w v); right; exact Hin.
Qed.

Lemma store_init_reg gen_gc k name :
  match @stack_remove.store_init a gen_gc k name with inl _ => True | inr i => i = k + 2 \/ i <= 7 end.
Proof.
  unfold stack_remove.store_init.
  apply (UPDATE_LIST_P (fun v : word a + N => match v with inl _ => True | inr i => i = k + 2 \/ i <= 7 end)).
  - intros z; exact Logic.I.
  - intros z y Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as _ <-; cbn beta iota;
              first [left; reflexivity|right; lia|destruct gen_gc; [left; reflexivity|right; lia]]|]).
    destruct Hin.
Qed.

Lemma asm_name_store_list_code (c : asm_config a) a0 t
    (Ha : reg_name a0 c = true) (Ht : reg_name t c = true)
    (Hbw : valid_imm c (inl asm.Add) bytes_in_word = true) (H0 : addr_offset_ok c (n2w 0) = true) :
  forall l, (forall i, In (inr i) l -> reg_name i c = true) ->
  stack_asm_name c (stack_remove.store_list_code a0 t l) = true.
Proof.
  induction l as [|[w|i] l IH]; intros Hl; [reflexivity| |];
    cbn [stack_remove.store_list_code list_Seq stack_asm_name inst_name arith_name addr_name reg_imm_name];
    repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end);
    try reflexivity; try assumption;
    try (apply IH; intros j Hj; apply Hl; right; exact Hj);
    try (apply Hl; left; reflexivity);
    try (replace (MEM Store [Load; Store; Load32; Store32]) with true by reflexivity; exact H0);
    try (destruct (two_reg_arith c); cbn [implb]; [|reflexivity];
         apply orb_true_iff; left; apply bool_decide_spec; reflexivity).
Qed.

Lemma asm_name_Seq (c : asm_config a) (p1 p2 : prog a) :
  stack_asm_name c (Seq p1 p2) = (stack_asm_name c p1 && stack_asm_name c p2)%bool.
Proof. reflexivity. Qed.

Lemma asm_name_init_code (c : asm_config a) gen_gc max_heap k
  (H0 : addr_offset_ok c (n2w 0) = true) (Hg : good_dimindex a) (Hv : forall n, n <= stack_remove.max_stack_alloc ->
     valid_imm c (inl asm.Sub) (n2w (n * (dimindex a DIV 8))) = true /\ valid_imm c (inl asm.Add) (n2w (n * (dimindex a DIV 8))) = true)
  (H4 : valid_imm c (inl asm.Add) (n2w 4) = true) (H8 : valid_imm c (inl asm.Add) (n2w 8) = true)
  (Hs : forall s, addr_offset_ok c (stack_remove.store_offset s) = true) (H7 : reg_name 7 c = true)
  (Hk2 : reg_name (k + 2) c = true) (Hk1 : reg_name (k + 1) c = true) (Hk : reg_name k c = true) (Hk0 : k <> 0) : stack_asm_name c (stack_remove.init_code gen_gc max_heap k) = true.
Proof.
  assert (Hbw : valid_imm c (inl asm.Add) bytes_in_word = true).
  { unfold bytes_in_word. destruct Hg as [E|E]; rewrite E; assumption. }
  assert (H7' : forall r, r <= 7 -> reg_name r c = true) by (intros r Hle; exact (reg_name_mono c 7 r H7 Hle)).
  rewrite init_code_unfold. rewrite !asm_name_Seq.
  repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end).
  all: try (apply asm_name_store_list_code; [exact Hk1|apply H7'; lia|exact Hbw|exact H0|];
            intros i Hin; apply in_map_iff in Hin as (nm & E & _);
            pose proof (store_init_reg gen_gc k nm) as R; rewrite E in R;
            destruct R as [->|Hle]; [exact Hk2|apply H7', Hle]).
  all: cbn [list_Seq stack_asm_name inst_name arith_name addr_name reg_imm_name].
  all: repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end).
  all: try sr_leaf c k Hg Hv Hk Hk2 Hk0.
  all: try (apply H7'; lia).
  all: try (apply N.ltb_lt; pose proof word_shift_small; pose proof (good_dimindex_ge Hg);
            rewrite w2n_n2w_small by first [exact Hg|lia]; lia).
  all: try (apply Bool.implb_true_iff; intros Hx; apply bool_decide_spec in Hx; exfalso; revert Hx;
       apply (n2w_small_ne0 Hg); pose proof word_shift_small; lia).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "stack_remove_stack_asm_name" *)
Theorem stack_remove_stack_asm_name : forall (c : asm_config a) jump gen_gc max_heap k start (prog0 : list (N * prog a)),
  EVERY (fun '(n, p) => stack_asm_name c p) prog0 /\ EVERY (fun '(n, p) => stack_asm_remove c p) prog0 /\
  addr_offset_ok c (n2w 0) /\ good_dimindex a /\
  (forall n, n <= stack_remove.max_stack_alloc ->
     valid_imm c (inl asm.Sub) (n2w (n * (dimindex a DIV 8))) /\
     valid_imm c (inl asm.Add) (n2w (n * (dimindex a DIV 8)))) /\
  valid_imm c (inl asm.Add) (n2w 4) /\ valid_imm c (inl asm.Add) (n2w 8) /\
  (forall s, addr_offset_ok c (stack_remove.store_offset s)) /\
  reg_name 7 c /\ reg_name (k + 2) c /\ reg_name (k + 1) c /\ reg_name k c /\ k <> 0 ->
  EVERY (fun '(n, p) => stack_asm_name c p)
    (stack_remove.compile jump (addr_offset c) gen_gc max_heap k start prog0).
Proof.
  intros c jump gen_gc max_heap k start prog0
    (Hn & Hr & H0 & Hg & Hv & H4 & H8 & Hs & H7 & Hk2 & Hk1 & Hk & Hk0); unfold is_true in *.
  unfold stack_remove.compile, stack_remove.init_stubs.
  cbn [app EVERY]. repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end).
  4: { induction prog0 as [|[n p] prog0 IH]; [reflexivity|].
       cbn [MAP map EVERY stack_remove.prog_comp] in Hn, Hr |- *.
       apply andb_true_iff in Hn as [Hn1 Hn2]; apply andb_true_iff in Hr as [Hr1 Hr2].
       apply andb_true_iff; split; [|apply IH; assumption].
       apply stack_remove_comp_stack_asm_name; repeat (first [exact Hv|exact Hs|assumption|reflexivity|split]). }
  - rewrite asm_name_Seq. apply andb_true_iff; split; [|reflexivity].
    apply asm_name_init_code; assumption.
  - unfold stack_remove.halt_inst. cbn [stack_asm_name inst_name].
    repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end); try reflexivity.
    apply (reg_name_mono c 7); [exact H7|lia].
  - unfold stack_remove.halt_inst. cbn [stack_asm_name inst_name].
    repeat (match goal with |- (_ && _) = true => apply andb_true_iff; split end); try reflexivity.
    apply (reg_name_mono c 7); [exact H7|lia].
Qed.

End AsmName.
