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
