(** * CakeML [stack_namesProof]: correctness of [stack_names]

    Port of [cakeml/compiler/backend/proofs/stack_namesProofScript.sml].

    Notes:
    - HOL's [rename_state compile_rest f s] updates five fields; it is
      written with [stackSem]'s [set_*] helpers.  HOL's
      [(I ## compile f ## I)] ([##] associates to the right) is
      [I ## (stack_names.compile f ## I)].
    - [stack_names$compile] and [stack_names$comp] are written qualified
      ([compile] is also a field of the [stackSem] state).
    - HOL's [~s.use_alloc] is [~ use_alloc s] (the [is_true] coercion).
    - Proof method for [comp_correct]: well-founded induction on [eval_lt]
      ([stackSem]); the Galette-only helpers (rewriting lemmas that move
      [rename_state] outwards, lemmas on [GENLIST], tactics) have no HOL
      original.
    - Not yet ported: [comp_correct] and everything after it
      ([compile_semantics], [make_init_semantics], [stack_names_lab_pres],
      [names_ok_imp], the [stack_asm_ok] and [call_args] theorems). *)

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
From Galette.HOL.src.floating_point Require Import binary_ieee machine_ieee.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics Require fpSem ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang stack_names.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem backendProps stackProps.
Import wordLang (word_loc, Word, Loc).
Import wordSem (buffer, buffer_flush, buffer_write, gc_fun_type, mem_load_byte_aux,
  mem_store_byte_aux, mem_load_32, mem_store_32, write_bytearray).
Import stack_names (find_name, ri_find_name, inst_find_name, dest_find_name, prog_comp, names_ok).
Open Scope N_scope.

Section RenameState.
Context {a : N} {cfg_t ffi_t : Type}.
Implicit Types s : state a cfg_t ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "rename_state_def" *)
Definition rename_state (compile_rest : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t))
    (f : sptree.spt N) (s : state a cfg_t ffi_t) : state a cfg_t ffi_t :=
  set_ffi_save_regs (IMAGE (find_name f) (ffi_save_regs s))
    (set_compile_oracle ((I ## (stack_names.compile f ## I)) ∘ compile_oracle s)
      (set_compile compile_rest
        (set_code (sptree.fromAList (stack_names.compile f (sptree.toAList (code s))))
          (set_regs (MAP_KEYS (find_name f) (regs s)) s)))).

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "rename_state_with_clock" *)
Theorem rename_state_with_clock : forall c f s k,
  rename_state c f (set_clock k s) = set_clock k (rename_state c f s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "rename_state_const" *)
Theorem rename_state_const : forall c f s,
  memory (rename_state c f s) = memory s /\
  be (rename_state c f s) = be s /\
  mdomain (rename_state c f s) = mdomain s /\
  sh_mdomain (rename_state c f s) = sh_mdomain s /\
  code_buffer (rename_state c f s) = code_buffer s /\
  clock (rename_state c f s) = clock s /\
  compile (rename_state c f s) = c /\
  use_stack (rename_state c f s) = use_stack s /\
  fp_regs (rename_state c f s) = fp_regs s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "rename_state_with_memory" *)
Theorem rename_state_with_memory : forall c f s k,
  rename_state c f (set_memory k s) = set_memory k (rename_state c f s).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "dec_clock_rename_state" *)
Theorem dec_clock_rename_state : forall c x y,
  dec_clock (rename_state c x y) = rename_state c x (dec_clock y).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "mem_load_rename_state" *)
Theorem mem_load_rename_state : forall x c f s,
  mem_load x (rename_state c f s) = mem_load x s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "mem_store_rename_state" *)
Theorem mem_store_rename_state : forall x y c f s,
  mem_store x y (rename_state c f s) = OPTION_MAP (rename_state c f) (mem_store x y s).
Proof. intros; unfold mem_store; cbn. destruct (classical_dec _); reflexivity. Qed.

Lemma BIJ_INJ_UNIV (f : sptree.spt N) :
  BIJ (find_name f) UNIV UNIV -> INJ (find_name f) UNIV UNIV.
Proof. intros [H _]; exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "FLOOKUP_rename_state_find_name" *)
Theorem FLOOKUP_rename_state_find_name : forall f c s k,
  BIJ (find_name f) UNIV UNIV ->
  FLOOKUP (regs (rename_state c f s)) (find_name f k) = FLOOKUP (regs s) k.
Proof. intros f c s k HB; apply FLOOKUP_MAP_KEYS_MAPPED, BIJ_INJ_UNIV, HB. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "get_var_find_name" *)
Theorem get_var_find_name : forall f v c s,
  BIJ (find_name f) UNIV UNIV ->
  get_var (find_name f v) (rename_state c f s) = get_var v s.
Proof. intros f v c s HB; exact (FLOOKUP_rename_state_find_name f c s v HB). Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "get_var_imm_find_name" *)
Theorem get_var_imm_find_name : forall f ri c s,
  BIJ (find_name f) UNIV UNIV ->
  get_var_imm (ri_find_name f ri) (rename_state c f s) = get_var_imm ri s.
Proof. intros f [r|w] c s HB; [exact (get_var_find_name f r c s HB)|reflexivity]. Qed.

Lemma set_regs_rename (f : sptree.spt N) {V} (m : fmap N V) :
  BIJ (find_name f) UNIV UNIV -> forall x y,
  MAP_KEYS (find_name f) (m |+ (x, y)) = MAP_KEYS (find_name f) m |+ (find_name f x, y).
Proof.
  intros HB x y; apply MAP_KEYS_FUPDATE.
  destruct (BIJ_INJ_UNIV f HB) as [_ HI]; split; [intros; exact Logic.I|].
  intros u v _; apply HI; split; exact Logic.I.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "set_var_find_name" *)
Theorem set_var_find_name : forall f c x y z,
  BIJ (find_name f) UNIV UNIV ->
  rename_state c f (set_var x y z) = set_var (find_name f x) y (rename_state c f z).
Proof.
  intros f c x y z HB; unfold rename_state, set_var; cbn.
  rewrite (set_regs_rename f _ HB); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "set_fp_var_find_name" *)
Theorem set_fp_var_find_name : forall c f x y z,
  rename_state c f (set_fp_var x y z) = set_fp_var x y (rename_state c f z).
Proof. reflexivity. Qed.

Ltac sh_rename :=
  intros f c x y s HB;
  unfold sh_mem_load, sh_mem_store, sh_mem_load_byte, sh_mem_store_byte,
    sh_mem_load16, sh_mem_store16, sh_mem_load32, sh_mem_store32;
  rewrite ?(get_var_find_name f x c s HB);
  cbn [sh_mdomain ffi set_ffi set_regs rename_state set_ffi_save_regs set_compile_oracle
       set_compile set_code ffi_save_regs regs compile_oracle code];
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x eqn:?; cbn beta iota zeta
         end; try reflexivity;
  unfold rename_state; cbn; rewrite ?(set_regs_rename f _ HB); reflexivity.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_load_rename_state" *)
Theorem sh_mem_load_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_load (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_load x y s), rename_state c f (SND (sh_mem_load x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_store_rename_state" *)
Theorem sh_mem_store_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_store (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_store x y s), rename_state c f (SND (sh_mem_store x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_load_byte_rename_state" *)
Theorem sh_mem_load_byte_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_load_byte (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_load_byte x y s), rename_state c f (SND (sh_mem_load_byte x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_store_byte_rename_state" *)
Theorem sh_mem_store_byte_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_store_byte (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_store_byte x y s), rename_state c f (SND (sh_mem_store_byte x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_load16_rename_state" *)
Theorem sh_mem_load16_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_load16 (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_load16 x y s), rename_state c f (SND (sh_mem_load16 x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_store16_rename_state" *)
Theorem sh_mem_store16_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_store16 (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_store16 x y s), rename_state c f (SND (sh_mem_store16 x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_load32_rename_state" *)
Theorem sh_mem_load32_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_load32 (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_load32 x y s), rename_state c f (SND (sh_mem_load32 x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_store32_rename_state" *)
Theorem sh_mem_store32_rename_state : forall f c x y s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_store32 (find_name f x) y (rename_state c f s) =
  (FST (sh_mem_store32 x y s), rename_state c f (SND (sh_mem_store32 x y s))).
Proof. sh_rename. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "sh_mem_op_rename_store" *)
Theorem sh_mem_op_rename_store : forall f op r ad c s,
  BIJ (find_name f) UNIV UNIV ->
  sh_mem_op op (find_name f r) ad (rename_state c f s) =
  (FST (sh_mem_op op r ad s), rename_state c f (SND (sh_mem_op op r ad s))).
Proof.
  intros f op r ad c s HB; destruct op; cbn [sh_mem_op].
  - apply sh_mem_load_rename_state, HB.
  - apply sh_mem_load_byte_rename_state, HB.
  - apply sh_mem_load16_rename_state, HB.
  - apply sh_mem_load32_rename_state, HB.
  - apply sh_mem_store_rename_state, HB.
  - apply sh_mem_store_byte_rename_state, HB.
  - apply sh_mem_store16_rename_state, HB.
  - apply sh_mem_store32_rename_state, HB.
Qed.

End RenameState.

Section Code.
Context {a : N} {cfg_t ffi_t : Type}.
Implicit Types s : state a cfg_t ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "prog_comp_eta" *)
Local Theorem prog_comp_eta : forall f,
  @prog_comp a f = fun '(x, y) => (x, stack_names.comp f y).
Proof. reflexivity. Qed.

Lemma lookup_rename_code f (cd : sptree.spt (prog a)) p :
  sptree.lookup p (sptree.fromAList (stack_names.compile f (sptree.toAList cd))) =
  OPTION_MAP (stack_names.comp f) (sptree.lookup p cd).
Proof.
  rewrite sptree.lookup_fromAList; unfold stack_names.compile; rewrite prog_comp_eta.
  rewrite ALOOKUP_MAP; cbn; rewrite sptree.ALOOKUP_toAList; reflexivity.
Qed.

Lemma find_code_rename_gen f dest (m : fmap N (word_loc a)) cd :
  BIJ (find_name f) UNIV UNIV ->
  find_code (dest_find_name f dest) (MAP_KEYS (find_name f) m)
    (sptree.fromAList (stack_names.compile f (sptree.toAList cd))) =
  OPTION_MAP (stack_names.comp f) (find_code dest m cd).
Proof.
  intros HB; destruct dest as [p|r]; cbn [dest_find_name find_code].
  - apply lookup_rename_code.
  - rewrite FLOOKUP_MAP_KEYS_MAPPED by apply BIJ_INJ_UNIV, HB.
    destruct (FLOOKUP m r) as [[w|l n]|]; try reflexivity.
    destruct (n =? 0); [apply lookup_rename_code|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "find_code_rename_state" *)
Theorem find_code_rename_state : forall f dest c s,
  BIJ (find_name f) UNIV UNIV ->
  find_code (dest_find_name f dest) (regs (rename_state c f s)) (code (rename_state c f s)) =
  OPTION_MAP (stack_names.comp f) (find_code dest (regs s) (code s)).
Proof. intros; apply find_code_rename_gen; assumption. Qed.

Lemma FLOOKUP_rename_regs f c s r :
  BIJ (find_name f) UNIV UNIV ->
  FLOOKUP (regs (rename_state c f s)) (find_name f r) = FLOOKUP (regs s) r.
Proof. apply FLOOKUP_rename_state_find_name. Qed.

Lemma bool_decide_iff (P Q : Prop) `{Decision P} `{Decision Q} :
  (P <-> Q) -> bool_decide P = bool_decide Q.
Proof.
  intros E; destruct (bool_decide P) eqn:E1; destruct (bool_decide Q) eqn:E2; try reflexivity.
  - apply bool_decide_spec in E1. pose proof (proj2 (bool_decide_spec Q) (proj1 E E1)); congruence.
  - apply bool_decide_spec in E2. pose proof (proj2 (bool_decide_spec P) (proj2 E E2)); congruence.
Qed.

Lemma Reg_find_name_eq f x y :
  BIJ (find_name f) UNIV UNIV ->
  bool_decide (@Reg a (find_name f x) = Reg (find_name f y)) = bool_decide (@Reg a x = Reg y).
Proof.
  intros HB; apply bool_decide_iff; split; intros E; injection E as E; f_equal; [|congruence].
  destruct HB as [[_ HI] _]; apply HI; [split; exact Logic.I|exact E].
Qed.

Lemma Imm_Reg_false (w : word a) r : bool_decide (@Imm a w = Reg r) = false.
Proof. destruct (bool_decide _) eqn:E; [apply bool_decide_spec in E; discriminate|reflexivity]. Qed.

Lemma rename_fields c f s :
  memory (rename_state c f s) = memory s /\ mdomain (rename_state c f s) = mdomain s /\ be (rename_state c f s) = be s /\ fp_regs (rename_state c f s) = fp_regs s.
Proof. repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "inst_rename" *)
Theorem inst_rename : forall f i c s,
  BIJ (find_name f) UNIV UNIV ->
  inst (inst_find_name f i) (rename_state c f s) = OPTION_MAP (rename_state c f) (inst i s).
Proof.
  intros f i c s HB.
  destruct i as [| | x | m r [ad w] | fp0]; [| | destruct x as [? ? ? ri|? ? ? ri| | | | | |] |
    destruct m | destruct fp0];
    try (destruct ri);
    cbn [inst inst_find_name ri_find_name]; unfold assign;
    cbn [word_exp get_vars wordLang.word_op MAP EVERY IS_SOME THE];
    unfold get_var, get_fp_var;
    destruct (rename_fields c f s) as (Fm & Fd & Fb & Ff);
    rewrite ?(FLOOKUP_rename_regs f c s _ HB), ?(Reg_find_name_eq f _ _ HB), ?Imm_Reg_false,
      ?Fm, ?Fd, ?Fb, ?Ff; try reflexivity;
    repeat (rewrite ?mem_store_rename_state, ?mem_load_rename_state; cbn [option_map];
            match goal with
            | |- context [match ?x with _ => _ end] => destruct x eqn:?; cbn beta iota zeta
            end);
    cbn [option_map]; try reflexivity;
    rewrite ?(set_var_find_name f c _ _ _ HB); try reflexivity;
    try (match goal with E : mem_store _ _ _ = _ |- _ => rewrite E end; reflexivity);
    cbn [option_map] in *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "MAP_FST_compile" *)
Theorem MAP_FST_compile : forall f (c : list (N * prog a)),
  MAP FST (stack_names.compile f c) = MAP FST c.
Proof.
  intros f c; unfold stack_names.compile; rewrite map_map; apply map_ext; intros [x y]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "domain_rename_state_code" *)
Theorem domain_rename_state_code : forall c f s,
  sptree.domain (code (rename_state c f s)) = sptree.domain (code s).
Proof.
  intros c f s; apply functional_extensionality; intros k; apply propositional_extensionality.
  rewrite !sptree.domain_lookup; cbn [code rename_state set_ffi_save_regs set_compile_oracle
    set_compile set_code]. rewrite lookup_rename_code.
  destruct (sptree.lookup k (code s)); cbn; split; intros [v H]; eauto; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "comp_STOP_Loop" *)
Local Theorem comp_STOP_Loop : forall f (c1 : prog a),
  stack_names.comp f (STOP (Loop c1)) = STOP (Loop (stack_names.comp f c1)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "get_labels_comp" *)
Local Theorem get_labels_comp : forall f (p : prog a),
  get_labels (stack_names.comp f p) = get_labels p.
Proof.
  intros f; fix IH 1; intros p; destruct p; cbn [stack_names.comp get_labels]; try reflexivity;
    repeat (match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x end;
            cbn [get_labels]);
    rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "loc_check_rename_state" *)
Local Theorem loc_check_rename_state : forall c f s l1 l2,
  loc_check (code (rename_state c f s)) (l1, l2) = loc_check (code s) (l1, l2).
Proof.
  intros c f s l1 l2; unfold loc_check.
  rewrite domain_rename_state_code. cbn [code rename_state set_ffi_save_regs set_compile_oracle
    set_compile set_code].
  apply propositional_extensionality. setoid_rewrite lookup_rename_code.
  split; (intros [H|[n [e [He Hl]]]]; [left; exact H|right]).
  - destruct (sptree.lookup n (code s)) as [e0|] eqn:E; [|discriminate].
    injection He as <-. rewrite get_labels_comp in Hl. eauto.
  - exists n, (stack_names.comp f e); rewrite He, get_labels_comp; split; [reflexivity|exact Hl].
Qed.

End Code.

(** ** Correctness of [comp] *)

Lemma bool_decide_Some_None {A} (x : A) {d : Decision (Some x = None)} :
  @bool_decide (Some x = None) d = false.
Proof. destruct (bool_decide _) eqn:E; [apply bool_decide_spec in E; discriminate|reflexivity]. Qed.

Lemma bool_decide_None_None {A} {d : Decision (@None A = None)} :
  @bool_decide (@None A = None) d = true.
Proof. apply bool_decide_spec; reflexivity. Qed.

Section Correct.
Context {a : N} {cfg_t ffi_t : Type} (f : sptree.spt N)
  (c : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t))
  (HB : BIJ (find_name f) UNIV UNIV).
Implicit Types s : state a cfg_t ffi_t.

Local Abbreviation rn := (rename_state c f).

(** Galette-only rewriting lemmas moving [rename_state] outwards. *)
Lemma R_use_alloc s : use_alloc (rn s) = use_alloc s. Proof. reflexivity. Qed.
Lemma R_use_store s : use_store (rn s) = use_store s. Proof. reflexivity. Qed.
Lemma R_use_stack s : use_stack (rn s) = use_stack s. Proof. reflexivity. Qed.
Lemma R_clock s : clock (rn s) = clock s. Proof. reflexivity. Qed.
Lemma R_memory s : memory (rn s) = memory s. Proof. reflexivity. Qed.
Lemma R_mdomain s : mdomain (rn s) = mdomain s. Proof. reflexivity. Qed.
Lemma R_sh_mdomain s : sh_mdomain (rn s) = sh_mdomain s. Proof. reflexivity. Qed.
Lemma R_be s : be (rn s) = be s. Proof. reflexivity. Qed.
Lemma R_ffi s : ffi (rn s) = ffi s. Proof. reflexivity. Qed.
Lemma R_stack s : stack (rn s) = stack s. Proof. reflexivity. Qed.
Lemma R_stack_space s : stack_space (rn s) = stack_space s. Proof. reflexivity. Qed.
Lemma R_bitmaps s : bitmaps (rn s) = bitmaps s. Proof. reflexivity. Qed.
Lemma R_store s : store (rn s) = store s. Proof. reflexivity. Qed.
Lemma R_fp_regs s : fp_regs (rn s) = fp_regs s. Proof. reflexivity. Qed.
Lemma R_code_buffer s : code_buffer (rn s) = code_buffer s. Proof. reflexivity. Qed.
Lemma R_data_buffer s : data_buffer (rn s) = data_buffer s. Proof. reflexivity. Qed.
Lemma R_compile s : compile (rn s) = c. Proof. reflexivity. Qed.
Lemma R_get_var v s : get_var (find_name f v) (rn s) = get_var v s.
Proof. apply get_var_find_name, HB. Qed.
Lemma R_get_var_imm ri s : get_var_imm (ri_find_name f ri) (rn s) = get_var_imm ri s.
Proof. apply get_var_imm_find_name, HB. Qed.
Lemma R_FLOOKUP k s : FLOOKUP (regs (rn s)) (find_name f k) = FLOOKUP (regs s) k.
Proof. apply FLOOKUP_rename_state_find_name, HB. Qed.
Lemma R_inst i s : inst (inst_find_name f i) (rn s) = OPTION_MAP rn (inst i s).
Proof. apply inst_rename, HB. Qed.
Lemma R_find_code dest s :
  find_code (dest_find_name f dest) (regs (rn s)) (code (rn s)) =
  OPTION_MAP (stack_names.comp f) (find_code dest (regs s) (code s)).
Proof. apply find_code_rename_state, HB. Qed.
Lemma R_find_code_inl dest s :
  find_code (inl dest) (regs (rn s)) (code (rn s)) =
  OPTION_MAP (stack_names.comp f) (find_code (inl dest) (regs s) (code s)).
Proof. exact (R_find_code (inl dest) s). Qed.
Lemma R_find_code_domsub dest lr s :
  find_code (dest_find_name f dest) (regs (rn s) \\ find_name f lr) (code (rn s)) =
  OPTION_MAP (stack_names.comp f) (find_code dest (regs s \\ lr) (code s)).
Proof.
  cbn [regs code rename_state set_ffi_save_regs set_compile_oracle set_compile set_code set_regs].
  rewrite DOMSUB_MAP_KEYS by exact HB. apply find_code_rename_gen, HB.
Qed.
Lemma R_lookup p s :
  sptree.lookup p (code (rn s)) = OPTION_MAP (stack_names.comp f) (sptree.lookup p (code s)).
Proof. apply lookup_rename_code. Qed.
Lemma R_dest_Seq (p : prog a) :
  dest_Seq (stack_names.comp f p) =
  OPTION_MAP (fun '(x, y) => (stack_names.comp f x, stack_names.comp f y)) (dest_Seq p).
Proof.
  destruct p; try reflexivity; match goal with x : addr _ |- _ => destruct x; reflexivity end.
Qed.
Lemma R_oracle s :
  compile_oracle (rn s) = (I ## (stack_names.compile f ## I)) ∘ compile_oracle s.
Proof. reflexivity. Qed.
Lemma R_compile_nil : stack_names.compile f ([] : list (N * prog a)) = [].
Proof. reflexivity. Qed.
Lemma R_compile_cons k (p : prog a) l :
  stack_names.compile f ((k, p) :: l) = (k, stack_names.comp f p) :: stack_names.compile f l.
Proof. reflexivity. Qed.
Lemma R_shift_FST k i (o : N -> cfg_t * (list (N * prog a) * list (word a))) :
  FST (shift_seq k ((I ## (stack_names.compile f ## I)) ∘ o) i) = FST (shift_seq k o i).
Proof. unfold shift_seq; cbn. destruct (o (i + k)) as [x [y z]]; reflexivity. Qed.
Lemma code_union_rename (cd : sptree.spt (prog a)) k p l :
  sptree.union (sptree.fromAList (stack_names.compile f (sptree.toAList cd)))
    (sptree.fromAList ((k, stack_names.comp f p) :: stack_names.compile f l)) =
  sptree.fromAList (stack_names.compile f
    (sptree.toAList (sptree.union cd (sptree.fromAList ((k, p) :: l))))).
Proof.
  apply sptree.spt_eq_thm.
  { split; [apply sptree.wf_union; split|]; apply sptree.wf_fromAList. }
  intros n. rewrite sptree.lookup_union, !lookup_rename_code, sptree.lookup_union.
  change ((k, stack_names.comp f p) :: stack_names.compile f l)
    with (stack_names.compile f ((k, p) :: l)).
  rewrite !sptree.lookup_fromAList. unfold stack_names.compile at 1.
  rewrite prog_comp_eta, ALOOKUP_MAP; cbn.
  destruct (sptree.lookup n cd); reflexivity.
Qed.
Lemma R_dec_clock s : dec_clock (rn s) = rn (dec_clock s). Proof. reflexivity. Qed.
Lemma R_set_var x y s : set_var (find_name f x) y (rn s) = rn (set_var x y s).
Proof. symmetry; apply set_var_find_name, HB. Qed.
Lemma R_empty_env s : empty_env (rn s) = rn (empty_env s).
Proof. unfold rename_state, empty_env; cbn. rewrite MAP_KEYS_FEMPTY; reflexivity. Qed.
Lemma R_loc_check s l1 l2 : loc_check (code (rn s)) (l1, l2) = loc_check (code s) (l1, l2).
Proof. apply loc_check_rename_state. Qed.
Lemma R_sh_mem_op op r ad s :
  sh_mem_op op (find_name f r) ad (rn s) = (FST (sh_mem_op op r ad s), rn (SND (sh_mem_op op r ad s))).
Proof. apply sh_mem_op_rename_store, HB. Qed.
Lemma R_word_exp_addr ad w s :
  word_exp (rn s) (wordLang.Op asm.Add [wordLang.Var (find_name f ad); wordLang.Const w]) =
  word_exp s (wordLang.Op asm.Add [wordLang.Var ad; wordLang.Const w]).
Proof. cbn [word_exp List.map]; rewrite R_FLOOKUP; reflexivity. Qed.
Lemma R_ffi_state x m s :
  set_ffi x (set_fp_regs FEMPTY (set_regs (DRESTRICT (regs (rn s)) (ffi_save_regs (rn s)))
    (set_memory m (rn s)))) =
  rn (set_ffi x (set_fp_regs FEMPTY (set_regs (DRESTRICT (regs s) (ffi_save_regs s)) (set_memory m s)))).
Proof.
  unfold rename_state; cbn. rewrite DRESTRICT_MAP_KEYS_IMAGE by apply BIJ_INJ_UNIV, HB.
  reflexivity.
Qed.

Create HintDb snr.
Hint Rewrite R_use_alloc R_use_store R_use_stack R_clock R_memory R_mdomain R_sh_mdomain R_be
  R_ffi R_stack R_stack_space R_bitmaps R_store R_fp_regs R_code_buffer R_data_buffer R_compile
  R_get_var R_get_var_imm R_FLOOKUP R_inst R_find_code R_find_code_inl R_find_code_domsub R_lookup
  R_dest_Seq R_oracle R_shift_FST R_compile_nil R_compile_cons R_dec_clock R_set_var R_empty_env R_loc_check R_sh_mem_op R_word_exp_addr R_ffi_state
  @bool_decide_Some_None @bool_decide_None_None : snr.

Definition sn_ok s : Prop :=
  use_alloc s = false /\ use_store s = false /\ use_stack s = false /\
  compile s = (fun cfg => c cfg ∘ stack_names.compile f).

Ltac sn_solve_ok :=
  unfold sn_ok in *; stk_fields; destruct_ands; repeat split; congruence.

Ltac sn_loop IH H :=
  repeat first
    [ progress (rewrite ?fix_clock_evaluate in H)
    | progress (autorewrite with snr; cbn [option_map PAIR_MAP I FST SND fst snd];
                cbn beta iota zeta)
    | progress (unfold STOP in * )
    | progress (rewrite ?bool_decide_Some_None, ?bool_decide_None_None in H; cbn [negb] in H)
    | progress (rewrite ?fix_clock_evaluate)
    | match goal with
      | E : fix_clock _ (evaluate _) = _ |- _ => rewrite fix_clock_evaluate in E
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in let Hk := fresh "Hk" in let Hi := fresh "Hi" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          pose proof (evaluate_consts p' s'' r' t E) as Hk;
          assert (Hi : evaluate (stack_names.comp f p', rn s'') = (r', rn t))
            by (apply (IH (p', s'') ltac:(stk_eval_lt) r' t E); sn_solve_ok);
          clear E; cbn [stack_names.comp] in Hi;
          try (rewrite Hi; cbn beta iota zeta)
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H |- *
      end ].

End Correct.
