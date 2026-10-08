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
    - [comp_correct] and the theorems after it are stated outside the
      section, quantifying HOL's free [f] and [c] explicitly. *)

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
(** Galette-only: equality of [stackSem] states field by field (avoids
    unfolding nested record updates, whose normal forms are huge). *)
Lemma state_ext s t :
  regs s = regs t -> fp_regs s = fp_regs t -> store s = store t -> stack s = stack t ->
  stack_space s = stack_space t -> memory s = memory t -> mdomain s = mdomain t ->
  sh_mdomain s = sh_mdomain t -> bitmaps s = bitmaps t -> compile s = compile t ->
  compile_oracle s = compile_oracle t -> code_buffer s = code_buffer t ->
  data_buffer s = data_buffer t -> gc_fun s = gc_fun t -> use_stack s = use_stack t ->
  use_store s = use_store t -> use_alloc s = use_alloc t -> clock s = clock t ->
  code s = code t -> ffi s = ffi t -> ffi_save_regs s = ffi_save_regs t -> be s = be t ->
  s = t.
Proof. destruct s, t; cbn; intros; subst; reflexivity. Qed.

Lemma R_install_state s cb db bm ptr k p l :
  set_compile_oracle (shift_seq 1 ((I ## (stack_names.compile f ## I)) ∘ compile_oracle s))
    (set_fp_regs FEMPTY
      (set_regs (DRESTRICT (regs (rn s)) (ffi_save_regs (rn s)) |+ (find_name f ptr, Loc k 0))
        (set_code (sptree.union (code (rn s))
                     (sptree.fromAList ((k, stack_names.comp f p) :: stack_names.compile f l)))
          (set_data_buffer db (set_code_buffer cb (set_bitmaps bm (rn s))))))) =
  rn (set_compile_oracle (shift_seq 1 (compile_oracle s))
    (set_fp_regs FEMPTY
      (set_regs (DRESTRICT (regs s) (ffi_save_regs s) |+ (ptr, Loc k 0))
        (set_code (sptree.union (code s) (sptree.fromAList ((k, p) :: l)))
          (set_data_buffer db (set_code_buffer cb (set_bitmaps bm s))))))).
Proof.
  apply state_ext; cbn [regs fp_regs store stack stack_space memory mdomain sh_mdomain bitmaps compile compile_oracle code_buffer data_buffer gc_fun use_stack use_store use_alloc clock code ffi ffi_save_regs be rename_state set_compile_oracle set_fp_regs set_regs set_code set_data_buffer set_code_buffer set_bitmaps set_ffi_save_regs set_compile].
  1: rewrite (set_regs_rename f _ HB), DRESTRICT_MAP_KEYS_IMAGE by apply BIJ_INJ_UNIV, HB;
     reflexivity.
  18: rewrite code_union_rename; reflexivity.
  all: reflexivity.
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
  R_dest_Seq R_oracle R_shift_FST R_install_state R_compile_nil R_compile_cons R_dec_clock R_set_var R_empty_env R_loc_check R_sh_mem_op R_word_exp_addr R_ffi_state
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

Lemma comp_correct_gen : forall (x : prog a * state a cfg_t ffi_t) r t,
  evaluate x = (r, t) -> sn_ok (snd x) ->
  evaluate (stack_names.comp f (fst x), rn (snd x)) = (r, rn t).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hok; cbn [fst snd] in *.
  pose proof Hok as (Hua & Hus & Hust & Hcomp).
  rewrite evaluate_eqn in H |- *.
  destruct p;
    repeat match goal with o : option (prog _ * _) |- _ => destruct o end;
    repeat match goal with q : (_ * _)%type |- _ => destruct q end;
    repeat match goal with ad : addr _ |- _ => destruct ad end;
    cbn [stack_names.comp]; cbn [evaluate_body] in H |- *; cbn [STOP] in H |- *;
    rewrite ?Hua, ?Hus, ?Hust, ?Hcomp in H; cbn [negb orb andb] in H; cbn beta iota zeta in H;
    autorewrite with snr; rewrite ?Hua, ?Hus, ?Hust; cbn [negb orb andb]; cbn beta iota zeta;
    sn_loop IH H;
    try (injection H as <- <-; reflexivity);
    try (match goal with E : sh_mem_op _ _ _ _ = _ |- _ => rewrite E; reflexivity end);
    try reflexivity.
Qed.

End Correct.

(** Galette-only: [semantics] only depends on the results and FFI states
    of the runs of the start call. *)
Lemma semantics_eq_of_evaluate {a : N} {c1 c2 ffi_t : Type} (start : N)
    (s1 : state a c1 ffi_t) (s2 : state a c2 ffi_t) (g : state a c2 ffi_t -> state a c1 ffi_t) :
  (forall k, evaluate (Call NONE (inl start) NONE, set_clock k s1) =
             let '(r, t) := evaluate (Call NONE (inl start) NONE, set_clock k s2) in (r, g t)) ->
  (forall t, ffi (g t) = ffi t) ->
  semantics start s1 = semantics start s2.
Proof.
  intros H Hg. unfold semantics; cbv zeta.
  assert (HF : forall k, FST (evaluate (Call NONE (inl start) NONE, set_clock k s1)) =
                         FST (evaluate (Call NONE (inl start) NONE, set_clock k s2))).
  { intros k; rewrite H; destruct (evaluate (Call NONE (inl start) NONE, set_clock k s2)); reflexivity. }
  assert (HI : forall k, ffi (SND (evaluate (Call NONE (inl start) NONE, set_clock k s1))) =
                         ffi (SND (evaluate (Call NONE (inl start) NONE, set_clock k s2)))).
  { intros k; rewrite H; destruct (evaluate (Call NONE (inl start) NONE, set_clock k s2)); apply Hg. }
  assert (E1 : (exists k, FST (evaluate (Call NONE (inl start) NONE, set_clock k s1)) <> SOME TimeOut /\
                 FST (evaluate (Call NONE (inl start) NONE, set_clock k s1)) <> SOME (Result (Loc 1 0)) /\
                 (forall w, FST (evaluate (Call NONE (inl start) NONE, set_clock k s1)) <> SOME (Halt (Word w))) /\
                 (forall f, FST (evaluate (Call NONE (inl start) NONE, set_clock k s1)) <> SOME (FinalFFI f))) =
               (exists k, FST (evaluate (Call NONE (inl start) NONE, set_clock k s2)) <> SOME TimeOut /\
                 FST (evaluate (Call NONE (inl start) NONE, set_clock k s2)) <> SOME (Result (Loc 1 0)) /\
                 (forall w, FST (evaluate (Call NONE (inl start) NONE, set_clock k s2)) <> SOME (Halt (Word w))) /\
                 (forall f, FST (evaluate (Call NONE (inl start) NONE, set_clock k s2)) <> SOME (FinalFFI f)))).
  { apply propositional_extensionality; split; intros [k Hk]; exists k; rewrite ?HF in *; rewrite <- ?HF in *; exact Hk. }
  rewrite E1. destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?P1 with _ => _ end = match some ?P2 with _ => _ end =>
    assert (EP : P1 = P2) end.
  { apply functional_extensionality; intros res; apply propositional_extensionality; split.
    - intros (k & t & r & o & He & Hm & ->).
      rewrite H in He. destruct (evaluate (Call NONE (inl start) NONE, set_clock k s2)) as [r2 t2] eqn:E2.
      injection He as -> <-. exists k, t2, r, o; rewrite Hg; auto.
    - intros (k & t & r & o & He & Hm & ->).
      exists k, (g t), r, o; rewrite H, He, Hg; auto. }
  rewrite EP. destruct (some _); [reflexivity|].
  f_equal; f_equal; f_equal; apply functional_extensionality; intros k; rewrite HI; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "comp_correct" *)
Theorem comp_correct {a : N} {cfg_t ffi_t : Type} (f : sptree.spt N)
    (c : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t)) :
  forall p (s : state a cfg_t ffi_t) r t,
    evaluate (p, s) = (r, t) /\ BIJ (find_name f) UNIV UNIV /\
    ~ use_alloc s /\ ~ use_store s /\ ~ use_stack s /\
    compile s = (fun cfg => c cfg ∘ stack_names.compile f) ->
    evaluate (stack_names.comp f p, rename_state c f s) = (r, rename_state c f t).
Proof.
  intros p s r t (H & HB & H1 & H2 & H3 & H4).
  apply (comp_correct_gen f c HB (p, s)); [exact H|].
  unfold sn_ok; repeat split; try assumption; apply not_true_is_false; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "compile_semantics" *)
Theorem compile_semantics {a : N} {cfg_t ffi_t : Type} (f : sptree.spt N)
    (c : cfg_t -> list (N * prog a) -> option (list word8 * cfg_t))
    (s : state a cfg_t ffi_t) start :
  BIJ (find_name f) UNIV UNIV /\
  ~ use_alloc s /\ ~ use_store s /\ ~ use_stack s /\
  compile s = (fun cfg => c cfg ∘ stack_names.compile f) ->
  semantics start (rename_state c f s) = semantics start s.
Proof.
  intros (HB & H1 & H2 & H3 & H4).
  apply (semantics_eq_of_evaluate start _ _ (rename_state c f)); [|reflexivity].
  intros k. destruct (evaluate (Call NONE (inl start) NONE, set_clock k s)) as [r t] eqn:E.
  rewrite <- rename_state_with_clock.
  exact (comp_correct f c (Call NONE (inl start) NONE) (set_clock k s) r t
           (conj E (conj HB (conj H1 (conj H2 (conj H3 H4)))))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "compile_semantics_alt" *)
Theorem compile_semantics_alt {a : N} {cfg_t ffi_t : Type} (f : sptree.spt N) start :
  forall (s t : state a cfg_t ffi_t),
    BIJ (find_name f) UNIV UNIV /\ rename_state (compile t) f s = t /\
    compile s = (fun c0 => compile t c0 ∘ stack_names.compile f) /\
    ~ use_alloc s /\ ~ use_store s /\ ~ use_stack s ->
    semantics start t = semantics start s.
Proof.
  intros s t (HB & Ht & Hc & H1 & H2 & H3).
  rewrite <- Ht at 1. apply compile_semantics; exact (conj HB (conj H1 (conj H2 (conj H3 Hc)))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "make_init_def" *)
Definition make_init {a : N} {cfg_t ffi_t : Type} (f : sptree.spt N) (code0 : sptree.spt (prog a))
    (oracle : N -> cfg_t * (list (N * prog a) * list (word a))) (s : state a cfg_t ffi_t)
    : state a cfg_t ffi_t :=
  set_ffi_save_regs (IMAGE (LINV (find_name f) UNIV) (ffi_save_regs s))
    (set_compile_oracle oracle
      (set_compile (fun cfg => compile s cfg ∘ stack_names.compile f)
        (set_regs (MAP_KEYS (LINV (find_name f) UNIV) (regs s))
          (set_code code0 s)))).

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "make_init_semantics" *)
Theorem make_init_semantics {a : N} {cfg_t ffi_t : Type} (f : sptree.spt N)
    (code0 : list (N * prog a)) (oracle : N -> cfg_t * (list (N * prog a) * list (word a)))
    (s : state a cfg_t ffi_t) start :
  ~ use_alloc s /\ ~ use_store s /\ ~ use_stack s /\
  BIJ (find_name f) UNIV UNIV /\ ALL_DISTINCT (MAP FST code0) /\
  code s = sptree.fromAList (stack_names.compile f code0) /\
  compile_oracle s = (I ## (stack_names.compile f ## I)) ∘ oracle ->
  semantics start s = semantics start (make_init f (sptree.fromAList code0) oracle s).
Proof.
  intros (H1 & H2 & H3 & HB & _ & Hc & Ho).
  apply (compile_semantics_alt f); split; [exact HB|]. split;
    [|split; [reflexivity|cbn [use_alloc use_store use_stack make_init set_ffi_save_regs
       set_compile_oracle set_compile set_regs set_code]; exact (conj H1 (conj H2 H3))]].
  unfold make_init, rename_state.
  apply state_ext; cbn [regs fp_regs store stack stack_space memory mdomain sh_mdomain bitmaps compile
       compile_oracle code_buffer data_buffer gc_fun use_stack use_store use_alloc clock code
       ffi ffi_save_regs be set_ffi_save_regs set_compile_oracle set_compile set_regs set_code];
    try reflexivity.
  - apply MAP_KEYS_BIJ_LINV, HB.
  - symmetry; exact Ho.
  - rewrite Hc. apply sptree.spt_eq_thm; [split; apply sptree.wf_fromAList|]. intros n.
    rewrite lookup_rename_code, !sptree.lookup_fromAList.
    unfold stack_names.compile; rewrite prog_comp_eta, ALOOKUP_MAP_2. reflexivity.
  - rewrite <- IMAGE_COMPOSE.
    replace (find_name f ∘ LINV (find_name f) UNIV) with (fun x : N => x); [apply IMAGE_ID|].
    apply functional_extensionality; intros x; symmetry; apply (BIJ_LINV_INV _ _ _ HB); exact Logic.I.
Qed.

Ltac sn_get_addr := repeat match goal with ad : addr _ |- _ => destruct ad end.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "stack_names_lab_pres" *)
Theorem stack_names_lab_pres {a : N} : forall f (p : prog a),
  extract_labels p = extract_labels (stack_names.comp f p).
Proof.
  intros f p; induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind.
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [|reflexivity].
    destruct h as [[p2 [l1' l2']]|]; cbn [stack_names.comp extract_labels];
      rewrite <- (Hr p1 _ eq_refl); try rewrite <- (Hh p2 _ eq_refl); reflexivity.
  - cbn [stack_names.comp extract_labels]; rewrite IH1, IH2; reflexivity.
  - cbn [stack_names.comp extract_labels]; rewrite IH1, IH2; reflexivity.
  - cbn [stack_names.comp extract_labels]; exact IH.
  - destruct p; try contradiction; sn_get_addr; reflexivity.
Qed.

Lemma bd_find_name f (x y : N) :
  bool_decide (x = y) = true -> bool_decide (find_name f x = find_name f y) = true.
Proof. rewrite !bool_decide_spec; intros ->; reflexivity. Qed.

Lemma call_args_comp {a : N} f : forall (p : prog a) ptr len ptr2 len2 ret,
  call_args p ptr len ptr2 len2 ret = true ->
  call_args (stack_names.comp f p) (find_name f ptr) (find_name f len) (find_name f ptr2)
    (find_name f len2) (find_name f ret) = true.
Proof.
  intros p; induction p as [ret0 dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros ptr len ptr2 len2 ret H.
  - destruct ret0 as [[p1 [lr [l1 l2]]]|]; [|reflexivity].
    destruct h as [[p2 [x1 x2]]|]; cbn [stack_names.comp call_args] in H |- *.
    all: apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2];
      apply andb_true_iff; split; [apply andb_true_iff; split|].
    all: first [apply (Hr p1 _ eq_refl), H1 | apply bd_find_name, H2
               | apply (Hh _ _ eq_refl), H3 | reflexivity].
  - cbn [stack_names.comp call_args] in H |- *; apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff; split; [apply IH1, H1|apply IH2, H2].
  - cbn [stack_names.comp call_args] in H |- *; apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff; split; [apply IH1, H1|apply IH2, H2].
  - cbn [stack_names.comp call_args] in H |- *; apply IH, H.
  - destruct p; try contradiction; sn_get_addr; cbn [stack_names.comp call_args] in H |- *;
      try reflexivity;
      repeat match goal with
      | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
      | |- (_ && _) = true => apply andb_true_iff; split
      end; apply bd_find_name; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "stack_names_call_args" *)
Theorem stack_names_call_args {a : N} : forall f (p p' : list (N * prog a)),
  stack_names.compile f p = p' /\ EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND p) ->
  EVERY (fun p => call_args p (find_name f 1) (find_name f 2) (find_name f 3) (find_name f 4)
                    (find_name f 0)) (MAP SND p').
Proof.
  intros f p p' [<- H]; unfold stack_names.compile.
  induction p as [|[n q] p IH]; [reflexivity|].
  cbn [MAP EVERY SND stack_names.prog_comp] in H |- *; apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff; split; [apply call_args_comp, H1|apply IH, H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "names_ok_imp" *)
Theorem names_ok_imp {a : N} (f : sptree.spt N) (c : asm_config a) :
  names_ok f (reg_count c) (avoid_regs c) ->
  forall n, reg_name n c -> reg_ok (find_name f n) c.
Proof.
  unfold names_ok, reg_name, is_true; intros H n Hn.
  apply andb_true_iff in H as [_ H].
  exact (proj1 (EVERY_GENLIST _ _ _) H n (proj1 (N.ltb_lt _ _) Hn)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "names_ok_imp2" *)
Theorem names_ok_imp2 {a : N} (f : sptree.spt N) (c : asm_config a) n n' :
  names_ok f (reg_count c) (avoid_regs c) /\ n <> n' /\ reg_name n c /\ reg_name n' c ->
  find_name f n <> find_name f n'.
Proof.
  unfold names_ok, reg_name, is_true; intros (H & Hne & Hn & Hn') E.
  apply andb_true_iff in H as [H _].
  apply Hne, (proj1 (ALL_DISTINCT_GENLIST _ _) H); repeat split;
    [apply N.ltb_lt, Hn|apply N.ltb_lt, Hn'|exact E].
Qed.

Lemma bool_decide_false_iff (P : Prop) {d : Decision P} : bool_decide P = false <-> ~ P.
Proof. unfold bool_decide; destruct (decide P); split; congruence || tauto. Qed.

Ltac sn_bnorm :=
  repeat match goal with
  | H : implb ?x _ = true |- _ =>
      let E := fresh "E" in destruct x eqn:E; cbn [implb] in H; [|clear H]
  | H : (_ || _) = false |- _ => apply orb_false_iff in H as [? ?]
  | H : (_ && _) = false |- _ => apply andb_false_iff in H as [?|?]
  | H : MEM _ _ = _ |- _ => cbn [MEM] in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H : (_ || _) = true |- _ => apply orb_true_iff in H as [?|?]
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : bool_decide _ = true |- _ => apply bool_decide_spec in H
  | H : bool_decide _ = false |- _ => apply bool_decide_false_iff in H
  | H : Reg _ = Reg _ |- _ => injection H as H
  end.

Ltac sn_leaf f c Hok :=
  first
    [ reflexivity | assumption | congruence
    | match goal with H : negb ?x = true |- ?x = false => apply negb_true_iff, H end
    | apply (names_ok_imp f c Hok); assumption
    | intros ?; eapply (names_ok_imp2 f c); [|eassumption];
        repeat split; first [exact Hok|assumption|congruence] ].

Ltac sn_goal f c Hok :=
  repeat match goal with
  | |- (_ && _) = true => apply andb_true_iff; split
  | |- implb _ _ = true => apply Bool.implb_true_iff; intros ?; sn_bnorm; subst
  | |- negb _ = true => apply negb_true_iff
  | |- bool_decide _ = false => apply bool_decide_false_iff
  | |- bool_decide _ = true => apply bool_decide_spec
  | |- (_ || _) = true =>
      apply orb_true_iff; first [left; solve [sn_goal f c Hok] | right; solve [sn_goal f c Hok]]
  end; try sn_leaf f c Hok.

(** Galette-only: [stack_names_comp_stack_asm_ok] for one instruction. *)
Lemma inst_find_name_ok {a : N} (f : sptree.spt N) (c : asm_config a) (i : asm.inst a) :
  inst_name c i -> names_ok f (reg_count c) (avoid_regs c) -> fixed_names f c ->
  inst_ok (stack_names.inst_find_name f i) c.
Proof.
  unfold is_true; intros H Hok Hfx.
  unfold fixed_names in Hfx.
  destruct i as [|r w|x|m r ad|x]; [reflexivity| | | |];
    [| destruct x as [b r1 r2 ri|l r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4];
       try destruct ri as [r3|w]
    | destruct ad as [r2 w]
    | destruct x];
    cbn [stack_names.inst_find_name stack_names.ri_find_name inst_name inst_ok arith_name arith_ok
         fp_name fp_ok addr_name reg_imm_name reg_imm_ok] in *;
    destruct (ISA c); cbn in Hfx |- *; sn_bnorm; subst; sn_goal f c Hok.
Qed.

Ltac sn_regs f c Hok :=
  repeat match goal with
  | H : reg_name ?r c = true |- _ =>
      let R := fresh "R" in
      pose proof (names_ok_imp f c Hok r H) as R; unfold reg_ok, is_true in R;
      apply andb_true_iff in R as [? ?]; revert H
  end; intros.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "stack_names_comp_stack_asm_ok" *)
Theorem stack_names_comp_stack_asm_ok {a : N} (c : asm_config a) : forall f (p : prog a),
  stack_asm_name c p /\ names_ok f (reg_count c) (avoid_regs c) /\ fixed_names f c ->
  stack_asm_ok c (stack_names.comp f p).
Proof.
  intros f p; unfold is_true.
  induction p as [ret dest h Hr Hh|p1 p2 IH1 IH2|c0 r ri p1 p2 IH1 IH2|p IH|p Hp]
    using prog_nested_ind; intros (H & Hok & Hfx).
  - destruct ret as [[p1 [lr [l1 l2]]]|]; [destruct h as [[p2 [x1 x2]]|]|];
      destruct dest as [l|r]; cbn [stack_names.comp stack_names.dest_find_name stack_asm_name stack_asm_ok] in H |- *;
      sn_bnorm; subst; sn_regs f c Hok; sn_bnorm; sn_goal f c Hok;
      first [ apply (Hr p1 _ eq_refl); repeat split; assumption
            | apply (Hh p2 _ eq_refl); repeat split; assumption ].
  - cbn [stack_names.comp stack_asm_name stack_asm_ok] in H |- *; sn_bnorm.
    apply andb_true_iff; split; [apply IH1|apply IH2]; repeat split; assumption.
  - cbn [stack_names.comp stack_asm_name stack_asm_ok] in H |- *; sn_bnorm.
    apply andb_true_iff; split; [apply IH1|apply IH2]; repeat split; assumption.
  - cbn [stack_names.comp stack_asm_name stack_asm_ok] in H |- *; apply IH; repeat split; assumption.
  - destruct p; try contradiction; sn_get_addr;
      cbn [stack_names.comp stack_asm_name stack_asm_ok addr_ok addr_name] in H |- *; try reflexivity;
      first [ apply inst_find_name_ok; assumption
            | sn_bnorm; subst; sn_regs f c Hok; sn_bnorm; sn_goal f c Hok ].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "stack_names_stack_asm_ok" *)
Theorem stack_names_stack_asm_ok {a : N} (c : asm_config a) f (prog0 : list (N * prog a)) :
  EVERY (fun '(n, p) => stack_asm_name c p) prog0 /\
  names_ok f (reg_count c) (avoid_regs c) /\ fixed_names f c ->
  EVERY (fun '(n, p) => stack_asm_ok c p) (stack_names.compile f prog0).
Proof.
  intros (H & Hok & Hfx); unfold stack_names.compile, is_true in *.
  induction prog0 as [|[n q] prog0 IH]; [reflexivity|].
  cbn [MAP EVERY stack_names.prog_comp] in H |- *; apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff; split; [apply stack_names_comp_stack_asm_ok; repeat split; assumption|].
  apply IH, H2.
Qed.
