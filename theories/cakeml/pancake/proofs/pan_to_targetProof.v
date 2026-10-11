(** * Correctness of the Pancake-to-target composition.
    Port of [cakeml/pancake/proofs/pan_to_targetProofScript.sml], in progress.
    HOL's [PERMUTES] is [BIJ f UNIV UNIV]; quantified predicates inside
    boolean [EVERY] are reflected using [bool_decide]. *)
From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmProps.
From Galette.cakeml.compiler.backend Require wordLang word_to_word word_to_stack
  word_depth stack_to_lab backend.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
From Galette.cakeml.compiler.backend.semantics Require wordSem wordConvs stackProps.
From Galette.cakeml.compiler.backend.proofs Require backendProof stack_to_labProof
  word_to_stackProof word_to_wordProof.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake Require pan_to_word pan_to_target crep_to_loop.
From Galette.cakeml.pancake.proofs Require pan_to_wordProof.
Open Scope N_scope.

Section Composition.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pancake_good_code_def" *)
Definition pancake_good_code (pan_code : list (decl a)) : bool :=
  EVERY pan_to_wordProof.good_panops pan_code.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_to_stack_compile_FST" *)
Theorem word_to_stack_compile_FST {B C : Type} (mc : machine_config a B C)
    wprog bitmaps c'' fs p :
  word_to_stack.compile (asmProps.config (target mc)) false wprog =
    (bitmaps, (c'', (fs, p))) ->
  MAP FST p = wordLang.raise_stub_location ::
    wordLang.store_consts_stub_location :: MAP FST wprog.
Proof.
  unfold word_to_stack.compile; cbv zeta.
  destruct (word_to_stack.compile_word_to_stack _ _ _ _ _) as [ps [sizes bm]] eqn:E.
  intros H; inversion H; subst; cbn [MAP List.map FST fst].
  do 2 f_equal; eapply compile_props.MAP_FST_compile_word_to_stack; exact E.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "FLOOKUP_MAP_KEYS_LINV" *)
Theorem FLOOKUP_MAP_KEYS_LINV {A V : Type} `{Inhabited A}
    (f : A -> A) (m : fmap A V) i :
  BIJ f UNIV UNIV -> FLOOKUP (MAP_KEYS (LINV f UNIV) m) i = FLOOKUP m (f i).
Proof.
  intros HB; rewrite <- (LINV_DEF f UNIV UNIV (proj1 HB) i Logic.I) at 1.
  apply FLOOKUP_MAP_KEYS_MAPPED, (proj1 (BIJ_LINV_BIJ f UNIV UNIV HB)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "compile_prog_max_def" *)
Definition compile_prog_max {B C : Type} (c : backend.config)
    (mc : machine_config a B C) (prog : list (decl a)) :=
  let asm_conf := asmProps.config (target mc) in
  let prog := pan_to_word.compile_prog (ISA asm_conf) prog in
  let '(col, wprog) := word_to_word.compile (backend.word_to_word_conf c) asm_conf prog in
  let '(bm, (c', (fs, p))) := word_to_stack.compile asm_conf false wprog in
  let max := word_depth.max_depth (word_to_stack.stack_frame_size c')
    (word_depth.full_call_graph bvl_to_bvi.InitGlobals_location (fromAList wprog)) in
  (backend.from_stack asm_conf c LN p bm, max).

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "good_dimindex_div_mul" *)
Theorem good_dimindex_div_mul : good_dimindex a -> forall n,
  n * dimindex a DIV 8 = n * (dimindex a DIV 8).
Proof. intros [H|H] n; rewrite H; cbn [dimindex]; nia. Qed.

End Composition.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_def" *)
Definition option_lt (n0 n1 : option N) : Prop :=
  match n0, n1 with _, NONE => True | NONE, SOME _ => False
  | SOME n1, SOME n2 => n1 < n2 end.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "option_lt_SOME" *)
Theorem option_lt_SOME : forall x n,
  option_lt x (SOME n) <-> exists m, x = SOME m /\ m < n.
Proof. intros [m|] n; cbn [option_lt]; split; intros H; try contradiction.
  - exists m; auto.
  - destruct H as [k [H Hk]]; inversion H; subst; exact Hk.
  - destruct H as [k [H _]]; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "InitGlobals_location_eq_first_name" *)
Theorem InitGlobals_location_eq_first_name :
  bvl_to_bvi.InitGlobals_location = crep_to_loop.first_name.
Proof. reflexivity. Qed.

Section Memory.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (wordSem.state a c ffi_t).

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "fun2set_update_eq" *)
Theorem fun2set_update_eq {A B : Type} `{EqDecision A} (m m' : A -> B) md x v :
  fun2set (m, md) = fun2set (m', md) ->
  fun2set ((x =+ v) m, md) = fun2set ((x =+ v) m', md).
Proof.
  rewrite !fun2set_eq; intros HE i Hi; rewrite !APPLY_UPDATE_THM.
  destruct (decide (x = i)); auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_var_const_memory" *)
Theorem get_var_const_memory x (y : state) m :
  wordSem.get_var x (wordSem.set_memory m y) = wordSem.get_var x y.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "set_var_const_memory" *)
Theorem set_var_const_memory v x (y : state) m :
  wordSem.set_var v x (wordSem.set_memory m y) =
  wordSem.set_memory m (wordSem.set_var v x y).
Proof. destruct y; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "unset_var_const_memory" *)
Theorem unset_var_const_memory v (y : state) m :
  wordSem.unset_var v (wordSem.set_memory m y) =
  wordSem.set_memory m (wordSem.unset_var v y).
Proof. destruct y; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_vars_const_memory" *)
Theorem get_vars_const_memory x (y : state) m :
  wordSem.get_vars x (wordSem.set_memory m y) = wordSem.get_vars x y.
Proof. induction x as [|v vs IH]; cbn [wordSem.get_vars]; rewrite ?get_var_const_memory, ?IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "set_vars_const_memory" *)
Theorem set_vars_const_memory vs xs (y : state) m :
  wordSem.set_vars vs xs (wordSem.set_memory m y) =
  wordSem.set_memory m (wordSem.set_vars vs xs y).
Proof. destruct y; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "get_var_imm_const_memory" *)
Theorem get_var_imm_const_memory ri (s : state) m :
  wordSem.get_var_imm ri (wordSem.set_memory m s) = wordSem.get_var_imm ri s.
Proof. destruct ri; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_const_memory" *)
Theorem mem_load_const_memory ad (s : state) m :
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) ->
  wordSem.mem_load ad (wordSem.set_memory m s) = wordSem.mem_load ad s.
Proof.
  intros H; pose proof (proj1 (fun2set_eq _ _ _) H) as HE; unfold wordSem.mem_load; cbn [wordSem.mdomain wordSem.set_memory].
  destruct (classical_dec _); [rewrite HE by assumption|]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_const_memory" *)
Theorem mem_store_const_memory ad w (s : state) m :
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) ->
  (wordSem.mem_store ad w s = NONE <->
   wordSem.mem_store ad w (wordSem.set_memory m s) = NONE) /\
  (wordSem.mem_store ad w s = SOME (wordSem.set_memory ((ad =+ w) (wordSem.memory s)) s) <->
   wordSem.mem_store ad w (wordSem.set_memory m s) = SOME (wordSem.set_memory ((ad =+ w) m) s)).
Proof.
  intros _; unfold wordSem.mem_store; cbn [wordSem.mdomain wordSem.set_memory].
  destruct (classical_dec _); destruct s; cbn; intuition congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_32_const_memory" *)
Theorem mem_load_32_const_memory (m m' : word a -> wordLang.word_loc a) dm be ad :
  fun2set (m, dm) = fun2set (m', dm) ->
  wordSem.mem_load_32 m dm be ad = wordSem.mem_load_32 m' dm be ad.
Proof.
  intros H; pose proof (proj1 (fun2set_eq _ _ _) H) as HE; unfold wordSem.mem_load_32.
  destruct (aligned 2 ad); [|reflexivity].
  destruct (classical_dec (byte_align ad IN dm)) as [Hd|Hd].
  - rewrite HE by exact Hd; reflexivity.
  - destruct (m (byte_align ad)), (m' (byte_align ad)); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_32_const_memory" *)
Theorem mem_store_32_const_memory (m m' : word a -> wordLang.word_loc a) dm be ad hw :
  fun2set (m, dm) = fun2set (m', dm) ->
  (wordSem.mem_store_32 m dm be ad hw = NONE <-> wordSem.mem_store_32 m' dm be ad hw = NONE) /\
  fun2set (THE (wordSem.mem_store_32 m dm be ad hw), dm) =
  fun2set (THE (wordSem.mem_store_32 m' dm be ad hw), dm).
Proof.
  intros H; pose proof (proj1 (fun2set_eq m m' dm) H) as HE.
  unfold wordSem.mem_store_32; destruct (aligned 2 ad); [|split; reflexivity].
  destruct (classical_dec (byte_align ad IN dm)) as [Hd|Hd].
  - rewrite <- HE by exact Hd; destruct (m (byte_align ad)); cbn [THE].
    + split; [split; discriminate|apply fun2set_update_eq; exact H].
    + split; reflexivity.
  - destruct (m (byte_align ad)), (m' (byte_align ad)); split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "word_exp_const_memory" *)
Theorem word_exp_const_memory : forall (s : state) exp m,
  fun2set (wordSem.memory s, wordSem.mdomain s) = fun2set (m, wordSem.mdomain s) ->
  wordSem.word_exp (wordSem.set_memory m s) exp = wordSem.word_exp s exp.
Proof.
  intros s exp m H.
  induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using wordConvs.exp_nested_ind;
    cbn [wordSem.word_exp]; try reflexivity.
  - rewrite IH; destruct (wordSem.word_exp s e) as [[w|? ?]|]; try reflexivity.
    apply mem_load_const_memory; exact H.
  - assert (HM : MAP (wordSem.word_exp (wordSem.set_memory m s)) es = MAP (wordSem.word_exp s) es).
    { induction IH as [|x xs Hx Hxs IHL]; cbn [MAP List.map]; [reflexivity|]. rewrite Hx, IHL; reflexivity. }
    rewrite HM; reflexivity.
  - rewrite IH1, IH2; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_load_byte_aux_const_memory" *)
Theorem mem_load_byte_aux_const_memory (m m' : word a -> wordLang.word_loc a) dm be w :
  fun2set (m, dm) = fun2set (m', dm) ->
  wordSem.mem_load_byte_aux m' dm be w = wordSem.mem_load_byte_aux m dm be w.
Proof.
  intros H; pose proof (proj1 (fun2set_eq _ _ _) H) as HE; unfold wordSem.mem_load_byte_aux.
  destruct (classical_dec (byte_align w IN dm)) as [Hd|Hd].
  - rewrite HE by exact Hd; reflexivity.
  - destruct (m (byte_align w)), (m' (byte_align w)); reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "mem_store_byte_aux_const_memory" *)
Theorem mem_store_byte_aux_const_memory (m m' : word a -> wordLang.word_loc a) dm be w b :
  fun2set (m, dm) = fun2set (m', dm) ->
  (wordSem.mem_store_byte_aux m dm be w b = NONE <-> wordSem.mem_store_byte_aux m' dm be w b = NONE) /\
  fun2set (THE (wordSem.mem_store_byte_aux m' dm be w b), dm) =
  fun2set (THE (wordSem.mem_store_byte_aux m dm be w b), dm).
Proof.
  intros H; pose proof (proj1 (fun2set_eq m m' dm) H) as HE.
  unfold wordSem.mem_store_byte_aux.
  destruct (classical_dec (byte_align w IN dm)) as [Hd|Hd].
  - rewrite <- HE by exact Hd; destruct (m (byte_align w)); cbn [THE].
    + split; [split; discriminate|symmetry; apply fun2set_update_eq; exact H].
    + split; reflexivity.
  - destruct (m (byte_align w)), (m' (byte_align w)); split; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "read_bytearray_const_memory" *)
Theorem read_bytearray_const_memory (m m' : word a -> wordLang.word_loc a) dm ptr len be :
  fun2set (m, dm) = fun2set (m', dm) ->
  read_bytearray ptr len (wordSem.mem_load_byte_aux m dm be) =
  read_bytearray ptr len (wordSem.mem_load_byte_aux m' dm be).
Proof.
  intros H; f_equal; apply functional_extensionality; intros w.
  symmetry; apply mem_load_byte_aux_const_memory; exact H.
Qed.

End Memory.
