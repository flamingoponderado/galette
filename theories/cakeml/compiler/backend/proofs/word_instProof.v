(** * CakeML [word_instProof]: correctness of [word_inst]

    Port of [cakeml/compiler/backend/proofs/word_instProofScript.sml].

    Notes:
    - HOL's free variables are quantified explicitly (first, when HOL's
      statement quantifies only some of them).  HOL's [s with locals := l]
      is [set_locals l s]; [x < temp] in [every_var] arguments is
      [x <? temp] (the [bool] predicates of [wordLang]).
    - Not ported (they are stated with HOL's [sorting$PERM], which Galette
      does not port; see [wordProps.code]): the local lemmas
      [PERM_SWAP_SIMP], [PERM_SWAP], [word_exp_op_permute_lem] and
      [pull_ops_simp_pull_ops_perm].  The last two are proved with Rocq's
      [Permutation] and are untagged.
    - HOL's free variable [c] (an [asm_config]) is [c0] ([c] is the
      configuration type of the states); HOL's [if x = tar then ...] is
      [if decide (x = tar) then ...].
    - HOL's [MEM] on expressions needs a decidable equality: a classical
      local instance ([exp_eq_dec_classical]), as [wordProps.code] does for
      programs.
    - [pull_ops_every_var_exp] is HOL's [val] after its
      [REWRITE_RULE [EVERY_MEM]] (the [MEM] form).
    - [binary_branch_exp_def] is a structural [Fixpoint] (HOL: well-founded
      recursion on [exp_size]) with HOL's clauses.
    - Proofs are by structural or well-founded induction (on expressions
      with [exp_nested_ind] or the Galette-only size [esize], on programs
      with [prog_nested_ind]) instead of HOL's recursion-induction
      principles, and use the Galette-only algebraic helpers on
      [word_and], [word_or], [word_xor] below. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.sort Require Import sorting.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang word_inst.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock locals_rel.
From Stdlib Require Import Permutation Btauto.
Open Scope N_scope.

(** ** Galette-only helpers *)

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "EL_FILTER" *)
Theorem EL_FILTER : forall {A} `{Inhabited A} (P : A -> bool) ls x,
  x < LENGTH (FILTER P ls) -> P (EL x (FILTER P ls)).
Proof.
  intros A HA P ls x Hx. rewrite EL_nth by exact Hx. rewrite LENGTH_length in Hx.
  assert (Hi : In (nth (N.to_nat x) (FILTER P ls) ARB) (FILTER P ls)) by (apply nth_In; lia).
  apply filter_In in Hi as [_ Hi]. exact Hi.
Qed.

(** *** Word algebra *)

Section WordAlg.
Context {a : N}.
Implicit Types v w x : word a.

Lemma mod_ones n : n MOD dimword a = N.land n (N.ones (dimindex a)).
Proof. unfold dimword. rewrite N.land_ones. reflexivity. Qed.

Lemma w2n_lt_dimword w : w2n w < dimword a.
Proof. destruct w as [n H]; cbn. apply sbool_is_true in H. apply N.ltb_lt, H. Qed.

Lemma w2n_masked w : N.land (w2n w) (N.ones (dimindex a)) = w2n w.
Proof. rewrite <- mod_ones. apply N.mod_small, w2n_lt_dimword. Qed.

Ltac bits :=
  apply word_eq_w2n; unfold word_and, word_or, word_xor, w2n, n2w; cbn [w2n_val];
  rewrite ?mod_ones; apply N.bits_inj; intros i;
  repeat progress (rewrite ?N.land_spec, ?N.lor_spec, ?N.lxor_spec); btauto.

Lemma word_and_comm v w : word_and v w = word_and w v. Proof. bits. Qed.
Lemma word_and_assoc v w x : word_and v (word_and w x) = word_and (word_and v w) x. Proof. bits. Qed.
Lemma word_or_comm v w : word_or v w = word_or w v. Proof. bits. Qed.
Lemma word_or_assoc v w x : word_or v (word_or w x) = word_or (word_or v w) x. Proof. bits. Qed.
Lemma word_xor_comm v w : word_xor v w = word_xor w v. Proof. bits. Qed.
Lemma word_xor_assoc v w x : word_xor v (word_xor w x) = word_xor (word_xor v w) x. Proof. bits. Qed.

Lemma w2n_1comp0 : w2n (word_1comp (n2w 0 : word a)) = N.ones (dimindex a).
Proof.
  pose proof (ZERO_LT_dimword a). unfold word_1comp, n2w, w2n; cbn [w2n_val].
  rewrite (N.Div0.mod_0_l (dimword a)). rewrite N.sub_0_r, N.mod_small by lia.
  unfold dimword. rewrite N.ones_equiv. lia.
Qed.

Lemma w2n_n2w' n : w2n (n2w n : word a) = n MOD dimword a.
Proof. reflexivity. Qed.

Lemma word_and_ones w : word_and w (word_1comp (n2w 0)) = w.
Proof.
  apply word_eq_w2n. unfold word_and. rewrite w2n_1comp0, w2n_n2w', mod_ones.
  rewrite <- N.land_assoc, N.land_diag. apply w2n_masked.
Qed.

Lemma word_ones_and w : word_and (word_1comp (n2w 0)) w = w.
Proof. rewrite word_and_comm. apply word_and_ones. Qed.

Lemma word_or_0 w : word_or w (n2w 0) = w.
Proof.
  apply word_eq_w2n. unfold word_or. rewrite w2n_n2w', (w2n_n2w' 0).
  pose proof (ZERO_LT_dimword a). rewrite (N.Div0.mod_0_l (dimword a)).
  rewrite N.lor_0_r. apply N.mod_small, w2n_lt_dimword.
Qed.

Lemma word_xor_0 w : word_xor w (n2w 0) = w.
Proof.
  apply word_eq_w2n. unfold word_xor. rewrite w2n_n2w', (w2n_n2w' 0).
  pose proof (ZERO_LT_dimword a). rewrite (N.Div0.mod_0_l (dimword a)).
  rewrite N.lxor_0_r. apply N.mod_small, w2n_lt_dimword.
Qed.

Lemma word_add_0' w : word_add w (n2w 0) = w.
Proof.
  apply word_eq_w2n. unfold word_add. rewrite w2n_n2w', (w2n_n2w' 0).
  pose proof (ZERO_LT_dimword a). rewrite (N.Div0.mod_0_l (dimword a)).
  rewrite N.add_0_r. apply N.mod_small, w2n_lt_dimword.
Qed.

Lemma word_and_0 w : word_and (n2w 0) w = n2w 0.
Proof.
  apply word_eq_w2n. unfold word_and. rewrite !w2n_n2w'.
  pose proof (ZERO_LT_dimword a). rewrite (N.Div0.mod_0_l (dimword a)).
  rewrite N.land_0_l. reflexivity.
Qed.

End WordAlg.

Section Ops.
Context {a : N}.

(** Galette-only: the [FOLDR] operator and unit of [word_op op] for
    [op <> Sub]. *)
Definition opf (op : binop) : word a -> word a -> word a :=
  match op with
  | And => word_and | asm.Add => word_add | Or => word_or | asm.Xor => word_xor
  | asm.Sub => word_sub
  end.
Definition ope (op : binop) : word a :=
  match op with And => word_1comp (n2w 0) | _ => n2w 0 end.

Lemma word_op_FOLDR op ws : op <> asm.Sub -> word_op op ws = SOME (FOLDR (opf op) (ope op) ws).
Proof. destruct op; intros H; first [congruence|reflexivity]. Qed.

Lemma opf_comm op x y : op <> asm.Sub -> opf op x y = opf op y x.
Proof.
  destruct op; intros H; cbn [opf];
    first [congruence|apply WORD_ADD_COMM|apply word_and_comm|apply word_or_comm|apply word_xor_comm].
Qed.

Lemma opf_assoc op x y z : op <> asm.Sub -> opf op x (opf op y z) = opf op (opf op x y) z.
Proof.
  destruct op; intros H; cbn [opf];
    first [congruence|apply WORD_ADD_ASSOC|apply word_and_assoc|apply word_or_assoc|apply word_xor_assoc].
Qed.

Lemma opf_unit_r op x : op <> asm.Sub -> opf op x (ope op) = x.
Proof.
  destruct op; intros H; cbn [opf ope];
    first [congruence|apply word_add_0'|apply word_and_ones|apply word_or_0|apply word_xor_0].
Qed.

Lemma opf_unit_l op x : op <> asm.Sub -> opf op (ope op) x = x.
Proof. intros H; rewrite opf_comm by exact H; apply opf_unit_r, H. Qed.

Lemma FOLDR_opf_app op l1 l2 :
  op <> asm.Sub -> FOLDR (opf op) (ope op) (l1 ++ l2) =
                   opf op (FOLDR (opf op) (ope op) l1) (FOLDR (opf op) (ope op) l2).
Proof.
  intros H; induction l1 as [|x l1 IH]; cbn [FOLDR app].
  - rewrite opf_unit_l by exact H. reflexivity.
  - rewrite IH, opf_assoc by exact H. reflexivity.
Qed.

Lemma FOLDR_opf_perm op l l' :
  op <> asm.Sub -> Permutation l l' -> FOLDR (opf op) (ope op) l = FOLDR (opf op) (ope op) l'.
Proof.
  intros H P; induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [FOLDR].
  - reflexivity.
  - rewrite IH; reflexivity.
  - rewrite !opf_assoc by exact H. rewrite (opf_comm op y x) by exact H. reflexivity.
  - congruence.
Qed.

Lemma the_words_perm (l l' : list (option (word_loc a))) :
  Permutation l l' ->
  match the_words l, the_words l' with
  | SOME ws, SOME ws' => Permutation ws ws'
  | NONE, NONE => True
  | _, _ => False
  end.
Proof.
  induction 1 as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [the_words].
  - constructor.
  - destruct (the_words l), (the_words l'); try contradiction;
      destruct x as [[]|]; auto; constructor; exact IH.
  - destruct (the_words l) as [ws|];
      destruct x as [[]|], y as [[]|]; cbn; auto; apply perm_swap.
  - destruct (the_words l), (the_words l'), (the_words l''); try contradiction; auto.
    eapply Permutation_trans; eassumption.
Qed.

End Ops.

Section PullExp.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma word_exp_Op s op ls :
  word_exp s (Op op ls) =
  match the_words (MAP (fun e => word_exp s e) ls) with
  | SOME ws => OPTION_MAP Word (word_op op ws)
  | NONE => NONE
  end.
Proof. reflexivity. Qed.

Lemma sub_as_add s (x : exp a) w :
  word_exp s (Op asm.Add [Const (word_2comp w); x]) = word_exp s (Op asm.Sub [x; Const w]).
Proof.
  rewrite !word_exp_Op; cbn [MAP List.map the_words].
  change (word_exp s (Const ?v)) with (SOME (@Word a v)).
  destruct (word_exp s x) as [[v|]|]; cbn [the_words option_map OPTION_MAP]; try reflexivity.
  cbn [word_op FOLDR]. f_equal; f_equal. unfold word_sub. rewrite word_add_0', WORD_ADD_COMM.
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "convert_sub_ok" *)
Theorem convert_sub_ok : forall s (ls : list (exp a)),
  word_exp s (convert_sub ls) = word_exp s (Op asm.Sub ls).
Proof.
  intros s ls. destruct ls as [|x [|y [|z t]]];
    [reflexivity|destruct x; reflexivity| |destruct x; try destruct y; reflexivity].
  destruct y; try (destruct x; reflexivity).
  destruct x; try (apply sub_as_add). reflexivity.
Qed.

Lemma word_exp_Op_nonsub s op ls :
  op <> asm.Sub ->
  word_exp s (Op op ls) =
  OPTION_MAP (fun ws => Word (FOLDR (opf op) (ope op) ws)) (the_words (MAP (fun e => word_exp s e) ls)).
Proof.
  intros H. rewrite word_exp_Op. destruct (the_words _); [|reflexivity].
  rewrite word_op_FOLDR by exact H. reflexivity.
Qed.

(** HOL's [word_exp_op_permute_lem] (stated with [PERM]); Galette-only. *)
Lemma word_exp_op_permute_lem s op ls ls' :
  op <> asm.Sub -> Permutation ls ls' -> word_exp s (Op op ls) = word_exp s (Op op ls').
Proof.
  intros H P. rewrite !word_exp_Op_nonsub by exact H.
  pose proof (the_words_perm _ _ (Permutation_map (fun e => word_exp s e) P)) as T.
  destruct (the_words (MAP _ ls)), (the_words (MAP _ ls')); try contradiction; cbn; [|reflexivity].
  rewrite (FOLDR_opf_perm op _ _ H T). reflexivity.
Qed.

End PullExp.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_simp_def" *)
Fixpoint pull_ops_simp {a} (op : binop) (l : list (exp a)) : list (exp a) :=
  match l with
  | [] => []
  | x :: xs =>
      match x with
      | Op op' ls => if decide (op = op') then ls ++ pull_ops_simp op xs else x :: pull_ops_simp op xs
      | _ => x :: pull_ops_simp op xs
      end
  end.

(** HOL's [pull_ops_simp_pull_ops_perm] (stated with [PERM]); Galette-only. *)
Lemma pull_ops_simp_pull_ops_perm {a} op (ls x : list (exp a)) :
  Permutation (pull_ops op ls x) (pull_ops_simp op ls ++ x).
Proof.
  revert x; induction ls as [|y ls IH]; intros x; cbn [pull_ops pull_ops_simp]; [reflexivity|].
  destruct y; try (rewrite IH; cbn; apply Permutation_sym, Permutation_middle).
  destruct (decide (op = b)).
  - rewrite IH, <- app_assoc. apply Permutation_app_swap_app.
  - rewrite IH; cbn; apply Permutation_sym, Permutation_middle.
Qed.

Section PullExp2.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma word_exp_Op_eq s op ls ls' :
  op <> asm.Sub ->
  OPTION_MAP (fun ws => FOLDR (opf op) (ope op) ws) (the_words (MAP (fun e => word_exp s e) ls)) =
  OPTION_MAP (fun ws => FOLDR (opf op) (ope op) ws) (the_words (MAP (fun e => word_exp s e) ls')) ->
  word_exp s (Op op ls) = word_exp s (Op op ls').
Proof.
  intros Hop H. rewrite !word_exp_Op_nonsub by exact Hop.
  destruct (the_words (MAP _ ls)), (the_words (MAP _ ls')); cbn in H |- *; congruence.
Qed.

Lemma word_exp_Op_inv s op ls ls' :
  op <> asm.Sub -> word_exp s (Op op ls) = word_exp s (Op op ls') ->
  OPTION_MAP (fun ws => FOLDR (opf op) (ope op) ws) (the_words (MAP (fun e => word_exp s e) ls)) =
  OPTION_MAP (fun ws => FOLDR (opf op) (ope op) ws) (the_words (MAP (fun e => word_exp s e) ls')).
Proof.
  intros Hop H. rewrite !word_exp_Op_nonsub in H by exact Hop.
  destruct (the_words (MAP _ ls)), (the_words (MAP _ ls')); cbn in H |- *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_simp_pull_ops_word_exp" *)
Theorem pull_ops_simp_pull_ops_word_exp : forall s op (ls : list (exp a)),
  op <> asm.Sub ->
  word_exp s (Op op (pull_ops op ls [])) = word_exp s (Op op (pull_ops_simp op ls)).
Proof.
  intros s op ls H. apply word_exp_op_permute_lem; [exact H|].
  pose proof (pull_ops_simp_pull_ops_perm op ls []) as P. rewrite app_nil_r in P. exact P.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_op_mono" *)
Theorem word_exp_op_mono : forall s op (ls ls' : list (exp a)) x,
  op <> asm.Sub ->
  word_exp s (Op op ls) = word_exp s (Op op ls') ->
  word_exp s (Op op (x :: ls)) = word_exp s (Op op (x :: ls')).
Proof.
  intros s op ls ls' x Hop H. apply word_exp_Op_inv in H; [|exact Hop].
  apply word_exp_Op_eq; [exact Hop|]. cbn [MAP List.map the_words].
  destruct (word_exp s x) as [[v|]|]; [|reflexivity..].
  destruct (the_words (MAP _ ls)), (the_words (MAP _ ls')); cbn in H |- *; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "the_words_append" *)
Theorem the_words_append : forall (ls ls' : list (option (word_loc a))),
  the_words (ls ++ ls') =
  match the_words ls with
  | NONE => NONE
  | SOME w => match the_words ls' with NONE => NONE | SOME w' => SOME (w ++ w') end
  end.
Proof.
  induction ls as [|x ls IH]; intros ls'; cbn [the_words app].
  - destruct (the_words ls'); reflexivity.
  - rewrite IH. destruct x as [[]|]; destruct (the_words ls), (the_words ls'); reflexivity.
Qed.

(** HOL's free variable [l] is quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_op_op" *)
Theorem word_exp_op_op : forall s op (l ls ls' : list (exp a)),
  op <> asm.Sub ->
  word_exp s (Op op ls) = word_exp s (Op op ls') ->
  word_exp s (Op op (l ++ ls)) = word_exp s (Op op (Op op l :: ls')).
Proof.
  intros s op l ls ls' Hop H. apply word_exp_Op_inv in H; [|exact Hop].
  apply word_exp_Op_eq; [exact Hop|].
  rewrite map_app, the_words_append. cbn [MAP List.map the_words].
  rewrite (word_exp_Op_nonsub s op l Hop).
  destruct (the_words (MAP _ l)) as [wl|]; cbn [option_map OPTION_MAP]; [|reflexivity].
  destruct (the_words (MAP _ ls)), (the_words (MAP _ ls')); cbn in H |- *; try congruence.
  injection H as H. rewrite FOLDR_opf_app by exact Hop. cbn [FOLDR]. rewrite H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_ok" *)
Theorem pull_ops_ok : forall s op (ls : list (exp a)),
  op <> asm.Sub -> word_exp s (Op op (pull_ops op ls [])) = word_exp s (Op op ls).
Proof.
  intros s op ls Hop. rewrite pull_ops_simp_pull_ops_word_exp by exact Hop.
  induction ls as [|x ls IH]; [reflexivity|]. cbn [pull_ops_simp].
  destruct x; try (apply word_exp_op_mono; assumption).
  destruct (decide (op = b)) as [<-|]; [|apply word_exp_op_mono; assumption].
  apply word_exp_op_op; assumption.
Qed.

(** HOL's free variables [A] and [w] are quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_swap_head" *)
Theorem word_exp_swap_head : forall s op (A : list (exp a)) w B,
  op <> asm.Sub ->
  word_exp s (Op op A) = SOME (Word w) ->
  word_exp s (Op op (B ++ A)) = word_exp s (Op op (Const w :: B)).
Proof.
  intros s op A w B Hop H. rewrite word_exp_Op_nonsub in H by exact Hop.
  apply word_exp_Op_eq; [exact Hop|].
  rewrite map_app, the_words_append. cbn [MAP List.map the_words word_exp].
  destruct (the_words (MAP _ A)) as [wa|]; [|discriminate]. injection H as <-.
  destruct (the_words (MAP _ B)) as [wb|]; [|reflexivity]. cbn [option_map OPTION_MAP FOLDR].
  rewrite FOLDR_opf_app, opf_comm by exact Hop. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "EVERY_is_const_word_exp" *)
Theorem EVERY_is_const_word_exp : forall s (ls : list (exp a)),
  EVERY is_const ls -> EVERY IS_SOME (MAP (fun a0 => word_exp s a0) ls).
Proof.
  intros s ls; induction ls as [|e ls IH]; intros H; [reflexivity|].
  cbn [EVERY MAP List.map] in H |- *. unfold is_true in *. apply andb_prop in H as [H1 H2].
  destruct e; try discriminate H1. cbn. apply IH, H2.
Qed.

Lemma the_words_consts s (ls : list (exp a)) :
  EVERY is_const ls -> the_words (MAP (fun e => word_exp s e) ls) = SOME (MAP rm_const ls).
Proof.
  induction ls as [|e ls IH]; intros H; [reflexivity|].
  cbn [EVERY] in H. unfold is_true in H. apply andb_prop in H as [H1 H2].
  destruct e; try discriminate H1. cbn [MAP List.map the_words word_exp]. rewrite IH by exact H2.
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "all_consts_simp" *)
Theorem all_consts_simp : forall s op (ls : list (exp a)),
  op <> asm.Sub -> EVERY is_const ls ->
  word_exp s (Op op ls) = SOME (Word (THE (word_op op (MAP rm_const ls)))).
Proof.
  intros s op ls Hop H. rewrite word_exp_Op_nonsub, the_words_consts, word_op_FOLDR by assumption.
  reflexivity.
Qed.

(** HOL's free variables are quantified. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "word_exp_reduce_const" *)
Theorem word_exp_reduce_const : forall s op w (rest : list (exp a)) x,
  word_exp s (Op op (Const w :: rest)) = SOME x ->
  word_exp s (reduce_const op w rest) = SOME x.
Proof.
  intros s op w rest x H. unfold reduce_const.
  destruct (decide (w = n2w 0)) as [->|]; [|exact H].
  destruct (decide (op = asm.Add \/ op = Or \/ op = asm.Xor)) as [Hop|Hop].
  - assert (Hs : op <> asm.Sub) by (intros ->; destruct Hop as [|[|]]; discriminate).
    assert (He : @ope a op = n2w 0) by (destruct Hop as [->|[->| ->]]; reflexivity).
    rewrite word_exp_Op_nonsub in H by exact Hs. cbn [MAP List.map the_words word_exp] in H.
    destruct rest as [|y [|z t]].
    + cbn [the_words option_map OPTION_MAP FOLDR MAP List.map] in H. injection H as <-. rewrite opf_unit_r by exact Hs. reflexivity.
    + cbn [MAP List.map the_words] in H.
      destruct (word_exp s y) as [[v|]|]; cbn [the_words option_map OPTION_MAP FOLDR] in H; try discriminate.
      injection H as <-. rewrite <- He, opf_unit_l, opf_unit_r by exact Hs. reflexivity.
    + rewrite word_exp_Op_nonsub by exact Hs.
      destruct (the_words _) as [ws|]; cbn [the_words option_map OPTION_MAP FOLDR] in H |- *; [|discriminate].
      injection H as <-. rewrite <- He, opf_unit_l by exact Hs. reflexivity.
  - destruct (decide (op = And)) as [->|]; [|exact H].
    cbn in H |- *. destruct (the_words _) as [ws|]; cbn in H; [|discriminate].
    injection H as <-. rewrite word_and_0. reflexivity.
Qed.

Lemma PART_eq {A} (P : A -> bool) l l1 l2 :
  PART P l l1 l2 = (rev (filter P l) ++ l1, rev (filter (fun x => negb (P x)) l) ++ l2).
Proof.
  revert l1 l2; induction l as [|h l IH]; intros l1 l2; [reflexivity|]. cbn [PART filter].
  destruct (P h); cbn [negb]; rewrite IH; cbn [rev]; rewrite <- !app_assoc; reflexivity.
Qed.

Lemma filter_partition_perm {A} (P : A -> bool) l :
  Permutation l (filter P l ++ filter (fun x => negb (P x)) l).
Proof.
  induction l as [|h l IH]; [reflexivity|]. cbn [filter].
  destruct (P h); cbn [negb app]; [constructor; exact IH|].
  apply Permutation_cons_app, IH.
Qed.

Lemma EVERY_rev_filter {A} (P : A -> bool) l : EVERY P (rev (filter P l)).
Proof.
  unfold is_true; apply EVERY_Forall, Forall_rev, Forall_forall.
  intros x Hx; apply filter_In in Hx as [_ Hx]; exact Hx.
Qed.

(** HOL's free variables are quantified. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "optimize_consts_ok" *)
Theorem optimize_consts_ok : forall s op (ls : list (exp a)) x,
  op <> asm.Sub /\ word_exp s (Op op ls) = SOME x ->
  word_exp s (optimize_consts op ls) = SOME x.
Proof.
  intros s op ls x [Hop H]. unfold optimize_consts, PARTITION. rewrite PART_eq, !app_nil_r.
  assert (P : Permutation ls (rev (filter is_const ls) ++ rev (filter (fun x => negb (is_const x)) ls))).
  { eapply Permutation_trans; [apply filter_partition_perm|].
    apply Permutation_app; apply Permutation_rev. }
  destruct (rev (filter is_const ls)) as [|h t] eqn:Ec.
  - rewrite <- H. symmetry. apply word_exp_op_permute_lem; [exact Hop|exact P].
  - cbn zeta. pose proof (EVERY_rev_filter is_const ls) as He. rewrite Ec in He.
    pose proof (all_consts_simp s op (h :: t) Hop He) as Hc.
    apply word_exp_reduce_const.
    rewrite <- (word_exp_swap_head s op (h :: t) _ _ Hop Hc).
    rewrite <- H. apply word_exp_op_permute_lem; [exact Hop|].
    symmetry. eapply Permutation_trans; [exact P|]. apply Permutation_app_comm.
Qed.

Lemma MAP_pull_exp s (es : list (exp a)) ws :
  Forall (fun e => forall s x, word_exp s e = SOME x -> word_exp s (pull_exp e) = SOME x) es ->
  the_words (MAP (fun e => word_exp s e) es) = SOME ws ->
  MAP (fun e => word_exp s e) (MAP pull_exp es) = MAP (fun e => word_exp s e) es.
Proof.
  intros F; revert ws; induction F as [|e es He F IH]; intros ws H; [reflexivity|].
  cbn [MAP List.map the_words] in H |- *.
  destruct (word_exp s e) as [[v|]|] eqn:E; try discriminate.
  destruct (the_words (MAP _ es)) as [ws'|] eqn:E2; [|discriminate].
  rewrite (He s _ E), (IH ws' eq_refl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_exp_ok" *)
Theorem pull_exp_ok : forall (exp : exp a) s x,
  word_exp s exp = SOME x -> word_exp s (pull_exp exp) = SOME x.
Proof.
  intros e. induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros s x H; try exact H.
  - cbn [pull_exp word_exp] in H |- *.
    destruct (word_exp s e) as [[v|]|] eqn:E; try discriminate. rewrite (IH s _ E). exact H.
  - assert (Hm : forall ws, the_words (MAP (fun e => word_exp s e) es) = SOME ws ->
                 word_exp s (Op op (MAP pull_exp es)) = word_exp s (Op op es)).
    { intros ws Hw. rewrite !word_exp_Op, (MAP_pull_exp s es ws IH Hw). reflexivity. }
    destruct (the_words (MAP (fun e => word_exp s e) es)) as [ws|] eqn:Ew;
      [|rewrite word_exp_Op, Ew in H; discriminate].
    destruct (decide (op = asm.Sub)) as [->|Hop].
    + cbn [pull_exp]. rewrite convert_sub_ok, (Hm ws eq_refl). exact H.
    + destruct es as [|e1 [|e2 rest]].
      * destruct op; try congruence; cbn in H |- *; injection H as <-; reflexivity.
      * rewrite word_exp_Op_nonsub in H by exact Hop. rewrite Ew in H. cbn in Ew.
        destruct (word_exp s e1) as [[v|]|] eqn:E1; try discriminate. injection Ew as <-.
        cbn in H. injection H as <-. rewrite opf_unit_r by exact Hop.
        inversion IH as [|? ? He1 _]; subst.
        assert (G : word_exp s (pull_exp e1) = SOME (Word v)) by exact (He1 s _ E1).
        destruct op; try congruence; exact G.
      * assert (G : word_exp s (pull_exp (Op op (e1 :: e2 :: rest))) =
                    word_exp s (optimize_consts op (pull_ops op (MAP pull_exp (e1 :: e2 :: rest)) []))).
        { destruct op; try congruence; reflexivity. }
        rewrite G. apply optimize_consts_ok. split; [exact Hop|].
        rewrite pull_ops_ok by exact Hop. rewrite (Hm ws eq_refl). exact H.
  - cbn [pull_exp word_exp] in H |- *.
    destruct (word_exp s e1) as [[v|]|] eqn:E1; try discriminate.
    destruct (word_exp s e2) as [[v2|]|] eqn:E2; try discriminate.
    rewrite (IH1 s _ E1), (IH2 s _ E2). exact H.
Qed.

End PullExp2.

(** ** [pull_exp] syntax *)

(** Galette-only: HOL's [MEM] on expressions needs a decidable equality;
    a classical instance (as [wordProps.code]'s for programs). *)
#[local] Instance exp_eq_dec_classical {a} : EqDecision (exp a) :=
  fun x y => match classical_dec (x = y) with left e => left e | right n => right n end.

Section PullSyntax.
Context {a : N}.

Lemma MEM_In' (x : exp a) l : MEM x l <-> In x l.
Proof. unfold is_true; apply MEM_In. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "convert_sub_every_var_exp" *)
Theorem convert_sub_every_var_exp : forall P (ls : list (exp a)),
  (forall x, MEM x ls -> every_var_exp P x) -> every_var_exp P (convert_sub ls).
Proof.
  intros P ls H. setoid_rewrite MEM_In' in H.
  assert (G : every_var_exp P (Op asm.Sub ls)).
  { cbn [every_var_exp]. unfold is_true; apply EVERY_Forall, Forall_forall. exact H. }
  destruct ls as [|x [|y [|z t]]].
  - exact G.
  - destruct x; exact G.
  - destruct x, y; try exact G; try reflexivity;
      cbn [convert_sub every_var_exp EVERY]; unfold is_true;
      rewrite (H _ (or_introl eq_refl)); reflexivity.
  - destruct x; try destruct y; exact G.
Qed.

Lemma EVERY_In_iff {B} (f : B -> bool) l : EVERY f l <-> (forall x, In x l -> f x).
Proof. unfold is_true; rewrite EVERY_Forall, Forall_forall; reflexivity. Qed.

(** HOL's free variables [P] and [op] are quantified first. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "optimize_consts_every_var_exp" *)
Theorem optimize_consts_every_var_exp : forall P op (ls : list (exp a)),
  (forall x, MEM x ls -> every_var_exp P x) -> every_var_exp P (optimize_consts op ls).
Proof.
  intros P op ls H. setoid_rewrite MEM_In' in H.
  unfold optimize_consts, PARTITION. rewrite PART_eq, !app_nil_r.
  assert (Hn : forall x, In x (rev (filter (fun x => negb (is_const x)) ls)) -> every_var_exp P x).
  { intros x Hx. apply in_rev, filter_In in Hx as [Hx _]. apply H, Hx. }
  destruct (rev (filter is_const ls)) as [|h t]; cbn zeta.
  - cbn [every_var_exp]. apply (proj2 (EVERY_In_iff _ _)), Hn.
  - unfold reduce_const.
    repeat match goal with |- context [decide ?P] => destruct (decide P) end;
      cbn [every_var_exp EVERY]; try reflexivity;
      try (destruct (rev (filter (fun x => negb (is_const x)) ls)) as [|y [|z u]] eqn:E;
           [reflexivity|apply Hn; left; reflexivity|]);
      try (apply (proj2 (EVERY_In_iff _ _)); exact Hn); try (apply (proj2 (EVERY_In_iff _ _)); rewrite <- E; exact Hn).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_ops_every_var_exp" *)
Theorem pull_ops_every_var_exp : forall P op (ls acc : list (exp a)),
  (forall e, MEM e acc -> every_var_exp P e) /\ (forall e, MEM e ls -> every_var_exp P e) ->
  forall e, MEM e (pull_ops op ls acc) -> every_var_exp P e.
Proof.
  intros P op ls. setoid_rewrite MEM_In'.
  induction ls as [|x ls IH]; intros acc [H1 H2] e He; cbn [pull_ops] in He; [apply H1, He|].
  assert (H2' : forall e, In e ls -> every_var_exp P e) by (intros; apply H2; right; assumption).
  assert (Hx : every_var_exp P x) by (apply H2; left; reflexivity).
  destruct x as [w|n|n|e0|op' l|sh e1 e2];
    try (refine (IH _ _ e He); split; [intros y [<-|Hy]; [exact Hx|apply H1, Hy]|exact H2']).
  destruct (decide (op = op')).
  - apply (IH (l ++ acc)); [split; [|exact H2']|exact He].
    intros y Hy. apply in_app_or in Hy as [Hy|Hy]; [|apply H1, Hy].
    cbn [every_var_exp] in Hx. apply (proj1 (EVERY_In_iff _ _) Hx), Hy.
  - refine (IH _ _ e He); split; [intros y [<-|Hy]; [exact Hx|apply H1, Hy]|exact H2'].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "pull_exp_every_var_exp" *)
Theorem pull_exp_every_var_exp : forall P (exp : exp a),
  every_var_exp P exp -> every_var_exp P (pull_exp exp).
Proof.
  intros P e. induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros H; try exact H.
  - exact (IH H).
  - cbn [every_var_exp] in H. pose proof (proj1 (EVERY_In_iff _ _) H) as Hall; clear H; rename Hall into H.
    assert (HM : forall x, MEM x (MAP pull_exp es) -> every_var_exp P x).
    { intros x Hx. apply MEM_In' in Hx. apply in_map_iff in Hx as [y [<- Hy]].
      rewrite Forall_forall in IH. apply IH; [exact Hy|apply H, Hy]. }
    destruct (decide (op = asm.Sub)) as [->|Hop].
    + cbn [pull_exp]. apply convert_sub_every_var_exp, HM.
    + destruct es as [|e1 [|e2 rest]].
      * destruct op; try congruence; reflexivity.
      * assert (G : every_var_exp P (pull_exp e1)) by (apply HM, MEM_In'; left; reflexivity).
        destruct op; try congruence; exact G.
      * assert (G : every_var_exp P (optimize_consts op (pull_ops op (MAP pull_exp (e1 :: e2 :: rest)) []))).
        { apply optimize_consts_every_var_exp. apply pull_ops_every_var_exp.
          split; [intros y Hy; discriminate Hy|exact HM]. }
        destruct op; try congruence; exact G.
  - cbn [every_var_exp pull_exp] in H |- *. unfold is_true in *.
    apply andb_prop in H as [H1 H2]. rewrite IH1, IH2 by assumption. reflexivity.
Qed.

End PullSyntax.

(** ** [flatten_exp] *)

Section Flatten.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

Lemma flatten_Op_cons op (x : exp a) xs :
  op <> asm.Sub -> xs <> [] ->
  flatten_exp (Op op (x :: xs)) = Op op [flatten_exp (Op op xs); flatten_exp x].
Proof. intros H1 H2. exact (proj1 (proj2 (proj2 (proj2 flatten_exp_eqns))) op x xs H1 H2). Qed.

Lemma flatten_Op_one op (x : exp a) : op <> asm.Sub -> flatten_exp (Op op [x]) = flatten_exp x.
Proof. intros H. exact (proj1 (proj2 (proj2 flatten_exp_eqns)) op x H). Qed.

Lemma flatten_Op_nil op : op <> asm.Sub -> flatten_exp (Op op []) = (op_consts op : exp a).
Proof. intros H. exact (proj1 (proj2 flatten_exp_eqns) op H). Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "flatten_exp_ok" *)
Theorem flatten_exp_ok : forall (exp : exp a) s x,
  word_exp s exp = SOME x -> word_exp s (flatten_exp exp) = SOME x.
Proof.
  intros e. induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros s x H; try exact H.
  - cbn [flatten_exp word_exp] in H |- *.
    destruct (word_exp s e) as [[v|]|] eqn:E; try discriminate. rewrite (IH s _ E). exact H.
  - destruct (decide (op = asm.Sub)) as [->|Hop].
    + rewrite (proj1 flatten_exp_eqns). rewrite word_exp_Op in H |- *.
      destruct (the_words (MAP (fun e => word_exp s e) es)) as [ws|] eqn:Ew; [|discriminate].
      assert (G : MAP (fun e => word_exp s e) (MAP flatten_exp es) = MAP (fun e => word_exp s e) es).
      { clear H. revert ws Ew; induction IH as [|e es He F IHF]; intros ws Ew; [reflexivity|].
        cbn [MAP List.map the_words] in Ew |- *.
        destruct (word_exp s e) as [[v|]|] eqn:E; try discriminate.
        destruct (the_words (MAP _ es)) as [ws'|] eqn:E2; [|discriminate].
        rewrite (He s _ E), (IHF ws' eq_refl). reflexivity. }
      rewrite G, Ew. exact H.
    + revert x H. induction IH as [|e es He F IHF]; intros x H.
      * rewrite flatten_Op_nil by exact Hop. destruct op; try congruence;
          cbn in H |- *; injection H as <-; reflexivity.
      * destruct es as [|e2 rest].
        -- rewrite flatten_Op_one by exact Hop.
           rewrite word_exp_Op_nonsub in H by exact Hop. cbn [MAP List.map the_words] in H.
           destruct (word_exp s e) as [[v|]|] eqn:E; cbn [the_words option_map OPTION_MAP FOLDR] in H;
             try discriminate.
           injection H as <-. rewrite opf_unit_r by exact Hop. apply He, E.
        -- rewrite flatten_Op_cons by (first [exact Hop|discriminate]).
           remember (e2 :: rest) as L eqn:EL.
           rewrite word_exp_Op_nonsub in H by exact Hop. cbn [MAP List.map the_words] in H.
           destruct (word_exp s e) as [[v|]|] eqn:E; try discriminate.
           destruct (the_words (MAP _ L)) as [ws|] eqn:Ew; [|discriminate].
           cbn [option_map OPTION_MAP FOLDR] in H. injection H as <-.
           assert (Hr : word_exp s (Op op L) = SOME (Word (FOLDR (opf op) (ope op) ws)))
             by (rewrite word_exp_Op_nonsub, Ew by exact Hop; reflexivity).
           rewrite word_exp_Op_nonsub by exact Hop. cbn [MAP List.map the_words].
           rewrite (IHF _ Hr), (He s _ E). cbn [option_map OPTION_MAP FOLDR].
           rewrite opf_unit_r, opf_comm by exact Hop. reflexivity.
  - cbn [flatten_exp word_exp] in H |- *.
    destruct (word_exp s e1) as [[v|]|] eqn:E1; try discriminate.
    destruct (word_exp s e2) as [[v2|]|] eqn:E2; try discriminate.
    rewrite (IH1 s _ E1), (IH2 s _ E2). exact H.
Qed.

End Flatten.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "binary_branch_exp_def" *)
Fixpoint binary_branch_exp {a} (e : exp a) : bool :=
  match e with
  | Op asm.Sub exps => EVERY binary_branch_exp exps
  | Op _ xs => (LENGTH xs =? 2) && EVERY binary_branch_exp xs
  | Load exp => binary_branch_exp exp
  | Shift shift exp nexp => binary_branch_exp exp && binary_branch_exp nexp
  | _ => true
  end.

Section FlattenSyntax.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "flatten_exp_binary_branch_exp" *)
Theorem flatten_exp_binary_branch_exp : forall (exp : exp a), binary_branch_exp (flatten_exp exp).
Proof.
  intros e. induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    try reflexivity.
  - exact IH.
  - destruct (decide (op = asm.Sub)) as [->|Hop].
    + rewrite (proj1 flatten_exp_eqns). cbn [binary_branch_exp]. apply (proj2 (EVERY_In_iff _ _)).
      intros x Hx. apply in_map_iff in Hx as [y [<- Hy]]. rewrite Forall_forall in IH. apply IH, Hy.
    + induction IH as [|e es He F IHF].
      * rewrite flatten_Op_nil by exact Hop. destruct op; try congruence; reflexivity.
      * destruct es as [|e2 rest].
        -- rewrite flatten_Op_one by exact Hop. exact He.
        -- rewrite flatten_Op_cons by (first [exact Hop|discriminate]).
           destruct op; try congruence; cbn [binary_branch_exp EVERY LENGTH]; unfold is_true;
             rewrite IHF, He; reflexivity.
  - cbn [flatten_exp binary_branch_exp]. unfold is_true in *. rewrite IH1, IH2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "flatten_exp_every_var_exp" *)
Theorem flatten_exp_every_var_exp : forall P (exp : exp a),
  every_var_exp P exp -> every_var_exp P (flatten_exp exp).
Proof.
  intros P e. induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros H; try exact H.
  - exact (IH H).
  - cbn [every_var_exp] in H. pose proof (proj1 (EVERY_In_iff _ _) H) as Hall; clear H; rename Hall into H.
    destruct (decide (op = asm.Sub)) as [->|Hop].
    + rewrite (proj1 flatten_exp_eqns). cbn [every_var_exp]. apply (proj2 (EVERY_In_iff _ _)).
      intros x Hx. apply in_map_iff in Hx as [y [<- Hy]]. rewrite Forall_forall in IH.
      apply IH; [exact Hy|apply H, Hy].
    + induction IH as [|e es He F IHF].
      * rewrite flatten_Op_nil by exact Hop. destruct op; try congruence; reflexivity.
      * assert (H1 : every_var_exp P e) by (apply H; left; reflexivity).
        assert (H2 : forall x, In x es -> every_var_exp P x) by (intros; apply H; right; assumption).
        destruct es as [|e2 rest].
        -- rewrite flatten_Op_one by exact Hop. exact (He H1).
        -- rewrite flatten_Op_cons by (first [exact Hop|discriminate]).
           cbn [every_var_exp EVERY]; unfold is_true; rewrite (IHF H2), (He H1); reflexivity.
  - cbn [every_var_exp flatten_exp] in H |- *. unfold is_true in *.
    apply andb_prop in H as [H1 H2]. rewrite IH1, IH2 by assumption. reflexivity.
Qed.

End FlattenSyntax.

(** ** [inst_select] correctness *)

Section ShiftZero.
Context {a : N}.

Lemma dimindex_ge1 : 1 <= dimindex a.
Proof. unfold dimindex; lia. Qed.

Lemma word_lsl_0 (w : word a) : word_lsl w 0 = w.
Proof.
  unfold word_lsl. destruct (dimindex a - 1 <? 0) eqn:E; [apply N.ltb_lt in E; lia|].
  apply word_eq_w2n. rewrite w2n_n2w', N.pow_0_r, N.mul_1_r. apply N.mod_small, w2n_lt_dimword.
Qed.

Lemma BITS_low_all n : BITS (dimindex a - 1) 0 n = n MOD dimword a.
Proof.
  unfold BITS, MOD_2EXP, DIV_2EXP, dimword. rewrite N.pow_0_r, N.div_1_r.
  pose proof dimindex_ge1. f_equal. f_equal. lia.
Qed.

Lemma word_lsr_0 (w : word a) : word_lsr w 0 = w.
Proof.
  unfold word_lsr, word_bits. unfold MIN.
  destruct (dimindex a - 1 <? dimindex a - 1) eqn:E; [apply N.ltb_lt in E; lia|].
  apply word_eq_w2n. rewrite w2n_n2w', BITS_low_all, N.Div0.mod_mod.
  apply N.mod_small, w2n_lt_dimword.
Qed.

Lemma word_asr_0 (w : word a) : word_asr w 0 = w.
Proof.
  unfold word_asr. rewrite word_lsr_0. destruct (word_msb w); [|reflexivity].
  unfold MIN. destruct (0 <? dimindex a) eqn:E; [|apply N.ltb_ge in E; pose proof dimindex_ge1; lia].
  rewrite N.sub_0_r. unfold word_lsl at 1.
  destruct (dimindex a - 1 <? dimindex a) eqn:E2; [|apply N.ltb_ge in E2; pose proof dimindex_ge1; lia].
  rewrite word_or_comm. apply word_or_0.
Qed.

Lemma word_ror_0 (w : word a) : word_ror w 0 = w.
Proof.
  unfold word_ror. pose proof dimindex_ge1. pose proof (ZERO_LT_dimword a).
  rewrite (N.Div0.mod_0_l (dimindex a)). rewrite N.sub_0_r, BITS_low_all.
  apply word_eq_w2n. rewrite w2n_n2w'. fold (dimword a).
  rewrite N.Div0.add_mod, N.Div0.mod_mul, N.add_0_r, !N.Div0.mod_mod.
  apply N.mod_small, w2n_lt_dimword.
Qed.

Lemma word_sh_0 sh (w : word a) : word_sh sh w 0 = Some w.
Proof.
  unfold word_sh. cbn [N.eqb negb andb].
  destruct sh; f_equal; [apply word_lsl_0|apply word_lsr_0|apply word_asr_0|apply word_ror_0].
Qed.

End ShiftZero.

Section InstSelectExp.
Context {a : N} {c ffi_t : Type}.
Implicit Types s : state a c ffi_t.

(** Galette-only: a size for well-founded induction on expressions. *)
Fixpoint esize (e : exp a) : nat :=
  match e with
  | Load e => Datatypes.S (esize e)
  | Op _ l => Datatypes.S (list_sum (List.map esize l))
  | Shift _ e1 e2 => Datatypes.S (esize e1 + esize e2)
  | _ => 1
  end.

Definition sel_post tar temp (w : word_loc a) s (loc' : num_map (word_loc a)) : Prop :=
  forall x, if decide (x = tar) then lookup x loc' = SOME w
            else if x <? temp then lookup x loc' = lookup x (locals s) else True.

Lemma sel_post_insert tar temp w s L :
  locals_rel temp (locals s) L -> sel_post tar temp w s (insert tar w L).
Proof.
  intros Hl x. rewrite lookup_insert. destruct (decide (x = tar)); [reflexivity|].
  destruct (x <? temp) eqn:E; [|exact Logic.I]. apply N.ltb_lt in E. symmetry; apply Hl, E.
Qed.

Lemma sel_post_temp temp v s L :
  sel_post temp temp v s L -> lookup temp L = SOME v /\ locals_rel temp (locals s) L.
Proof.
  intros H. split.
  - specialize (H temp). destruct (decide (temp = temp)); [exact H|congruence].
  - intros x Hx. specialize (H x). destruct (decide (x = temp)); [lia|].
    apply N.ltb_lt in Hx. rewrite Hx in H. symmetry; exact H.
Qed.

Lemma ev_seq_none (p q : prog a) s s1 :
  evaluate (p, s) = (NONE, s1) -> evaluate (Seq p q, s) = evaluate (q, s1).
Proof. intros H. rewrite (evaluate_eqn (Seq p q)); cbn [evaluate_body]. rewrite fix_clock_evaluate, H. reflexivity. Qed.

Lemma ev_binop op tar r2 (ri : reg_imm a) L s v1 v2 r :
  lookup r2 L = SOME (Word v1) ->
  match ri with Reg r3 => lookup r3 L | Imm w => SOME (Word w) end = SOME (Word v2) ->
  word_op op [v1; v2] = SOME r ->
  evaluate (Inst (Arith (Binop op tar r2 ri)), set_locals L s) =
  (NONE, set_locals (insert tar (Word r) L) s).
Proof.
  intros H1 H2 H3. rewrite evaluate_eqn; cbn [evaluate_body inst]; unfold assign.
  destruct ri as [r3|w]; cbn [word_exp MAP List.map]; unfold get_var; cbn [locals set_locals];
    rewrite H1; try rewrite H2; cbn [the_words]; [|injection H2 as <-]; rewrite H3; reflexivity.
Qed.

Lemma ev_shift sh tar r2 (ri : reg_imm a) L s v1 v2 r :
  lookup r2 L = SOME (Word v1) ->
  match ri with Reg r3 => lookup r3 L | Imm w => SOME (Word w) end = SOME (Word v2) ->
  word_sh sh v1 (w2n v2) = SOME r ->
  evaluate (Inst (Arith (asm.Shift sh tar r2 ri)), set_locals L s) =
  (NONE, set_locals (insert tar (Word r) L) s).
Proof.
  intros H1 H2 H3. rewrite evaluate_eqn; cbn [evaluate_body inst]; unfold assign.
  destruct ri as [r3|w]; cbn [word_exp]; unfold get_var; cbn [locals set_locals];
    rewrite H1; try rewrite H2; [|injection H2 as <-]; rewrite H3; reflexivity.
Qed.

Lemma ev_opcurrheap op tar r2 L s v1 ch r :
  lookup r2 L = SOME (Word v1) -> get_store stackLang.CurrHeap s = SOME (Word ch) ->
  word_op op [v1; ch] = SOME r ->
  evaluate (OpCurrHeap op tar r2, set_locals L s) = (NONE, set_locals (insert tar (Word r) L) s).
Proof.
  intros H1 H2 H3. rewrite evaluate_eqn; cbn [evaluate_body word_exp MAP List.map].
  unfold get_var; cbn [locals set_locals]. rewrite H1.
  change (get_store stackLang.CurrHeap (set_locals L s)) with (get_store stackLang.CurrHeap s). rewrite H2.
  cbn [the_words]. rewrite H3. reflexivity.
Qed.

Lemma ev_load tar a0 (w0 : word a) L s v x :
  lookup a0 L = SOME (Word v) -> mem_load (FOLDR word_add (n2w 0) [v; w0]) s = SOME x ->
  evaluate (Inst (Mem asm.Load tar (Addr a0 w0)), set_locals L s) =
  (NONE, set_locals (insert tar x L) s).
Proof.
  intros H1 H2. rewrite evaluate_eqn; cbn [evaluate_body inst word_exp MAP List.map].
  unfold get_var; cbn [locals set_locals]. rewrite H1. cbn [the_words word_op OPTION_MAP option_map].
  change (mem_load ?y (set_locals L s)) with (mem_load y s). rewrite H2. reflexivity.
Qed.

Lemma ev_move1 tar r L s x :
  lookup r L = SOME x ->
  evaluate (@Move a 0 [(tar, r)], set_locals L s) = (NONE, set_locals (insert tar x L) s).
Proof.
  intros H. rewrite evaluate_eqn; cbn [evaluate_body MAP List.map fst snd FST SND ALL_DISTINCT MEM negb andb].
  cbn [get_vars]. unfold get_var; cbn [locals set_locals]. rewrite H. reflexivity.
Qed.

Lemma ev_const tar (w : word a) L s :
  evaluate (Inst (asm.Const tar w), set_locals L s) = (NONE, set_locals (insert tar (Word w) L) s).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma the_words_length (l : list (option (word_loc a))) ws :
  the_words l = SOME ws -> length ws = length l.
Proof.
  revert ws; induction l as [|x l IH]; intros ws H; cbn in H; [injection H as <-; reflexivity|].
  destruct x as [[v|]|]; try discriminate. destruct (the_words l) as [ws'|]; [|discriminate].
  injection H as <-. cbn. rewrite (IH ws' eq_refl). reflexivity.
Qed.

Lemma word_op_comm2 op (x y : word a) : op <> asm.Sub -> word_op op [x; y] = word_op op [y; x].
Proof.
  intros H. rewrite !word_op_FOLDR by exact H. cbn [FOLDR].
  rewrite !opf_unit_r, opf_comm by exact H. reflexivity.
Qed.

Lemma load_case c0 tar temp (e : exp a) :
  (exists e' w', e = Op asm.Add [e'; Const w'] /\ addr_offset_ok c0 w' /\
     inst_select_exp c0 tar temp (Load e) =
     Seq (inst_select_exp c0 temp temp e') (Inst (Mem asm.Load tar (Addr temp w')))) \/
  inst_select_exp c0 tar temp (Load e) =
  Seq (inst_select_exp c0 temp temp e) (Inst (Mem asm.Load tar (Addr temp (n2w 0)))).
Proof.
  destruct e as [| | | |op l|]; try (right; reflexivity).
  destruct op; try (right; reflexivity).
  destruct l as [|e' [|y [|z t]]]; try (right; reflexivity);
    destruct y; try (right; reflexivity).
  cbn [inst_select_exp]. destruct (addr_offset_ok c0 w) eqn:E; [left; eauto|right; reflexivity].
Qed.

(** HOL's [c] (an [asm_config]) is [c0]; HOL's [x < temp] is [x <? temp]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "inst_select_exp_thm" *)
Theorem inst_select_exp_thm : forall c0 tar temp (exp : exp a) s w loc,
  binary_branch_exp exp /\ every_var_exp (fun x => x <? temp) exp /\
  locals_rel temp (locals s) loc /\ word_exp s exp = SOME w ->
  exists loc',
    evaluate (inst_select_exp c0 tar temp exp, set_locals loc s) = (NONE, set_locals loc' s) /\
    forall x, if decide (x = tar) then lookup x loc' = SOME w
              else if x <? temp then lookup x loc' = lookup x (locals s) else True.
Proof.
  intros c0 tar temp e. revert tar temp.
  remember (esize e) as n eqn:Hn. revert e Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros e Hn tar temp s w loc (Hb & Hv & Hl & H).
  change (exists loc', evaluate (inst_select_exp c0 tar temp e, set_locals loc s) =
                       (NONE, set_locals loc' s) /\ sel_post tar temp w s loc').
  (* the recursive call on a smaller expression, with target [temp] *)
  assert (IHt : forall e', (esize e' < n)%nat -> forall s' w' loc',
            binary_branch_exp e' -> every_var_exp (fun x => x <? temp) e' ->
            locals_rel temp (locals s') loc' -> word_exp s' e' = SOME w' ->
            exists l1, evaluate (inst_select_exp c0 temp temp e', set_locals loc' s') =
                       (NONE, set_locals l1 s') /\
                       lookup temp l1 = SOME w' /\ locals_rel temp (locals s') l1).
  { intros e' Hlt s' w' loc' Hb' Hv' Hl' He'.
    destruct (IH _ Hlt e' eq_refl temp temp s' w' loc' (conj Hb' (conj Hv' (conj Hl' He'))))
      as [l1 [Ev Hp]].
    exists l1. split; [exact Ev|]. exact (sel_post_temp _ _ _ _ Hp). }
  destruct e as [w0|v|nm|e|op l|sh e e0].
  - (* Const *)
    cbn in H. injection H as <-. exists (insert tar (Word w0) loc). split.
    + apply ev_const.
    + apply sel_post_insert, Hl.
  - (* Var *)
    cbn [every_var_exp] in Hv. apply N.ltb_lt in Hv.
    exists (insert tar w loc). split.
    + apply ev_move1. rewrite <- (Hl v Hv). exact H.
    + apply sel_post_insert, Hl.
  - (* Lookup *)
    exists (insert tar w loc). split.
    + rewrite evaluate_eqn; cbn [evaluate_body inst_select_exp].
      change (get_store nm (set_locals loc s)) with (get_store nm s). cbn in H. rewrite H. reflexivity.
    + apply sel_post_insert, Hl.
  - (* Load *)
    cbn [binary_branch_exp every_var_exp] in Hb, Hv. cbn [word_exp] in H.
    destruct (word_exp s e) as [[ad|]|] eqn:E; try discriminate.
    destruct (load_case c0 tar temp e) as [[e' [w' [-> [Hok Ep]]]]|Ep]; rewrite Ep.
    + cbn [binary_branch_exp every_var_exp EVERY LENGTH] in Hb, Hv. unfold is_true in Hb, Hv.
      apply andb_prop in Hb as [_ Hb]. apply andb_prop in Hb as [Hb _].
      apply andb_prop in Hv as [Hv _].
      rewrite word_exp_Op in E. cbn [MAP List.map the_words word_exp] in E.
      destruct (word_exp s e') as [[v|]|] eqn:E'; try discriminate.
      assert (Ead : FOLDR word_add (n2w 0) [v; w'] = ad)
        by (cbn [word_op the_words option_map OPTION_MAP] in E; congruence).
      destruct (IHt e' ltac:(subst n; cbn; lia) s (Word v) loc Hb Hv Hl E') as [l1 [Ev [Ht Hl1]]].
      exists (insert tar w l1). split; [|apply sel_post_insert, Hl1].
      rewrite (ev_seq_none _ _ _ _ Ev). apply (ev_load _ _ _ _ _ v w Ht).
      rewrite Ead. exact H.
    + destruct (IHt e ltac:(subst n; cbn; lia) s (Word ad) loc Hb Hv Hl E) as [l1 [Ev [Ht Hl1]]].
      exists (insert tar w l1). split; [|apply sel_post_insert, Hl1].
      rewrite (ev_seq_none _ _ _ _ Ev). apply (ev_load _ _ _ _ _ ad w Ht).
      cbn [FOLDR]. rewrite !word_add_0'. exact H.
  - (* Op *)
    rewrite word_exp_Op in H.
    destruct (the_words (MAP (fun e => word_exp s e) l)) as [ws|] eqn:Ew; [|discriminate].
    pose proof (the_words_length _ _ Ew) as Hlen. rewrite length_map in Hlen.
    destruct l as [|e1 [|e2 [|e3 l']]];
      try (exfalso; destruct op;
           first [ cbn [binary_branch_exp] in Hb; unfold is_true in Hb;
                   apply andb_prop in Hb as [Hb _]; apply N.eqb_eq in Hb;
                   rewrite LENGTH_length in Hb; cbn [length] in Hb; lia
                 | destruct ws as [|? [|? [|? ?]]]; cbn [length] in Hlen; try discriminate Hlen;
                   cbn [word_op OPTION_MAP option_map] in H; discriminate H ]).
    assert (Hb12 : binary_branch_exp e1 /\ binary_branch_exp e2).
    { destruct op; cbn [binary_branch_exp EVERY LENGTH] in Hb; unfold is_true in Hb;
        rewrite ?Bool.andb_true_iff in Hb; tauto. }
    destruct Hb12 as [Hb1 Hb2].
    cbn [every_var_exp EVERY] in Hv. unfold is_true in Hv. rewrite !Bool.andb_true_iff in Hv.
    destruct Hv as [Hv1 [Hv2 _]].
    cbn [MAP List.map the_words] in Ew.
    destruct (word_exp s e1) as [[v1|]|] eqn:E1; try discriminate.
    destruct (word_exp s e2) as [[v2|]|] eqn:E2; try discriminate.
    injection Ew as <-.
    destruct (word_op op [v1; v2]) as [r|] eqn:Er; [|discriminate]. injection H as <-.
    assert (Hlt1 : (esize e1 < n)%nat) by (subst n; cbn; lia).
    assert (Hlt2 : (esize e2 < n)%nat) by (subst n; cbn; lia).
    (* generic second operand: evaluated into [temp + 1] *)
    assert (Gen : forall l1, locals_rel temp (locals s) l1 ->
              exists l2, evaluate (inst_select_exp c0 (temp + 1) (temp + 1) e2, set_locals l1 s) =
                         (NONE, set_locals l2 s) /\
                         lookup (temp + 1) l2 = SOME (Word v2) /\
                         (forall x, x < temp + 1 -> lookup x l2 = lookup x l1)).
    { intros l1 Hl1.
      assert (Hv2' : every_var_exp (fun x => x <? temp + 1) e2).
      { apply (every_var_exp_mono (fun x => x <? temp)); split; [|exact Hv2].
        intros x Hx; unfold is_true in *; apply N.ltb_lt in Hx; apply N.ltb_lt; lia. }
      assert (E2' : word_exp (set_locals l1 s) e2 = SOME (Word v2))
        by (rewrite (locals_rel_word_exp_simp temp l1 s e2 (conj Hv2 Hl1)); exact E2).
      destruct (IH _ Hlt2 e2 eq_refl (temp + 1) (temp + 1) (set_locals l1 s) (Word v2) l1
                  (conj Hb2 (conj Hv2' (conj (fun x _ => eq_refl) E2')))) as [l2 [Ev Hp]].
      exists l2. split; [exact Ev|]. split.
      - specialize (Hp (temp + 1)). destruct (decide _); [exact Hp|congruence].
      - intros x Hx. specialize (Hp x). destruct (decide (x = temp + 1)); [lia|].
        apply N.ltb_lt in Hx. rewrite Hx in Hp. exact Hp. }
    cbn [inst_select_exp].
    destruct (is_Lookup_CurrHeap e2) eqn:Ec2.
    + destruct e2 as [| |nm| | |]; try discriminate Ec2. destruct nm; try discriminate Ec2.
      destruct (IHt e1 Hlt1 s (Word v1) loc Hb1 Hv1 Hl E1) as [l1 [Ev [Ht Hl1]]].
      exists (insert tar (Word r) l1). split; [|apply sel_post_insert, Hl1].
      rewrite (ev_seq_none _ _ _ _ Ev). exact (ev_opcurrheap _ _ _ _ _ _ _ _ Ht E2 Er).
    + destruct (is_Lookup_CurrHeap e1 && negb (bool_decide (op = asm.Sub))) eqn:Ec1.
      * apply andb_prop in Ec1 as [Ec1 Hop0].
        assert (Hop : op <> asm.Sub).
        { intros ->. apply Bool.negb_true_iff in Hop0.
          rewrite (proj2 (bool_decide_spec (asm.Sub = asm.Sub)) eq_refl) in Hop0. discriminate. }
        destruct e1 as [| |nm| | |]; try discriminate Ec1. destruct nm; try discriminate Ec1.
        destruct (IHt e2 Hlt2 s (Word v2) loc Hb2 Hv2 Hl E2) as [l1 [Ev [Ht Hl1]]].
        exists (insert tar (Word r) l1). split; [|apply sel_post_insert, Hl1].
        rewrite (ev_seq_none _ _ _ _ Ev). apply (ev_opcurrheap _ _ _ _ _ _ _ _ Ht E1).
        rewrite word_op_comm2 by exact Hop. exact Er.
      * destruct (IHt e1 Hlt1 s (Word v1) loc Hb1 Hv1 Hl E1) as [l1 [Ev [Ht Hl1]]].
        destruct e2 as [w2| | | | |].
        1:{ cbn in E2. injection E2 as ->.
           destruct (valid_imm c0 (inl op) v2) eqn:Evi.
           ++ exists (insert tar (Word r) l1). split; [|apply sel_post_insert, Hl1].
              rewrite (ev_seq_none _ _ _ _ Ev). exact (ev_binop _ _ _ (Imm v2) _ _ _ _ _ Ht eq_refl Er).
           ++ destruct (bool_decide (op = asm.Add) && valid_imm c0 (inl asm.Sub) (word_2comp v2)) eqn:Ea.
              ** apply andb_prop in Ea as [Ea _]. apply bool_decide_spec in Ea. subst op.
                 exists (insert tar (Word r) l1). split; [|apply sel_post_insert, Hl1].
                 rewrite (ev_seq_none _ _ _ _ Ev).
                 apply (ev_binop _ _ _ (Imm (word_2comp v2)) _ _ _ _ _ Ht eq_refl).
                 cbn [word_op FOLDR] in Er |- *. injection Er as <-.
                 rewrite WORD_SUB_RNEG, word_add_0'. reflexivity.
              ** exists (insert tar (Word r) (insert (temp + 1) (Word v2) l1)). split.
                 --- rewrite (ev_seq_none _ _ _ _ Ev), (ev_seq_none _ _ _ _ (ev_const _ _ _ _)).
                     eapply (ev_binop _ _ _ (Reg (temp + 1)) _ _ _ _ _); [|cbn|exact Er].
                     +++ rewrite lookup_insert. destruct (decide (temp = temp + 1)); [lia|exact Ht].
                     +++ rewrite lookup_insert. destruct (decide _); [reflexivity|congruence].
                 --- apply sel_post_insert. intros x Hx. rewrite lookup_insert.
                     destruct (decide (x = temp + 1)); [lia|]. apply Hl1, Hx. }
        all: destruct (Gen l1 Hl1) as [l2 [Ev2 [Ht2 Hl2]]];
          exists (insert tar (Word r) l2); split;
          [ rewrite (ev_seq_none _ _ _ _ Ev), (ev_seq_none _ _ _ _ Ev2);
            eapply (ev_binop _ _ _ (Reg (temp + 1)) _ _ _ _ _); [|exact Ht2|exact Er];
            rewrite (Hl2 temp ltac:(lia)); exact Ht
          | apply sel_post_insert; intros x Hx; rewrite (Hl2 x ltac:(lia)); apply Hl1, Hx ].
  - (* Shift *)
    cbn [binary_branch_exp every_var_exp] in Hb, Hv. unfold is_true in Hb, Hv.
    apply andb_prop in Hb as [Hb1 Hb2]. apply andb_prop in Hv as [Hv1 Hv2].
    cbn [word_exp] in H.
    destruct (word_exp s e) as [[v1|]|] eqn:E1; try discriminate.
    destruct (word_exp s e0) as [[v2|]|] eqn:E2; try discriminate.
    destruct (word_sh sh v1 (w2n v2)) as [r|] eqn:Er; [|discriminate]. injection H as <-.
    assert (Hlt1 : (esize e < n)%nat) by (subst n; cbn; lia).
    assert (Hlt2 : (esize e0 < n)%nat) by (subst n; cbn; lia).
    destruct (IHt e Hlt1 s (Word v1) loc Hb1 Hv1 Hl E1) as [l1 [Ev [Ht Hl1]]].
    assert (Gen : exists l2, evaluate (inst_select_exp c0 (temp + 1) (temp + 1) e0, set_locals l1 s) =
                             (NONE, set_locals l2 s) /\
                             lookup (temp + 1) l2 = SOME (Word v2) /\
                             (forall x, x < temp + 1 -> lookup x l2 = lookup x l1)).
    { assert (Hv2' : every_var_exp (fun x => x <? temp + 1) e0).
      { apply (every_var_exp_mono (fun x => x <? temp)); split; [|exact Hv2].
        intros x Hx; unfold is_true in *; apply N.ltb_lt in Hx; apply N.ltb_lt; lia. }
      assert (E2' : word_exp (set_locals l1 s) e0 = SOME (Word v2))
        by (rewrite (locals_rel_word_exp_simp temp l1 s e0 (conj Hv2 Hl1)); exact E2).
      destruct (IH _ Hlt2 e0 eq_refl (temp + 1) (temp + 1) (set_locals l1 s) (Word v2) l1
                  (conj Hb2 (conj Hv2' (conj (fun x _ => eq_refl) E2')))) as [l2 [Ev' Hp]].
      exists l2. split; [exact Ev'|]. split.
      - specialize (Hp (temp + 1)). destruct (decide _); [exact Hp|congruence].
      - intros x Hx. specialize (Hp x). destruct (decide (x = temp + 1)); [lia|].
        apply N.ltb_lt in Hx. rewrite Hx in Hp. exact Hp. }
    destruct e0 as [w2| | | | |].
    1:{ cbn in E2. injection E2 as ->. cbn [inst_select_exp].
      destruct (w2n v2 <? dimindex a) eqn:Elt.
      * cbn zeta. destruct (w2n v2 =? 0) eqn:Ez.
        -- apply N.eqb_eq in Ez. rewrite Ez, word_sh_0 in Er. injection Er as <-.
           exists (insert tar (Word v1) l1). split; [|apply sel_post_insert, Hl1].
           rewrite (ev_seq_none _ _ _ _ Ev). apply ev_move1, Ht.
        -- exists (insert tar (Word r) l1). split; [|apply sel_post_insert, Hl1].
           rewrite (ev_seq_none _ _ _ _ Ev).
           eapply (ev_shift _ _ _ (Imm (n2w (w2n v2))) _ _ _ _ _ Ht eq_refl).
           rewrite w2n_n2w', N.mod_small; [exact Er|]. apply w2n_lt_dimword.
      * exfalso. apply N.ltb_ge in Elt. pose proof (dimindex_ge1 (a := a)).
        unfold word_sh in Er.
        replace (negb (w2n v2 =? 0) && (dimindex a <=? w2n v2)) with true in Er; [discriminate|].
        symmetry. apply andb_true_intro. split; [apply Bool.negb_true_iff, N.eqb_neq; lia|apply N.leb_le; lia].
    }
    all: destruct Gen as [l2 [Ev2 [Ht2 Hl2]]];
        exists (insert tar (Word r) l2); split;
        [ cbn [inst_select_exp]; rewrite (ev_seq_none _ _ _ _ Ev), (ev_seq_none _ _ _ _ Ev2);
          eapply (ev_shift _ _ _ (Reg (temp + 1)) _ _ _ _ _); [|exact Ht2|exact Er];
          rewrite (Hl2 temp ltac:(lia)); exact Ht
        | apply sel_post_insert; intros x Hx; rewrite (Hl2 x ltac:(lia)); apply Hl1, Hx ].
Qed.

End InstSelectExp.

Section InstSelect.
Context {a : N} {c ffi_t : Type}.
Implicit Types s st : state a c ffi_t.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "locals_rm" *)
Theorem locals_rm : forall (D : state a c ffi_t), set_locals (locals D) D = D.
Proof. intros [] ; reflexivity. Qed.

(** Galette-only: the conclusion of [inst_select_thm]. *)
Definition isel_post temp (res : option (result a)) (rst : state a c ffi_t) loc' : Prop :=
  match res with
  | NONE => locals_rel temp (locals rst) loc'
  | SOME (Break _) => locals_rel temp (locals rst) loc'
  | SOME (Continue _) => locals_rel temp (locals rst) loc'
  | SOME _ => locals rst = loc'
  end.

Lemma isel_post_refl temp res rst : isel_post temp res rst (locals rst).
Proof. destruct res as [[]|]; cbn; try reflexivity; intros x _; reflexivity. Qed.

(** The preprocessed expression of [inst_select]: its value and syntax. *)
Lemma pre_exp_facts temp (exp : exp a) st w :
  every_var_exp (fun x => x <? temp) exp -> word_exp st exp = SOME w ->
  word_exp st (flatten_exp (pull_exp exp)) = SOME w /\
  binary_branch_exp (flatten_exp (pull_exp exp)) /\
  every_var_exp (fun x => x <? temp) (flatten_exp (pull_exp exp)).
Proof.
  intros Hv H. split; [apply flatten_exp_ok, pull_exp_ok, H|]. split.
  - apply flatten_exp_binary_branch_exp.
  - apply flatten_exp_every_var_exp, pull_exp_every_var_exp, Hv.
Qed.

Lemma addr_sel2 c0 temp (E : exp a) st loc ad :
  binary_branch_exp E -> every_var_exp (fun x => x <? temp) E ->
  locals_rel temp (locals st) loc -> word_exp st E = SOME (Word ad) ->
  exists l1, evaluate (inst_select_exp c0 temp temp E, set_locals loc st) = (NONE, set_locals l1 st) /\
    word_exp (set_locals l1 st) (Op asm.Add [Var temp; Const (n2w 0)]) = SOME (Word ad) /\
    word_exp (set_locals l1 st) (Var temp) = SOME (Word ad) /\
    locals_rel temp (locals st) l1.
Proof.
  intros Hb Hv Hl H.
  destruct (inst_select_exp_thm c0 temp temp E st (Word ad) loc (conj Hb (conj Hv (conj Hl H))))
    as [l1 [Ev Hp]].
  destruct (sel_post_temp _ _ _ _ Hp) as [Ht Hl1].
  exists l1. split; [exact Ev|]. split; [|split; [exact Ht|exact Hl1]].
  cbn [word_exp MAP List.map the_words]. unfold get_var; cbn [locals set_locals]. rewrite Ht.
  cbn [the_words word_op FOLDR option_map OPTION_MAP]. rewrite !word_add_0'. reflexivity.
Qed.

Lemma addr_sel1 c0 temp (e' : exp a) w' st loc ad :
  binary_branch_exp (Op asm.Add [e'; Const w']) ->
  every_var_exp (fun x => x <? temp) (Op asm.Add [e'; Const w']) ->
  locals_rel temp (locals st) loc -> word_exp st (Op asm.Add [e'; Const w']) = SOME (Word ad) ->
  exists l1, evaluate (inst_select_exp c0 temp temp e', set_locals loc st) = (NONE, set_locals l1 st) /\
    word_exp (set_locals l1 st) (Op asm.Add [Var temp; Const w']) = SOME (Word ad) /\
    locals_rel temp (locals st) l1.
Proof.
  intros Hb Hv Hl H.
  cbn [binary_branch_exp every_var_exp EVERY LENGTH] in Hb, Hv. unfold is_true in Hb, Hv.
  apply andb_prop in Hb as [_ Hb]. apply andb_prop in Hb as [Hb _].
  apply andb_prop in Hv as [Hv _].
  rewrite word_exp_Op in H. cbn [MAP List.map the_words word_exp] in H.
  destruct (word_exp st e') as [[v|]|] eqn:E'; try discriminate.
  destruct (inst_select_exp_thm c0 temp temp e' st (Word v) loc (conj Hb (conj Hv (conj Hl E'))))
    as [l1 [Ev Hp]].
  destruct (sel_post_temp _ _ _ _ Hp) as [Ht Hl1].
  exists l1. split; [exact Ev|]. split; [|exact Hl1].
  cbn [word_exp MAP List.map the_words]. unfold get_var; cbn [locals set_locals]. rewrite Ht.
  exact H.
Qed.

End InstSelect.

Section InstSelectThm.
Context {a : N} {c ffi_t : Type}.
Implicit Types s st : state a c ffi_t.

Lemma store_case c0 temp (exp : exp a) var :
  (exists e' w', flatten_exp (pull_exp exp) = Op asm.Add [e'; Const w'] /\ addr_offset_ok c0 w' /\
     inst_select c0 temp (Store exp var) =
     Seq (inst_select_exp c0 temp temp e') (Inst (Mem asm.Store var (Addr temp w')))) \/
  inst_select c0 temp (Store exp var) =
  Seq (inst_select_exp c0 temp temp (flatten_exp (pull_exp exp)))
      (Inst (Mem asm.Store var (Addr temp (n2w 0)))).
Proof.
  cbn [inst_select]. cbn zeta. destruct (flatten_exp (pull_exp exp)) as [| | | |op l|] eqn:E;
    try (right; reflexivity).
  destruct op; try (right; reflexivity).
  destruct l as [|e' [|y [|z t]]]; try (right; reflexivity); destruct y; try (right; reflexivity).
  destruct (addr_offset_ok c0 w) eqn:Ew; [left; eauto|right; reflexivity].
Qed.

Lemma share_case c0 temp op v (exp : exp a) :
  (exists e' w', flatten_exp (pull_exp exp) = Op asm.Add [e'; Const w'] /\
     inst_select c0 temp (ShareInst op v exp) =
     Seq (inst_select_exp c0 temp temp e') (ShareInst op v (Op asm.Add [Var temp; Const w']))) \/
  inst_select c0 temp (ShareInst op v exp) =
  Seq (inst_select_exp c0 temp temp (flatten_exp (pull_exp exp))) (ShareInst op v (Var temp)).
Proof.
  cbn [inst_select]. cbn zeta. destruct (flatten_exp (pull_exp exp)) as [| | | |op' l|] eqn:E;
    try (right; reflexivity).
  destruct op'; try (right; reflexivity).
  destruct l as [|e' [|y [|z t]]]; try (right; reflexivity); destruct y; try (right; reflexivity).
  match goal with |- context [if ?b then _ else _] => destruct b end; [left; eauto|right; reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "locals_rel_cut_envs_local" *)
Theorem locals_rel_cut_envs_local : forall temp (loc loc' : num_map (word_loc a)) names x,
  locals_rel temp loc loc' /\ every_name (fun x => x <? temp) names /\ cut_envs names loc = SOME x ->
  cut_envs names loc' = SOME x.
Proof. intros temp loc loc' names x H. exact (locals_rel_cut_envs temp loc loc' names x H). Qed.

Lemma isel_post_exit_loop temp r (rst : state a c ffi_t) l : isel_post temp r rst l -> isel_post temp (exit_loop r) rst l.
Proof. destruct r as [[]|]; cbn; auto. Qed.

(** HOL's [c] (an [asm_config]) is [c0]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "inst_select_Loop_helper" *)
Theorem inst_select_Loop_helper : forall (s : state a c ffi_t) names (prog : prog a) exit_names res rst c0 temp loc,
  (forall (st : state a c ffi_t) res rst loc,
     evaluate (prog, st) = (res, rst) /\ res <> SOME Error /\ locals_rel temp (locals st) loc ->
     exists loc',
       evaluate (inst_select c0 temp prog, set_locals loc st) = (res, set_locals loc' rst) /\
       match res with
       | NONE => locals_rel temp (locals rst) loc'
       | SOME (Break _) => locals_rel temp (locals rst) loc'
       | SOME (Continue _) => locals_rel temp (locals rst) loc'
       | SOME _ => locals rst = loc'
       end) /\
  evaluate (Loop names prog exit_names, s) = (res, rst) /\ res <> SOME Error /\
  every_var (fun x => x <? temp) prog /\ every_name (fun x => x <? temp) (names, LN) /\
  every_name (fun x => x <? temp) (exit_names, LN) /\ locals_rel temp (locals s) loc ->
  exists loc',
    evaluate (Loop names (inst_select c0 temp prog) exit_names, set_locals loc s) =
    (res, set_locals loc' rst) /\
    match res with
    | NONE => locals_rel temp (locals rst) loc'
    | SOME (Break _) => locals_rel temp (locals rst) loc'
    | SOME (Continue _) => locals_rel temp (locals rst) loc'
    | SOME _ => locals rst = loc'
    end.
Proof.
  intros s names prog exit_names res rst c0 temp loc (HB & H & Hr & Hv & Hn1 & Hn2 & Hl).
  change (exists loc', evaluate (Loop names (inst_select c0 temp prog) exit_names, set_locals loc s) =
                       (res, set_locals loc' rst) /\ isel_post temp res rst loc').
  revert loc res rst H Hr Hl.
  remember (N.to_nat (clock s)) as n eqn:Hn. revert s Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros s Hn loc res rst H Hr Hl.
  rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
  unfold cut_state in H |- *. cbn [locals set_locals].
  destruct (cut_env (names, LN) (locals s)) as [env|] eqn:Ec; [|injection H as <- _; congruence].
  rewrite (locals_rel_cut_env temp (locals s) loc (names, LN) env (conj Hl (conj Hn1 Ec))).
  change (set_locals env (set_locals loc s)) with (set_locals env s).
  rewrite fix_clock_evaluate in H |- *.
  destruct (evaluate (prog, set_locals env s)) as [r t] eqn:E1.
  assert (Hr1 : r <> SOME Error).
  { intros ->. cbn [cont_loop] in H. rewrite bd_false in H by discriminate.
    injection H as <- _. apply Hr; reflexivity. }
  destruct (HB (set_locals env s) r t (locals (set_locals env s)) (conj E1 (conj Hr1 (fun x _ => eq_refl))))
    as [l1 [Ev1 Hp1]].
  change (set_locals (locals (set_locals env s)) (set_locals env s)) with (set_locals env s) in Ev1.
  rewrite Ev1.
  destruct (cont_loop r) eqn:Ecl.
  - assert (Hl1 : locals_rel temp (locals t) l1)
      by (destruct r as [[]|]; cbn in Ecl; try discriminate; exact Hp1).
    change (clock (set_locals l1 t)) with (clock t).
    destruct (clock t =? 0) eqn:Ez.
    + injection H as <- <-. exists (locals (flush_state true t)). split.
      * destruct t; reflexivity.
      * reflexivity.
    + unfold STOP in *. apply N.eqb_neq in Ez.
      pose proof (evaluate_clock _ _ _ _ E1) as [Hc _]. cbn [clock set_locals] in Hc.
      exact (IH (N.to_nat (clock (dec_clock t))) ltac:(unfold dec_clock; cbn [clock set_clock]; lia)
               (dec_clock t) eq_refl l1 res rst H Hr Hl1).
  - destruct (bool_decide (r = SOME (Break 0))) eqn:Eb.
    + apply bool_decide_spec in Eb; subst r.
      unfold cut_state in H |- *. cbn [locals set_locals].
      destruct (cut_env (exit_names, LN) (locals t)) as [env2|] eqn:Ec2; [|injection H as <- _; congruence].
      rewrite (locals_rel_cut_env temp (locals t) l1 (exit_names, LN) env2 (conj Hp1 (conj Hn2 Ec2))).
      injection H as <- <-. exists env2. split; [reflexivity|]. intros x _; reflexivity.
    + injection H as <- <-. exists l1. split; [reflexivity|]. apply isel_post_exit_loop, Hp1.
Qed.

Lemma evaluate_Seq_eq (p1 p2 : prog a) (s : state a c ffi_t) :
  evaluate (Seq p1 p2, s) =
  let '(res, s1) := evaluate (p1, s) in
  if bool_decide (res = NONE) then evaluate (p2, s1) else (res, s1).
Proof. rewrite (evaluate_eqn (Seq p1 p2) s); cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

Lemma push_map (f : prog a -> prog a) envs (h : option (N * (prog a * (N * N)))) l (st : state a c ffi_t) :
  push_env envs (match h with
                 | None => None
                 | Some (n, (p, (l1, l2))) => Some (n, (f p, (l1, l2)))
                 end) (set_locals l st) = set_locals l (push_env envs h st).
Proof. destruct h as [[? [? [? ?]]]|]; unfold push_env; destruct (env_to_list _ _); reflexivity. Qed.

Lemma set_locals_set_locals l l' (st : state a c ffi_t) : set_locals l (set_locals l' st) = set_locals l st.
Proof. reflexivity. Qed.

Lemma bool_atoms_and (x y : bool) : is_true (x && y) <-> is_true x /\ is_true y.
Proof. unfold is_true; apply Bool.andb_true_iff. Qed.

(** HOL's [c] (an [asm_config]) is [c0]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "inst_select_thm" *)
Theorem inst_select_thm : forall c0 temp (prog : prog a) st res rst loc,
  evaluate (prog, st) = (res, rst) /\ every_var (fun x => x <? temp) prog /\
  res <> SOME Error /\ locals_rel temp (locals st) loc ->
  exists loc',
    evaluate (inst_select c0 temp prog, set_locals loc st) = (res, set_locals loc' rst) /\
    match res with
    | NONE => locals_rel temp (locals rst) loc'
    | SOME (Break _) => locals_rel temp (locals rst) loc'
    | SOME (Continue _) => locals_rel temp (locals rst) loc'
    | SOME _ => locals rst = loc'
    end.
Proof.
  intros c0 temp prog.
  induction prog as [ |  |  | v exp |  | sv sexp | exp var | q IHq | ret dest args h IHret IHh | q1 q2 IH1 IH2 | cmp r1 ri q1 q2 IH1 IH2 | names q exit_names IHq |  |  |  |  |  |  |  |  |  |  |  |  |  | op v exp]
    using prog_nested_ind;
    intros st res rst loc (H & Hv & Hr & Hl);
    try (cbn [inst_select]; apply (locals_rel_evaluate_thm _ st res rst loc temp);
         repeat split; assumption).
  - (* Assign *)
    cbn [inst_select]. cbn [every_var] in Hv. apply bool_atoms_and in Hv as [Hv1 Hv2].
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (word_exp st exp) as [w|] eqn:E; [|injection H as <- _; congruence].
    injection H as <- <-.
    destruct (pre_exp_facts temp exp st w Hv2 E) as (E' & Hb' & Hv').
    destruct (inst_select_exp_thm c0 v temp _ st w loc (conj Hb' (conj Hv' (conj Hl E'))))
      as [l1 [Ev Hp]].
    exists l1. split; [exact Ev|]. cbn [isel_post].
    intros x Hx. specialize (Hp x). unfold set_var; cbn [locals set_locals]. rewrite lookup_insert.
    destruct (decide (x = v)); [symmetry; exact Hp|]. apply N.ltb_lt in Hx. rewrite Hx in Hp.
    symmetry; exact Hp.
  - (* Set *)
    cbn [inst_select]. cbn zeta. cbn [every_var] in Hv.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (bool_decide _ || bool_decide _) eqn:Eh; [injection H as <- _; congruence|].
    destruct (word_exp st sexp) as [w|] eqn:E; [|injection H as <- _; congruence].
    injection H as <- <-.
    destruct (pre_exp_facts temp sexp st w Hv E) as (E' & Hb' & Hv').
    destruct (inst_select_exp_thm c0 temp temp _ st w loc (conj Hb' (conj Hv' (conj Hl E'))))
      as [l1 [Ev Hp]].
    destruct (sel_post_temp _ _ _ _ Hp) as [Ht Hl1].
    exists l1. split; [|exact Hl1].
    rewrite (ev_seq_none _ _ _ _ Ev). rewrite evaluate_eqn; cbn [evaluate_body word_exp].
    rewrite Eh. unfold get_var; cbn [locals set_locals]. rewrite Ht. reflexivity.
  - (* Store *)
    cbn [every_var] in Hv. apply bool_atoms_and in Hv as [Hv1 Hv2]. apply N.ltb_lt in Hv1.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (word_exp st exp) as [[ad|]|] eqn:E; try (injection H as <- _; congruence).
    destruct (get_var var st) as [x|] eqn:Eg; [|injection H as <- _; congruence].
    destruct (mem_store ad x st) as [st1|] eqn:Em; [|injection H as <- _; congruence].
    injection H as <- <-.
    assert (Eg' : forall l1, locals_rel temp (locals st) l1 -> get_var var (set_locals l1 st) = SOME x)
      by (intros l1 Hl1; rewrite (locals_rel_get_var_simp temp st l1 var (conj Hv1 Hl1)); exact Eg).
    assert (Hst : locals st1 = locals st) by exact (proj1 (mem_store_const _ _ _ _ Em)).
    destruct (pre_exp_facts temp exp st (Word ad) Hv2 E) as (E' & Hb' & Hv').
    destruct (store_case c0 temp exp var) as [[e' [w' [Ee [Hok Ep]]]]|Ep]; rewrite Ep.
    + rewrite Ee in E', Hb', Hv'.
      destruct (addr_sel1 c0 temp e' w' st loc ad Hb' Hv' Hl E') as [l1 [Ev [Ea Hl1]]].
      exists l1. split; [|cbn [isel_post]; rewrite Hst; exact Hl1].
      rewrite (ev_seq_none _ _ _ _ Ev). rewrite evaluate_eqn; cbn [evaluate_body inst].
      rewrite Ea, (Eg' l1 Hl1), mem_store_set_locals, Em. reflexivity.
    + destruct (addr_sel2 c0 temp _ st loc ad Hb' Hv' Hl E') as [l1 [Ev [Ea [_ Hl1]]]].
      exists l1. split; [|cbn [isel_post]; rewrite Hst; exact Hl1].
      rewrite (ev_seq_none _ _ _ _ Ev). rewrite evaluate_eqn; cbn [evaluate_body inst].
      rewrite Ea, (Eg' l1 Hl1), mem_store_set_locals, Em. reflexivity.
  - (* MustTerminate *)
    cbn [inst_select]. cbn [every_var] in Hv.
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
    change (termdep (set_locals loc st)) with (termdep st).
    destruct (termdep st =? 0); [injection H as <- _; congruence|].
    destruct (evaluate (q, set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      as [r1 t1] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Et; [injection H as <- _; congruence|].
    injection H as <- <-.
    destruct (IHq _ r1 t1 loc (conj E1 (conj Hv (conj Hr Hl)))) as [l1 [Ev Hp]].
    change (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) (set_locals loc st)))
      with (set_locals loc (set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st))).
    rewrite Ev. cbn beta iota zeta. rewrite Et. exists l1. split; [reflexivity|exact Hp].
  - (* Call *)
    cbn [inst_select]. cbn zeta. cbn [every_var] in Hv. apply bool_atoms_and in Hv as [Hargs Hv].
    destruct ret as [[n [names [rh [l1 l2]]]]|].
    2:{ destruct h as [[hv [hp [hl1 hl2]]]|].
        - exfalso. rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
          split_H H; try (injection H as <- _; congruence).
          all: match goal with E : @bool_decide (SOME _ = NONE) _ = true |- _ =>
            apply bool_decide_spec in E; discriminate E end.
        - apply (locals_rel_evaluate_thm _ st res rst loc temp). repeat split; try assumption.
          cbn [every_var]. unfold is_true in *. rewrite Hargs. reflexivity. }
    cbn beta iota in IHret, Hv. rewrite !bool_atoms_and in Hv. destruct Hv as [[[Hn Hnm] Hvrh] Hvh].
    rewrite evaluate_eqn in H; cbn [evaluate_body add_ret_loc] in H.
    rewrite (evaluate_eqn (Call _ _ _ _)); cbn [evaluate_body add_ret_loc].
    rewrite (locals_rel_get_vars_simp temp st loc args (conj Hargs Hl)).
    destruct (get_vars args st) as [xs|] eqn:Eg; [|injection H as <- _; congruence].
    destruct (bad_dest_args dest args) eqn:Ebd; [injection H as <- _; congruence|].
    change (code (set_locals loc st)) with (code st).
    change (state_stack_size (set_locals loc st)) with (state_stack_size st).
    destruct (find_code dest (Loc l1 l2 :: xs) (code st) (state_stack_size st))
      as [[args1 [prog ss]]|] eqn:Ef; [|injection H as <- _; congruence].
    destruct (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ec1;
      [injection H as <- _; congruence|].
    change (locals (set_locals loc st)) with loc.
    destruct (cut_envs names (locals st)) as [envs|] eqn:Ece; [|injection H as <- _; congruence].
    rewrite (locals_rel_cut_envs temp (locals st) loc names envs (conj Hl (conj Hnm Ece))).
    change (clock (set_locals loc st)) with (clock st).
    change (dec_clock (set_locals loc st)) with (set_locals loc (dec_clock st)).
    rewrite !(push_map (inst_select c0 temp)).
    rewrite !(proj1 (call_env_with_const _ _ _ _ 0 0 (compile st) (compile_oracle st) (code st) 0 (permute st))).
    destruct (clock st =? 0) eqn:Ez.
    { injection H as <- <-. exists (locals (flush_state true
        (set_stack_max (stack_max (call_env args1 ss (push_env envs h st))) (set_stack [] st)))).
      rewrite locals_rm. split; [reflexivity|]. reflexivity. }
    rewrite ?fix_clock_evaluate in H |- *.
    destruct (evaluate (prog, call_env args1 ss (push_env envs h (dec_clock st)))) as [r1 t1] eqn:E1.
    destruct r1 as [[x ys|x y|k|k| | |f|]|];
      try (injection H as <- _; congruence);
      try (injection H as <- <-; exists (locals t1); rewrite locals_rm; split; [reflexivity|first [reflexivity|apply isel_post_refl]]).
    + destruct (negb (bool_decide (x = Loc l1 l2)) || negb (LENGTH ys =? LENGTH n)) eqn:Ec2;
        [injection H as <- _; congruence|].
      destruct (pop_env t1) as [t2|] eqn:Ep; [|injection H as <- _; congruence].
      destruct (⌜domain (locals t2) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
        [|injection H as <- _; congruence].
      destruct (IHret _ res rst (locals (set_vars n ys t2)) (conj H (conj Hvrh (conj Hr (fun x _ => eq_refl)))))
        as [l' [Ev Hp]].
      rewrite locals_rm in Ev. exists l'. split; [exact Ev|exact Hp].
    + destruct h as [[hn [hp [hl1 hl2]]]|].
      * cbn beta iota in IHh, Hvh. apply bool_atoms_and in Hvh as [_ Hvhp].
        destruct (negb (bool_decide (x = Loc hl1 hl2))) eqn:Ec2; [injection H as <- _; congruence|].
        destruct (⌜domain (locals t1) = domain (FST envs) UNION domain (SND envs)⌝) eqn:Ed;
          [|injection H as <- _; congruence].
        destruct (IHh _ res rst (locals (set_var hn y t1)) (conj H (conj Hvhp (conj Hr (fun x _ => eq_refl)))))
          as [l' [Ev Hp]].
        rewrite locals_rm in Ev. exists l'. split; [exact Ev|exact Hp].
      * injection H as <- <-. exists (locals t1). rewrite locals_rm.
        split; [reflexivity|first [reflexivity|apply isel_post_refl]].
  - (* Seq *)
    cbn [inst_select]. cbn [every_var] in Hv. apply bool_atoms_and in Hv as [Hv1 Hv2].
    rewrite evaluate_Seq_eq in H |- *.
    destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error).
    { intros ->. rewrite bd_false in H by discriminate. injection H as <- _. congruence. }
    destruct (IH1 st r1 s1 loc (conj E1 (conj Hv1 (conj Hr1 Hl)))) as [l1 [Ev Hp]].
    rewrite Ev. destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En; subst r1.
      exact (IH2 s1 res rst l1 (conj H (conj Hv2 (conj Hr Hp)))).
    + injection H as <- <-. exists l1. split; [reflexivity|exact Hp].
  - (* If *)
    cbn [inst_select]. cbn [every_var] in Hv. rewrite !bool_atoms_and in Hv.
    destruct Hv as [[[Hv1 Hv2] Hv3] Hv4]. apply N.ltb_lt in Hv1.
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
    rewrite (locals_rel_get_var_simp temp st loc r1 (conj Hv1 Hl)).
    rewrite (locals_rel_get_var_imm_simp temp st loc ri (conj Hv2 Hl)).
    split_H H; try (injection H as <- _; congruence).
    + exact (IH1 st res rst loc (conj H (conj Hv3 (conj Hr Hl)))).
    + exact (IH2 st res rst loc (conj H (conj Hv4 (conj Hr Hl)))).
  - (* Loop *)
    cbn [inst_select]. cbn [every_var] in Hv. rewrite !bool_atoms_and in Hv.
    destruct Hv as [[Hn1 Hvq] Hn2].
    apply (inst_select_Loop_helper st names q exit_names res rst c0 temp loc).
    repeat split; try assumption.
    + intros st' res' rst' loc' (H' & Hr' & Hl'). exact (IHq st' res' rst' loc' (conj H' (conj Hvq (conj Hr' Hl')))).
    + unfold every_name; cbn [FST SND fst snd]. rewrite Hn1. reflexivity.
    + unfold every_name; cbn [FST SND fst snd]. rewrite Hn2. reflexivity.
  - (* ShareInst *)
    cbn [every_var] in Hv. apply bool_atoms_and in Hv as [Hv1 Hv2]. apply N.ltb_lt in Hv1.
    rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
    destruct (word_exp st exp) as [[ad|]|] eqn:E; try (injection H as <- _; congruence).
    destruct (pre_exp_facts temp exp st (Word ad) Hv2 E) as (E' & Hb' & Hv').
    destruct (share_case c0 temp op v exp) as [[e' [w' [Ee Ep]]]|Ep]; rewrite Ep.
    + rewrite Ee in E', Hb', Hv'.
      destruct (addr_sel1 c0 temp e' w' st loc ad Hb' Hv' Hl E') as [l1 [Ev [Ea Hl1]]].
      destruct (share_inst_locals_rel temp op v ad st rst l1 res H Hr Hv1 Hl1) as [l2 [Es Hp]].
      exists l2. split; [|exact Hp].
      rewrite (ev_seq_none _ _ _ _ Ev). rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Ea. exact Es.
    + destruct (addr_sel2 c0 temp _ st loc ad Hb' Hv' Hl E') as [l1 [Ev [_ [Ea Hl1]]]].
      destruct (share_inst_locals_rel temp op v ad st rst l1 res H Hr Hv1 Hl1) as [l2 [Es Hp]].
      exists l2. split; [|exact Hp].
      rewrite (ev_seq_none _ _ _ _ Ev). rewrite evaluate_eqn; cbn [evaluate_body]. rewrite Ea. exact Es.
Qed.

End InstSelectThm.

(** ** [three_to_two_reg] *)

Section ThreeToTwo.
Context {a : N} {c ffi_t : Type}.
Implicit Types s st : state a c ffi_t.

(** Galette-only: [q] behaves as [p] whenever [p] does not fail. *)
Definition sim (p q : prog a) : Prop :=
  forall s res s', evaluate (p, s) = (res, s') /\ res <> SOME Error -> evaluate (q, s) = (res, s').

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "three_to_two_reg_Loop" *)
Theorem three_to_two_reg_Loop : forall s names (prog : prog a) exit_names res s',
  (forall v res s', evaluate (prog, v) = (res, s') /\ res <> SOME Error ->
                    evaluate (three_to_two_reg prog, v) = (res, s')) /\
  evaluate (Loop names prog exit_names, s) = (res, s') /\ res <> SOME Error ->
  evaluate (Loop names (three_to_two_reg prog) exit_names, s) = (res, s').
Proof.
  intros s names prog exit_names res s' (Hs & H & Hr).
  revert res s' H Hr.
  remember (N.to_nat (clock s)) as n eqn:Hn. revert s Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros s Hn res s' H Hr.
  rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
  destruct (cut_state (names, LN) s) as [s0|] eqn:Ec; [|exact H].
  rewrite fix_clock_evaluate in H |- *.
  destruct (evaluate (prog, s0)) as [r t] eqn:E1.
  assert (Hr1 : r <> SOME Error).
  { intros ->. cbn [cont_loop] in H. rewrite bd_false in H by discriminate.
    injection H as <- _. apply Hr; reflexivity. }
  rewrite (Hs _ _ _ (conj E1 Hr1)).
  destruct (cont_loop r); [|exact H].
  destruct (clock t =? 0) eqn:Ez; [exact H|].
  apply N.eqb_neq in Ez. unfold STOP in *.
  pose proof (evaluate_clock _ _ _ _ E1) as [Hc _].
  pose proof (cut_state_clock _ _ _ Ec) as [Hc' _].
  exact (IH (N.to_nat (clock (dec_clock t))) ltac:(unfold dec_clock; cbn [clock set_clock]; lia)
           (dec_clock t) eq_refl res s' H Hr).
Qed.

Lemma sim_Seq p1 q1 p2 q2 : sim p1 q1 -> sim p2 q2 -> sim (Seq p1 p2) (Seq q1 q2).
Proof.
  intros S1 S2 s res s' [H Hr]. rewrite evaluate_Seq_eq in H |- *.
  destruct (evaluate (p1, s)) as [r t] eqn:E.
  destruct (classical_dec (r = SOME Error)) as [->|Hn].
  { rewrite bd_false in H by discriminate. injection H as <- _. congruence. }
  rewrite (S1 _ _ _ (conj E Hn)). destruct (bool_decide (r = NONE)); [|exact H].
  apply S2. split; assumption.
Qed.

Lemma sim_If cmp r ri p1 q1 p2 q2 : sim p1 q1 -> sim p2 q2 -> sim (If cmp r ri p1 p2) (If cmp r ri q1 q2).
Proof.
  intros S1 S2 s res s' [H Hr]. rewrite evaluate_eqn in H |- *. cbn [evaluate_body] in H |- *.
  split_H H; try exact H; [apply S1|apply S2]; split; assumption.
Qed.

Lemma sim_MustTerminate p q : sim p q -> sim (MustTerminate p) (MustTerminate q).
Proof.
  intros S s res s' [H Hr]. rewrite evaluate_eqn in H |- *. cbn [evaluate_body] in H |- *.
  destruct (termdep s =? 0); [exact H|].
  destruct (evaluate (p, _)) as [r t] eqn:E.
  destruct (bool_decide (r = SOME TimeOut)) eqn:Et; [injection H as <- _; congruence|].
  injection H as <- <-. rewrite (S _ _ _ (conj E Hr)), Et. reflexivity.
Qed.

Lemma sim_Call (f : prog a -> prog a) ret dest args h :
  match ret with Some (_, (_, (q, _))) => sim q (f q) | None => True end ->
  match h with Some (_, (q, _)) => sim q (f q) | None => True end ->
  sim (Call ret dest args h)
      (Call (match ret with
             | None => None
             | Some (x1, (x2, (q1, (x3, x4)))) => Some (x1, (x2, (f q1, (x3, x4))))
             end) dest args
            (match h with
             | None => None
             | Some (y1, (q2, (y2, y3))) => Some (y1, (f q2, (y2, y3)))
             end)).
Proof.
  intros S1 S2 s res s' [H Hr].
  destruct ret as [[x1 [x2 [q1 [x3 x4]]]]|], h as [[y1 [q2 [y2 y3]]]|];
    cbn iota in S1, S2;
    rewrite evaluate_eqn in H |- *; cbn [evaluate_body add_ret_loc] in H |- *;
    unfold push_env in H |- *;
    revert H;
    repeat first
      [ progress (rewrite ?fix_clock_evaluate)
      | match goal with
        | |- context [@bool_decide (SOME ?x = NONE) ?d] =>
            let F := fresh "F" in
            assert (F : @bool_decide (SOME x = NONE) d = false) by (apply bd_false; discriminate);
            rewrite F; clear F
        end
      | match goal with
        | |- ?P -> _ =>
            match P with
            | context [match ?x with _ => _ end] =>
                let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
            end
        end ];
    intros H; first [exact H | apply S1; split; assumption | apply S2; split; assumption].
Qed.

Lemma ev_move_s (r1 r2 : N) s v2 :
  get_var r2 s = SOME v2 ->
  evaluate (@Move a 0 [(r1, r2)], s) = (NONE, set_locals (insert r1 v2 (locals s)) s).
Proof.
  intros H. rewrite evaluate_eqn; cbn [evaluate_body MAP List.map fst snd FST SND ALL_DISTINCT MEM negb andb].
  cbn [get_vars]. rewrite H. reflexivity.
Qed.

(** Run both the original and the two-register version: unfold and
    case-split [H], then compute the goal. *)
Ltac split_inner H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
             end
         end.

Ltac t2_run H :=
  rewrite evaluate_eqn in H; cbn [evaluate_body inst] in H; unfold assign in H;
  cbn [word_exp MAP List.map get_vars the_words] in H; unfold get_var in H;
  split_inner H; try (injection H as <- _; congruence);
  injection H as <- <-;
  rewrite evaluate_Seq_eq; erewrite ev_move_s by (unfold get_var; eassumption);
  rewrite bd_true by reflexivity;
  rewrite evaluate_eqn; cbn [evaluate_body inst]; unfold assign;
  cbn [word_exp MAP List.map get_vars the_words]; unfold get_var; cbn [locals set_locals];
  repeat match goal with |- context [get_store ?x (set_locals ?l ?s)] =>
           change (get_store x (set_locals l s)) with (get_store x s) end;
  rewrite ?lookup_insert;
  repeat match goal with
         | |- context [decide (?x = ?x)] => destruct (decide (x = x)); [|congruence]
         | Hne : ?x <> ?y |- context [decide (?y = ?x)] =>
             destruct (decide (y = x)); [congruence|]
         | Hne : ?x <> ?y |- context [decide (?x = ?y)] =>
             destruct (decide (x = y)); [congruence|]
         end;
  repeat first
    [ progress rw_cases
    | match goal with E : ?X = (_, _) |- context [?X] => rewrite E; cbn beta iota zeta end ];
  unfold set_var; cbn [locals set_locals]; rewrite ?insert_shadow; try reflexivity.

(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "three_to_two_reg_correct" *)
Theorem three_to_two_reg_correct : forall (prog : prog a) s res s',
  every_inst distinct_tar_reg prog /\ evaluate (prog, s) = (res, s') /\ res <> SOME Error ->
  evaluate (three_to_two_reg prog, s) = (res, s').
Proof.
  intros prog. change (forall s res s', every_inst distinct_tar_reg prog /\ evaluate (prog, s) = (res, s') /\ res <> SOME Error ->
    evaluate (three_to_two_reg prog, s) = (res, s')).
  induction prog as [ |  | i |  |  |  |  | q IHq | ret dest args h IHret IHh | q1 q2 IH1 IH2 | cmp r1 ri q1 q2 IH1 IH2 | names q exit_names IHq |  |  |  |  |  |  |  | b r1 r2 |  |  |  |  |  | ]
    using prog_nested_ind; intros st res st' (Hd & H & Hr);
    try (exact H).
  - (* Inst *)
    cbn [every_inst distinct_tar_reg] in Hd.
    destruct i as [|r w|ar|m r ad|f]; try exact H.
    destruct ar as [bop r1 r2 ri|sh r1 r2 ri|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4];
      try exact H; cbn [three_to_two_reg]; cbn [distinct_tar_reg] in Hd.
    + destruct ri as [r3|w].
      * assert (Hne : r3 <> r1) by (intros ->; rewrite bd_true in Hd by reflexivity; discriminate Hd).
        t2_run H.
      * t2_run H.
    + destruct ri as [r3|w].
      * assert (Hne : r3 <> r1) by (intros ->; rewrite bd_true in Hd by reflexivity; discriminate Hd).
        t2_run H.
      * t2_run H.
    + unfold is_true in Hd. apply andb_prop in Hd as [Hd1 Hd2].
      apply Bool.negb_true_iff, N.eqb_neq in Hd1. apply Bool.negb_true_iff, N.eqb_neq in Hd2.
      t2_run H.
    + apply Bool.negb_true_iff, N.eqb_neq in Hd. t2_run H.
    + apply Bool.negb_true_iff, N.eqb_neq in Hd. t2_run H.
  - (* MustTerminate *)
    cbn [every_inst] in Hd. cbn [three_to_two_reg].
    exact (sim_MustTerminate q (three_to_two_reg q) (fun s r s' Hs => IHq s r s' (conj Hd Hs)) st res st' (conj H Hr)).
  - (* Call *)
    cbn [three_to_two_reg]. cbn zeta.
    destruct ret as [[x1 [x2 [q1 [x3 x4]]]]|].
    + cbn [every_inst] in Hd. apply andb_prop in Hd as [Hd1 Hd2]. cbn beta iota in IHret.
      apply (sim_Call three_to_two_reg (Some (x1, (x2, (q1, (x3, x4)))))).
      * exact (fun s r s' Hs => IHret s r s' (conj Hd1 Hs)).
      * destruct h as [[? [q2 [? ?]]]|]; [|exact Logic.I]. cbn beta iota in IHh, Hd2.
        exact (fun s r s' Hs => IHh s r s' (conj Hd2 Hs)).
      * split; assumption.
    + destruct h as [[? [q2 [? ?]]]|].
      * exfalso. rewrite evaluate_eqn in H; cbn [evaluate_body] in H.
        split_H H; try (injection H as <- _; congruence).
        all: match goal with E : @bool_decide (SOME _ = NONE) _ = true |- _ =>
          apply bool_decide_spec in E; discriminate E end.
      * exact H.
  - (* Seq *)
    cbn [every_inst] in Hd. apply andb_prop in Hd as [Hd1 Hd2]. cbn [three_to_two_reg].
    exact (sim_Seq q1 _ q2 _ (fun s r s' Hs => IH1 s r s' (conj Hd1 Hs))
             (fun s r s' Hs => IH2 s r s' (conj Hd2 Hs)) st res st' (conj H Hr)).
  - (* If *)
    cbn [every_inst] in Hd. apply andb_prop in Hd as [Hd1 Hd2]. cbn [three_to_two_reg].
    exact (sim_If cmp r1 ri q1 _ q2 _ (fun s r s' Hs => IH1 s r s' (conj Hd1 Hs))
             (fun s r s' Hs => IH2 s r s' (conj Hd2 Hs)) st res st' (conj H Hr)).
  - (* Loop *)
    cbn [every_inst] in Hd. cbn [three_to_two_reg].
    apply three_to_two_reg_Loop. repeat split; try assumption.
    intros v r s' Hs. exact (IHq v r s' (conj Hd Hs)).
  - (* OpCurrHeap *)
    cbn [every_inst distinct_tar_reg] in Hd. cbn [three_to_two_reg].
    assert (Hne : r2 <> r1) by (intros ->; rewrite bd_true in Hd by reflexivity; discriminate Hd).
    t2_run H.
Qed.

(** HOL's free variables are quantified. *)
(*! HOL "cakeml/compiler/backend/proofs/word_instProofScript.sml" "evaluate_three_to_two_reg_prog" *)
Theorem evaluate_three_to_two_reg_prog : forall (prog : prog a) s res s' t,
  evaluate (prog, s) = (res, s') /\ res <> SOME Error /\ every_inst distinct_tar_reg prog ->
  evaluate (three_to_two_reg_prog t prog, s) = (res, s').
Proof.
  intros prog s res s' t (H & Hr & Hd). unfold three_to_two_reg_prog.
  destruct t; [|exact H]. apply three_to_two_reg_correct; repeat split; assumption.
Qed.

End ThreeToTwo.
