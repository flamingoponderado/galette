(** * CakeML [word_to_stackProof]: syntactic properties of the output

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    10760-12411): label preservation ([word_to_stack_lab_pres]), the asm
    naming conventions ([stack_asm_name], [stack_asm_remove]),
    [alloc_arg], [reg_bound], [call_args], code and handler labels,
    [no_install] and [no_shmemop].

    Notes:
    - The stackLang predicates of [stackProps] are boolean; the wordLang
      conventions of [wordConvs] too.  The two [extract_labels],
      [no_install] and [get_code_labels] are written qualified
      ([wordConvs.x] / [stackProps.x]).
    - HOL's variables named [a] are renamed ([a0]) since [a] is the word
      width.
    - HOL's [compile] returns [(bytes, c, fs, p)], the right-nested tuple
      [(bytes, (c, (fs, p)))] here.
    - HOL's ML binding [wconvs] (a list of definitions) and the rebound
      [reg_bound_ind]/[reg_bound_def]/[reg_bound_inst_def] are not
      theorems and are not ported.  HOL's [get_code_labels_wReg] is a
      [val] proved with [Q.prove] (not stored): it is the Galette-only
      [get_code_labels_wRegWrite1]/[get_code_labels_wRegWrite2] here.
    - Proofs are by structural induction on the wordLang program (HOL:
      [comp_ind]); the many cases are discharged by unfolding the
      compiler's helpers and splitting the conditionals. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc parmove.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordProps.code.
From Galette.cakeml.compiler.backend.semantics Require Import backendProps stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props.
Open Scope N_scope.

(** ** Galette-only tactics *)

(** Split all [let]s, [match]es and [if]s of the goal, keeping equations. *)
Ltac split_goal :=
  repeat match goal with
  | |- context [if ?X then _ else _] => let E := fresh "E" in destruct X eqn:E; cbn beta iota zeta
  | |- context [match ?X with (_, _) => _ end] =>
      lazymatch X with
      | (_, _) => fail
      | match _ with _ => _ end => fail
      | _ => let E := fresh "E" in destruct X as [? ?] eqn:E
      end; cbn beta iota zeta
  | |- context [match ?X with _ => _ end] =>
      lazymatch X with
      | (_, _) => fail
      | match _ with _ => _ end => fail
      | _ => let E := fresh "E" in destruct X eqn:E end;
      cbn beta iota zeta
  end.

Ltac bool_split :=
  repeat match goal with
  | H : is_true (_ && _) |- _ => apply andb_true_iff in H as [? ?]
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | |- is_true (_ && _) => apply andb_true_iff; split
  | |- (_ && _) = true => apply andb_true_iff; split
  end.

Section StackMove.
Context {a : N}.

Lemma stack_move_ind (P : prog a -> Prop) (p : prog a) i offset :
  P p ->
  (forall q start, P q -> P (Seq q (Seq (StackLoad i (start + offset)) (StackStore i start)))) ->
  forall n start, P (stack_move n start offset i p).
Proof.
  intros Hp Hs n; induction n as [|n IH] using N.peano_ind; intros start.
  - rewrite (proj1 (stack_move_def 0 start offset i p)). exact Hp.
  - rewrite (proj2 (stack_move_def n start offset i p)). apply Hs, IH.
Qed.

Lemma copy_ret_aux_ind (P : prog a -> Prop) k f :
  P Skip ->
  (forall n q, P q -> P (list_Seq [StackLoad k n; StackStore k (n + f); q])) ->
  forall n, P (copy_ret_aux k f n).
Proof.
  intros H0 Hs n; induction n as [|n IH] using N.peano_ind.
  - rewrite copy_ret_aux_def. exact H0.
  - rewrite copy_ret_aux_def. replace (SUC n =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    cbv zeta. replace (SUC n - 1) with n by lia. apply Hs, IH.
Qed.

End StackMove.

(** ** Labels *)

Section Labels.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_no_labs" *)
Theorem stack_move_no_labs : forall n a0 b c (p : prog a),
  stackProps.extract_labels p = [] ->
  stackProps.extract_labels (stack_move n a0 b c p) = [].
Proof.
  intros n a0 b c p H. revert n a0. apply (stack_move_ind (fun q => stackProps.extract_labels q = [])); [exact H|].
  intros q start Hq. cbn [stackProps.extract_labels]. rewrite Hq. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "extract_labels_copy_ret_aux" *)
Theorem extract_labels_copy_ret_aux : forall k f n,
  stackProps.extract_labels (@copy_ret_aux a k f n) = [].
Proof.
  intros k f. apply (copy_ret_aux_ind (fun q => stackProps.extract_labels q = [])); [reflexivity|].
  intros n q Hq. cbn [list_Seq stackProps.extract_labels]. rewrite Hq. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "extract_labels_copy_ret" *)
Theorem extract_labels_copy_ret : forall perf b kf vs (kont : prog a),
  stackProps.extract_labels (copy_ret perf b kf vs kont) = stackProps.extract_labels kont.
Proof.
  intros perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [stackProps.extract_labels]. rewrite extract_labels_copy_ret_aux.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "extract_labels_wStackLoad_Skip" *)
Theorem extract_labels_wStackLoad_Skip : forall xs,
  stackProps.extract_labels (@wStackLoad a xs Skip) = [].
Proof.
  induction xs as [|[r i] xs IH]; [reflexivity|]. cbn [wStackLoad stackProps.extract_labels].
  rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "extract_labels_stack_move_StackAlloc" *)
Theorem extract_labels_stack_move_StackAlloc : forall k n start offset i,
  stackProps.extract_labels (@stack_move a n start offset i (StackAlloc k)) = [].
Proof. intros; apply stack_move_no_labs; reflexivity. Qed.

Lemma extract_labels_wStackLoad xs (p : prog a) :
  stackProps.extract_labels (wStackLoad xs p) = stackProps.extract_labels p.
Proof. induction xs as [|[r i] xs IH]; [reflexivity|]. cbn. exact IH. Qed.

Lemma extract_labels_wMoveAux l kf : stackProps.extract_labels (@wMoveAux a l kf) = [].
Proof.
  destruct kf as [k [f f']].
  induction l as [|xy l IH]; [reflexivity|].
  destruct l as [|xy' l']; cbn [wMoveAux] in *;
    [destruct xy as [[x|x] [y|y]]; reflexivity|].
  cbn [stackProps.extract_labels]. rewrite IH.
  destruct xy as [[x|x] [y|y]]; reflexivity.
Qed.

Lemma extract_labels_wRegWrite1 g r kf :
  (forall n, stackProps.extract_labels (g n) = []) ->
  stackProps.extract_labels (@wRegWrite1 a g r kf) = [].
Proof.
  intros H. destruct kf as [k [f f']]. unfold wRegWrite1.
  destruct (r DIV 2 <? k); cbn [stackProps.extract_labels]; rewrite ?H; reflexivity.
Qed.

Lemma extract_labels_wRegWrite2 g r kf :
  (forall n, stackProps.extract_labels (g n) = []) ->
  stackProps.extract_labels (@wRegWrite2 a g r kf) = [].
Proof.
  intros H. destruct kf as [k [f f']]. unfold wRegWrite2.
  destruct (r DIV 2 <? k); cbn [stackProps.extract_labels]; rewrite ?H; reflexivity.
Qed.

Lemma extract_labels_wInst i kf : stackProps.extract_labels (@wInst a i kf) = [].
Proof.
  destruct_inst i; unfold wInst; split_goal;
    rewrite ?extract_labels_wStackLoad;
    repeat first [ apply extract_labels_wRegWrite1; intros
                 | apply extract_labels_wRegWrite2; intros ];
    reflexivity.
Qed.

Lemma extract_labels_wShareInst op v ad kf :
  stackProps.extract_labels (@wShareInst a op v ad kf) = [].
Proof.
  destruct op, ad; unfold wShareInst; split_goal; rewrite ?extract_labels_wStackLoad;
    repeat first [ apply extract_labels_wRegWrite1; intros ]; reflexivity.
Qed.

Lemma extract_labels_wLive live bs kf :
  stackProps.extract_labels (FST (@wLive a live bs kf)) = [].
Proof. destruct kf as [k [f f']]. unfold wLive. split_goal; reflexivity. Qed.

Lemma extract_labels_call_dest dest args kf :
  stackProps.extract_labels (FST (@call_dest a dest args kf)) = [].
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?extract_labels_wStackLoad_Skip; reflexivity.
Qed.

Lemma extract_labels_StackArgs dest n kf :
  stackProps.extract_labels (@StackArgs a dest n kf) = [].
Proof. destruct kf as [k [f f']]. apply extract_labels_stack_move_StackAlloc. Qed.

Lemma extract_labels_PushHandler perf l1 l2 kf :
  stackProps.extract_labels (@PushHandler a perf l1 l2 kf) = [].
Proof. destruct kf as [k [f f']]; destruct perf; reflexivity. Qed.

Lemma extract_labels_PopHandler perf kf (p : prog a) :
  stackProps.extract_labels (PopHandler perf kf p) = stackProps.extract_labels p.
Proof. destruct kf as [k [f f']]; reflexivity. Qed.

Lemma extract_labels_StackHandlerArgs perf dest n kf :
  stackProps.extract_labels (@StackHandlerArgs a perf dest n kf) = [].
Proof. destruct kf as [k [f f']]; apply extract_labels_StackArgs. Qed.

Lemma extract_labels_perf_call_prefix l1 l2 k :
  stackProps.extract_labels (@perf_call_prefix a l1 l2 k) = [].
Proof. reflexivity. Qed.

Lemma extract_labels_perf_call_suffix :
  stackProps.extract_labels (@perf_call_suffix a) = [].
Proof. reflexivity. Qed.

Lemma extract_labels_SeqStackFree n (p : prog a) :
  stackProps.extract_labels (SeqStackFree n p) = stackProps.extract_labels p.
Proof. unfold SeqStackFree; destruct (n =? 0); reflexivity. Qed.

Lemma extract_labels_wMove xs kf : stackProps.extract_labels (@wMove a xs kf) = [].
Proof. destruct kf as [k [f f']]; apply extract_labels_wMoveAux. Qed.

Ltac el_simpl :=
  rewrite ?extract_labels_wStackLoad, ?extract_labels_wInst, ?extract_labels_wMove,
    ?extract_labels_wShareInst, ?extract_labels_PushHandler, ?extract_labels_PopHandler,
    ?extract_labels_StackHandlerArgs, ?extract_labels_perf_call_prefix,
    ?extract_labels_perf_call_suffix, ?extract_labels_SeqStackFree, ?extract_labels_StackArgs,
    ?extract_labels_copy_ret.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_lab_pres" *)
Theorem word_to_stack_lab_pres : forall ac perf (p : wordLang.prog a) bs kf,
  wordConvs.extract_labels p = stackProps.extract_labels (FST (comp ac perf p bs kf)).
Proof.
  intros ac perf p. induction p using wordConvs.prog_nested_ind; intros bs0 kf0; cbn [comp].
  all: split_goal; cbn [FST fst wordConvs.extract_labels stackProps.extract_labels].
  all: repeat match goal with
       | E : comp _ _ ?p ?b ?k = (?q, _), IH : forall bs kf, wordConvs.extract_labels ?p = _ |- _ =>
           rewrite (IH b k), E in *; cbn [FST fst] in *; clear E
       end.
  all: repeat match goal with
       | E : call_dest ?d ?ar ?k = (?q, _) |- _ =>
           let H := fresh in pose proof (extract_labels_call_dest d ar k) as H;
           rewrite E in H; cbn [FST fst] in H; rewrite H; clear E
       | E : wLive ?l ?b ?k = (?q, _) |- _ =>
           let H := fresh in pose proof (extract_labels_wLive l b k) as H;
           rewrite E in H; cbn [FST fst] in H; rewrite H; clear E
       end.
  all: el_simpl; cbn [stackProps.extract_labels app]; el_simpl;
    try (symmetry; apply extract_labels_wRegWrite1; reflexivity);
    rewrite ?app_nil_r; try reflexivity.
  all: match goal with IH : forall bs kf, _ = _ |- _ => apply IH end.
Qed.

Lemma compile_prog_lab_pres ac perf (p : wordLang.prog a) n k bs :
  stackProps.extract_labels (FST (compile_prog ac perf p n k bs)) = wordConvs.extract_labels p.
Proof.
  unfold compile_prog. cbv zeta. destruct (comp _ _ _ _ _) as [q1 bm] eqn:E.
  cbn [FST fst stackProps.extract_labels app]. match type of E with comp _ _ _ ?b ?kf = _ => rewrite (word_to_stack_lab_pres ac perf p b kf), E end.
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_lab_pres" *)
Theorem compile_word_to_stack_lab_pres : forall ac k (p : list (N * (N * wordLang.prog a))) perf b q r,
  compile_word_to_stack ac perf k p b = (q, r) /\
  EVERY (fun '(l, (m, e)) =>
    EVERY (fun '(l1, l2) => (l1 =? l) && negb (l2 =? 0) && negb (l2 =? 1)) (wordConvs.extract_labels e) &&
    ALL_DISTINCT (wordConvs.extract_labels e)) p ->
  EVERY (fun '(l, e) =>
    EVERY (fun '(l1, l2) => (l1 =? l) && negb (l2 =? 0) && negb (l2 =? 1)) (stackProps.extract_labels e) &&
    ALL_DISTINCT (stackProps.extract_labels e)) q.
Proof.
  intros ac k p; induction p as [|[i [n e]] p IH]; intros perf b q r [E H];
    cbn [compile_word_to_stack] in E.
  - injection E as <- _. reflexivity.
  - destruct (compile_prog ac perf e n k b) as [prog [f bm]] eqn:Ep.
    destruct (compile_word_to_stack ac perf k p bm) as [progs [fs bm']] eqn:Ew.
    injection E as <- _. cbn [EVERY] in H |- *. apply andb_true_iff in H as [H1 H2].
    apply andb_true_iff; split.
    + pose proof (compile_prog_lab_pres ac perf e n k b) as Hl. rewrite Ep in Hl.
      cbn [FST fst] in Hl. rewrite Hl. exact H1.
    + eapply IH; split; [exact Ew|exact H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_compile_lab_pres" *)
Theorem word_to_stack_compile_lab_pres : forall asm_conf (prog : list (N * (N * wordLang.prog a))),
  EVERY (fun '(n, (m, p)) =>
    let labs := wordConvs.extract_labels p in
    EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) labs &&
    ALL_DISTINCT labs) prog ->
  let '(bytes, (c, (f, p))) := word_to_stack.compile asm_conf false prog in
    MAP FST p = wordLang.raise_stub_location :: wordLang.store_consts_stub_location :: MAP FST prog /\
    EVERY (fun '(n, p) =>
      let labs := stackProps.extract_labels p in
      EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) labs &&
      ALL_DISTINCT labs) p.
Proof.
  intros asm_conf prog H. unfold word_to_stack.compile. cbv zeta.
  destruct (compile_word_to_stack _ _ _ _ _) as [progs [fs bm]] eqn:E. split.
  - cbn [MAP List.map FST fst]. do 2 f_equal. eapply MAP_FST_compile_word_to_stack; exact E.
  - cbn [EVERY]. apply andb_true_iff; split; [reflexivity|].
    apply andb_true_iff; split; [reflexivity|].
    eapply compile_word_to_stack_lab_pres; split; [exact E|exact H].
Qed.

End Labels.


(** ** Asm naming conventions *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVEN_DIV_2_props" *)
Theorem EVEN_DIV_2_props : forall a0 b,
  a0 MOD 2 = 0 /\ b MOD 2 = 0 ->
  (a0 <> b -> a0 DIV 2 <> b DIV 2) /\ (a0 <> 0 -> a0 DIV 2 <> 0).
Proof.
  intros a0 b [Ha Hb].
  pose proof (N.div_mod a0 2 ltac:(lia)) as Da. pose proof (N.div_mod b 2 ltac:(lia)) as Db.
  split; intros H E; apply H; lia.
Qed.

Ltac to_prop :=
  repeat match goal with
  | H : is_true _ |- _ => unfold is_true in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H : _ /\ _ |- _ => destruct H as [? ?]
  | H : (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply N.leb_le in H
  | H : (_ <=? _) = false |- _ => apply N.leb_gt in H
  | H : (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H : bool_decide _ = true |- _ => apply bool_decide_spec in H
  | H : bool_decide _ = false |- _ => apply bool_decide_false in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : implb _ _ = true |- _ => rewrite Bool.implb_true_iff in H
  | H : (_ || _) = true |- _ => apply orb_true_iff in H
  | H : is_phy_var _ = true |- _ => unfold is_phy_var in H
  | H : two_reg_inst (Arith _) = true |- _ => cbn [two_reg_inst] in H
  | H : bool_decide _ = true -> _ |- _ => rewrite bool_decide_spec in H
  | H : (_ =? _) = true -> _ |- _ => rewrite N.eqb_eq in H
  | H : (_ || _) = true -> _ |- _ => rewrite orb_true_iff in H
  | H : ?P -> _, H2 : ?P |- _ => lazymatch type of P with Prop => specialize (H H2) end
  | H : is_true ?b -> _, H2 : ?b = true |- _ => specialize (H H2)
  | H : ?b = true -> _, H2 : ?b = true |- _ => specialize (H H2)
  end.

Lemma bool_decide_false_iff' (P : Prop) {d : Decision P} : bool_decide P = false <-> ~ P.
Proof. split; [apply bool_decide_false|intros H; destruct (bool_decide P) eqn:E; [apply bool_decide_spec in E; contradiction|reflexivity]]. Qed.

(** Evaluate [MEM] on closed memop lists. *)
Ltac mem_eval :=
  repeat match goal with
  | |- context [MEM ?x ?l] =>
      lazymatch x with ISA _ => fail | _ =>
      let v := eval vm_compute in (MEM x l) in change (MEM x l) with v end
  | H : context [MEM ?x ?l] |- _ =>
      lazymatch x with ISA _ => fail | _ =>
      let v := eval vm_compute in (MEM x l) in change (MEM x l) with v in H end
  end; cbn beta iota in *.

(** [lia], first without the parity hypotheses (which make [lia] slow). *)
Ltac lia_fast :=
  first [ (repeat match goal with
                  | H : context [N.modulo _ _] |- _ => clear H
                  | H : forall _, _ |- _ => clear H
                  end; lia)
        | (repeat match goal with H : forall _, _ |- _ => clear H end; lia) ].

Ltac nm_leaf :=
  mem_eval; to_prop;
  repeat match goal with
  | H : context [if ?b then _ else _] |- _ => let X := fresh "X" in destruct b eqn:X; to_prop
  end;
  repeat match goal with
  | |- (_ && _) = true => apply andb_true_iff; split
  | |- _ /\ _ => split
  | |- True => exact Logic.I
  | |- (_ <? _) = true => apply N.ltb_lt
  | |- (_ =? _) = true => apply N.eqb_eq
  | |- bool_decide _ = true => apply bool_decide_spec
  | |- negb _ = true => apply negb_true_iff
  | |- bool_decide _ = false => apply bool_decide_false_iff'
  | |- implb _ _ = true => apply Bool.implb_true_iff; intro
  | |- (_ || _) = true => apply orb_true_iff
  | |- is_true _ => unfold is_true
  end; to_prop; try reflexivity; try assumption;
  try (match goal with
       | |- _ < _ => lia_fast | |- _ <= _ => lia_fast | |- @eq N _ _ => lia_fast
       | |- ~ (@eq N _ _) => lia_fast | |- False => lia_fast end);
  try (left; apply bool_decide_spec; lia);
  try (right; apply bool_decide_spec; reflexivity);
  try (match goal with |- _ <> _ => discriminate end);
  try (match goal with Hn : _ \/ ISA _ <> _ |- ISA _ <> _ =>
         destruct Hn as [Hn|Hn]; [exfalso; exact (Hn eq_refl)|exact Hn] end).

Ltac inst_hyps :=
  repeat match goal with
  | H : inst_arg_convention ?i = true |- _ =>
      lazymatch i with
      | Arith _ => cbn [inst_arg_convention] in H
      | Mem _ _ _ => cbn [inst_arg_convention] in H
      | FP _ => cbn [inst_arg_convention] in H
      | asm.Const _ _ => cbn [inst_arg_convention] in H
      end
  | H : wordLang.every_var_inst _ ?i = true |- _ =>
      lazymatch i with
      | Arith _ => cbn [wordLang.every_var_inst wordLang.every_var_imm] in H
      | Mem _ _ _ => cbn [wordLang.every_var_inst wordLang.every_var_imm] in H
      | FP _ => cbn [wordLang.every_var_inst wordLang.every_var_imm] in H
      | asm.Const _ _ => cbn [wordLang.every_var_inst wordLang.every_var_imm] in H
      end
  end.

Section AsmName.
Context {a : N}.
Implicit Types (c : asm_config a).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "call_dest_stack_asm_name" *)
Theorem call_dest_stack_asm_name : forall c d (a0 : list N) k q0 d',
  @call_dest a d a0 k = (q0, d') ->
  stack_asm_name c q0 /\
  match d' with
  | inr r => r <= FST k + 1
  | inl l => True
  end.
Proof.
  intros c d a0 [k [f f']] q0 d' E. unfold call_dest, wReg2 in E.
  destruct d as [pos|]; [injection E as <- <-; split; [reflexivity|exact Logic.I]|].
  destruct (LENGTH a0 =? 0); [injection E as <- <-; split; [reflexivity|exact Logic.I]|].
  destruct (LAST a0 DIV 2 <? k) eqn:Ek; injection E as <- <-; cbn; split; try reflexivity; to_prop; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_stack_asm_name" *)
Theorem wLive_stack_asm_name : forall c q bs kf q1 bs',
  FST kf + 1 < reg_count c - LENGTH (avoid_regs c) /\
  @wLive a q bs kf = (q1, bs') ->
  stack_asm_name c q1.
Proof.
  intros c q bs [k [f f']] q1 bs' [H E]. unfold wLive in E.
  destruct (f =? 0); [injection E as <- _; reflexivity|].
  destruct (insert_bitmap _ bs) eqn:Ei. injection E as <- _.
  cbn [FST fst] in H. cbn. rewrite andb_true_r. apply N.ltb_lt. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_stack_asm_name" *)
Theorem stack_move_stack_asm_name : forall c n start offset i (p : prog a),
  stack_asm_name c (stack_move n start offset i p) = stack_asm_name c p.
Proof.
  intros c n start offset i p. revert n start.
  apply (stack_move_ind (fun q => stack_asm_name c q = stack_asm_name c p)); [reflexivity|].
  intros q start Hq. cbn. rewrite Hq, !andb_true_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_stack_asm_name" *)
Theorem copy_ret_aux_stack_asm_name : forall c k f n, stack_asm_name c (@copy_ret_aux a k f n).
Proof.
  intros c k f. apply (copy_ret_aux_ind (fun q => is_true (stack_asm_name c q))); [reflexivity|].
  intros n q Hq. cbn. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_stack_asm_name" *)
Theorem copy_ret_stack_asm_name : forall c perf b kf vs (kont : prog a),
  stack_asm_name c (copy_ret perf b kf vs kont) = stack_asm_name c kont.
Proof.
  intros c perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [stack_asm_name]. rewrite copy_ret_aux_stack_asm_name.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

Lemma wInst_stack_asm_name c (i : asm.inst a) k f f' :
  wordLang.every_var_inst is_phy_var i -> inst_ok_less c i -> inst_arg_convention i ->
  (two_reg_arith c -> two_reg_inst i) ->
  k + 1 < reg_count c - LENGTH (avoid_regs c) -> 4 < k ->
  stack_asm_name c (wInst i (k, (f, f'))).
Proof.
  intros Hv Hok Harg Htwo Hk Hk4.
  destruct_inst i; unfold wInst, wRegWrite1, wRegWrite2, wReg1, wReg2 in *; split_goal;
    cbn [wStackLoad stack_asm_name inst_name arith_name fp_name addr_name reg_imm_name app
         wordLang.every_var_inst wordLang.every_var_imm inst_ok_less inst_arg_convention two_reg_inst is_phy_var] in *.
  all: unfold reg_name; nm_leaf.
Qed.

Lemma wMoveAux_stack_asm_name c l k f f' :
  k + 1 < reg_count c - LENGTH (avoid_regs c) ->
  (forall x y, In (x, y) l ->
     match x with inl r => r <= k + 1 | inr _ => True end /\
     match y with inl r => r <= k + 1 | inr _ => True end) ->
  stack_asm_name c (@wMoveAux a l (k, (f, f'))).
Proof.
  intros Hk; induction l as [|[x y] l IH]; intros Hl; [reflexivity|].
  assert (Hxy := Hl x y (or_introl eq_refl)).
  assert (Hs : stack_asm_name c (wMoveSingle (x, y) (k, (f, f')))).
  { destruct x as [x|x], y as [y|y]; cbn in Hxy |- *; destruct Hxy as [Hx Hy]; try reflexivity.
    unfold reg_name. nm_leaf. }
  destruct l as [|xy' l']; cbn [wMoveAux] in *; [exact Hs|].
  cbn [stack_asm_name]. apply andb_true_iff; split; [exact Hs|].
  apply IH. intros x' y' Hi. apply Hl. right; exact Hi.
Qed.

Lemma wMove_stack_asm_name c xs k f f' :
  k + 1 < reg_count c - LENGTH (avoid_regs c) ->
  stack_asm_name c (@wMove a xs (k, (f, f'))).
Proof.
  intros Hk. unfold wMove. apply wMoveAux_stack_asm_name; [exact Hk|].
  intros x y Hi. apply in_map_iff in Hi as [[u v] [E _]]. injection E as <- <-.
  unfold format_var. split;
    [destruct u as [u|]|destruct v as [v|]]; try (destruct (u <? k) eqn:Eu);
    try (destruct (v <? k) eqn:Ev); to_prop; try exact Logic.I; lia.
Qed.

Lemma stack_asm_name_wStackLoad c l (p : prog a) :
  stack_asm_name c (wStackLoad l p) = stack_asm_name c p.
Proof. induction l as [|[r i] l IH]; [reflexivity|]. cbn. exact IH. Qed.

(** The hypotheses of [word_to_stack_stack_asm_name_lem] (Galette-only
    bundle). *)
Definition nm_hyps c k (p : wordLang.prog a) : Prop :=
  post_alloc_conventions k p /\ full_inst_ok_less c p /\
  (two_reg_arith c -> every_inst two_reg_inst p) /\ (no_share_inst p \/ ISA c <> Ag32).

Ltac nm_hyps_split H :=
  unfold nm_hyps, post_alloc_conventions, no_share_inst in H;
  cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention full_inst_ok_less every_inst
       not_created_subprogs] in H.

Lemma nm_hyps_intro c k (p : wordLang.prog a) :
  wordLang.every_var is_phy_var p -> wordLang.every_stack_var (fun x => 2 * k <=? x) p ->
  call_arg_convention p -> full_inst_ok_less c p ->
  (two_reg_arith c -> every_inst two_reg_inst p) -> (no_share_inst p \/ ISA c <> Ag32) ->
  nm_hyps c k p.
Proof.
  intros H1 H2 H3 H4 H5 H6. unfold nm_hyps, post_alloc_conventions. unfold is_true in *.
  rewrite H1, H2, H3. auto.
Qed.

Ltac nsi_tac :=
  match goal with
  | |- no_share_inst ?p \/ _ =>
      match goal with
      | Hn : _ \/ ISA _ <> _ |- _ =>
          let Hx := fresh in destruct Hn as [Hx|Hx]; [left; to_prop|right; exact Hx];
          match goal with Hy : not_created_subprogs _ p |- _ => exact Hy end
      end
  end.

Ltac nm_ih_side :=
  first [ assumption
        | (let Ht := fresh "Ht" in intro Ht;
           repeat match goal with Hx : is_true (two_reg_arith _) -> _ |- _ => specialize (Hx Ht) end;
           to_prop; assumption)
        | nsi_tac ].

Ltac nm_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?k = (?q, _),
    IH : forall bs, nm_hyps ?c _ ?p -> is_true (stack_asm_name ?c (FST (comp ?c ?pf ?p bs ?k))) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (stack_asm_name c q))
        by (replace q with (FST (comp c pf p b k)) by (rewrite E; reflexivity); apply IH;
            apply nm_hyps_intro; to_prop; nm_ih_side);
      clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- context [stack_asm_name ?c _] =>
      let H := fresh "Hq" in
      assert (H : is_true (stack_asm_name c q))
        by (eapply wLive_stack_asm_name; split; [|exact E]; cbn [FST fst]; lia);
      clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- context [stack_asm_name ?c _] =>
      let H := fresh "Hq" in let Hd := fresh "Hd" in
      destruct (call_dest_stack_asm_name c _ _ _ _ _ E) as [H Hd]; clear E;
      destruct d'; cbn [FST fst] in Hd
  end.

Lemma stack_asm_name_main c k f f' :
  k + 1 < reg_count c - LENGTH (avoid_regs c) -> 4 < k ->
  forall (p : wordLang.prog a) bs, nm_hyps c k p ->
  stack_asm_name c (FST (comp c false p bs (k, (f, f')))).
Proof.
  intros Hk Hk4 p. induction p using wordConvs.prog_nested_ind; intros bs0 Hh; cbn [comp].
  all: nm_hyps_split Hh; unfold wShareInst, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply wMove_stack_asm_name; exact Hk).
  all: try (match goal with |- is_true (stack_asm_name _ (wInst _ _)) => idtac end;
            destruct Hh as (Hh1 & Hh2 & Hh3 & _); to_prop; apply wInst_stack_asm_name; auto).
  all: try (match goal with IH : forall _, nm_hyps _ _ ?p -> _ |- is_true (stack_asm_name _ (FST (comp _ _ ?p _ _))) =>
              apply IH end;
            apply nm_hyps_intro; to_prop; auto;
            nsi_tac).
  all: nm_ih.
  all: unfold wShareInst, wRegWrite1, wRegWrite2, wReg1, wReg2, SeqStackFree, StackHandlerArgs, StackArgs,
         PushHandler, PopHandler, handler_slots;
       split_goal;
       cbn [stack_asm_name wStackLoad inst_name arith_name fp_name addr_name reg_imm_name app list_Seq];
       rewrite ?stack_asm_name_wStackLoad, ?stack_move_stack_asm_name, ?copy_ret_stack_asm_name;
       cbn [stack_asm_name wStackLoad inst_name arith_name fp_name addr_name reg_imm_name app list_Seq].
  all: unfold reg_name; nm_leaf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_stack_asm_name_lem" *)
Theorem word_to_stack_stack_asm_name_lem : forall c perf (p : wordLang.prog a) bs kf,
  perf = false /\
  post_alloc_conventions (FST kf) p /\
  full_inst_ok_less c p /\
  (two_reg_arith c -> every_inst two_reg_inst p) /\
  (no_share_inst p \/ ISA c <> Ag32) /\
  FST kf + 1 < reg_count c - LENGTH (avoid_regs c) /\
  4 < FST kf ->
  stack_asm_name c (FST (comp c perf p bs kf)).
Proof.
  intros c perf p bs [k [f f']] (-> & H1 & H2 & H3 & H4 & H5 & H6). cbn [FST fst] in *.
  apply stack_asm_name_main; auto. repeat split; assumption.
Qed.

End AsmName.


Section AsmRemove.
Context {a : N}.
Implicit Types (c : asm_config a).

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "call_dest_stack_asm_remove" *)
Theorem call_dest_stack_asm_remove : forall c d (a0 : list N) k q0 d',
  FST k + 1 < reg_count c - LENGTH (avoid_regs c) /\
  @call_dest a d a0 k = (q0, d') ->
  stack_asm_remove c q0 /\
  match d' with
  | inr r => r <= FST k + 1
  | inl l => True
  end.
Proof.
  intros c d a0 [k [f f']] q0 d' [H E]. cbn [FST fst] in *. unfold call_dest, wReg2 in E.
  destruct d as [pos|]; [injection E as <- <-; split; [reflexivity|exact Logic.I]|].
  destruct (LENGTH a0 =? 0); [injection E as <- <-; split; [reflexivity|exact Logic.I]|].
  destruct (LAST a0 DIV 2 <? k) eqn:Ek; injection E as <- <-; cbn; unfold reg_name;
    nm_leaf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_stack_asm_remove" *)
Theorem wLive_stack_asm_remove : forall c q bs kf q1 bs',
  FST kf + 1 < reg_count c - LENGTH (avoid_regs c) /\
  @wLive a q bs kf = (q1, bs') ->
  stack_asm_remove c q1.
Proof.
  intros c q bs [k [f f']] q1 bs' [H E]. unfold wLive in E.
  destruct (f =? 0); [injection E as <- _; reflexivity|].
  destruct (insert_bitmap _ bs) eqn:Ei. injection E as <- _.
  cbn [FST fst] in H. cbn. unfold reg_name. nm_leaf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_stack_asm_remove" *)
Theorem stack_move_stack_asm_remove : forall c n start offset i (p : prog a),
  reg_name i c ->
  stack_asm_remove c (stack_move n start offset i p) = stack_asm_remove c p.
Proof.
  intros c n start offset i p Hi. revert n start.
  apply (stack_move_ind (fun q => stack_asm_remove c q = stack_asm_remove c p)); [reflexivity|].
  intros q start Hq. cbn. rewrite Hq. unfold is_true in Hi. rewrite Hi, !andb_true_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_stack_asm_remove" *)
Theorem copy_ret_aux_stack_asm_remove : forall c k f n,
  reg_name k c -> stack_asm_remove c (@copy_ret_aux a k f n).
Proof.
  intros c k f n Hk. revert n.
  apply (copy_ret_aux_ind (fun q => is_true (stack_asm_remove c q))); [reflexivity|].
  intros n q Hq. cbn. unfold is_true in *. rewrite Hk, Hq. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_stack_asm_remove" *)
Theorem copy_ret_stack_asm_remove : forall c b kf vs (kont : prog a),
  reg_name (FST kf) c ->
  stack_asm_remove c (copy_ret false b kf vs kont) = stack_asm_remove c kont.
Proof.
  intros c b [k [f f']] vs kont Hk. cbn [FST fst] in Hk. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [stack_asm_remove]. rewrite copy_ret_aux_stack_asm_remove by exact Hk.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

Lemma stack_asm_remove_wStackLoad c l (p : prog a) :
  stack_asm_remove c (wStackLoad l p) = EVERY (fun '(r, _) => reg_name r c) l && stack_asm_remove c p.
Proof.
  induction l as [|[r i] l IH]; [reflexivity|]. cbn [wStackLoad stack_asm_remove EVERY].
  rewrite IH. destruct (reg_name r c), (EVERY _ l), (stack_asm_remove c p); reflexivity.
Qed.

Lemma wMoveAux_stack_asm_remove c l k f f' :
  k + 1 < reg_count c - LENGTH (avoid_regs c) ->
  (forall x y, In (x, y) l ->
     match x with inl r => r <= k + 1 | inr _ => True end /\
     match y with inl r => r <= k + 1 | inr _ => True end) ->
  stack_asm_remove c (@wMoveAux a l (k, (f, f'))).
Proof.
  intros Hk; induction l as [|[x y] l IH]; intros Hl; [reflexivity|].
  assert (Hxy := Hl x y (or_introl eq_refl)).
  assert (Hs : stack_asm_remove c (wMoveSingle (x, y) (k, (f, f')))).
  { destruct x as [x|x], y as [y|y]; cbn in Hxy |- *; destruct Hxy as [Hx Hy]; try reflexivity;
    unfold reg_name; nm_leaf. }
  destruct l as [|xy' l']; cbn [wMoveAux] in *; [exact Hs|].
  cbn [stack_asm_remove]. apply andb_true_iff; split; [exact Hs|].
  apply IH. intros x' y' Hi. apply Hl. right; exact Hi.
Qed.

Lemma wMove_stack_asm_remove c xs k f f' :
  k + 1 < reg_count c - LENGTH (avoid_regs c) ->
  stack_asm_remove c (@wMove a xs (k, (f, f'))).
Proof.
  intros Hk. unfold wMove. apply wMoveAux_stack_asm_remove; [exact Hk|].
  intros x y Hi. apply in_map_iff in Hi as [[u v] [E _]]. injection E as <- <-.
  unfold format_var. split;
    [destruct u as [u|]|destruct v as [v|]]; try (destruct (u <? k) eqn:Eu);
    try (destruct (v <? k) eqn:Ev); to_prop; try exact Logic.I; lia.
Qed.

Ltac rm_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?k = (?q, _),
    IH : forall bs, is_true (stack_asm_remove ?c (FST (comp ?c ?pf ?p bs ?k))) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (stack_asm_remove c q))
        by (replace q with (FST (comp c pf p b k)) by (rewrite E; reflexivity); apply IH);
      clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- context [stack_asm_remove ?c _] =>
      let H := fresh "Hq" in
      assert (H : is_true (stack_asm_remove c q))
        by (eapply wLive_stack_asm_remove; split; [|exact E]; cbn [FST fst]; lia);
      clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- context [stack_asm_remove ?c _] =>
      let H := fresh "Hq" in let Hd := fresh "Hd" in let Hc := fresh "Hc" in
      assert (Hc : FST kf + 1 < reg_count c - LENGTH (avoid_regs c)) by (cbn [FST fst]; lia);
      destruct (call_dest_stack_asm_remove c _ _ _ _ _ (conj Hc E)) as [H Hd];
      clear E; destruct d'; cbn [FST fst] in Hd
  end.

Lemma stack_asm_remove_main c k f f' :
  k + 1 < reg_count c - LENGTH (avoid_regs c) ->
  forall (p : wordLang.prog a) bs,
  stack_asm_remove c (FST (comp c false p bs (k, (f, f')))).
Proof.
  intros Hk p. induction p using wordConvs.prog_nested_ind; intros bs0; cbn [comp].
  all: unfold wShareInst, wInst, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply wMove_stack_asm_remove; exact Hk).
  all: try (match goal with IH : forall _, is_true (stack_asm_remove _ (FST (comp _ _ ?p _ _)))
              |- is_true (stack_asm_remove _ (FST (comp _ _ ?p _ _))) => apply IH end).
  all: rm_ih.
  all: unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots;
       split_goal;
       cbn [stack_asm_remove wStackLoad app list_Seq EVERY];
       rewrite ?stack_asm_remove_wStackLoad, ?stack_move_stack_asm_remove, ?copy_ret_stack_asm_remove;
       cbn [stack_asm_remove wStackLoad app list_Seq EVERY].
  all: cbn [FST fst]; unfold reg_name; nm_leaf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_stack_asm_remove_lem" *)
Theorem word_to_stack_stack_asm_remove_lem : forall c perf (p : wordLang.prog a) bs kf,
  FST kf + 1 < reg_count c - LENGTH (avoid_regs c) /\ perf = false ->
  stack_asm_remove c (FST (comp c perf p bs kf)).
Proof.
  intros c perf p bs [k [f f']] [H ->]. apply stack_asm_remove_main. exact H.
Qed.

End AsmRemove.

(** ** [alloc_arg], [reg_bound], [call_args] *)

Section AllocArg.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_alloc_arg" *)
Theorem stack_move_alloc_arg : forall n st off i (p : prog a),
  alloc_arg p -> alloc_arg (stack_move n st off i p).
Proof.
  intros n st off i p H. revert n st.
  apply (stack_move_ind (fun q => is_true (alloc_arg q))); [exact H|].
  intros q start Hq. cbn. rewrite andb_true_r. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_arg_copy_ret_aux" *)
Theorem alloc_arg_copy_ret_aux : forall k f n, alloc_arg (@copy_ret_aux a k f n).
Proof.
  intros k f. apply (copy_ret_aux_ind (fun q => is_true (alloc_arg q))); [reflexivity|].
  intros n q Hq. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_arg_copy_ret" *)
Theorem alloc_arg_copy_ret : forall perf b kf vs (kont : prog a),
  alloc_arg (copy_ret perf b kf vs kont) = alloc_arg kont.
Proof.
  intros perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [alloc_arg]. rewrite alloc_arg_copy_ret_aux.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

Lemma alloc_arg_wStackLoad l (p : prog a) : alloc_arg (wStackLoad l p) = alloc_arg p.
Proof. induction l as [|[r i] l IH]; [reflexivity|]. exact IH. Qed.

Lemma alloc_arg_wMoveAux l kf : alloc_arg (@wMoveAux a l kf).
Proof.
  destruct kf as [k [f f']]. induction l as [|xy l IH]; [reflexivity|].
  destruct l as [|xy' l']; cbn [wMoveAux] in *;
    [destruct xy as [[x|x] [y|y]]; reflexivity|].
  cbn [alloc_arg]. unfold is_true in *. rewrite IH. destruct xy as [[x|x] [y|y]]; reflexivity.
Qed.

Lemma alloc_arg_wLive live bs kf : alloc_arg (FST (@wLive a live bs kf)).
Proof. destruct kf as [k [f f']]. unfold wLive. split_goal; reflexivity. Qed.

Lemma alloc_arg_call_dest dest args kf : alloc_arg (FST (@call_dest a dest args kf)).
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?alloc_arg_wStackLoad; reflexivity.
Qed.

Ltac aa_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?k = (?q, _),
    IH : forall bs kf, is_true (alloc_arg (FST (comp ?c ?pf ?p bs kf))) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (alloc_arg q))
        by (replace q with (FST (comp c pf p b k)) by (rewrite E; reflexivity); apply IH);
      clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- _ =>
      let H := fresh "Hq" in
      pose proof (alloc_arg_wLive l b kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- _ =>
      let H := fresh "Hq" in
      pose proof (alloc_arg_call_dest d ar kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_alloc_arg" *)
Theorem word_to_stack_alloc_arg : forall c perf (p : wordLang.prog a) n args,
  perf = false ->
  alloc_arg (FST (comp c perf p n args)).
Proof.
  intros c perf p n args ->. revert n args.
  induction p using wordConvs.prog_nested_ind; intros bs0 [k [f f']]; cbn [comp].
  all: unfold wShareInst, wInst, wMove, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply alloc_arg_wMoveAux).
  all: try (match goal with IH : forall _ _, is_true (alloc_arg (FST (comp _ _ ?p _ _)))
              |- is_true (alloc_arg (FST (comp _ _ ?p _ _))) => apply IH end).
  all: aa_ih.
  all: unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots;
       split_goal;
       cbn [alloc_arg wStackLoad app list_Seq];
       rewrite ?alloc_arg_wStackLoad, ?alloc_arg_copy_ret;
       cbn [alloc_arg wStackLoad app list_Seq].
  all: nm_leaf.
  all: try (apply stack_move_alloc_arg; reflexivity).
Qed.

End AllocArg.

Section RegBound.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_reg_bound" *)
Theorem stack_move_reg_bound : forall n st off i (p : prog a) k,
  i < k /\ reg_bound p k ->
  reg_bound (stack_move n st off i p) k.
Proof.
  intros n st off i p k [Hi H]. revert n st.
  apply (stack_move_ind (fun q => is_true (reg_bound q k))); [exact H|].
  intros q start Hq. cbn. unfold is_true in *. rewrite Hq. apply N.ltb_lt in Hi. rewrite Hi. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_reg_bound" *)
Theorem copy_ret_aux_reg_bound : forall k f n, reg_bound (@copy_ret_aux a k f n) (k + 2).
Proof.
  intros k f. apply (copy_ret_aux_ind (fun q => is_true (reg_bound q (k + 2)))); [reflexivity|].
  intros n q Hq. cbn. unfold is_true in *. rewrite Hq. replace (k <? k + 2) with true by (symmetry; apply N.ltb_lt; lia).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_reg_bound" *)
Theorem copy_ret_reg_bound : forall perf b k f f' vs (kont : prog a),
  reg_bound kont (k + 2) ->
  reg_bound (copy_ret perf b (k, (f, f')) vs kont) (k + 2).
Proof.
  intros perf b k f f' vs kont H. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [exact H|].
  cbn [reg_bound]. unfold is_true in *. rewrite copy_ret_aux_reg_bound.
  destruct (num_stack_ret k vs =? 0); cbn; rewrite H; reflexivity.
Qed.

Lemma reg_bound_wStackLoad l (p : prog a) k :
  reg_bound (wStackLoad l p) k = EVERY (fun '(r, _) => r <? k) l && reg_bound p k.
Proof.
  induction l as [|[r i] l IH]; [reflexivity|]. cbn [wStackLoad reg_bound EVERY].
  rewrite IH. destruct (r <? k), (EVERY _ l), (reg_bound p k); reflexivity.
Qed.

Lemma reg_bound_wMoveAux l k f f' :
  (forall x y, In (x, y) l ->
     match x with inl r => r <= k + 1 | inr _ => True end /\
     match y with inl r => r <= k + 1 | inr _ => True end) ->
  reg_bound (@wMoveAux a l (k, (f, f'))) (k + 2).
Proof.
  induction l as [|[x y] l IH]; intros Hl; [reflexivity|].
  assert (Hxy := Hl x y (or_introl eq_refl)).
  assert (Hs : reg_bound (@wMoveSingle a (x, y) (k, (f, f'))) (k + 2)).
  { destruct x as [x|x], y as [y|y]; cbn in Hxy |- *; destruct Hxy as [Hx Hy]; nm_leaf. }
  destruct l as [|xy' l']; cbn [wMoveAux] in *; [exact Hs|].
  cbn [reg_bound]. apply andb_true_iff; split; [exact Hs|].
  apply IH. intros x' y' Hi. apply Hl. right; exact Hi.
Qed.

Lemma reg_bound_wLive live bs k f f' :
  reg_bound (FST (@wLive a live bs (k, (f, f')))) (k + 2).
Proof. unfold wLive. split_goal; cbn; nm_leaf. Qed.

Lemma reg_bound_call_dest dest args k f f' :
  reg_bound (FST (@call_dest a dest args (k, (f, f')))) (k + 2) /\
  match SND (@call_dest a dest args (k, (f, f'))) with inr r => r < k + 2 | inl _ => True end.
Proof.
  unfold call_dest, wReg2. destruct dest as [pos|]; [split; [reflexivity|exact Logic.I]|].
  destruct (LENGTH args =? 0); [split; [reflexivity|exact Logic.I]|].
  destruct (LAST args DIV 2 <? k) eqn:E; cbn; to_prop; nm_leaf.
Qed.

Lemma post_alloc_conventions_intro k (p : wordLang.prog a) :
  wordLang.every_var is_phy_var p -> wordLang.every_stack_var (fun x => 2 * k <=? x) p ->
  call_arg_convention p -> post_alloc_conventions k p.
Proof. intros H1 H2 H3. unfold post_alloc_conventions, is_true in *. rewrite H1, H2, H3. reflexivity. Qed.

Ltac rb_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?kf = (?q, _),
    IH : forall bs, is_true (post_alloc_conventions ?k ?p) -> is_true (reg_bound (FST (comp ?c ?pf ?p bs ?kf)) ?m) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (reg_bound q m))
        by (replace q with (FST (comp c pf p b kf)) by (rewrite E; reflexivity); apply IH;
            apply post_alloc_conventions_intro; to_prop; assumption);
      clear E
  | E : wLive ?l ?b (?k, (?f, ?f')) = (?q, _) |- _ =>
      let H := fresh "Hq" in
      pose proof (reg_bound_wLive l b k f f') as H; rewrite E in H; cbn [FST fst] in H; clear E
  | E : call_dest ?d ?ar (?k, (?f, ?f')) = (?q, ?d') |- _ =>
      let H := fresh "Hq" in let Hd := fresh "Hd" in
      destruct (reg_bound_call_dest d ar k f f') as [H Hd]; rewrite E in H, Hd;
      cbn [FST fst SND snd] in H, Hd; clear E; destruct d'
  end.

Lemma reg_bound_main c k f f' :
  4 <= k ->
  forall (p : wordLang.prog a) bs, post_alloc_conventions k p ->
  reg_bound (FST (comp c false p bs (k, (f, f')))) (k + 2).
Proof.

  intros Hk4 p. induction p using wordConvs.prog_nested_ind; intros bs0 Hh; cbn [comp].
  all: unfold post_alloc_conventions in Hh;
    cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hh.
  all: unfold wShareInst, wInst, wMove, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply reg_bound_wMoveAux; intros x y Hi; apply in_map_iff in Hi as [[u v] [Eu _]];
            injection Eu as <- <-; unfold format_var; split;
            [destruct u as [u|]|destruct v as [v|]]; try (destruct (u <? k) eqn:Eu');
            try (destruct (v <? k) eqn:Ev'); to_prop; try exact Logic.I; lia).
  all: try (match goal with IH : forall _, _ -> is_true (reg_bound (FST (comp _ _ ?p _ _)) _)
              |- is_true (reg_bound (FST (comp _ _ ?p _ _)) _) => apply IH end;
            apply post_alloc_conventions_intro; to_prop; assumption).
  all: rb_ih.
  all: unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots;
       split_goal;
       cbn [reg_bound reg_bound_inst wStackLoad app list_Seq EVERY];
       rewrite ?reg_bound_wStackLoad;
       cbn [reg_bound reg_bound_inst wStackLoad app list_Seq EVERY].
  all: to_prop; inst_hyps; cbn [reg_bound]; unfold is_true;
    repeat match goal with |- (_ && _) = true => apply andb_true_iff; split end.
  all: try (apply copy_ret_reg_bound).
  all: try (apply stack_move_reg_bound; split).
  all: try (apply negb_true_iff, bool_decide_false_iff'; discriminate).
  all: cbn [reg_bound]; nm_leaf.
  all: discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_reg_bound" *)
Theorem word_to_stack_reg_bound : forall c perf (p : wordLang.prog a) n args,
  post_alloc_conventions (FST args) p /\ 4 <= FST args /\ perf = false ->
  reg_bound (FST (comp c perf p n args)) (FST args + 2).
Proof.
  intros c perf p n [k [f f']] (H & Hk & ->). cbn [FST fst] in *. apply reg_bound_main; assumption.
Qed.

Lemma reg_bound_inst_mono (i : asm.inst a) k k' :
  reg_bound_inst i k -> k <= k' -> reg_bound_inst i k'.
Proof.
  intros H Hk. destruct_inst i; cbn [reg_bound_inst] in *; nm_leaf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "reg_bound_mono" *)
Theorem reg_bound_mono : forall (p : prog a) k k',
  reg_bound p k /\ k <= k' -> reg_bound p k'.
Proof.
  intros p; induction p using stackProps.prog_nested_ind; intros k k' [Hp Hk].
  - cbn [reg_bound] in *. destruct dest, ret as [[y [r ?]]|], h as [[y2 ?]|];
      to_prop; nm_leaf;
      first [ eapply H; [reflexivity|]; split; eassumption
            | eapply H0; [reflexivity|]; split; eassumption ].
  - cbn [reg_bound] in *. to_prop. nm_leaf; [eapply IHp1|eapply IHp2]; split; eassumption.
  - cbn [reg_bound] in *. destruct ri; to_prop; nm_leaf; [eapply IHp1|eapply IHp2|eapply IHp1|eapply IHp2];
      split; eassumption.
  - cbn [reg_bound] in *. eapply IHp; split; eassumption.
  - destruct p; try contradiction; cbn [reg_bound] in *; to_prop; nm_leaf;
      try (destruct a0; nm_leaf);
      eapply reg_bound_inst_mono; eassumption.
Qed.

End RegBound.


Section CallArgs.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_call_args" *)
Theorem stack_move_call_args : forall n st off i (p : prog a),
  call_args p 1 2 3 4 0 -> call_args (stack_move n st off i p) 1 2 3 4 0.
Proof.
  intros n st off i p H. revert n st.
  apply (stack_move_ind (fun q => is_true (call_args q 1 2 3 4 0))); [exact H|].
  intros q start Hq. cbn. rewrite andb_true_r. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_call_args" *)
Theorem copy_ret_aux_call_args : forall k f n, call_args (@copy_ret_aux a k f n) 1 2 3 4 0.
Proof.
  intros k f. apply (copy_ret_aux_ind (fun q => is_true (call_args q 1 2 3 4 0))); [reflexivity|].
  intros n q Hq. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_call_args" *)
Theorem copy_ret_call_args : forall perf b kf vs (kont : prog a),
  call_args (copy_ret perf b kf vs kont) 1 2 3 4 0 = call_args kont 1 2 3 4 0.
Proof.
  intros perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [call_args]. rewrite copy_ret_aux_call_args.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

Lemma call_args_wStackLoad l (p : prog a) :
  call_args (wStackLoad l p) 1 2 3 4 0 = call_args p 1 2 3 4 0.
Proof. induction l as [|[r i] l IH]; [reflexivity|]. exact IH. Qed.

Lemma call_args_wMoveAux l kf : call_args (@wMoveAux a l kf) 1 2 3 4 0.
Proof.
  destruct kf as [k [f f']]. induction l as [|xy l IH]; [reflexivity|].
  destruct l as [|xy' l']; cbn [wMoveAux] in *;
    [destruct xy as [[x|x] [y|y]]; reflexivity|].
  cbn [call_args]. unfold is_true in *. rewrite IH. destruct xy as [[x|x] [y|y]]; reflexivity.
Qed.

Lemma call_args_wLive live bs kf : call_args (FST (@wLive a live bs kf)) 1 2 3 4 0.
Proof. destruct kf as [k [f f']]. unfold wLive. split_goal; reflexivity. Qed.

Lemma call_args_call_dest dest args kf : call_args (FST (@call_dest a dest args kf)) 1 2 3 4 0.
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?call_args_wStackLoad; reflexivity.
Qed.

Ltac ca_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?kf = (?q, _),
    IH : forall bs, is_true (post_alloc_conventions ?k ?p) -> is_true (call_args (FST (comp ?c ?pf ?p bs ?kf)) 1 2 3 4 0) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (call_args q 1 2 3 4 0))
        by (replace q with (FST (comp c pf p b kf)) by (rewrite E; reflexivity); apply IH;
            apply post_alloc_conventions_intro; to_prop; assumption);
      clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- _ =>
      let H := fresh "Hq" in
      pose proof (call_args_wLive l b kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- _ =>
      let H := fresh "Hq" in
      pose proof (call_args_call_dest d ar kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  end.

Lemma call_args_main c k f f' :
  forall (p : wordLang.prog a) bs, post_alloc_conventions k p ->
  call_args (FST (comp c false p bs (k, (f, f')))) 1 2 3 4 0.
Proof.
  intros p. induction p using wordConvs.prog_nested_ind; intros bs0 Hh; cbn [comp].
  all: unfold post_alloc_conventions in Hh;
    cbn [wordLang.every_var wordLang.every_stack_var call_arg_convention] in Hh.
  all: unfold wShareInst, wInst, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply call_args_wMoveAux).
  all: try (match goal with IH : forall _, _ -> is_true (call_args (FST (comp _ _ ?p _ _)) _ _ _ _ _)
              |- is_true (call_args (FST (comp _ _ ?p _ _)) _ _ _ _ _) => apply IH end;
            apply post_alloc_conventions_intro; to_prop; assumption).
  all: ca_ih.
  all: unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots;
       split_goal;
       cbn [call_args wStackLoad app list_Seq];
       rewrite ?call_args_wStackLoad, ?copy_ret_call_args;
       cbn [call_args wStackLoad app list_Seq].
  all: to_prop; inst_hyps; unfold is_true;
    repeat match goal with |- (_ && _) = true => apply andb_true_iff; split end.
  all: try (apply stack_move_call_args; reflexivity).
  all: nm_leaf.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_call_args" *)
Theorem word_to_stack_call_args : forall c perf (p : wordLang.prog a) n args,
  post_alloc_conventions (FST args) p /\ perf = false ->
  call_args (FST (comp c perf p n args)) 1 2 3 4 0.
Proof.
  intros c perf p n [k [f f']] [H ->]. apply call_args_main. exact H.
Qed.

End CallArgs.

(** ** Gluing the conventions together *)

Section Glue.
Context {a : N}.

Lemma compile_prog_shape ac perf (p : wordLang.prog a) n k bs :
  exists m f f',
    FST (compile_prog ac perf p n k bs) = Seq (StackAlloc m) (FST (comp ac perf p bs (k, (f, f')))).
Proof.
  unfold compile_prog. cbv zeta. destruct (comp _ _ _ _ _) as [q1 bm] eqn:E.
  cbn [FST fst]. eexists _, _, _. rewrite E. reflexivity.
Qed.

Lemma compile_word_to_stack_Forall (P : prog a -> Prop) (Q : wordLang.prog a -> Prop) ac perf k :
  (forall m (p : wordLang.prog a) bs f f', Q p -> P (Seq (StackAlloc m) (FST (comp ac perf p bs (k, (f, f')))))) ->
  forall (progs : list (N * (N * wordLang.prog a))) bm q r,
  compile_word_to_stack ac perf k progs bm = (q, r) ->
  Forall (fun '(n, (m, p)) => Q p) progs ->
  Forall (fun '(n, p) => P p) q.
Proof.
  intros HP progs; induction progs as [|[i [n p]] progs IH]; intros bm q r E HQ;
    cbn [compile_word_to_stack] in E.
  - injection E as <- _. constructor.
  - destruct (compile_prog ac perf p n k bm) as [prog [f bm1]] eqn:Ep.
    destruct (compile_word_to_stack ac perf k progs bm1) as [progs' [fs bm']] eqn:Ew.
    injection E as <- _. inversion HQ as [|? ? HQ1 HQ2]; subst. constructor.
    + destruct (compile_prog_shape ac perf p n k bm) as (m & f1 & f1' & Hs).
      rewrite Ep in Hs. cbn [FST fst] in Hs. rewrite Hs. apply HP. exact HQ1.
    + eapply IH; eassumption.
Qed.

Lemma EVERY_Forall_iff {A} (P : A -> bool) l : is_true (EVERY P l) <-> Forall (fun x => is_true (P x)) l.
Proof. unfold is_true. apply EVERY_Forall. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_convs" *)
Theorem compile_word_to_stack_convs : forall c k (p : list (N * (N * wordLang.prog a))) bm q bm',
  compile_word_to_stack c false k p bm = (q, bm') /\
  EVERY (fun '(n, (m, p)) =>
    ⌜is_true (full_inst_ok_less c p) /\
     (is_true (two_reg_arith c) -> is_true (every_inst two_reg_inst p)) /\
     (no_share_inst p \/ ISA c <> Ag32) /\
     is_true (post_alloc_conventions k p)⌝) p /\
  4 < k /\ k + 1 < reg_count c - LENGTH (avoid_regs c) ->
  EVERY (fun '(x, y) =>
    stack_asm_name c y && stack_asm_remove c y && alloc_arg y && reg_bound y (k + 2) &&
    call_args y 1 2 3 4 0) q.
Proof.
  intros c k p bm q bm' (E & H & Hk4 & Hk).
  apply EVERY_Forall_iff in H. apply EVERY_Forall_iff.
  assert (H' : Forall (fun '(n, (m, p)) =>
    is_true (full_inst_ok_less c p) /\
     (is_true (two_reg_arith c) -> is_true (every_inst two_reg_inst p)) /\
     (no_share_inst p \/ ISA c <> Ag32) /\
     is_true (post_alloc_conventions k p)) p).
  { eapply Forall_impl; [|exact H]. intros [n [m pp]] Hx. apply bool_decide_spec in Hx. exact Hx. }
  pose proof (compile_word_to_stack_Forall
    (fun y => is_true (stack_asm_name c y && stack_asm_remove c y && alloc_arg y && reg_bound y (k + 2) &&
                       call_args y 1 2 3 4 0))
    (fun pp => is_true (full_inst_ok_less c pp) /\
     (is_true (two_reg_arith c) -> is_true (every_inst two_reg_inst pp)) /\
     (no_share_inst pp \/ ISA c <> Ag32) /\
     is_true (post_alloc_conventions k pp)) c false k) as L.
  refine (Forall_impl _ _ (L _ p bm q bm' E H')).
  - intros [x y] Hy. exact Hy.
  - intros m pp bs f f' (H1 & H2 & H3 & H4). cbn [stack_asm_name stack_asm_remove alloc_arg reg_bound call_args].
    pose proof (word_to_stack_stack_asm_name_lem c false pp bs (k, (f, f'))) as A1.
    pose proof (word_to_stack_stack_asm_remove_lem c false pp bs (k, (f, f'))) as A2.
    pose proof (word_to_stack_alloc_arg c false pp bs (k, (f, f')) eq_refl) as A3.
    pose proof (word_to_stack_reg_bound c false pp bs (k, (f, f'))) as A4.
    pose proof (word_to_stack_call_args c false pp bs (k, (f, f'))) as A5.
    cbn [FST fst] in *.
    unfold is_true in *. rewrite A1, A2, A3, A4, A5 by (repeat split; auto; lia). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_stack_convs" *)
Theorem word_to_stack_stack_convs : forall ac (p : list (N * (N * wordLang.prog a))) bytes c' f' p' k,
  word_to_stack.compile ac false p = (bytes, (c', (f', p'))) /\
  EVERY (post_alloc_conventions k) (MAP (fun x => SND (SND x)) p) /\
  k = reg_count ac - (5 + LENGTH (avoid_regs ac)) /\
  4 <= k ->
  EVERY alloc_arg (MAP SND p') /\
  EVERY (fun p => reg_bound p (k + 2)) (MAP SND p') /\
  EVERY (fun p => call_args p 1 2 3 4 0) (MAP SND p').
Proof.
  intros ac p bytes c' f' p' k (E & H & Ek & Hk4).
  unfold word_to_stack.compile in E. cbv zeta in E. rewrite <- Ek in E.
  destruct (compile_word_to_stack _ _ _ _ _) as [progs [fs bm]] eqn:Ew. injection E as _ _ _ <-.
  apply EVERY_Forall_iff in H. rewrite Forall_map in H.
  assert (HQ : Forall (fun '(n, (m, p)) => is_true (post_alloc_conventions k p)) p).
  { eapply Forall_impl; [|exact H]. intros [n [m pp]] Hx. exact Hx. }
  pose proof (compile_word_to_stack_Forall
    (fun y => is_true (alloc_arg y) /\ is_true (reg_bound y (k + 2)) /\ is_true (call_args y 1 2 3 4 0))
    (fun pp => is_true (post_alloc_conventions k pp)) ac false k) as L.
  assert (HR : Forall (fun '(n, y) =>
    is_true (alloc_arg y) /\ is_true (reg_bound y (k + 2)) /\ is_true (call_args y 1 2 3 4 0)) progs).
  { refine (L _ p _ progs _ Ew HQ).
    intros m pp bs f f'' Hp. cbn [alloc_arg reg_bound call_args].
    pose proof (word_to_stack_alloc_arg ac false pp bs (k, (f, f'')) eq_refl) as A3.
    pose proof (word_to_stack_reg_bound ac false pp bs (k, (f, f''))) as A4.
    pose proof (word_to_stack_call_args ac false pp bs (k, (f, f''))) as A5.
    cbn [FST fst] in *. unfold is_true in *. rewrite A3, A4, A5 by (repeat split; auto; lia).
    repeat split. }
  cbn [MAP List.map SND snd].
  rewrite !EVERY_Forall_iff. rewrite Forall_forall in HR.
  clear Ek.
  repeat split; (constructor; [cbn [SND snd raise_stub store_consts_stub list_Seq handler_slots
                                    alloc_arg reg_bound call_args reg_bound_inst]; nm_leaf
                              |constructor; [cbn [SND snd raise_stub store_consts_stub list_Seq handler_slots
                                    alloc_arg reg_bound call_args reg_bound_inst]; nm_leaf|]]);
    apply Forall_forall; intros y Hy; apply in_map_iff in Hy as [[n y'] [Ey Hy]];
    cbn [SND snd] in Ey; subst y'; apply HR in Hy; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_stack_asm_convs" *)
Theorem word_to_stack_stack_asm_convs : forall c (progs : list (N * (N * wordLang.prog a))),
  EVERY (fun '(n, (m, p)) =>
    ⌜is_true (full_inst_ok_less c p) /\
     (is_true (two_reg_arith c) -> is_true (every_inst two_reg_inst p)) /\
     (no_share_inst p \/ ISA c <> Ag32) /\
     is_true (post_alloc_conventions (reg_count c - (LENGTH (avoid_regs c) + 5)) p)⌝) progs /\
  4 < reg_count c - (LENGTH (avoid_regs c) + 5) ->
  EVERY (fun '(n, p) => stack_asm_name c p && stack_asm_remove c p)
    (SND (SND (SND (word_to_stack.compile c false progs)))).
Proof.
  intros c progs [H Hk]. unfold word_to_stack.compile. cbv zeta.
  replace (5 + LENGTH (avoid_regs c)) with (LENGTH (avoid_regs c) + 5) by lia.
  destruct (compile_word_to_stack _ _ _ _ _) as [q [fs bm]] eqn:Ew. cbn [SND snd].
  assert (Hk2 : reg_count c - (LENGTH (avoid_regs c) + 5) + 1 < reg_count c - LENGTH (avoid_regs c)) by lia.
  pose proof (compile_word_to_stack_convs c _ progs _ q _ (conj Ew (conj H (conj Hk Hk2)))) as R.
  apply EVERY_Forall_iff in R. apply EVERY_Forall_iff.
  constructor; [|constructor].
  - cbn. unfold reg_name. nm_leaf.
  - cbn. unfold reg_name. nm_leaf.
  - eapply Forall_impl; [|exact R]. intros [x y] Hy. cbn beta iota in *. to_prop. unfold is_true. apply andb_true_iff; split; assumption.
Qed.

End Glue.

(** ** Code labels *)

Ltac set_unfold :=
  unfold pred_set.UNION, pred_set.INSERT, pred_set.EMPTY, pred_set.IN, pred_set.IMAGE,
    pred_set.SUBSET, pred_set.BIGUNION in *.

Section CodeLabels.
Context {a : N}.

Lemma get_code_labels_wRegWrite1 (g : N -> prog a) r kf :
  (forall n, stackProps.get_code_labels (g n) = {}) ->
  stackProps.get_code_labels (wRegWrite1 g r kf) = {}.
Proof.
  intros H. destruct kf as [k [f f']]. unfold wRegWrite1. destruct (r DIV 2 <? k); [apply H|].
  cbn [stackProps.get_code_labels]. rewrite H. apply set_ext; intros x; set_unfold; tauto.
Qed.

Lemma get_code_labels_wRegWrite2 (g : N -> prog a) r kf :
  (forall n, stackProps.get_code_labels (g n) = {}) ->
  stackProps.get_code_labels (wRegWrite2 g r kf) = {}.
Proof.
  intros H. destruct kf as [k [f f']]. unfold wRegWrite2. destruct (r DIV 2 <? k); [apply H|].
  cbn [stackProps.get_code_labels]. rewrite H. apply set_ext; intros x; set_unfold; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_code_handler_labels_wStackLoad" *)
Theorem get_code_handler_labels_wStackLoad : forall ls (x : prog a) n,
  stackProps.get_code_labels (wStackLoad ls x) = stackProps.get_code_labels x /\
  stack_get_handler_labels n (wStackLoad ls x) = stack_get_handler_labels n x.
Proof.
  induction ls as [|[r i] ls IH]; intros x n; [split; reflexivity|].
  cbn [wStackLoad stackProps.get_code_labels stack_get_handler_labels].
  destruct (IH x n) as [H1 H2]. rewrite H1, H2. split; apply set_ext; intros y; set_unfold; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_code_labels" *)
Theorem wLive_code_labels : forall q bs kf q' bs',
  @wLive a q bs kf = (q', bs') ->
  stackProps.get_code_labels q' = {}.
Proof.
  intros q bs [k [f f']] q' bs' E. unfold wLive in E.
  destruct (f =? 0); [injection E as <- _; reflexivity|].
  destruct (insert_bitmap _ bs). injection E as <- _. cbn. apply set_ext; intros y; set_unfold; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_code_labels" *)
Theorem stack_move_code_labels : forall a0 b c d (e : prog a),
  stackProps.get_code_labels (stack_move a0 b c d e) = stackProps.get_code_labels e.
Proof.
  intros a0 b c d e. revert a0 b.
  apply (stack_move_ind (fun q => stackProps.get_code_labels q = stackProps.get_code_labels e));
    [reflexivity|].
  intros q start Hq. cbn. rewrite Hq. apply set_ext; intros y; set_unfold; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_code_handler_labels_copy_ret_aux" *)
Theorem get_code_handler_labels_copy_ret_aux : forall m k f n,
  stackProps.get_code_labels (@copy_ret_aux a k f n) = {} /\
  stack_get_handler_labels m (@copy_ret_aux a k f n) = {}.
Proof.
  intros m k f. apply (copy_ret_aux_ind (fun q => stackProps.get_code_labels q = {} /\
    stack_get_handler_labels m q = {})); [split; reflexivity|].
  intros n q [H1 H2]. cbn. rewrite H1, H2. split; apply set_ext; intros y; set_unfold; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_code_handler_labels_copy_ret" *)
Theorem get_code_handler_labels_copy_ret : forall m perf b kf vs (kont : prog a),
  stackProps.get_code_labels (copy_ret perf b kf vs kont) = stackProps.get_code_labels kont /\
  stack_get_handler_labels m (copy_ret perf b kf vs kont) = stack_get_handler_labels m kont.
Proof.
  intros m perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [split; reflexivity|].
  cbn [stackProps.get_code_labels stack_get_handler_labels].
  destruct (get_code_handler_labels_copy_ret_aux m k (if b then f + handler_slots perf else f)
    (num_stack_ret k vs)) as [H1 H2]. rewrite H1, H2.
  destruct (num_stack_ret k vs =? 0); cbn [stackProps.get_code_labels stack_get_handler_labels];
    split; apply set_ext; intros y; set_unfold; tauto.
Qed.

Lemma gcl_empty_Seq (p q : prog a) :
  stackProps.get_code_labels p = {} -> stackProps.get_code_labels q = {} ->
  stackProps.get_code_labels (Seq p q) = {}.
Proof. intros H1 H2. cbn. rewrite H1, H2. apply set_ext; intros y; set_unfold; tauto. Qed.

Lemma gcl_wMoveAux l kf : stackProps.get_code_labels (@wMoveAux a l kf) = {}.
Proof.
  destruct kf as [k [f f']]. induction l as [|xy l IH]; [reflexivity|].
  destruct l as [|xy' l']; cbn [wMoveAux] in *;
    [destruct xy as [[x|x] [y|y]]; try reflexivity; apply gcl_empty_Seq; reflexivity|].
  apply gcl_empty_Seq; [|exact IH]. destruct xy as [[x|x] [y|y]]; try reflexivity.
  apply gcl_empty_Seq; reflexivity.
Qed.

Lemma gcl_wInst i kf : stackProps.get_code_labels (@wInst a i kf) = {}.
Proof.
  destruct_inst i; unfold wInst; split_goal;
    rewrite ?(proj1 (get_code_handler_labels_wStackLoad _ _ 0));
    repeat first [ apply get_code_labels_wRegWrite1; intros
                 | apply get_code_labels_wRegWrite2; intros ];
    reflexivity.
Qed.

Lemma gcl_wShareInst op v ad kf : stackProps.get_code_labels (@wShareInst a op v ad kf) = {}.
Proof.
  destruct op, ad; unfold wShareInst; split_goal;
    rewrite ?(proj1 (get_code_handler_labels_wStackLoad _ _ 0));
    repeat first [ apply get_code_labels_wRegWrite1; intros ]; reflexivity.
Qed.

Lemma gcl_call_dest dest args kf :
  forall x, x IN stackProps.get_code_labels (FST (@call_dest a dest args kf)) -> False.
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?(proj1 (get_code_handler_labels_wStackLoad _ _ 0)); intros x Hx; exact Hx.
Qed.

Lemma sghl_call_dest n dest args kf :
  forall x, x IN stack_get_handler_labels n (FST (@call_dest a dest args kf)) -> False.
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?(proj2 (get_code_handler_labels_wStackLoad _ _ n)); intros x Hx; exact Hx.
Qed.

Lemma sghl_wLive n live bs kf :
  forall x, x IN stack_get_handler_labels n (FST (@wLive a live bs kf)) -> False.
Proof. destruct kf as [k [f f']]. unfold wLive. split_goal; intros x Hx; cbn in Hx; set_unfold; tauto. Qed.

Lemma call_dest_dest dest args kf :
  match SND (@call_dest a dest args kf) with
  | inl l => dest = Some l \/ l = wordLang.raise_stub_location
  | inr _ => True
  end.
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. destruct dest; [left; reflexivity|].
  destruct (LENGTH args =? 0); [right; reflexivity|]. destruct (_ <? k); exact Logic.I.
Qed.

Ltac cl_ih n :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?kf = (?q, _),
    IH : forall bs, is_true (good_handlers n ?p) -> forall x, x IN stackProps.get_code_labels (FST (comp ?c ?pf ?p bs ?kf)) -> _ |- _ =>
      let H := fresh "Hq" in
      assert (H := IH b ltac:(to_prop; assumption)); rewrite E in H; cbn [FST fst] in H; clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- _ =>
      let H := fresh "Hq" in let H2 := fresh "Hh" in
      assert (H : forall y, y IN stackProps.get_code_labels q -> False)
        by (rewrite (wLive_code_labels l b kf q _ E); intros ? []);
      pose proof (sghl_wLive n l b kf) as H2; rewrite E in H2; cbn [FST fst] in H2; clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- _ =>
      let H := fresh "Hq" in let H2 := fresh "Hh" in let H3 := fresh "Hd" in
      pose proof (gcl_call_dest d ar kf) as H; pose proof (sghl_call_dest n d ar kf) as H2;
      pose proof (call_dest_dest d ar kf) as H3;
      rewrite E in H, H2, H3; cbn [FST fst SND snd] in H, H2, H3; clear E
  end.

Lemma stack_move_handler_labels n0 a0 b c d (e : prog a) :
  stack_get_handler_labels n0 (stack_move a0 b c d e) = stack_get_handler_labels n0 e.
Proof.
  revert a0 b.
  apply (stack_move_ind (fun q => stack_get_handler_labels n0 q = stack_get_handler_labels n0 e));
    [reflexivity|].
  intros q start Hq. cbn. rewrite Hq. apply set_ext; intros y; set_unfold; tauto.
Qed.

Lemma code_labels_main c k f f' n :
  forall (p : wordLang.prog a) bs, good_handlers n p ->
  forall x, x IN stackProps.get_code_labels (FST (comp c false p bs (k, (f, f')))) ->
    x = (wordLang.raise_stub_location, 0) \/ x = (wordLang.store_consts_stub_location, 0) \/
    (exists m, x = (m, 0) /\ m IN wordConvs.get_code_labels p) \/
    x IN stack_get_handler_labels n (FST (comp c false p bs (k, (f, f')))).
Proof.
  intros p. induction p using wordConvs.prog_nested_ind; intros bs0 Hh; cbn [comp].
  all: cbn [good_handlers] in Hh.
  all: unfold wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: rewrite ?gcl_wInst, ?gcl_wShareInst.
  all: try (unfold wMove; destruct (k, (f, f')); rewrite gcl_wMoveAux).
  all: try (match goal with IH : forall _, _ -> forall x, x IN stackProps.get_code_labels (FST (comp _ _ ?p _ _)) -> _
              |- forall x, x IN stackProps.get_code_labels (FST (comp _ _ ?p _ _)) -> _ =>
              intros x Hx; destruct (IH _ Hh x Hx) as [?|[?|[[m [? ?]]|?]]]; auto; right; right; left;
              exists m; split; auto end).
  all: cl_ih n.
  all: intros x Hx;
    rewrite ?(proj1 (get_code_handler_labels_wStackLoad _ _ n)),
      ?(proj2 (get_code_handler_labels_wStackLoad _ _ n)) in *;
    unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots in *;
    split_goal; cbn [stackProps.get_code_labels stack_get_handler_labels wordConvs.get_code_labels
                     wStackLoad list_Seq] in *;
    rewrite ?(proj1 (get_code_handler_labels_copy_ret n _ _ _ _ _)),
      ?(proj2 (get_code_handler_labels_copy_ret n _ _ _ _ _)), ?stack_move_code_labels in *;
    cbn [stackProps.get_code_labels stack_get_handler_labels] in *.
  all: rewrite ?stack_move_handler_labels in *; cbn [stack_get_handler_labels] in *.
  all: repeat match goal with
       | H : context [match ?s with inl _ => _ | inr _ => _ end] |- _ =>
           is_var s; destruct s; cbn beta iota in *
       end.
  all: set_unfold;
    repeat match goal with
    | H : False |- _ => contradiction
    | H : SOME _ = SOME _ |- _ => injection H as H
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | Hq : forall y : (N * N), _ -> _, Hx : _ |- _ =>
        let H := fresh in pose proof (Hq _ Hx) as H; clear Hx
    end; subst.
  all: try tauto.
  all: try (right; right; left; eexists; split; [reflexivity|tauto]).
  all: to_prop; subst;
    repeat match goal with |- context [decide ?P] => destruct (decide P); try contradiction end;
    try (destruct dest; cbn beta iota in *); subst; try tauto;
    try (right; right; left; eexists; split; [reflexivity|tauto]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_comp_code_labels" *)
Theorem word_to_stack_comp_code_labels : forall c perf (prog : wordLang.prog a) bs kf n,
  good_handlers n prog /\ perf = false ->
  stackProps.get_code_labels (FST (comp c perf prog bs kf)) SUBSET
  (wordLang.raise_stub_location, 0) INSERT
    (wordLang.store_consts_stub_location, 0) INSERT
      ((IMAGE (fun n => (n, 0)) (wordConvs.get_code_labels prog)) UNION
       stack_get_handler_labels n (FST (comp c perf prog bs kf))).
Proof.
  intros c perf prog bs [k [f f']] n [H ->] x Hx.
  destruct (code_labels_main c k f f' n prog bs H x Hx) as [E|[E|[(m & E & Hm)|E]]];
    set_unfold; [left; exact E|right; left; exact E| |].
  - right; right; left. exists m. auto.
  - right; right; right. exact E.
Qed.

Lemma In_set {A} (x : A) l : x IN set l <-> In x l.
Proof.
  induction l as [|y l IH]; cbn [LIST_TO_SET In]; set_unfold; [tauto|].
  rewrite <- IH. set_unfold. split; intros [H|H]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_code_labels" *)
Theorem compile_word_to_stack_code_labels : forall ac perf k (p : list (N * (N * wordLang.prog a))) bs p' bs',
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) p /\
  perf = false /\
  compile_word_to_stack ac perf k p bs = (p', bs') ->
  BIGUNION (IMAGE stackProps.get_code_labels (set (MAP SND p'))) SUBSET
  (wordLang.raise_stub_location, 0) INSERT
  (wordLang.store_consts_stub_location, 0) INSERT
  IMAGE (fun n => (n, 0)) (BIGUNION (set (MAP (fun '(n, (m, pp)) => wordConvs.get_code_labels pp) p))) UNION
  BIGUNION (set (MAP (fun '(n, pp) => stack_get_handler_labels n pp) p')).
Proof.
  intros ac perf k p; induction p as [|[i [n pp]] p IH]; intros bs p' bs' (Hg & -> & E);
    cbn [compile_word_to_stack] in E.
  - injection E as <- _. intros x Hx. set_unfold. destruct Hx as (s0 & (y & Es & Hy) & _).
    cbn in Hy. contradiction.
  - destruct (compile_prog ac false pp n k bs) as [prog [f bm1]] eqn:Ep.
    destruct (compile_word_to_stack ac false k p bm1) as [progs [fs bm']] eqn:Ew.
    injection E as <- _. cbn [EVERY] in Hg. to_prop.
    specialize (IH _ _ _ (conj H0 (conj eq_refl Ew))).
    intros x Hx. set_unfold. destruct Hx as (s0 & (y & Es & Hy) & Hx).
    cbn [MAP List.map SND snd LIST_TO_SET] in Hy. destruct Hy as [Hy|Hy].
    + subst y s0.
      destruct (compile_prog_shape ac false pp n k bs) as (m & f1 & f1' & Hs).
      rewrite Ep in Hs. cbn [FST fst] in Hs. subst prog.
      cbn [stackProps.get_code_labels stack_get_handler_labels] in Hx. set_unfold.
      destruct Hx as [[]|Hx].
      pose proof (word_to_stack_comp_code_labels ac false pp bs (k, (f1, f1')) i (conj H eq_refl) x Hx) as R.
      set_unfold. destruct R as [R|[R|[(z & -> & Hz)|R]]]; [left; exact R|right; left; exact R| |].
      * right; right; left. exists z. split; [reflexivity|].
        exists (wordConvs.get_code_labels pp). split; [|exact Hz]. cbn. left; reflexivity.
      * right; right; right. exists (stack_get_handler_labels i (Seq (StackAlloc m) (FST (comp ac false pp bs (k, (f1, f1')))))).
        split; [cbn; left; reflexivity|]. cbn [stack_get_handler_labels]. set_unfold. right. exact R.
    + assert (Hx' : BIGUNION (IMAGE stackProps.get_code_labels (set (MAP SND progs))) x).
      { set_unfold. exists s0. split; [exists y; split; [exact Es|exact Hy]|exact Hx]. }
      specialize (IH x Hx'). set_unfold.
      destruct IH as [R|[R|[(z & -> & (s1 & Hs1 & Hz))|(s1 & Hs1 & R)]]]; [left; exact R|right; left; exact R| |].
      * right; right; left. exists z. split; [reflexivity|]. exists s1. split; [|exact Hz].
        cbn [MAP List.map LIST_TO_SET]. right. exact Hs1.
      * right; right; right. exists s1. split; [|exact R]. cbn [MAP List.map LIST_TO_SET]. right. exact Hs1.
Qed.

Lemma In_MAP_FST {A B} (l : list (A * B)) x : In x (MAP FST l) <-> exists y, In (x, y) l.
Proof.
  rewrite in_map_iff. split; [intros [[u v] [<- H]]; exists v; exact H|intros [y H]; exists (x, y); auto].
Qed.

(** The labels of the two stubs. *)
Lemma stub_code_labels k x :
  x IN stackProps.get_code_labels (@raise_stub a false k) \/
  x IN stackProps.get_code_labels (@store_consts_stub a k) -> False.
Proof. cbn. set_unfold. tauto. Qed.

Lemma stub_handler_labels n k x :
  x IN stack_get_handler_labels n (@raise_stub a false k) \/
  x IN stack_get_handler_labels n (@store_consts_stub a k) -> False.
Proof. cbn. set_unfold. tauto. Qed.

(** Every label of the [compile_word_to_stack] output (pointwise form of
    [compile_word_to_stack_code_labels]). *)
Lemma cwts_label ac k (p : list (N * (N * wordLang.prog a))) bs p' bs' x :
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) p ->
  compile_word_to_stack ac false k p bs = (p', bs') ->
  (exists y, In y p' /\ x IN stackProps.get_code_labels (SND y)) ->
  x = (wordLang.raise_stub_location, 0) \/ x = (wordLang.store_consts_stub_location, 0) \/
  (exists m, x = (m, 0) /\ exists q, In q p /\ m IN wordConvs.get_code_labels (SND (SND q))) \/
  (exists y, In y p' /\ x IN stack_get_handler_labels (FST y) (SND y)).
Proof.
  intros Hg E (y & Hy & Hx).
  pose proof (compile_word_to_stack_code_labels ac false k p bs p' bs' (conj Hg (conj eq_refl E)) x) as R.
  set_unfold. destruct R as [R|[R|[(z & -> & s1 & Hs1 & Hz)|(s1 & Hs1 & R)]]].
  - exists (stackProps.get_code_labels (SND y)). split; [|exact Hx]. exists (SND y). split; [reflexivity|].
    apply In_set, in_map_iff. exists y; auto.
  - left; exact R.
  - right; left; exact R.
  - right; right; left. exists z. split; [reflexivity|]. apply In_set, in_map_iff in Hs1 as [[q1 [q2 q3]] [<- Hq]].
    exists (q1, (q2, q3)). auto.
  - right; right; right. apply In_set, in_map_iff in Hs1 as [[q1 q2] [<- Hq]]. exists (q1, q2). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_good_code_labels" *)
Theorem word_to_stack_good_code_labels : forall asm_conf (progs : list (N * (N * wordLang.prog a))) bytes bs fs prog' elabs,
  word_to_stack.compile asm_conf false progs = (bytes, (bs, (fs, prog'))) /\
  good_code_labels progs elabs ->
  stack_good_code_labels prog' elabs.
Proof.
  intros asm_conf progs bytes bs fs prog' elabs [E [Hg Hl]].
  unfold word_to_stack.compile in E. cbv zeta in E.
  destruct (compile_word_to_stack _ _ _ _ _) as [q [fs1 bm]] eqn:Ew. injection E as _ _ _ <-.
  pose proof (MAP_FST_compile_word_to_stack _ _ _ _ _ _ _ Ew) as Hf.
  unfold stack_good_code_labels. intros x Hx. set_unfold.
  destruct Hx as (s0 & (y & -> & Hy) & Hx). apply In_set in Hy.
  cbn [MAP List.map SND snd In] in Hy.
  destruct Hy as [<-|[<-|Hy]]; [exfalso; exact (stub_code_labels _ x (or_introl Hx))
                               |exfalso; exact (stub_code_labels _ x (or_intror Hx))|].
  apply in_map_iff in Hy as [y' [<- Hy]].
  destruct (cwts_label asm_conf _ progs _ q _ x Hg Ew (ex_intro _ y' (conj Hy Hx)))
    as [R|[R|[(m & -> & q0 & Hq0 & Hm)|(y1 & Hy1 & R)]]].
  - subst x. do 3 left. right. exists wordLang.raise_stub_location. split; [reflexivity|].
    apply In_set. cbn. left; reflexivity.
  - subst x. do 3 left. right. exists wordLang.store_consts_stub_location. split; [reflexivity|].
    apply In_set. cbn. right; left; reflexivity.
  - assert (Hm' : (set (MAP FST progs) UNION elabs) m).
    { apply Hl. set_unfold. exists (wordConvs.get_code_labels (SND (SND q0))). split; [|exact Hm].
      apply In_set, in_map_iff. exists q0. split; [|exact Hq0]. destruct q0 as [? [? ?]]. reflexivity. }
    set_unfold. destruct Hm' as [Hm'|Hm'].
    + do 3 left. right. exists m. split; [reflexivity|]. apply In_set. cbn [MAP List.map In]. right; right.
      rewrite Hf. apply In_set. exact Hm'.
    + do 2 left. right. exists m. split; [reflexivity|]. exact Hm'.
  - do 4 left. exists (stack_get_handler_labels (FST y1) (SND y1)). split; [|exact R].
    apply In_set, in_map_iff. exists y1. split; [destruct y1; reflexivity|]. cbn. right; right; exact Hy1.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_good_code_labels_incr" *)
Theorem word_to_stack_good_code_labels_incr : forall ac k (prog : list (N * (N * wordLang.prog a))) bs prog' fs' bs' elabs,
  wordLang.raise_stub_location IN elabs /\
  wordLang.store_consts_stub_location IN elabs /\
  compile_word_to_stack ac false k prog bs = (prog', (fs', bs')) ->
  good_code_labels prog elabs ->
  stack_good_code_labels prog' elabs.
Proof.
  intros ac k prog bs prog' fs' bs' elabs (Hr & Hs & Ew) [Hg Hl].
  pose proof (MAP_FST_compile_word_to_stack _ _ _ _ _ _ _ Ew) as Hf.
  unfold stack_good_code_labels. intros x Hx. set_unfold.
  destruct Hx as (s0 & (y & -> & Hy) & Hx). apply In_set in Hy.
  apply in_map_iff in Hy as [y' [<- Hy]].
  destruct (cwts_label ac _ prog _ prog' _ x Hg Ew (ex_intro _ y' (conj Hy Hx)))
    as [R|[R|[(m & -> & q0 & Hq0 & Hm)|(y1 & Hy1 & R)]]].
  - subst x. do 2 left. right. exists wordLang.raise_stub_location. split; [reflexivity|exact Hr].
  - subst x. do 2 left. right. exists wordLang.store_consts_stub_location. split; [reflexivity|exact Hs].
  - assert (Hm' : (set (MAP FST prog) UNION elabs) m).
    { apply Hl. set_unfold. exists (wordConvs.get_code_labels (SND (SND q0))). split; [|exact Hm].
      apply In_set, in_map_iff. exists q0. split; [|exact Hq0]. destruct q0 as [? [? ?]]. reflexivity. }
    set_unfold. destruct Hm' as [Hm'|Hm'].
    + do 3 left. right. exists m. split; [reflexivity|]. rewrite Hf. exact Hm'.
    + do 2 left. right. exists m. split; [reflexivity|]. exact Hm'.
  - do 4 left. exists (stack_get_handler_labels (FST y1) (SND y1)). split; [|exact R].
    apply In_set, in_map_iff. exists y1. split; [destruct y1; reflexivity|exact Hy1].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "sub_union_lemma" *)
Theorem sub_union_lemma : forall {A} (x y z : A -> Prop), x SUBSET y -> x SUBSET y UNION z.
Proof. intros A x y z H e He. set_unfold. left. apply H, He. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_good_handler_labels" *)
Theorem word_to_stack_good_handler_labels : forall asm_conf (prog : list (N * (N * wordLang.prog a))) bytes bs fs prog',
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) prog ->
  word_to_stack.compile asm_conf false prog = (bytes, (bs, (fs, prog'))) ->
  stack_good_handler_labels prog'.
Proof.
  intros asm_conf progs bytes bs fs prog' Hg E.
  unfold word_to_stack.compile in E. cbv zeta in E.
  destruct (compile_word_to_stack _ _ _ _ _) as [q [fs1 bm]] eqn:Ew. injection E as _ _ _ <-.
  unfold stack_good_handler_labels, restrict_nonzero. intros x Hx. set_unfold.
  destruct Hx as [(s0 & (y & -> & Hy) & Hx) Hnz]. apply In_set in Hy.
  cbn [MAP List.map SND snd In] in Hy.
  destruct Hy as [<-|[<-|Hy]]; [exfalso; exact (stub_code_labels _ x (or_introl Hx))
                               |exfalso; exact (stub_code_labels _ x (or_intror Hx))|].
  apply in_map_iff in Hy as [y' [<- Hy]].
  destruct (cwts_label asm_conf _ progs _ q _ x Hg Ew (ex_intro _ y' (conj Hy Hx)))
    as [R|[R|[(m & -> & q0 & Hq0 & Hm)|(y1 & Hy1 & R)]]];
    try (subst x; cbn in Hnz; exfalso; apply Hnz; reflexivity);
    try (cbn in Hnz; exfalso; apply Hnz; reflexivity).
  left. exists (stack_get_handler_labels (FST y1) (SND y1)). split; [|exact R].
  apply In_set, in_map_iff. exists y1. split; [destruct y1; reflexivity|]. cbn. right; right; exact Hy1.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_good_handler_labels_incr" *)
Theorem word_to_stack_good_handler_labels_incr : forall ac k (prog : list (N * (N * wordLang.prog a))) bs prog' fs' bs',
  EVERY (fun '(n, (m, pp)) => good_handlers n pp) prog ->
  compile_word_to_stack ac false k prog bs = (prog', (fs', bs')) ->
  stack_good_handler_labels prog'.
Proof.
  intros ac k prog bs prog' fs' bs' Hg Ew.
  unfold stack_good_handler_labels, restrict_nonzero. intros x Hx. set_unfold.
  destruct Hx as [(s0 & (y & -> & Hy) & Hx) Hnz]. apply In_set in Hy.
  apply in_map_iff in Hy as [y' [<- Hy]].
  destruct (cwts_label ac _ prog _ prog' _ x Hg Ew (ex_intro _ y' (conj Hy Hx)))
    as [R|[R|[(m & -> & q0 & Hq0 & Hm)|(y1 & Hy1 & R)]]];
    try (subst x; cbn in Hnz; exfalso; apply Hnz; reflexivity);
    try (cbn in Hnz; exfalso; apply Hnz; reflexivity).
  left. exists (stack_get_handler_labels (FST y1) (SND y1)). split; [|exact R].
  apply In_set, in_map_iff. exists y1. split; [destruct y1; reflexivity|exact Hy1].
Qed.

End CodeLabels.

(** ** [no_install] and [no_shmemop] *)

Section NoInstall.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wMoveAux_no_install_lem" *)
Theorem wMoveAux_no_install_lem : forall xs kf, stackProps.no_install (@wMoveAux a xs kf).
Proof.
  intros xs [k [f f']]. induction xs as [|xy l IH]; [reflexivity|].
  destruct l as [|xy' l']; cbn [wMoveAux] in *;
    [destruct xy as [[x|x] [y|y]]; reflexivity|].
  cbn [stackProps.no_install]. unfold is_true in *. rewrite IH. destruct xy as [[x|x] [y|y]]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wStackLoad_no_install_lem" *)
Theorem wStackLoad_no_install_lem : forall l (prog : prog a),
  stackProps.no_install (wStackLoad l prog) = stackProps.no_install prog.
Proof. induction l as [|[r i] l IH]; intros prog; [reflexivity|]. exact (IH prog). Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite1_no_install_lem" *)
Theorem wRegWrite1_no_install_lem : forall (prog : N -> prog a) r kf,
  (forall reg, stackProps.no_install (prog reg)) ->
  stackProps.no_install (wRegWrite1 prog r kf).
Proof.
  intros prog r [k [f f']] H. unfold wRegWrite1. destruct (r DIV 2 <? k); [apply H|].
  cbn. rewrite andb_true_r. apply H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite2_no_install_lem" *)
Theorem wRegWrite2_no_install_lem : forall (prog : N -> prog a) r kf,
  (forall reg, stackProps.no_install (prog reg)) ->
  stackProps.no_install (wRegWrite2 prog r kf).
Proof.
  intros prog r [k [f f']] H. unfold wRegWrite2. destruct (r DIV 2 <? k); [apply H|].
  cbn. rewrite andb_true_r. apply H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_no_install_lem" *)
Theorem wLive_no_install_lem : forall live bs kf, stackProps.no_install (FST (@wLive a live bs kf)).
Proof. intros live bs [k [f f']]. unfold wLive. split_goal; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_no_install_lem" *)
Theorem stack_move_no_install_lem : forall n start offset i (p : prog a),
  stackProps.no_install (stack_move n start offset i p) = stackProps.no_install p.
Proof.
  intros n start offset i p. revert n start.
  apply (stack_move_ind (fun q => stackProps.no_install q = stackProps.no_install p)); [reflexivity|].
  intros q start Hq. cbn. rewrite Hq, andb_true_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_no_install" *)
Theorem copy_ret_aux_no_install : forall k f n, stackProps.no_install (@copy_ret_aux a k f n).
Proof.
  intros k f. apply (copy_ret_aux_ind (fun q => is_true (stackProps.no_install q))); [reflexivity|].
  intros n q Hq. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_no_install" *)
Theorem copy_ret_no_install : forall perf b kf vs (kont : prog a),
  stackProps.no_install (copy_ret perf b kf vs kont) = stackProps.no_install kont.
Proof.
  intros perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [stackProps.no_install]. rewrite copy_ret_aux_no_install.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

Lemma no_install_call_dest dest args kf : stackProps.no_install (FST (@call_dest a dest args kf)).
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?wStackLoad_no_install_lem; reflexivity.
Qed.

Ltac ni_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?kf = (?q, _),
    IH : forall bs kf, wordConvs.no_install ?p -> is_true (stackProps.no_install (FST (comp ?c ?pf ?p bs kf))) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (stackProps.no_install q))
        by (replace q with (FST (comp c pf p b kf)) by (rewrite E; reflexivity); apply IH;
            unfold wordConvs.no_install; tauto);
      clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- _ =>
      let H := fresh "Hq" in
      pose proof (wLive_no_install_lem l b kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- _ =>
      let H := fresh "Hq" in
      pose proof (no_install_call_dest d ar kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  end.

Lemma no_install_main c (p : wordLang.prog a) :
  forall bs kf, wordConvs.no_install p ->
  stackProps.no_install (FST (comp c false p bs kf)).
Proof.
  induction p using wordConvs.prog_nested_ind; intros bs0 [k [f f']] Hh; cbn [comp].
  all: unfold wordConvs.no_install in Hh; cbn [not_created_subprogs] in Hh.
  all: unfold wShareInst, wInst, wMove, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply wMoveAux_no_install_lem).
  all: try (match goal with IH : forall _ _, _ -> is_true (stackProps.no_install (FST (comp _ _ ?p _ _)))
              |- is_true (stackProps.no_install (FST (comp _ _ ?p _ _))) => apply IH end;
            unfold wordConvs.no_install; tauto).
  all: ni_ih.
  all: unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots;
       split_goal;
       cbn [stackProps.no_install wStackLoad app list_Seq];
       rewrite ?wStackLoad_no_install_lem, ?copy_ret_no_install, ?stack_move_no_install_lem;
       cbn [stackProps.no_install wStackLoad app list_Seq].
  all: to_prop; unfold is_true;
    repeat match goal with |- (_ && _) = true => apply andb_true_iff; split end.
  all: try reflexivity; try assumption.
  all: try (exfalso; match goal with H : _ <> _ |- _ => apply H; reflexivity end).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_no_install" *)
Theorem comp_no_install : forall ac perf (prog : wordLang.prog a) bs kf prog' bs',
  wordConvs.no_install prog /\
  comp ac perf prog bs kf = (prog', bs') /\ perf = false ->
  stackProps.no_install prog'.
Proof.
  intros ac perf prog bs kf prog' bs' (H & E & ->).
  pose proof (no_install_main ac prog bs kf H) as R. rewrite E in R. exact R.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_no_install" *)
Theorem compile_word_to_stack_no_install : forall ac perf k (prog : list (N * (N * wordLang.prog a))) bs prog' fs' bs',
  EVERY (fun '(n, (m, pp)) => ⌜wordConvs.no_install pp⌝) prog /\
  compile_word_to_stack ac perf k prog bs = (prog', (fs', bs')) /\
  perf = false ->
  EVERY (fun '(a0, p) => stackProps.no_install p) prog'.
Proof.
  intros ac perf k prog bs prog' fs' bs' (H & E & ->).
  apply EVERY_Forall_iff in H. apply EVERY_Forall_iff.
  pose proof (compile_word_to_stack_Forall (fun y => is_true (stackProps.no_install y))
    (fun pp => wordConvs.no_install pp) ac false k) as L.
  refine (Forall_impl _ _ (L _ prog bs prog' _ E _)).
  - intros [x y] Hy. exact Hy.
  - intros m pp b f f' Hp. cbn [stackProps.no_install]. apply (no_install_main ac pp b _ Hp).
  - eapply Forall_impl; [|exact H]. intros [n [m pp]] Hx. apply bool_decide_spec in Hx. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_to_stack_compile_no_install" *)
Theorem word_to_stack_compile_no_install : forall (prog : list (N * (N * wordLang.prog a))) ac bm c fs p,
  ALL_DISTINCT (MAP FST prog) /\
  wordProps.code.no_install_code (fromAList prog) /\
  word_to_stack.compile ac false prog = (bm, (c, (fs, p))) ->
  EVERY (fun '(n, x) => stackProps.no_install x) p.
Proof.
  intros prog ac bm c fs p (Hd & Hn & E).
  unfold word_to_stack.compile in E. cbv zeta in E.
  destruct (compile_word_to_stack _ _ _ _ _) as [q [fs1 bm1]] eqn:Ew. injection E as _ _ _ <-.
  cbn [EVERY]. apply andb_true_iff; split; [reflexivity|]. apply andb_true_iff; split; [reflexivity|].
  eapply compile_word_to_stack_no_install. split; [|split; [exact Ew|reflexivity]].
  apply EVERY_Forall_iff, Forall_forall. intros [n [m pp]] Hin. apply bool_decide_spec.
  apply (Hn n m). rewrite lookup_fromAList. apply ALOOKUP_ALL_DISTINCT_MEM. split; [exact Hd|].
  apply MEM_In. exact Hin.
Qed.

End NoInstall.

Section NoShmemop.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wMoveAux_no_shmemop_lem" *)
Theorem wMoveAux_no_shmemop_lem : forall xs kf, no_shmemop (@wMoveAux a xs kf).
Proof.
  intros xs [k [f f']]. induction xs as [|xy l IH]; [reflexivity|].
  destruct l as [|xy' l']; cbn [wMoveAux] in *;
    [destruct xy as [[x|x] [y|y]]; reflexivity|].
  cbn [no_shmemop]. unfold is_true in *. rewrite IH. destruct xy as [[x|x] [y|y]]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wStackLoad_no_shmemop_lem" *)
Theorem wStackLoad_no_shmemop_lem : forall l (prog : prog a),
  no_shmemop (wStackLoad l prog) = no_shmemop prog.
Proof. induction l as [|[r i] l IH]; intros prog; [reflexivity|]. exact (IH prog). Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite1_no_shmemop_lem" *)
Theorem wRegWrite1_no_shmemop_lem : forall (prog : N -> prog a) r kf,
  (forall reg, no_shmemop (prog reg)) ->
  no_shmemop (wRegWrite1 prog r kf).
Proof.
  intros prog r [k [f f']] H. unfold wRegWrite1. destruct (r DIV 2 <? k); [apply H|].
  cbn. rewrite andb_true_r. apply H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite2_no_shmemop_lem" *)
Theorem wRegWrite2_no_shmemop_lem : forall (prog : N -> prog a) r kf,
  (forall reg, no_shmemop (prog reg)) ->
  no_shmemop (wRegWrite2 prog r kf).
Proof.
  intros prog r [k [f f']] H. unfold wRegWrite2. destruct (r DIV 2 <? k); [apply H|].
  cbn. rewrite andb_true_r. apply H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_no_shmemop_lem" *)
Theorem wLive_no_shmemop_lem : forall live bs kf, no_shmemop (FST (@wLive a live bs kf)).
Proof. intros live bs [k [f f']]. unfold wLive. split_goal; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_no_shmemop_lem" *)
Theorem stack_move_no_shmemop_lem : forall n start offset i (p : prog a),
  no_shmemop (stack_move n start offset i p) = no_shmemop p.
Proof.
  intros n start offset i p. revert n start.
  apply (stack_move_ind (fun q => no_shmemop q = no_shmemop p)); [reflexivity|].
  intros q start Hq. cbn. rewrite Hq, andb_true_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_aux_no_shmemop" *)
Theorem copy_ret_aux_no_shmemop : forall k f n, no_shmemop (@copy_ret_aux a k f n).
Proof.
  intros k f. apply (copy_ret_aux_ind (fun q => is_true (no_shmemop q))); [reflexivity|].
  intros n q Hq. exact Hq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_no_shmemop" *)
Theorem copy_ret_no_shmemop : forall perf b kf vs (kont : prog a),
  no_shmemop (copy_ret perf b kf vs kont) = no_shmemop kont.
Proof.
  intros perf b [k [f f']] vs kont. unfold copy_ret, SeqStackFree.
  destruct (num_stack_ret k vs =? 0); [reflexivity|].
  cbn [no_shmemop]. rewrite copy_ret_aux_no_shmemop.
  destruct (num_stack_ret k vs =? 0); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "perf_call_prefix_no_shmemop" *)
Theorem perf_call_prefix_no_shmemop : forall l1 l2 kf0, no_shmemop (@perf_call_prefix a l1 l2 kf0).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "perf_call_suffix_no_shmemop" *)
Theorem perf_call_suffix_no_shmemop : no_shmemop (@perf_call_suffix a).
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PushHandler_no_shmemop" *)
Theorem PushHandler_no_shmemop : forall perf l1 l2 kff, no_shmemop (@PushHandler a perf l1 l2 kff).
Proof. intros perf l1 l2 [k [f f']]; destruct perf; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PopHandler_no_shmemop" *)
Theorem PopHandler_no_shmemop : forall perf kff (prog : prog a),
  no_shmemop (PopHandler perf kff prog) = no_shmemop prog.
Proof. intros perf [k [f f']] prog; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "StackHandlerArgs_no_shmemop" *)
Theorem StackHandlerArgs_no_shmemop : forall perf dest arg_count kff,
  no_shmemop (@StackHandlerArgs a perf dest arg_count kff).
Proof.
  intros perf dest arg_count [k [f f']]. unfold StackHandlerArgs, StackArgs.
  rewrite stack_move_no_shmemop_lem. reflexivity.
Qed.

Lemma no_shmemop_call_dest dest args kf : no_shmemop (FST (@call_dest a dest args kf)).
Proof.
  destruct kf as [k [f f']]. unfold call_dest, wReg2. split_goal; cbn [FST fst];
    rewrite ?wStackLoad_no_shmemop_lem; reflexivity.
Qed.

Ltac ns_ih :=
  repeat match goal with
  | E : comp ?c ?pf ?p ?b ?kf = (?q, _),
    IH : forall bs kf, no_share_inst ?p -> is_true (no_shmemop (FST (comp ?c ?pf ?p bs kf))) |- _ =>
      let H := fresh "Hq" in
      assert (H : is_true (no_shmemop q))
        by (replace q with (FST (comp c pf p b kf)) by (rewrite E; reflexivity); apply IH;
            unfold no_share_inst; tauto);
      clear E
  | E : wLive ?l ?b ?kf = (?q, _) |- _ =>
      let H := fresh "Hq" in
      pose proof (wLive_no_shmemop_lem l b kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  | E : call_dest ?d ?ar ?kf = (?q, ?d') |- _ =>
      let H := fresh "Hq" in
      pose proof (no_shmemop_call_dest d ar kf) as H; rewrite E in H; cbn [FST fst] in H; clear E
  end.

Lemma no_shmemop_main c perf (p : wordLang.prog a) :
  forall bs kf, no_share_inst p ->
  no_shmemop (FST (comp c perf p bs kf)).
Proof.
  induction p using wordConvs.prog_nested_ind; intros bs0 [k [f f']] Hh; cbn [comp].
  all: unfold no_share_inst in Hh; cbn [not_created_subprogs] in Hh.
  all: unfold wShareInst, wInst, wMove, wRegWrite1, wRegWrite2, wReg1, wReg2;
    split_goal; cbn beta iota in *; cbn [FST fst] in *.
  all: try (apply wMoveAux_no_shmemop_lem).
  all: try (match goal with IH : forall _ _, _ -> is_true (no_shmemop (FST (comp _ _ ?p _ _)))
              |- is_true (no_shmemop (FST (comp _ _ ?p _ _))) => apply IH end;
            unfold no_share_inst; tauto).
  all: try (exfalso; match goal with H : _ <> _ |- _ => apply H; reflexivity end).
  all: ns_ih.
  all: unfold SeqStackFree, StackHandlerArgs, StackArgs, PushHandler, PopHandler, handler_slots,
         perf_call_prefix, perf_call_suffix;
       split_goal;
       cbn [no_shmemop wStackLoad app list_Seq];
       rewrite ?wStackLoad_no_shmemop_lem, ?copy_ret_no_shmemop, ?stack_move_no_shmemop_lem;
       cbn [no_shmemop wStackLoad app list_Seq].
  all: to_prop; unfold is_true;
    repeat match goal with |- (_ && _) = true => apply andb_true_iff; split end.
  all: try reflexivity; try assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_no_shmemop" *)
Theorem comp_no_shmemop : forall ac perf (prog : wordLang.prog a) bs kf prog' bs',
  no_share_inst prog /\
  comp ac perf prog bs kf = (prog', bs') ->
  no_shmemop prog'.
Proof.
  intros ac perf prog bs kf prog' bs' (H & E).
  pose proof (no_shmemop_main ac perf prog bs kf H) as R. rewrite E in R. exact R.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_word_to_stack_no_share_inst" *)
Theorem compile_word_to_stack_no_share_inst : forall ac perf k (prog : list (N * (N * wordLang.prog a))) bs prog' fs' bs',
  EVERY (fun '(n, (m, pp)) => ⌜no_share_inst pp⌝) prog /\
  compile_word_to_stack ac perf k prog bs = (prog', (fs', bs')) ->
  EVERY (fun '(a0, p) => no_shmemop p) prog'.
Proof.
  intros ac perf k prog bs prog' fs' bs' (H & E).
  apply EVERY_Forall_iff in H. apply EVERY_Forall_iff.
  pose proof (compile_word_to_stack_Forall (fun y => is_true (no_shmemop y))
    (fun pp => no_share_inst pp) ac perf k) as L.
  refine (Forall_impl _ _ (L _ prog bs prog' _ E _)).
  - intros [x y] Hy. exact Hy.
  - intros m pp b f f' Hp. cbn [no_shmemop]. apply (no_shmemop_main ac perf pp b _ Hp).
  - eapply Forall_impl; [|exact H]. intros [n [m pp]] Hx. apply bool_decide_spec in Hx. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_no_shmemop" *)
Theorem compile_no_shmemop : forall cf (prog : list (N * (N * wordLang.prog a))) bs fs ns prog',
  word_to_stack.compile cf false prog = (bs, (fs, (ns, prog'))) /\
  EVERY (fun '(n, (m, pp)) => ⌜no_share_inst pp⌝) prog ->
  EVERY (fun '(a0, p) => no_shmemop p) prog'.
Proof.
  intros cf prog bs fs ns prog' (E & H).
  unfold word_to_stack.compile in E. cbv zeta in E.
  destruct (compile_word_to_stack _ _ _ _ _) as [q [fs1 bm1]] eqn:Ew. injection E as _ _ _ <-.
  cbn [EVERY]. apply andb_true_iff; split; [reflexivity|]. apply andb_true_iff; split; [reflexivity|].
  eapply compile_word_to_stack_no_share_inst. split; [exact H|exact Ew].
Qed.

End NoShmemop.
