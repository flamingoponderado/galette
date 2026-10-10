(** * CakeML [word_cseProof]: correctness of [word_cse]

    Port of [cakeml/compiler/backend/proofs/word_cseProofScript.sml].

    Notes:
    - Galette has no theory of HOL's [balanced_map] invariant ([invariant],
      [to_fmap], [key_set]; nor [toto]'s [TotOrd] or [comparison]'s
      [good_cmp]).  The knowledge invariant is therefore stated over the
      entries of the instruction and load maps (Galette-only [bm_mem]: the
      pair occurs in the map's in-order entry list) instead of over
      [balanced_map$lookup] results, and [wf_data] drops its two
      [invariant listCmp] conjuncts.  Every [balanced_map$lookup] result is
      an entry ([bm_lookup_mem]), and [insert] and [bm_inter_eq] only keep
      entries or add the inserted one, so no balance or ordering invariant
      is needed.  Consequently these HOL theorems, stated with that theory,
      are not ported: [TotOrd_listCmp], [good_cmp_listCmp],
      [invariant_listCmp_empty], [bm_inter_eq_acc_thm],
      [invariant_bm_inter_eq], [lookup_bm_inter_eq], [lookup_insert_listCmp];
      the Galette-only [bm_mem_insert] and [bm_mem_inter_eq] replace them.
    - [wf_data] and [sem_inv] are records of HOL's conjuncts; HOL's
      [(:'a)] argument of [wf_data] is the explicit width [a].
    - HOL's [s with f := v] is [set_f v s]; [data with f := v] uses the
      Galette-only [with_*] updates; [ODD]/[EVEN] are HOL's.
    - Proofs of the instruction facts go through the Galette-only values
      [arith_val] and [load_val] (what a storable arith instruction or a load
      writes); the Galette-only lemmas and tactics have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.HOL.examples.data_structures.balanced_bst Require balanced_map.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require stackLang.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang word_cse.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock.
Open Scope N_scope.

(** ** Galette-only tactics *)

Lemma bd_true (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Lemma Some_eq_inv {A} (x y : A) : Some x = Some y -> x = y.
Proof. intros H; injection H; auto. Qed.

Ltac inv_eqs :=
  repeat match goal with
  | H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H; subst
  | H : Some _ = Some _ |- _ => apply Some_eq_inv in H; subst
  | H : Some _ = None |- _ => discriminate H
  | H : None = Some _ |- _ => discriminate H
  end.

Ltac case_split :=
  match goal with
  | H : context [match ?e with _ => _ end] |- _ =>
      let E := fresh "E" in destruct e eqn:E; try rewrite E in *
  | |- context [match ?e with _ => _ end] =>
      let E := fresh "E" in destruct e eqn:E; try rewrite E in *
  end.

Ltac bsplit :=
  unfold is_true in *;
  repeat match goal with
  | H : andb _ _ = true |- _ => apply andb_prop in H; destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- andb _ _ = true => apply andb_true_intro; split
  | |- _ /\ _ => split
  end.

Ltac in_simp :=
  repeat match goal with
  | H : In _ (_ ++ _) |- _ => apply in_app_or in H
  | H : In _ (_ :: _) |- _ => destruct H as [H|H]
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : In _ [] |- _ => destruct H
  end.

(** ** Balanced maps: entries *)

Section BM.
Context {K V : Type}.

(** Galette-only: the in-order entries of a balanced map. *)
Fixpoint bm_elems (t : balanced_map.balanced_map K V) : list (K * V) :=
  match t with
  | balanced_map.Tip => []
  | balanced_map.Bin _ k v l r => bm_elems l ++ (k, v) :: bm_elems r
  end.

Definition bm_mem (k : K) (v : V) (t : balanced_map.balanced_map K V) : Prop :=
  In (k, v) (bm_elems t).

Lemma bm_mem_empty k v : ~ bm_mem k v balanced_map.empty.
Proof. intros []. Qed.

Lemma bm_elems_balanceL k x (l r : balanced_map.balanced_map K V) e :
  In e (bm_elems (balanced_map.balanceL k x l r)) ->
  e = (k, x) \/ In e (bm_elems l) \/ In e (bm_elems r).
Proof.
  unfold balanced_map.balanceL; intros H; repeat case_split; inv_eqs;
    cbn [bm_elems] in *; in_simp; subst; repeat (rewrite in_app_iff; cbn [In]); tauto.
Qed.

Lemma bm_elems_balanceR k x (l r : balanced_map.balanced_map K V) e :
  In e (bm_elems (balanced_map.balanceR k x l r)) ->
  e = (k, x) \/ In e (bm_elems l) \/ In e (bm_elems r).
Proof.
  unfold balanced_map.balanceR; intros H; repeat case_split; inv_eqs;
    cbn [bm_elems] in *; in_simp; subst; repeat (rewrite in_app_iff; cbn [In]); tauto.
Qed.

Lemma bm_elems_insert cmp k x (t : balanced_map.balanced_map K V) e :
  In e (bm_elems (balanced_map.insert cmp k x t)) -> e = (k, x) \/ In e (bm_elems t).
Proof.
  induction t as [|s k' v' l IHl r IHr]; cbn [balanced_map.insert].
  - unfold balanced_map.singleton; cbn; intuition.
  - cbn [bm_elems]; rewrite in_app_iff; cbn [In]. destruct (cmp k k').
    + intros H; apply bm_elems_balanceL in H as [->|[H|H]]; auto.
      apply IHl in H as [->|H]; auto.
    + cbn [bm_elems]; rewrite in_app_iff; cbn [In]; intuition.
    + intros H; apply bm_elems_balanceR in H as [->|[H|H]]; auto.
      apply IHr in H as [->|H]; auto.
Qed.

End BM.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "listCmpEq_correct" *)
Theorem listCmpEq_correct : forall L1 L2, listCmp L1 L2 = EQUAL <-> L1 = L2.
Proof.
  induction L1 as [|h t IH]; intros [|h' t']; cbn; try (split; congruence).
  destruct (h =? h') eqn:E; [apply N.eqb_eq in E; subst; rewrite IH; split; congruence|].
  apply N.eqb_neq in E. destruct (h' <? h); split; congruence.
Qed.

Lemma bm_lookup_mem {V} k (v : V) t :
  balanced_map.lookup listCmp k t = Some v -> bm_mem k v t.
Proof.
  unfold bm_mem; induction t as [|s k' v' l IHl r IHr]; cbn; [discriminate|].
  rewrite in_app_iff; cbn [In]. destruct (listCmp k k') eqn:E; intros H.
  - left; auto.
  - apply listCmpEq_correct in E; subst; inv_eqs; right; left; reflexivity.
  - right; right; auto.
Qed.

(** Galette-only replacement of [lookup_insert_listCmp]. *)
Lemma bm_mem_insert {V} k (v : V) i x m :
  bm_mem k v (balanced_map.insert listCmp i x m) -> (k = i /\ v = x) \/ bm_mem k v m.
Proof.
  unfold bm_mem; intros H; apply bm_elems_insert in H as [H|H]; [left|right; exact H].
  injection H; auto.
Qed.

Lemma bm_mem_inter_eq_acc {V} `{EqDecision V} (m2 m1 acc : balanced_map.balanced_map (list N) V) k v :
  bm_mem k v (bm_inter_eq_acc m2 m1 acc) ->
  bm_mem k v acc \/ (bm_mem k v m1 /\ bm_mem k v m2).
Proof.
  revert acc; induction m1 as [|s k' v' l IHl r IHr]; intros acc Hm; cbn [bm_inter_eq_acc] in Hm;
    [left; exact Hm|].
  unfold bm_mem in *; cbn [bm_elems]; rewrite in_app_iff; cbn [In].
  apply IHl in Hm as [Hm|[H1 H2]]; [|right; auto].
  apply IHr in Hm as [Hm|[H1 H2]]; [|right; auto].
  destruct (bool_decide _) eqn:B; [|left; exact Hm].
  apply bool_decide_spec, bm_lookup_mem in B.
  apply bm_elems_insert in Hm as [Hm|Hm]; [|left; exact Hm].
  injection Hm as -> ->; right; auto.
Qed.

(** Galette-only replacement of [lookup_bm_inter_eq]. *)
Lemma bm_mem_inter_eq {V} `{EqDecision V} (m1 m2 : balanced_map.balanced_map (list N) V) k v :
  bm_mem k v (bm_inter_eq m1 m2) -> bm_mem k v m1 /\ bm_mem k v m2.
Proof.
  unfold bm_inter_eq; intros Hm; apply bm_mem_inter_eq_acc in Hm as [Hm|Hm]; [destruct Hm|exact Hm].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "antisym_listCmp" *)
Theorem antisym_listCmp : forall x y, listCmp x y = GREATER <-> listCmp y x = LESS.
Proof.
  induction x as [|h t IH]; intros [|h' t']; cbn; try (split; congruence).
  rewrite (N.eqb_sym h' h). destruct (h =? h') eqn:E; [apply IH|].
  apply N.eqb_neq in E.
  destruct (h' <? h) eqn:L1, (h <? h') eqn:L2; rewrite ?N.ltb_lt, ?N.ltb_ge in *;
    split; intros; try congruence; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "transit_listCmp" *)
Theorem transit_listCmp : forall x y z,
  listCmp x y = LESS /\ listCmp y z = LESS -> listCmp x z = LESS.
Proof.
  induction x as [|h t IH]; intros [|h' t'] [|h'' t''] [H1 H2]; cbn in *; try congruence.
  destruct (h =? h') eqn:E1.
  - apply N.eqb_eq in E1; subst h'.
    destruct (h =? h'') eqn:E2; eauto.
  - destruct (h' <? h) eqn:L1; [discriminate|].
    destruct (h' =? h'') eqn:E2.
    + apply N.eqb_eq in E2; subst h''. rewrite E1, L1. reflexivity.
    + destruct (h'' <? h') eqn:L2; [discriminate|].
      apply N.eqb_neq in E1, E2. rewrite N.ltb_ge in *.
      destruct (h =? h'') eqn:E; [apply N.eqb_eq in E; subst; lia|].
      destruct (h'' <? h) eqn:L3; [rewrite N.ltb_lt in L3; lia|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_listCmp_empty" *)
Theorem lookup_listCmp_empty : forall {V} k,
  balanced_map.lookup listCmp k (balanced_map.empty : balanced_map.balanced_map (list N) V) = None.
Proof. reflexivity. Qed.

(** ** The invariant *)

(** Galette-only: HOL's [data with f := v]. *)
Definition with_to_canonical (tc : num_map N) (d : knowledge) : knowledge :=
  {| to_canonical := tc; to_latest := to_latest d; gets_mem := gets_mem d;
     instrs_mem := instrs_mem d; loads_mem := loads_mem d |}.
Definition with_to_latest (tl : num_map N) (d : knowledge) : knowledge :=
  {| to_canonical := to_canonical d; to_latest := tl; gets_mem := gets_mem d;
     instrs_mem := instrs_mem d; loads_mem := loads_mem d |}.
Definition with_gets_mem (g : list (stackLang.store_name * N)) (d : knowledge) : knowledge :=
  {| to_canonical := to_canonical d; to_latest := to_latest d; gets_mem := g;
     instrs_mem := instrs_mem d; loads_mem := loads_mem d |}.
Definition with_instrs_mem (m : balanced_map.balanced_map (list N) N) (d : knowledge) : knowledge :=
  {| to_canonical := to_canonical d; to_latest := to_latest d; gets_mem := gets_mem d;
     instrs_mem := m; loads_mem := loads_mem d |}.
Definition with_loads_mem (m : balanced_map.balanced_map (list N) N) (d : knowledge) : knowledge :=
  {| to_canonical := to_canonical d; to_latest := to_latest d; gets_mem := gets_mem d;
     instrs_mem := instrs_mem d; loads_mem := m |}.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "in_names_set_def" *)
Definition in_names_set {a} (x : arith a) (tc : num_map N) : bool :=
  EVERY (fun r => bool_decide (lookup r tc = Some r)) (arithReads x).

Lemma in_names_set_iff {a} (x : arith a) tc :
  in_names_set x tc <-> forall r, In r (arithReads x) -> lookup r tc = Some r.
Proof.
  unfold in_names_set, is_true; rewrite EVERY_Forall, Forall_forall.
  split; intros H r Hr; specialize (H r Hr); [apply bool_decide_spec in H|apply bool_decide_spec];
    exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_def" *)
Record wf_data (a : N) (data : knowledge) : Prop := {
  wf_tc : forall r v, lookup r (to_canonical data) = Some v ->
    lookup v (to_canonical data) = Some v /\ is_true (ODD r) /\ is_true (ODD v);
  wf_tl : forall r v, lookup r (to_latest data) = Some v ->
    r IN domain (to_canonical data) /\ v IN domain (to_canonical data);
  wf_instrs : forall k v, bm_mem k v (instrs_mem data) -> lookup v (to_canonical data) = Some v;
  wf_arith : forall (x : arith a) v, bm_mem (instToNumList (Arith x)) v (instrs_mem data) ->
    in_names_set x (to_canonical data) /\ is_true (can_mem_arith x);
  wf_och : forall op src v, bm_mem (OpCurrHeapToNumList op src) v (instrs_mem data) ->
    lookup src (to_canonical data) = Some src;
  wf_gets : forall x v, ALOOKUP (gets_mem data) x = Some v -> lookup v (to_canonical data) = Some v;
  wf_gets_distinct : is_true (ALL_DISTINCT (MAP FST (gets_mem data)));
  wf_loads : forall k v, bm_mem k v (loads_mem data) -> lookup v (to_canonical data) = Some v;
  wf_loads_addr : forall op a0 (ofs : word a) v,
    bm_mem (loadToNumList op a0 ofs) v (loads_mem data) -> lookup a0 (to_canonical data) = Some a0
}.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "sem_inv_def" *)
Record sem_inv {a c ffi_t} (data : knowledge) (s : state a c ffi_t) : Prop := {
  si_tc : forall r v, lookup r (to_canonical data) = Some v -> get_var r s = get_var v s;
  si_tl : forall r v, lookup r (to_latest data) = Some v -> get_var r s = get_var v s;
  si_const : forall n (w : word a) v, bm_mem (instToNumList (asm.Const n w)) v (instrs_mem data) ->
    lookup v (locals s) = Some (Word w);
  si_arith : forall (x : arith a) v, bm_mem (instToNumList (Arith x)) v (instrs_mem data) ->
    exists w, get_var v s = Some w /\
      evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s);
  si_och : forall op src v, bm_mem (OpCurrHeapToNumList op src) v (instrs_mem data) ->
    exists w, word_exp s (Op op [Var src; Lookup stackLang.CurrHeap]) = Some w /\
      get_var v s = Some w;
  si_loc : forall l v, bm_mem [48; l] v (instrs_mem data) -> lookup v (locals s) = Some (Loc l 0);
  si_gets : forall x v, ALOOKUP (gets_mem data) x = Some v ->
    exists w, FLOOKUP (store s) x = Some w /\ get_var v s = Some w;
  si_loads : forall op a0 (ofs : word a) v,
    ~ is_store op -> bm_mem (loadToNumList op a0 ofs) v (loads_mem data) ->
    exists w, get_var v s = Some w /\
      forall r, evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s)
}.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_def" *)
Definition data_inv {a c ffi_t} (data : knowledge) (s : state a c ffi_t) : Prop :=
  wf_data a data /\ sem_inv data s.

(** ** Instruction values (Galette-only) *)

Section Vals.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types s : state.

Definition ri_exp (ri : reg_imm a) : exp a :=
  match ri with Reg r3 => Var r3 | Imm w => Const w end.

(** What a storable arith instruction writes to its destination. *)
Definition arith_val (x : arith a) s : option (word_loc a) :=
  match x with
  | Binop op _ r2 ri => word_exp s (Op op [Var r2; ri_exp ri])
  | asm.Shift sh _ r2 ri => word_exp s (Shift sh (Var r2) (ri_exp ri))
  | Div _ r2 r3 =>
      match get_vars [r3; r2] s with
      | SOME [Word q; Word w2] =>
          if negb (bool_decide (q = n2w 0)) then Some (Word (word_quot w2 q)) else None
      | _ => None
      end
  | _ => None
  end.

(** What a load writes to its destination. *)
Definition load_val (op : memop) (a0 : N) (ofs : word a) s : option (word_loc a) :=
  match op with
  | asm.Load =>
      match word_exp s (Op asm.Add [Var a0; Const ofs]) with
      | SOME (Word w) => mem_load w s
      | _ => None
      end
  | Load8 =>
      match word_exp s (Op asm.Add [Var a0; Const ofs]) with
      | SOME (Word w) =>
          match mem_load_byte_aux (memory s) (mdomain s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (Word (w2w w))
          end
      | _ => None
      end
  | Load32 =>
      match word_exp s (Op asm.Add [Var a0; Const ofs]) with
      | SOME (Word w) =>
          match mem_load_32 (memory s) (mdomain s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (Word (w2w w))
          end
      | _ => None
      end
  | _ => None
  end.

Lemma evaluate_Inst_eq (i : asm.inst a) s :
  evaluate (Inst i, s) = match inst i s with Some s1 => (None, s1) | None => (Some Error, s) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma set_var_inj r (w1 w2 : word_loc a) s : set_var r w1 s = set_var r w2 s -> w1 = w2.
Proof.
  intros H; apply (f_equal (fun t => lookup r (locals t))) in H; unfold set_var in H;
    cbn [locals set_locals] in H; rewrite !lookup_insert in H.
  destruct (decide (r = r)); [injection H; auto|congruence].
Qed.

Lemma inst_arith_val (x : arith a) s :
  can_mem_arith x ->
  inst (Arith x) s = option_map (fun w => set_var (firstRegOfArith x) w s) (arith_val x s).
Proof.
  intros H; destruct x; cbn [can_mem_arith] in H; try discriminate H;
    cbn [inst arith_val firstRegOfArith]; unfold assign.
  - destruct r; cbn [ri_exp]; destruct (word_exp _ _); reflexivity.
  - destruct r; cbn [ri_exp]; destruct (word_exp _ _); reflexivity.
  - cbn zeta. repeat case_split; reflexivity.
Qed.

Lemma eval_arith_iff (x : arith a) w s :
  can_mem_arith x ->
  (evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s) <->
   arith_val x s = Some w).
Proof.
  intros H; rewrite evaluate_Inst_eq, (inst_arith_val x s H).
  destruct (arith_val x s) as [w'|]; cbn [option_map]; split; intros E; inv_eqs;
    try discriminate; try reflexivity.
  - f_equal; eapply set_var_inj; eauto.
Qed.

Lemma arith_val_agree (x : arith a) (s1 s2 : state) :
  can_mem_arith x ->
  (forall r, In r (arithReads x) -> lookup r (locals s1) = lookup r (locals s2)) ->
  arith_val x s1 = arith_val x s2.
Proof.
  intros H Hr; destruct x; cbn [can_mem_arith] in H; try discriminate H;
    cbn [arith_val arithReads] in *.
  - destruct r; cbn [ri_exp word_exp MAP List.map]; unfold get_var;
      rewrite ?(Hr n0), ?(Hr n1) by (cbn; auto); reflexivity.
  - destruct r; cbn [ri_exp word_exp MAP List.map]; unfold get_var;
      rewrite ?(Hr n0), ?(Hr n1) by (cbn; auto); reflexivity.
  - cbn [get_vars]; unfold get_var; rewrite (Hr n0), (Hr n1) by (cbn; auto); reflexivity.
Qed.

Lemma inst_load_val op r a0 ofs s :
  ~ is_store op ->
  inst (Mem op r (Addr a0 ofs)) s = option_map (fun w => set_var r w s) (load_val op a0 ofs s).
Proof.
  intros H; destruct op; cbn [is_store] in H; try (exfalso; apply H; reflexivity);
    cbn [inst load_val]; repeat case_split; reflexivity.
Qed.

Lemma eval_load_iff op r a0 ofs w s :
  ~ is_store op ->
  (evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s) <->
   load_val op a0 ofs s = Some w).
Proof.
  intros H; rewrite evaluate_Inst_eq, (inst_load_val op r a0 ofs s H).
  destruct (load_val op a0 ofs s) as [w'|]; cbn [option_map]; split; intros E; inv_eqs;
    try discriminate; try reflexivity.
  - f_equal; eapply set_var_inj; eauto.
Qed.

Lemma load_val_agree op a0 ofs (s1 s2 : state) :
  lookup a0 (locals s1) = lookup a0 (locals s2) ->
  memory s1 = memory s2 -> mdomain s1 = mdomain s2 -> be s1 = be s2 ->
  load_val op a0 ofs s1 = load_val op a0 ofs s2.
Proof.
  intros Ha Hm Hd Hb; destruct op; cbn [load_val word_exp MAP List.map]; unfold get_var;
    rewrite ?Ha; try reflexivity; unfold mem_load; rewrite ?Hm, ?Hd, ?Hb; reflexivity.
Qed.

End Vals.

(** ** Basic facts *)

Section Basic.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types s : state.

Lemma lookup_any_cases (x : N) (t : num_map N) :
  (lookup x t = None /\ lookup_any x t x = x) \/
  (exists v, lookup x t = Some v /\ lookup_any x t x = v).
Proof. unfold lookup_any; destruct (lookup x t); eauto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_correct" *)
Theorem canonicalRegs_correct : forall data r s,
  data_inv data s -> get_var (canonicalRegs data r) s = get_var r s.
Proof.
  intros data r s [_ S]; unfold canonicalRegs.
  destruct (lookup_any_cases r (to_canonical data)) as [[_ ->]|[v [Hv ->]]]; [reflexivity|].
  symmetry; apply (si_tc _ _ S _ _ Hv).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs'_correct" *)
Theorem canonicalRegs'_correct : forall a0 data r s,
  data_inv data s -> get_var (canonicalRegs' a0 data r) s = get_var r s.
Proof.
  intros a0 data r s H; unfold canonicalRegs'; cbn zeta.
  destruct (canonicalRegs data r =? a0); [reflexivity|apply canonicalRegs_correct, H].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_correct_bis" *)
Theorem canonicalRegs_correct_bis : forall data r s,
  data_inv data s -> lookup (canonicalRegs data r) (locals s) = lookup r (locals s).
Proof. intros; apply canonicalRegs_correct; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalArith_correct" *)
Theorem canonicalArith_correct : forall data s (x : arith a),
  data_inv data s -> inst (Arith (canonicalArith data x)) s = inst (Arith x) s.
Proof.
  intros data s x H.
  assert (G : forall r, get_var (canonicalRegs data r) s = get_var r s)
    by (intros; apply canonicalRegs_correct, H).
  assert (G' : forall a0 r, get_var (canonicalRegs' a0 data r) s = get_var r s)
    by (intros; apply canonicalRegs'_correct, H).
  destruct x; cbn [canonicalArith inst]; unfold assign; cbn [get_vars word_exp MAP List.map];
    rewrite ?G, ?G'; try reflexivity.
  all: destruct r; cbn [canonicalImmReg' word_exp MAP List.map]; rewrite ?G, ?G'; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wordToNum_unique" *)
Theorem wordToNum_unique : forall (c1 c2 : word a), wordToNum c1 = wordToNum c2 <-> c1 = c2.
Proof.
  intros c1 c2; unfold wordToNum; split; [|intros ->; reflexivity].
  intros H; rewrite <- (n2w_w2n c1), <- (n2w_w2n c2), H; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "arithOpToNum_eq" *)
Theorem arithOpToNum_eq : forall op1 op2, arithOpToNum op1 = arithOpToNum op2 <-> op1 = op2.
Proof. intros [] []; cbn; split; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "memOpToNum_eq" *)
Theorem memOpToNum_eq : forall op1 op2, memOpToNum op1 = memOpToNum op2 <-> op1 = op2.
Proof. intros [] []; cbn; split; congruence. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "firstRegOfArith_canonicalArith" *)
Theorem firstRegOfArith_canonicalArith : forall data (x : arith a),
  firstRegOfArith (canonicalArith data x) = firstRegOfArith x.
Proof. intros data []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_locals" *)
Theorem data_inv_locals : forall s, set_locals (locals s) s = s.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "insert_eq" *)
Theorem insert_eq : forall (n1 n2 : N) (v1 v2 : word_loc a) l,
  insert n1 v1 l = insert n1 v2 l <-> v1 = v2.
Proof.
  intros n1 n2 v1 v2 l; split; [|intros ->; reflexivity].
  intros H; apply (f_equal (lookup n1)) in H; rewrite !lookup_insert in H.
  destruct (decide (n1 = n1)); [injection H; auto|congruence].
Qed.

Lemma MEM_iff (x : N) l : ~ is_true (MEM x l) <-> ~ In x l.
Proof. unfold is_true; rewrite MEM_In; tauto. Qed.

Lemma set_var_set_memory r w m s : set_var r w (set_memory m s) = set_memory m (set_var r w s).
Proof. destruct s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_set_var" *)
Theorem evaluate_arith_set_var : forall (x : arith a) r u w s,
  can_mem_arith x /\ ~ MEM r (arithReads x) ->
  (evaluate (Inst (Arith x), set_var r u s) =
     (None, set_var (firstRegOfArith x) w (set_var r u s)) <->
   evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s)).
Proof.
  intros x r u w s [H1 H2]; rewrite !eval_arith_iff by exact H1.
  rewrite (arith_val_agree x (set_var r u s) s H1); [reflexivity|].
  intros r' Hr'; unfold set_var; cbn [locals set_locals]; rewrite lookup_insert.
  destruct (decide (r' = r)); [subst; apply MEM_iff in H2; contradiction|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_any_dest" *)
Theorem evaluate_load_any_dest : forall op r0 a0 ofs w s r,
  ~ is_store op /\ evaluate (Inst (Mem op r0 (Addr a0 ofs)), s) = (None, set_var r0 w s) ->
  evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s).
Proof.
  intros op r0 a0 ofs w s r [H1 H2]; rewrite eval_load_iff in * by exact H1; exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_set_var" *)
Theorem evaluate_load_set_var : forall op r a0 ofs n u w s,
  ~ is_store op /\ a0 <> n ->
  (evaluate (Inst (Mem op r (Addr a0 ofs)), set_var n u s) =
     (None, set_var r w (set_var n u s)) <->
   evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s)).
Proof.
  intros op r a0 ofs n u w s [H1 H2]; rewrite !eval_load_iff by exact H1.
  rewrite (load_val_agree op a0 ofs (set_var n u s) s); try reflexivity.
  unfold set_var; cbn [locals set_locals]; rewrite lookup_insert.
  destruct (decide (a0 = n)); [contradiction|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_change_addr" *)
Theorem evaluate_load_change_addr : forall op r a0 a' ofs w s,
  ~ is_store op /\ lookup a' (locals s) = lookup a0 (locals s) /\
  evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s) ->
  evaluate (Inst (Mem op r (Addr a' ofs)), s) = (None, set_var r w s).
Proof.
  intros op r a0 a' ofs w s (H1 & H2 & H3); rewrite eval_load_iff in * by exact H1.
  rewrite <- H3. destruct op; cbn [load_val word_exp MAP List.map]; unfold get_var;
    rewrite ?H2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_memory" *)
Theorem evaluate_arith_memory : forall (x : arith a) w s m,
  can_mem_arith x ->
  (evaluate (Inst (Arith x), set_memory m s) =
     (None, set_memory m (set_var (firstRegOfArith x) w s)) <->
   evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s)).
Proof.
  intros x w s m H; rewrite <- set_var_set_memory, !eval_arith_iff by exact H.
  rewrite (arith_val_agree x (set_memory m s) s H); [reflexivity|]. intros; reflexivity.
Qed.

End Basic.

(** ** Transport of the invariant *)

Section Transport.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types s : state.

Lemma in_dom {A} (t : num_map A) r v : lookup r t = Some v -> r IN domain t.
Proof. intros H; apply domain_lookup; eauto. Qed.

Lemma not_in_dom {A} (t : num_map A) r : lookup r t = None -> ~ r IN domain t.
Proof. intros H D; apply domain_lookup in D as [v Hv]; congruence. Qed.

(** Galette-only: [sem_inv] depends only on the tracked locals, the store
    entries it mentions and (when loads are recorded) the memory. *)
Lemma sem_inv_agree data (s1 s2 : state) :
  wf_data a data -> sem_inv data s1 ->
  (forall r, r IN domain (to_canonical data) -> lookup r (locals s2) = lookup r (locals s1)) ->
  FLOOKUP (store s2) stackLang.CurrHeap = FLOOKUP (store s1) stackLang.CurrHeap ->
  (forall x v, ALOOKUP (gets_mem data) x = Some v -> FLOOKUP (store s2) x = FLOOKUP (store s1) x) ->
  ((forall k v, ~ bm_mem k v (loads_mem data)) \/
   (memory s2 = memory s1 /\ mdomain s2 = mdomain s1 /\ be s2 = be s1)) ->
  sem_inv data s2.
Proof.
  intros W S Hl Hc Hg Hm.
  assert (Gv : forall r v, lookup r (to_canonical data) = Some v -> get_var r s2 = get_var r s1)
    by (intros r v Hr; unfold get_var; apply Hl; eapply in_dom; eauto).
  destruct S as [S1 S2 S3 S4 S5 S6 S7 S8]; constructor.
  - intros r v Hr. rewrite (Gv r v Hr), (Gv v v (proj1 (wf_tc _ _ W _ _ Hr))). eauto.
  - intros r v Hr. destruct (wf_tl _ _ W _ _ Hr) as [D1 D2].
    unfold get_var; rewrite (Hl r D1), (Hl v D2). apply S2, Hr.
  - intros n w v Hv. rewrite (Hl v); [eauto|]. eapply in_dom, (wf_instrs _ _ W _ _ Hv).
  - intros x v Hv. destruct (S4 x v Hv) as [w [Hw He]].
    pose proof (wf_arith _ _ W _ _ Hv) as [Hn Hcm]. exists w. split.
    + rewrite (Gv v v (wf_instrs _ _ W _ _ Hv)); exact Hw.
    + rewrite eval_arith_iff in * by exact Hcm. rewrite <- He. apply arith_val_agree; [exact Hcm|].
      intros r Hr. apply Hl. eapply in_dom, (proj1 (in_names_set_iff x _) Hn), Hr.
  - intros op src v Hv. destruct (S5 op src v Hv) as [w [Hw Hg']]. exists w. split.
    + rewrite <- Hw. cbn [word_exp MAP List.map]. unfold get_store.
      rewrite (Gv src src (wf_och _ _ W _ _ _ Hv)), Hc. reflexivity.
    + rewrite (Gv v v (wf_instrs _ _ W _ _ Hv)); exact Hg'.
  - intros l v Hv. rewrite (Hl v); [eauto|]. eapply in_dom, (wf_instrs _ _ W _ _ Hv).
  - intros x v Hv. destruct (S7 x v Hv) as [w [Hw Hg']]. exists w.
    rewrite (Hg x v Hv), (Gv v v (wf_gets _ _ W _ _ Hv)). auto.
  - intros op a0 ofs v Hs Hv. destruct (S8 op a0 ofs v Hs Hv) as [w [Hw He]]. exists w. split.
    + rewrite (Gv v v (wf_loads _ _ W _ _ Hv)); exact Hw.
    + intros r. specialize (He r). rewrite eval_load_iff in * by exact Hs. rewrite <- He.
      destruct Hm as [Hm|(H1 & H2 & H3)]; [exfalso; eapply Hm; eauto|].
      apply load_val_agree; auto. apply Hl. eapply in_dom, (wf_loads_addr _ _ W _ _ _ _ Hv).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_untracked" *)
Theorem wf_data_untracked : forall data n,
  wf_data a data /\ lookup n (to_canonical data) = None ->
  (forall r v, lookup r (to_canonical data) = Some v -> r <> n /\ v <> n) /\
  (forall r v, lookup r (to_latest data) = Some v -> r <> n /\ v <> n) /\
  (forall k v, bm_mem k v (instrs_mem data) -> v <> n) /\
  (forall (x : arith a) v, bm_mem (instToNumList (Arith x)) v (instrs_mem data) ->
     ~ MEM n (arithReads x) /\ can_mem_arith x) /\
  (forall op src v, bm_mem (OpCurrHeapToNumList op src) v (instrs_mem data) -> src <> n) /\
  (forall x v, ALOOKUP (gets_mem data) x = Some v -> v <> n) /\
  (forall k v, bm_mem k v (loads_mem data) -> v <> n) /\
  (forall op a0 (ofs : word a) v, bm_mem (loadToNumList op a0 ofs) v (loads_mem data) -> a0 <> n).
Proof.
  intros data n [W Hn].
  assert (D : forall r, r IN domain (to_canonical data) -> r <> n)
    by (intros r Hr ->; exact (not_in_dom _ _ Hn Hr)).
  repeat split; intros.
  - eapply D, in_dom; eauto.
  - eapply D, in_dom, (proj1 (wf_tc _ _ W _ _ H)).
  - apply D, (wf_tl _ _ W _ _ H).
  - apply D, (wf_tl _ _ W _ _ H).
  - eapply D, in_dom, (wf_instrs _ _ W _ _ H).
  - apply MEM_iff. intros Hr. destruct (wf_arith _ _ W _ _ H) as [Hs _].
    exact (D n (in_dom _ _ _ (proj1 (in_names_set_iff x _) Hs n Hr)) eq_refl).
  - apply (wf_arith _ _ W _ _ H).
  - eapply D, in_dom, (wf_och _ _ W _ _ _ H).
  - eapply D, in_dom, (wf_gets _ _ W _ _ H).
  - eapply D, in_dom, (wf_loads _ _ W _ _ H).
  - eapply D, in_dom, (wf_loads_addr _ _ W _ _ _ _ H).
Qed.

Lemma lookup_set_var_other r n u s : r <> n -> lookup r (locals (set_var n u s)) = lookup r (locals s).
Proof.
  intros H; unfold set_var; cbn [locals set_locals]; rewrite lookup_insert.
  destruct (decide (r = n)); [contradiction|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_var" *)
Theorem data_inv_set_var : forall data s n v,
  lookup n (to_canonical data) = None -> (data_inv data (set_var n v s) <-> data_inv data s).
Proof.
  intros data s n v Hn.
  assert (D : forall r, r IN domain (to_canonical data) -> r <> n)
    by (intros r Hr ->; exact (not_in_dom _ _ Hn Hr)).
  split; intros [W S]; split; auto; eapply sem_inv_agree; eauto; try reflexivity;
    try (intros; reflexivity); try (right; repeat split; reflexivity).
  - intros r Hr; symmetry; apply lookup_set_var_other, D, Hr.
  - intros r Hr; apply lookup_set_var_other, D, Hr.
Qed.

Lemma lookup_unset_var_other r n s : r <> n -> lookup r (locals (unset_var n s)) = lookup r (locals s).
Proof.
  intros H; unfold unset_var; cbn [locals set_locals]; rewrite lookup_delete.
  destruct (decide (r = n)); [contradiction|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_unset_var" *)
Theorem evaluate_arith_unset_var : forall (x : arith a) r w s,
  can_mem_arith x /\ ~ MEM r (arithReads x) ->
  (evaluate (Inst (Arith x), unset_var r s) =
     (None, set_var (firstRegOfArith x) w (unset_var r s)) <->
   evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s)).
Proof.
  intros x r w s [H1 H2]; rewrite !eval_arith_iff by exact H1.
  rewrite (arith_val_agree x (unset_var r s) s H1); [reflexivity|].
  intros r' Hr'; apply lookup_unset_var_other. intros ->. apply MEM_iff in H2; contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_unset_var" *)
Theorem evaluate_load_unset_var : forall op r a0 ofs n w s,
  ~ is_store op /\ a0 <> n ->
  (evaluate (Inst (Mem op r (Addr a0 ofs)), unset_var n s) =
     (None, set_var r w (unset_var n s)) <->
   evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s)).
Proof.
  intros op r a0 ofs n w s [H1 H2]; rewrite !eval_load_iff by exact H1.
  rewrite (load_val_agree op a0 ofs (unset_var n s) s); try reflexivity.
  apply lookup_unset_var_other, H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_unset_var" *)
Theorem data_inv_unset_var : forall data s n,
  lookup n (to_canonical data) = None -> (data_inv data (unset_var n s) <-> data_inv data s).
Proof.
  intros data s n Hn.
  assert (D : forall r, r IN domain (to_canonical data) -> r <> n)
    by (intros r Hr ->; exact (not_in_dom _ _ Hn Hr)).
  split; intros [W S]; split; auto; eapply sem_inv_agree; eauto; try reflexivity;
    try (intros; reflexivity); try (right; repeat split; reflexivity).
  - intros r Hr; symmetry; apply lookup_unset_var_other, D, Hr.
  - intros r Hr; apply lookup_unset_var_other, D, Hr.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "not_seen_data_inv_alist_insert" *)
Theorem not_seen_data_inv_alist_insert : forall data s l r v,
  lookup r (to_canonical data) = None ->
  data_inv data (set_locals l s) -> data_inv data (set_locals (insert r v l) s).
Proof.
  intros data s l r v Hr H.
  assert (E : set_locals (insert r v l) s = set_var r v (set_locals l s)) by (destruct s; reflexivity).
  rewrite E; apply data_inv_set_var; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_empty" *)
Theorem data_inv_empty : forall s, data_inv empty_data s.
Proof.
  intros s; split; constructor; cbn; intros;
    repeat match goal with H : False |- _ => destruct H | H : None = Some _ |- _ => discriminate H end;
    try reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_memory" *)
Theorem data_inv_memory : forall data s m,
  data_inv data s -> data_inv (with_loads_mem balanced_map.empty data) (set_memory m s).
Proof.
  intros data s m [W S].
  assert (W' : wf_data a (with_loads_mem balanced_map.empty data)).
  { destruct W; constructor; cbn [with_loads_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
      auto; intros * H; destruct H. }
  split; [exact W'|].
  apply (sem_inv_agree _ s); auto; try reflexivity; try (intros; reflexivity).
  all: try (left; intros k v H; destruct H; fail).
  destruct S; constructor; cbn [with_loads_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto. intros op a0 ofs v _ H; destruct H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_agree" *)
Theorem evaluate_arith_agree : forall (x : arith a) w (s1 s2 : state),
  evaluate (Inst (Arith x), s1) = (None, set_var (firstRegOfArith x) w s1) /\
  can_mem_arith x /\ locals s2 = locals s1 ->
  evaluate (Inst (Arith x), s2) = (None, set_var (firstRegOfArith x) w s2).
Proof.
  intros x w s1 s2 (H1 & H2 & H3); rewrite eval_arith_iff in * by exact H2.
  rewrite <- H1; apply arith_val_agree; auto. intros; rewrite H3; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_agree" *)
Theorem evaluate_load_agree : forall op r a0 ofs w (s1 s2 : state),
  evaluate (Inst (Mem op r (Addr a0 ofs)), s1) = (None, set_var r w s1) /\
  ~ is_store op /\ locals s2 = locals s1 /\ memory s2 = memory s1 /\
  mdomain s2 = mdomain s1 /\ be s2 = be s1 ->
  evaluate (Inst (Mem op r (Addr a0 ofs)), s2) = (None, set_var r w s2).
Proof.
  intros op r a0 ofs w s1 s2 (H1 & H2 & H3 & H4 & H5 & H6); rewrite eval_load_iff in * by exact H2.
  rewrite <- H1; apply load_val_agree; auto. rewrite H3; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_state_agree" *)
Theorem data_inv_state_agree : forall data (s1 s2 : state),
  data_inv data s1 /\ locals s2 = locals s1 /\ store s2 = store s1 /\ memory s2 = memory s1 /\
  mdomain s2 = mdomain s1 /\ be s2 = be s1 ->
  data_inv data s2.
Proof.
  intros data s1 s2 ([W S] & H1 & H2 & H3 & H4 & H5); split; [exact W|].
  eapply sem_inv_agree; eauto.
  all: first [intros; rewrite H1; reflexivity | rewrite H2; reflexivity
             | intros; rewrite H2; reflexivity | right; auto].
Qed.

End Transport.

(** ** If-join merge *)

Lemma inter_eq_some (m1 m2 : num_map N) k v :
  lookup k (inter_eq m1 m2) = Some v <-> lookup k m1 = Some v /\ lookup k m2 = Some v.
Proof.
  rewrite lookup_inter_eq. destruct (lookup k m1) as [x|]; [|split; [discriminate|intros [? _]; discriminate]].
  destruct (decide (lookup k m2 = Some x)) as [E|E]; split.
  - intros H; inv_eqs; auto.
  - intros [H1 H2]; inv_eqs; reflexivity.
  - intros H; discriminate.
  - intros [H1 H2]; inv_eqs; contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "ALL_DISTINCT_MAP_FST_FILTER" *)
Theorem ALL_DISTINCT_MAP_FST_FILTER : forall {A B} `{EqDecision A} (l : list (A * B)) P,
  ALL_DISTINCT (MAP FST l) -> ALL_DISTINCT (MAP FST (FILTER P l)).
Proof.
  intros A B EA l P; unfold is_true; rewrite !ALL_DISTINCT_NoDup_list.
  induction l as [|[x y] l IH]; cbn; [auto|]. intros Hd; inversion Hd; subst.
  destruct (P (x, y)); cbn; [|auto]. constructor; [|auto].
  intros Hin; apply H1. apply in_map_iff in Hin as [[x' y'] [Ex Hin]]; cbn in Ex; subst x'.
  apply filter_In in Hin as [Hin _]. apply in_map_iff; exists (x, y'); auto.
Qed.

Lemma ALOOKUP_gets_merge (g1 g2 : list (stackLang.store_name * N)) x v :
  is_true (ALL_DISTINCT (MAP FST g1)) ->
  ALOOKUP (FILTER (fun '(x, v) => bool_decide (ALOOKUP g2 x = Some v)) g1) x = Some v ->
  ALOOKUP g1 x = Some v /\ ALOOKUP g2 x = Some v.
Proof.
  intros Hd H. apply ALOOKUP_In, filter_In in H as [Hin Hp].
  apply bool_decide_spec in Hp. split; [|exact Hp].
  apply ALOOKUP_ALL_DISTINCT_MEM; split; [exact Hd|]. unfold is_true; rewrite MEM_In; exact Hin.
Qed.

Section Merge.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_merge" *)
Theorem wf_data_merge : forall d1 d2,
  wf_data a d1 /\ wf_data a d2 -> wf_data a (merge_data d1 d2).
Proof.
  intros d1 d2 [W1 W2]; unfold merge_data; constructor;
    cbn [to_canonical to_latest gets_mem instrs_mem loads_mem].
  - intros r v Hr. apply inter_eq_some in Hr as [H1 H2].
    destruct (wf_tc _ _ W1 _ _ H1) as (A1 & A2 & A3). destruct (wf_tc _ _ W2 _ _ H2) as (B1 & _).
    split; [apply inter_eq_some; auto|auto].
  - intros r v Hr; discriminate Hr.
  - intros k v Hk. apply bm_mem_inter_eq in Hk as [H1 H2].
    apply inter_eq_some; split; [eapply (wf_instrs _ _ W1)|eapply (wf_instrs _ _ W2)]; eauto.
  - intros x v Hk. apply bm_mem_inter_eq in Hk as [H1 H2].
    destruct (wf_arith _ _ W1 _ _ H1) as [N1 C1]. destruct (wf_arith _ _ W2 _ _ H2) as [N2 _].
    split; [|exact C1]. apply in_names_set_iff; intros r Hr. apply inter_eq_some; split;
      [apply (proj1 (in_names_set_iff _ _) N1)|apply (proj1 (in_names_set_iff _ _) N2)]; auto.
  - intros op src v Hk. apply bm_mem_inter_eq in Hk as [H1 H2].
    apply inter_eq_some; split; [eapply (wf_och _ _ W1)|eapply (wf_och _ _ W2)]; eauto.
  - intros x v Hx. apply ALOOKUP_gets_merge in Hx as [H1 H2]; [|apply (wf_gets_distinct _ _ W1)].
    apply inter_eq_some; split; [eapply (wf_gets _ _ W1)|eapply (wf_gets _ _ W2)]; eauto.
  - apply ALL_DISTINCT_MAP_FST_FILTER, (wf_gets_distinct _ _ W1).
  - intros k v Hk. apply bm_mem_inter_eq in Hk as [H1 H2].
    apply inter_eq_some; split; [eapply (wf_loads _ _ W1)|eapply (wf_loads _ _ W2)]; eauto.
  - intros op a0 ofs v Hk. apply bm_mem_inter_eq in Hk as [H1 H2].
    apply inter_eq_some; split; [eapply (wf_loads_addr _ _ W1)|eapply (wf_loads_addr _ _ W2)]; eauto.
Qed.

Lemma sem_inv_merge d1 d2 (s : state) :
  wf_data a d1 -> sem_inv d1 s -> sem_inv (merge_data d1 d2) s.
Proof.
  intros W1 S; destruct S as [S1 S2 S3 S4 S5 S6 S7 S8]; unfold merge_data; constructor;
    cbn [to_canonical to_latest gets_mem instrs_mem loads_mem].
  - intros r v Hr; apply inter_eq_some in Hr as [H1 _]; eauto.
  - intros r v Hr; discriminate Hr.
  - intros n w v Hk; apply bm_mem_inter_eq in Hk as [H1 _]; eauto.
  - intros x v Hk; apply bm_mem_inter_eq in Hk as [H1 _]; eauto.
  - intros op src v Hk; apply bm_mem_inter_eq in Hk as [H1 _]; eauto.
  - intros l v Hk; apply bm_mem_inter_eq in Hk as [H1 _]; eauto.
  - intros x v Hx. apply ALOOKUP_gets_merge in Hx as [H1 _]; [eauto|apply (wf_gets_distinct _ _ W1)].
  - intros op a0 ofs v Hs Hk; apply bm_mem_inter_eq in Hk as [H1 _]; eauto.
Qed.

Lemma merge_data_sym_mem d1 d2 :
  (forall k v, bm_mem k v (instrs_mem (merge_data d1 d2)) -> bm_mem k v (instrs_mem d2)) /\
  (forall k v, bm_mem k v (loads_mem (merge_data d1 d2)) -> bm_mem k v (loads_mem d2)).
Proof.
  unfold merge_data; cbn [instrs_mem loads_mem]; split; intros k v H;
    apply bm_mem_inter_eq in H as [_ H]; exact H.
Qed.

Lemma sem_inv_merge_r d1 d2 (s : state) :
  wf_data a d1 -> wf_data a d2 -> sem_inv d2 s -> sem_inv (merge_data d1 d2) s.
Proof.
  intros W1 W2 S; destruct S as [S1 S2 S3 S4 S5 S6 S7 S8]; unfold merge_data; constructor;
    cbn [to_canonical to_latest gets_mem instrs_mem loads_mem].
  - intros r v Hr; apply inter_eq_some in Hr as [_ H2]; eauto.
  - intros r v Hr; discriminate Hr.
  - intros n w v Hk; apply bm_mem_inter_eq in Hk as [_ H2]; eauto.
  - intros x v Hk; apply bm_mem_inter_eq in Hk as [_ H2]; eauto.
  - intros op src v Hk; apply bm_mem_inter_eq in Hk as [_ H2]; eauto.
  - intros l v Hk; apply bm_mem_inter_eq in Hk as [_ H2]; eauto.
  - intros x v Hx. apply ALOOKUP_gets_merge in Hx as [_ H2]; [eauto|apply (wf_gets_distinct _ _ W1)].
  - intros op a0 ofs v Hs Hk; apply bm_mem_inter_eq in Hk as [_ H2]; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_merge_l" *)
Theorem data_inv_merge_l : forall d1 d2 (s : state),
  wf_data a d1 /\ wf_data a d2 /\ sem_inv d1 s -> data_inv (merge_data d1 d2) s.
Proof.
  intros d1 d2 s (W1 & W2 & S); split; [apply wf_data_merge; auto|apply sem_inv_merge; auto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_merge_r" *)
Theorem data_inv_merge_r : forall d1 d2 (s : state),
  wf_data a d1 /\ wf_data a d2 /\ sem_inv d2 s -> data_inv (merge_data d1 d2) s.
Proof.
  intros d1 d2 s (W1 & W2 & S); split; [apply wf_data_merge; auto|apply sem_inv_merge_r; auto].
Qed.

End Merge.

(** ** Well-formedness of knowledge updates *)

Lemma lookup_insert_fresh (t : num_map N) x y r v :
  lookup x t = None -> lookup r t = Some v -> lookup r (insert x y t) = Some v.
Proof.
  intros H1 H2; rewrite lookup_insert; destruct (decide (r = x)); [subst; congruence|exact H2].
Qed.

Lemma domain_insert_mono {A} (t : num_map A) x y r :
  r IN domain t -> r IN domain (insert x y t).
Proof.
  intros H; apply domain_lookup in H as [v Hv]; apply domain_lookup.
  rewrite lookup_insert; destruct (decide (r = x)); eauto.
Qed.


(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "shiftToNum_eq" *)
Theorem shiftToNum_eq : forall s1 s2, shiftToNum s1 = shiftToNum s2 <-> s1 = s2.
Proof. intros [] []; cbn; split; congruence. Qed.

Ltac keys :=
  try unfold instToNumList in *; try unfold arithToNumList in *;
  try unfold OpCurrHeapToNumList in *; try unfold loadToNumList in *;
  try unfold regImmToNumList in *; cbn [app] in *;
  repeat match goal with
  | H : _ :: _ = _ :: _ |- _ => injection H as; subst
  | H : _ = _ |- _ => discriminate H
  | H : arithOpToNum _ = arithOpToNum _ |- _ => apply arithOpToNum_eq in H; subst
  | H : shiftToNum _ = shiftToNum _ |- _ => apply shiftToNum_eq in H; subst
  | H : memOpToNum _ = memOpToNum _ |- _ => apply memOpToNum_eq in H; subst
  | H : wordToNum _ = wordToNum _ |- _ => apply wordToNum_unique in H; subst
  | H : ?x + 100 = ?y + 100 |- _ => assert (x = y) by lia; subst; clear H
  end.

Section Keys.
Context {a : N}.

Lemma arith_keys_val (a1 a2 : arith a) :
  can_mem_arith a1 -> arithToNumList a1 = arithToNumList a2 ->
  can_mem_arith a2 /\ arithReads a2 = arithReads a1 /\
  forall {c ffi_t} (s : state a c ffi_t), arith_val a2 s = arith_val a1 s.
Proof.
  intros H1 H2; destruct a1; cbn [can_mem_arith] in H1; try discriminate H1;
    destruct a2; cbn [arithToNumList regImmToNumList] in H2; try (destruct r); try (destruct r0);
    cbn [app regImmToNumList] in H2; keys; try discriminate H1.
  all: repeat match goal with
         | H : arithOpToNum _ = arithOpToNum _ |- _ => apply arithOpToNum_eq in H; subst
         | H : shiftToNum _ = shiftToNum _ |- _ => apply shiftToNum_eq in H; subst
         | H : wordToNum _ = wordToNum _ |- _ => apply wordToNum_unique in H; subst
         | H : ?x + 100 = ?y + 100 |- _ => assert (x = y) by lia; subst; clear H
         end.
  all: split; [exact H1|split; [reflexivity|intros; reflexivity]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "arith_keys_eq" *)
Theorem arith_keys_eq : forall (a1 a2 : arith a),
  can_mem_arith a1 /\ arithToNumList a1 = arithToNumList a2 ->
  can_mem_arith a2 /\ arithReads a2 = arithReads a1 /\
  forall {c ffi_t} (s : state a c ffi_t) w,
    evaluate (Inst (Arith a1), s) = (None, set_var (firstRegOfArith a1) w s) ->
    evaluate (Inst (Arith a2), s) = (None, set_var (firstRegOfArith a2) w s).
Proof.
  intros a1 a2 [H1 H2]; destruct (arith_keys_val a1 a2 H1 H2) as (C & R & V).
  split; [exact C|split; [exact R|]]. intros c ffi_t s w E.
  rewrite eval_arith_iff in * by assumption. rewrite V; exact E.
Qed.

End Keys.

Section WF.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_empty" *)
Theorem wf_data_empty : wf_data a empty_data.
Proof.
  constructor; cbn; intros;
    repeat match goal with H : False |- _ => destruct H | H : None = Some _ |- _ => discriminate H end;
    try reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_loads_wipe" *)
Theorem wf_data_loads_wipe : forall data,
  wf_data a data -> wf_data a (with_loads_mem balanced_map.empty data).
Proof.
  intros data W; destruct W; constructor; cbn [with_loads_mem to_canonical to_latest gets_mem
    instrs_mem loads_mem]; auto; intros * H; destruct H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_invalidate" *)
Theorem wf_data_invalidate : forall data r, wf_data a data -> wf_data a (invalidate_data data r).
Proof. intros data r W; unfold invalidate_data; destruct (keep_data _ _); [exact W|apply wf_data_empty]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_invalidate_regs" *)
Theorem wf_data_invalidate_regs : forall rs data,
  wf_data a data -> wf_data a (invalidate_regs data rs).
Proof. induction rs; intros; cbn; auto using wf_data_invalidate. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_to_canonical" *)
Theorem wf_data_insert_to_canonical : forall data x y,
  wf_data a data /\ lookup x (to_canonical data) = None /\
  lookup y (insert x y (to_canonical data)) = Some y /\ is_true (ODD x) /\ is_true (ODD y) ->
  wf_data a (with_to_canonical (insert x y (to_canonical data)) data).
Proof.
  intros data x y (W & Hx & Hy & Ox & Oy).
  pose proof (lookup_insert_fresh (to_canonical data) x y) as F.
  constructor; cbn [with_to_canonical to_canonical to_latest gets_mem instrs_mem loads_mem].
  - intros r v Hr. rewrite lookup_insert in Hr. destruct (decide (r = x)); [inv_eqs; auto|].
    destruct (wf_tc _ _ W _ _ Hr) as (A1 & A2 & A3). auto.
  - intros r v Hr. destruct (wf_tl _ _ W _ _ Hr). split; apply domain_insert_mono; auto.
  - intros k v Hk. apply F; [exact Hx|]. eapply wf_instrs; eauto.
  - intros x0 v Hk. destruct (wf_arith _ _ W _ _ Hk) as [N1 C1]. split; [|exact C1].
    apply in_names_set_iff; intros r Hr. apply F; [exact Hx|]. apply (proj1 (in_names_set_iff _ _) N1), Hr.
  - intros op src v Hk. apply F; [exact Hx|]. eapply wf_och; eauto.
  - intros x0 v Hk. apply F; [exact Hx|]. eapply wf_gets; eauto.
  - apply (wf_gets_distinct _ _ W).
  - intros k v Hk. apply F; [exact Hx|]. eapply wf_loads; eauto.
  - intros op a0 ofs v Hk. apply F; [exact Hx|]. eapply wf_loads_addr; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_to_latest" *)
Theorem wf_data_insert_to_latest : forall data x y,
  wf_data a data /\ x IN domain (to_canonical data) /\ y IN domain (to_canonical data) ->
  wf_data a (with_to_latest (insert x y (to_latest data)) data).
Proof.
  intros data x y (W & Hx & Hy); destruct W; constructor;
    cbn [with_to_latest to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  intros r v Hr; rewrite lookup_insert in Hr. destruct (decide (r = x)); [inv_eqs; auto|eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_register_read" *)
Theorem wf_data_register_read : forall data r, wf_data a data -> wf_data a (register_read data r).
Proof.
  intros data r W; unfold register_read, keep_data.
  destruct (negb (EVEN r)) eqn:Er; cbn [andb]; [|exact W].
  destruct (lookup r (to_canonical data)) eqn:Hr; cbn [IS_NONE]; [exact W|].
  assert (Or : is_true (ODD r)) by (unfold is_true; rewrite <- N.negb_even; exact Er).
  apply (wf_data_insert_to_canonical data r r); split; [exact W|]; split; [exact Hr|].
  split; [|split; exact Or].
  rewrite lookup_insert; destruct (decide (r = r)); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_register_reads" *)
Theorem wf_data_register_reads : forall rs data,
  wf_data a data -> wf_data a (register_reads data rs).
Proof. induction rs; intros; cbn; auto using wf_data_register_read. Qed.

Ltac new_or_old Hk :=
  apply bm_mem_insert in Hk as [[Ek ->]|Hk]; [keys|].

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_Const" *)
Theorem wf_data_insert_instrs_Const : forall data r n (w : word a),
  wf_data a data /\ lookup r (to_canonical data) = Some r ->
  wf_data a (with_instrs_mem (balanced_map.insert listCmp (instToNumList (asm.Const n w)) r
                                (instrs_mem data)) data).
Proof.
  intros data r n w [W Hr]; destruct W; constructor;
    cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros k v Hk; new_or_old Hk; eauto.
  - intros x v Hk; new_or_old Hk; eauto.
  - intros op src v Hk; new_or_old Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_Arith" *)
Theorem wf_data_insert_instrs_Arith : forall data r (x : arith a),
  wf_data a data /\ lookup r (to_canonical data) = Some r /\ can_mem_arith x /\
  in_names_set x (to_canonical data) ->
  wf_data a (with_instrs_mem (balanced_map.insert listCmp (instToNumList (Arith x)) r
                                (instrs_mem data)) data).
Proof.
  intros data r x (W & Hr & Hc & Hn); destruct W; constructor;
    cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros k v Hk; new_or_old Hk; eauto.
  - intros x0 v Hk. apply bm_mem_insert in Hk as [[Ek ->]|Hk]; [|eauto].
    cbn [instToNumList] in Ek. injection Ek as Ek.
    destruct (arith_keys_val x x0 Hc (eq_sym Ek)) as (C & R & _). split; [|exact C].
    apply in_names_set_iff; rewrite R; apply in_names_set_iff, Hn.
  - intros op src v Hk; new_or_old Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_OpCurrHeap" *)
Theorem wf_data_insert_instrs_OpCurrHeap : forall data r op src,
  wf_data a data /\ lookup r (to_canonical data) = Some r /\ lookup src (to_canonical data) = Some src ->
  wf_data a (with_instrs_mem (balanced_map.insert listCmp (OpCurrHeapToNumList op src) r
                                (instrs_mem data)) data).
Proof.
  intros data r op src (W & Hr & Hs); destruct W; constructor;
    cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros k v Hk; new_or_old Hk; eauto.
  - intros x v Hk; new_or_old Hk; eauto.
  - intros op' src' v Hk; new_or_old Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_instrs_LocValue" *)
Theorem wf_data_insert_instrs_LocValue : forall data r l,
  wf_data a data /\ lookup r (to_canonical data) = Some r ->
  wf_data a (with_instrs_mem (balanced_map.insert listCmp [48; l] r (instrs_mem data)) data).
Proof.
  intros data r l [W Hr]; destruct W; constructor;
    cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros k v Hk; new_or_old Hk; eauto.
  - intros x v Hk; new_or_old Hk; eauto.
  - intros op src v Hk; new_or_old Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_loads" *)
Theorem wf_data_insert_loads : forall data r op a0 (ofs : word a),
  wf_data a data /\ lookup r (to_canonical data) = Some r /\ lookup a0 (to_canonical data) = Some a0 ->
  wf_data a (with_loads_mem (balanced_map.insert listCmp (loadToNumList op a0 ofs) r
                               (loads_mem data)) data).
Proof.
  intros data r op a0 ofs (W & Hr & Ha); destruct W; constructor;
    cbn [with_loads_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros k v Hk; new_or_old Hk; eauto.
  - intros op' a1 ofs' v Hk. apply bm_mem_insert in Hk as [[Ek ->]|Hk]; [|eauto].
    keys; exact Ha.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_insert_gets" *)
Theorem wf_data_insert_gets : forall data name v,
  wf_data a data /\ lookup v (to_canonical data) = None /\ is_true (ODD v) /\
  ALOOKUP (gets_mem data) name = None ->
  wf_data a {| to_canonical := insert v v (to_canonical data);
               to_latest := insert v v (to_latest data);
               gets_mem := (name, v) :: gets_mem data;
               instrs_mem := instrs_mem data; loads_mem := loads_mem data |}.
Proof.
  intros data name v (W & Hv & Ov & Hn).
  pose proof (wf_data_insert_to_canonical data v v) as T.
  assert (Vv : lookup v (insert v v (to_canonical data)) = Some v)
    by (rewrite lookup_insert; destruct (decide (v = v)); [reflexivity|congruence]).
  destruct (T (conj W (conj Hv (conj Vv (conj Ov Ov))))) as [T1 T2 T3 T4 T5 T6 T7 T8 T9].
  cbn [with_to_canonical to_canonical to_latest gets_mem instrs_mem loads_mem] in *.
  constructor; cbn [to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros r v' Hr. rewrite lookup_insert in Hr. destruct (decide (r = v)); [inv_eqs|].
    + split; apply domain_lookup; eauto.
    + destruct (wf_tl _ _ W _ _ Hr); split; apply domain_insert_mono; auto.
  - intros x v' Hx. cbn [ALOOKUP] in Hx. destruct (decide (name = x)); [inv_eqs; exact Vv|eauto].
  - cbn [MAP ALL_DISTINCT FST]. apply andb_true_intro; split; [|apply (wf_gets_distinct _ _ W)].
    apply negb_true_iff. destruct (MEM name _) eqn:E; [|reflexivity].
    exfalso. apply ALOOKUP_NONE in Hn. apply Hn. exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_filter_gets" *)
Theorem wf_data_filter_gets : forall data x,
  wf_data a data ->
  wf_data a (with_gets_mem (FILTER (fun '(m, n) => negb (bool_decide (m = x))) (gets_mem data)) data).
Proof.
  intros data x W; destruct W; constructor;
    cbn [with_gets_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros y v Hy. apply ALOOKUP_In, filter_In in Hy as [Hy _].
    apply (wf_gets0 y). apply ALOOKUP_ALL_DISTINCT_MEM; split; [auto|unfold is_true; rewrite MEM_In; exact Hy].
  - apply ALL_DISTINCT_MAP_FST_FILTER; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_cons_gets" *)
Theorem wf_data_cons_gets : forall data x h,
  wf_data a data /\ ALOOKUP (gets_mem data) x = None /\ lookup h (to_canonical data) = Some h ->
  wf_data a (with_gets_mem ((x, h) :: gets_mem data) data).
Proof.
  intros data x h (W & Hx & Hh); destruct W; constructor;
    cbn [with_gets_mem to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros y v Hy. cbn [ALOOKUP] in Hy. destruct (decide (x = y)); [inv_eqs; exact Hh|eauto].
  - cbn [MAP ALL_DISTINCT FST]. apply andb_true_intro; split; [|auto].
    apply negb_true_iff. destruct (MEM x _) eqn:E; [|reflexivity].
    exfalso. apply ALOOKUP_NONE in Hx. apply Hx. exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_reinsert_canonical" *)
Theorem wf_data_reinsert_canonical : forall data v,
  wf_data a data /\ is_true (ODD v) ->
  wf_data a (with_to_canonical (insert v (lookup_any v (to_canonical data) v) (to_canonical data)) data).
Proof.
  intros data v [W Ov]; unfold lookup_any.
  destruct (lookup v (to_canonical data)) as [x|] eqn:E.
  - rewrite (insert_unchanged _ _ _ E). destruct W; constructor; auto.
  - apply wf_data_insert_to_canonical; repeat (split; [auto|]); auto.
    rewrite lookup_insert; destruct (decide (v = v)); [reflexivity|congruence].
Qed.

End WF.

(** ** Knowledge updates *)

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "register_read_simps" *)
Theorem register_read_simps : forall data r,
  instrs_mem (register_read data r) = instrs_mem data /\
  to_latest (register_read data r) = to_latest data /\
  gets_mem (register_read data r) = gets_mem data /\
  loads_mem (register_read data r) = loads_mem data.
Proof. intros data r; unfold register_read; destruct (_ && _); repeat split. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "register_reads_simps" *)
Theorem register_reads_simps : forall rs data,
  instrs_mem (register_reads data rs) = instrs_mem data /\
  to_latest (register_reads data rs) = to_latest data /\
  gets_mem (register_reads data rs) = gets_mem data /\
  loads_mem (register_reads data rs) = loads_mem data.
Proof.
  induction rs as [|r rs IH]; intros data; [repeat split|]; cbn [register_reads].
  destruct (IH (register_read data r)) as (A & B & C & D).
  destruct (register_read_simps data r) as (A' & B' & C' & D').
  rewrite A, B, C, D, A', B', C', D'; repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_register_read" *)
Theorem lookup_register_read : forall x data r,
  lookup x (to_canonical (register_read data r)) =
  if decide (x = r /\ ~ is_true (EVEN r) /\ lookup r (to_canonical data) = None)
  then Some r else lookup x (to_canonical data).
Proof.
  intros x data r; unfold register_read, keep_data.
  destruct (EVEN r) eqn:Er; cbn [negb andb].
  - destruct (decide _) as [Hd|Hd]; [|reflexivity]. exfalso.
    destruct Hd as (_ & Hd & _). apply Hd; reflexivity.
  - destruct (lookup r (to_canonical data)) eqn:Hr; cbn [IS_NONE].
    + destruct (decide _) as [Hd|Hd]; [|reflexivity]. destruct Hd as (_ & _ & Hd); discriminate Hd.
    + cbn [to_canonical]. rewrite lookup_insert.
      destruct (decide (x = r)) as [->|n]; destruct (decide _) as [Hd|Hd]; auto.
      * exfalso; apply Hd; split; [reflexivity|split; [intros Hf; discriminate Hf|reflexivity]].
      * destruct Hd as [E _]; contradiction.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_register_reads" *)
Theorem lookup_register_reads : forall rs data x,
  lookup x (to_canonical (register_reads data rs)) =
  if decide (MEM x rs /\ ~ is_true (EVEN x) /\ lookup x (to_canonical data) = None)
  then Some x else lookup x (to_canonical data).
Proof.
  induction rs as [|r rs IH]; intros data x; cbn [register_reads].
  - destruct (decide _) as [(H & _)|]; [discriminate H|reflexivity].
  - assert (MC : is_true (MEM x (r :: rs)) <-> x = r \/ is_true (MEM x rs))
      by (unfold is_true; rewrite !MEM_In; cbn [In]; intuition).
    rewrite IH, !lookup_register_read.
    destruct (decide (x = r /\ ~ is_true (EVEN r) /\ lookup r (to_canonical data) = None)) as [P|P].
    + destruct P as (-> & Pe & Pl).
      destruct (decide (is_true (MEM r rs) /\ ~ is_true (EVEN r) /\ Some r = None)) as [Q|Q];
        [destruct Q as (_ & _ & Q); discriminate Q|].
      destruct (decide _) as [R|R]; [reflexivity|].
      exfalso; apply R; split; [apply MC; left; reflexivity|split; assumption].
    + destruct (decide (is_true (MEM x rs) /\ ~ is_true (EVEN x) /\ lookup x (to_canonical data) = None))
        as [Q|Q]; destruct (decide (is_true (MEM x (r :: rs)) /\ ~ is_true (EVEN x) /\
                                    lookup x (to_canonical data) = None)) as [R|R];
        try reflexivity.
      * exfalso; apply R; destruct Q as (Q1 & Q2 & Q3); split; [apply MC; right; exact Q1|auto].
      * exfalso; apply Q; destruct R as (R1 & R2 & R3); split; [|auto].
        apply MC in R1 as [->|R1]; [exfalso; apply P; auto|exact R1].
Qed.

Section DataInv.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types s : state.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_to_canonical" *)
Theorem data_inv_insert_to_canonical : forall data s x y,
  data_inv data s /\ lookup x (to_canonical data) = None /\
  lookup y (insert x y (to_canonical data)) = Some y /\ is_true (ODD x) /\ is_true (ODD y) /\
  get_var x s = get_var y s ->
  data_inv (with_to_canonical (insert x y (to_canonical data)) data) s.
Proof.
  intros data s x y ([W S] & Hx & Hy & Ox & Oy & G); split;
    [apply wf_data_insert_to_canonical; auto|].
  destruct S; constructor; cbn [with_to_canonical to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  intros r v Hr; rewrite lookup_insert in Hr; destruct (decide (r = x)); [inv_eqs; exact G|eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_to_latest" *)
Theorem data_inv_insert_to_latest : forall data s x y,
  data_inv data s /\ x IN domain (to_canonical data) /\ y IN domain (to_canonical data) /\
  get_var x s = get_var y s ->
  data_inv (with_to_latest (insert x y (to_latest data)) data) s.
Proof.
  intros data s x y ([W S] & Hx & Hy & G); split; [apply wf_data_insert_to_latest; auto|].
  destruct S; constructor; cbn [with_to_latest to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  intros r v Hr; rewrite lookup_insert in Hr; destruct (decide (r = x)); [inv_eqs; exact G|eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_gets" *)
Theorem data_inv_insert_gets : forall data s name v w,
  data_inv data s /\ lookup v (to_canonical data) = None /\ is_true (ODD v) /\
  ALOOKUP (gets_mem data) name = None /\
  FLOOKUP (store s) name = Some w /\ get_var v s = Some w ->
  data_inv {| to_canonical := insert v v (to_canonical data);
              to_latest := insert v v (to_latest data);
              gets_mem := (name, v) :: gets_mem data;
              instrs_mem := instrs_mem data; loads_mem := loads_mem data |} s.
Proof.
  intros data s name v w ([W S] & Hv & Ov & Hn & Hs & Hg); split; [apply wf_data_insert_gets; auto|].
  destruct S; constructor; cbn [to_canonical to_latest gets_mem instrs_mem loads_mem]; auto.
  - intros r v' Hr; rewrite lookup_insert in Hr; destruct (decide (r = v)); [inv_eqs; reflexivity|eauto].
  - intros r v' Hr; rewrite lookup_insert in Hr; destruct (decide (r = v)); [inv_eqs; reflexivity|eauto].
  - intros x v' Hx. cbn [ALOOKUP] in Hx. destruct (decide (name = x)); [inv_eqs; eauto|eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_filter_gets" *)
Theorem data_inv_filter_gets : forall data s x,
  data_inv data s ->
  data_inv (with_gets_mem (FILTER (fun '(m, n) => negb (bool_decide (m = x))) (gets_mem data)) data) s.
Proof.
  intros data s x [W S]; split; [apply wf_data_filter_gets; auto|].
  destruct S; constructor; cbn [with_gets_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  intros y v Hy. apply ALOOKUP_In, filter_In in Hy as [Hy _].
  apply (si_gets0 y). apply ALOOKUP_ALL_DISTINCT_MEM; split;
    [apply (wf_gets_distinct _ _ W)|unfold is_true; rewrite MEM_In; exact Hy].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_cons_gets" *)
Theorem data_inv_cons_gets : forall data s x h w,
  data_inv data s /\ ALOOKUP (gets_mem data) x = None /\ lookup h (to_canonical data) = Some h /\
  FLOOKUP (store s) x = Some w /\ get_var h s = Some w ->
  data_inv (with_gets_mem ((x, h) :: gets_mem data) data) s.
Proof.
  intros data s x h w ([W S] & Hx & Hh & Hs & Hg); split; [apply wf_data_cons_gets; auto|].
  destruct S; constructor; cbn [with_gets_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  intros y v Hy. cbn [ALOOKUP] in Hy. destruct (decide (x = y)); [inv_eqs; eauto|eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_store" *)
Theorem data_inv_set_store : forall data s x w,
  data_inv data s /\ x <> stackLang.CurrHeap /\ ALOOKUP (gets_mem data) x = None ->
  data_inv data (set_store x w s).
Proof.
  intros data s x w ([W S] & Hx & Hn); split; [exact W|].
  eapply sem_inv_agree; eauto; try reflexivity.
  all: first
    [ right; repeat split
    | unfold set_store; cbn [store set_store_field]; rewrite FLOOKUP_UPDATE;
      destruct (decide _); [congruence|reflexivity]
    | intros y v Hy; unfold set_store; cbn [store set_store_field]; rewrite FLOOKUP_UPDATE;
      destruct (decide _); [subst; congruence|reflexivity] ].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_reinsert_canonical" *)
Theorem data_inv_reinsert_canonical : forall data s v,
  data_inv data s /\ is_true (ODD v) ->
  data_inv (with_to_canonical (insert v (lookup_any v (to_canonical data) v) (to_canonical data)) data) s.
Proof.
  intros data s v [H Ov]; unfold lookup_any.
  destruct (lookup v (to_canonical data)) as [x|] eqn:E.
  - rewrite (insert_unchanged _ _ _ E). destruct H as [W S]; split; [destruct W; constructor; auto|].
    destruct S; constructor; auto.
  - apply data_inv_insert_to_canonical; repeat (split; [auto|]); auto.
    rewrite lookup_insert; destruct (decide (v = v)); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "empty_data_loads_wipe" *)
Theorem empty_data_loads_wipe : with_loads_mem balanced_map.empty empty_data = empty_data.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_empty_data" *)
Theorem lookup_empty_data : forall r, lookup r (to_canonical empty_data) = None.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_register_read" *)
Theorem data_inv_register_read : forall data s r, data_inv data s -> data_inv (register_read data r) s.
Proof.
  intros data s r H; unfold register_read, keep_data.
  destruct (negb (EVEN r)) eqn:Er; cbn [andb]; [|exact H].
  destruct (lookup r (to_canonical data)) eqn:Hr; cbn [IS_NONE]; [exact H|].
  assert (Or : is_true (ODD r)) by (unfold is_true; rewrite <- N.negb_even; exact Er).
  apply (data_inv_insert_to_canonical data s r r); split; [exact H|]; split; [exact Hr|].
  split; [|split; [exact Or|split; [exact Or|reflexivity]]].
  rewrite lookup_insert; destruct (decide (r = r)); [reflexivity|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_register_reads" *)
Theorem data_inv_register_reads : forall rs data s,
  data_inv data s -> data_inv (register_reads data rs) s.
Proof. induction rs; intros; cbn; auto using data_inv_register_read. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_invalidate_regs_mono" *)
Theorem lookup_invalidate_regs_mono : forall ws data r,
  lookup r (to_canonical data) = None -> lookup r (to_canonical (invalidate_regs data ws)) = None.
Proof.
  induction ws as [|w ws IH]; intros data r H; cbn [invalidate_regs]; [exact H|].
  apply IH. unfold invalidate_data; destruct (keep_data _ _); [exact H|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_invalidate_regs" *)
Theorem lookup_invalidate_regs : forall ws data r,
  MEM r ws -> lookup r (to_canonical (invalidate_regs data ws)) = None.
Proof.
  induction ws as [|w ws IH]; intros data r H; [discriminate H|]. cbn [invalidate_regs].
  unfold is_true in H; rewrite MEM_In in H; destruct H as [->|H].
  - apply lookup_invalidate_regs_mono. unfold invalidate_data, keep_data.
    destruct (lookup r (to_canonical data)) eqn:E; cbn [IS_NONE]; [reflexivity|exact E].
  - apply IH. unfold is_true; rewrite MEM_In; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_invalidate_regs" *)
Theorem data_inv_invalidate_regs : forall ws data s,
  data_inv data s -> data_inv (invalidate_regs data ws) s.
Proof.
  induction ws as [|w ws IH]; intros data s H; cbn [invalidate_regs]; [exact H|].
  apply IH. unfold invalidate_data; destruct (keep_data _ _); [exact H|apply data_inv_empty].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_fp_var" *)
Theorem data_inv_set_fp_var : forall data v x s,
  data_inv data (set_fp_var v x s) <-> data_inv data s.
Proof.
  intros data v x s; split; intros H; eapply data_inv_state_agree; split; eauto;
    repeat split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "with_locals_insert" *)
Theorem with_locals_insert : forall s r (v : word_loc a) l,
  set_locals (insert r v l) s = set_var r v (set_locals l s).
Proof. intros [] r v l; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_alist_insert_locals" *)
Theorem data_inv_alist_insert_locals : forall xs ys data s l,
  EVERY (fun x => bool_decide (lookup x (to_canonical data) = None)) xs ->
  (data_inv data (set_locals (alist_insert xs ys l) s) <-> data_inv data (set_locals l s)).
Proof.
  induction xs as [|x xs IH]; intros ys data s l H; [reflexivity|].
  destruct ys as [|y ys]; [reflexivity|]. cbn [alist_insert]. cbn [EVERY] in H; bsplit.
  rewrite with_locals_insert, data_inv_set_var by (apply (proj1 (bool_decide_spec _)); auto).
  apply IH; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_set_vars" *)
Theorem data_inv_set_vars : forall xs ys data s,
  EVERY (fun x => bool_decide (lookup x (to_canonical data) = None)) xs ->
  (data_inv data (set_vars xs ys s) <-> data_inv data s).
Proof.
  intros xs ys data s H; unfold set_vars. rewrite data_inv_alist_insert_locals by exact H.
  rewrite data_inv_locals; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_Move1" *)
Theorem evaluate_Move1 : forall pri r k w s,
  get_var k s = Some w -> evaluate (Move pri [(r, k)], s) = (None, set_var r w s).
Proof.
  intros pri r k w s H; rewrite evaluate_eqn; cbn [evaluate_body MAP List.map fst snd ALL_DISTINCT
    MEM get_vars]; rewrite H. reflexivity.
Qed.

Ltac new_or_old' Hk :=
  apply bm_mem_insert in Hk as [[Ek ->]|Hk]; [keys|].

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_Const" *)
Theorem data_inv_insert_instrs_Const : forall data s r n (w : word a),
  data_inv data s /\ lookup r (to_canonical data) = Some r /\ lookup r (locals s) = Some (Word w) ->
  data_inv (with_instrs_mem (balanced_map.insert listCmp (instToNumList (asm.Const n w)) r
                               (instrs_mem data)) data) s.
Proof.
  intros data s r n w ([W S] & Hr & Hl); split; [apply wf_data_insert_instrs_Const; auto|].
  destruct S; constructor; cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  - intros n' w' v Hk; new_or_old' Hk; eauto.
  - intros x v Hk; new_or_old' Hk; eauto.
  - intros op src v Hk; new_or_old' Hk; eauto.
  - intros l v Hk; new_or_old' Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_Arith" *)
Theorem data_inv_insert_instrs_Arith : forall data s r (x : arith a) w,
  data_inv data s /\ lookup r (to_canonical data) = Some r /\ can_mem_arith x /\
  in_names_set x (to_canonical data) /\ get_var r s = Some w /\
  evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s) ->
  data_inv (with_instrs_mem (balanced_map.insert listCmp (instToNumList (Arith x)) r
                               (instrs_mem data)) data) s.
Proof.
  intros data s r x w ([W S] & Hr & Hc & Hn & Hg & He); split;
    [apply wf_data_insert_instrs_Arith; auto|].
  destruct S; constructor; cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  - intros n' w' v Hk; new_or_old' Hk; eauto.
  - intros x0 v Hk. apply bm_mem_insert in Hk as [[Ek ->]|Hk]; [|eauto].
    cbn [instToNumList] in Ek. injection Ek as Ek.
    destruct (arith_keys_eq x x0 (conj Hc (eq_sym Ek))) as (_ & _ & E). exists w; split; auto.
  - intros op src v Hk; new_or_old' Hk; eauto.
  - intros l v Hk; new_or_old' Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_OpCurrHeap" *)
Theorem data_inv_insert_instrs_OpCurrHeap : forall data s r op src w,
  data_inv data s /\ lookup r (to_canonical data) = Some r /\
  lookup src (to_canonical data) = Some src /\
  word_exp s (Op op [Var src; Lookup stackLang.CurrHeap]) = Some w /\ get_var r s = Some w ->
  data_inv (with_instrs_mem (balanced_map.insert listCmp (OpCurrHeapToNumList op src) r
                               (instrs_mem data)) data) s.
Proof.
  intros data s r op src w ([W S] & Hr & Hs & He & Hg); split;
    [apply wf_data_insert_instrs_OpCurrHeap; auto|].
  destruct S; constructor; cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  - intros n' w' v Hk; new_or_old' Hk; eauto.
  - intros x v Hk; new_or_old' Hk; eauto.
  - intros op' src' v Hk; new_or_old' Hk; eauto.
  - intros l v Hk; new_or_old' Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_instrs_LocValue" *)
Theorem data_inv_insert_instrs_LocValue : forall data s r l,
  data_inv data s /\ lookup r (to_canonical data) = Some r /\ lookup r (locals s) = Some (Loc l 0) ->
  data_inv (with_instrs_mem (balanced_map.insert listCmp [48; l] r (instrs_mem data)) data) s.
Proof.
  intros data s r l ([W S] & Hr & Hl); split; [apply wf_data_insert_instrs_LocValue; auto|].
  destruct S; constructor; cbn [with_instrs_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  - intros n' w' v Hk; new_or_old' Hk; eauto.
  - intros x v Hk; new_or_old' Hk; eauto.
  - intros op src v Hk; new_or_old' Hk; eauto.
  - intros l' v Hk; new_or_old' Hk; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_loads" *)
Theorem data_inv_insert_loads : forall data s r op a0 (ofs : word a) w,
  data_inv data s /\ lookup r (to_canonical data) = Some r /\
  lookup a0 (to_canonical data) = Some a0 /\ ~ is_store op /\ get_var r s = Some w /\
  (forall r', evaluate (Inst (Mem op r' (Addr a0 ofs)), s) = (None, set_var r' w s)) ->
  data_inv (with_loads_mem (balanced_map.insert listCmp (loadToNumList op a0 ofs) r
                              (loads_mem data)) data) s.
Proof.
  intros data s r op a0 ofs w ([W S] & Hr & Ha & Hs & Hg & He); split;
    [apply wf_data_insert_loads; auto|].
  destruct S; constructor; cbn [with_loads_mem to_canonical to_latest gets_mem instrs_mem loads_mem];
    auto.
  intros op' a1 ofs' v Hs' Hk; new_or_old' Hk; eauto.
Qed.

Lemma ODD_not_EVEN n : ~ is_true (EVEN n) <-> is_true (ODD n).
Proof. unfold is_true; rewrite <- N.negb_even; destruct (EVEN n); cbn; split; congruence. Qed.

Lemma get_var_lookup_any data s r' w :
  data_inv data s -> get_var r' s = Some w ->
  get_var (lookup_any r' (to_latest data) r') s = Some w.
Proof.
  intros [_ S] H; unfold lookup_any. destruct (lookup r' (to_latest data)) eqn:E; [|exact H].
  rewrite <- (si_tl _ _ S _ _ E); exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_aux_correct" *)
Theorem add_to_data_aux_correct : forall data s r i (p : prog a) w data' p',
  data_inv data s /\ lookup r (to_canonical data) = None /\
  add_to_data_aux data r i p = (data', p') /\
  evaluate (p, s) = (None, set_var r w s) /\
  (forall v, balanced_map.lookup listCmp i (instrs_mem data) = Some v -> get_var v s = Some w) /\
  (~ is_true (EVEN r) ->
     data_inv (with_instrs_mem (balanced_map.insert listCmp i r
                 (instrs_mem (with_to_canonical (insert r r (to_canonical data)) data)))
                 (with_to_canonical (insert r r (to_canonical data)) data)) (set_var r w s)) ->
  evaluate (p', s) = (None, set_var r w s) /\ data_inv data' (set_var r w s).
Proof.
  intros data s r i p w data' p' (H & Hr & Ha & He & Hv & Hn); unfold add_to_data_aux in Ha.
  destruct (balanced_map.lookup listCmp i (instrs_mem data)) as [r'|] eqn:El.
  - pose proof (Hv r' eq_refl) as Gr'. pose proof (get_var_lookup_any data s r' w H Gr') as Gk.
    destruct (EVEN r) eqn:Er; inv_eqs.
    + split; [apply evaluate_Move1, Gk|apply data_inv_set_var; auto].
    + split; [apply evaluate_Move1, Gk|].
      destruct H as [W S]. pose proof (wf_instrs _ _ W _ _ (bm_lookup_mem _ _ _ El)) as Hr'.
      destruct (wf_tc _ _ W _ _ Hr') as (_ & _ & Or').
      assert (Ne : r' <> r) by (intros ->; congruence).
      assert (H1 : data_inv (with_to_canonical (insert r r' (to_canonical data)) data) (set_var r w s)).
      { apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto; split; auto|].
        split; [exact Hr|]. split; [rewrite lookup_insert; destruct (decide (r' = r)); [congruence|exact Hr']|].
        split; [apply (proj1 (ODD_not_EVEN r)); unfold is_true; rewrite Er; intros Hf; discriminate Hf|].
        split; [exact Or'|]. rewrite !get_var_set_var. destruct (decide (r = r)); [|congruence].
        destruct (decide (r' = r)); [congruence|]. symmetry; exact Gr'. }
      apply (data_inv_insert_to_latest (with_to_canonical (insert r r' (to_canonical data)) data) _ r' r).
      split; [exact H1|]. cbn [with_to_canonical to_canonical].
      split; [apply domain_lookup; exists r'; rewrite lookup_insert; destruct (decide (r' = r));
              [congruence|exact Hr']|].
      split; [apply domain_lookup; exists r'; rewrite lookup_insert; destruct (decide (r = r));
              [reflexivity|congruence]|].
      rewrite !get_var_set_var. destruct (decide (r = r)); [|congruence].
      destruct (decide (r' = r)); [congruence|exact Gr'].
  - destruct (EVEN r) eqn:Er; inv_eqs.
    + split; [exact He|apply data_inv_set_var; auto].
    + split; [exact He|].
      specialize (Hn ltac:(intros Hf; discriminate Hf)).
      apply (data_inv_insert_to_latest
        (with_instrs_mem (balanced_map.insert listCmp i r
           (instrs_mem (with_to_canonical (insert r r (to_canonical data)) data)))
           (with_to_canonical (insert r r (to_canonical data)) data)) _ r r).
      split; [exact Hn|]. cbn [with_instrs_mem with_to_canonical to_canonical].
      assert (D : r IN domain (insert r r (to_canonical data)))
        by (apply domain_lookup; exists r; rewrite lookup_insert; destruct (decide (r = r));
            [reflexivity|congruence]).
      repeat split; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_self_or_fresh_wf" *)
Theorem canonicalRegs_self_or_fresh_wf : forall data x,
  wf_data a data ->
  lookup (canonicalRegs data x) (to_canonical data) = Some (canonicalRegs data x) \/
  lookup (canonicalRegs data x) (to_canonical data) = None.
Proof.
  intros data x W; unfold canonicalRegs, lookup_any.
  destruct (lookup x (to_canonical data)) as [v|] eqn:E; [left|right; exact E].
  exact (proj1 (wf_tc _ _ W _ _ E)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs_self_or_fresh" *)
Theorem canonicalRegs_self_or_fresh : forall data s x,
  data_inv data s ->
  lookup (canonicalRegs data x) (to_canonical data) = Some (canonicalRegs data x) \/
  lookup (canonicalRegs data x) (to_canonical data) = None.
Proof. intros data s x [W _]; apply canonicalRegs_self_or_fresh_wf, W. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs'_self_or_fresh_wf" *)
Theorem canonicalRegs'_self_or_fresh_wf : forall data r1 x,
  wf_data a data /\ lookup r1 (to_canonical data) = None ->
  lookup (canonicalRegs' r1 data x) (to_canonical data) = Some (canonicalRegs' r1 data x) \/
  lookup (canonicalRegs' r1 data x) (to_canonical data) = None.
Proof.
  intros data r1 x [W H1]; unfold canonicalRegs'; cbn zeta.
  destruct (canonicalRegs data x =? r1) eqn:E; [|apply canonicalRegs_self_or_fresh_wf, W].
  apply N.eqb_eq in E. unfold canonicalRegs, lookup_any in E.
  destruct (lookup x (to_canonical data)) as [v|] eqn:Ex; [|right; first [exact Ex|reflexivity]].
  subst v. pose proof (proj1 (wf_tc _ _ W _ _ Ex)). congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalRegs'_self_or_fresh" *)
Theorem canonicalRegs'_self_or_fresh : forall data s r1 x,
  data_inv data s /\ lookup r1 (to_canonical data) = None ->
  lookup (canonicalRegs' r1 data x) (to_canonical data) = Some (canonicalRegs' r1 data x) \/
  lookup (canonicalRegs' r1 data x) (to_canonical data) = None.
Proof. intros data s r1 x [[W _] H]; apply canonicalRegs'_self_or_fresh_wf; auto. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "can_mem_arith_ODD_reads" *)
Theorem can_mem_arith_ODD_reads : forall (x : arith a),
  can_mem_arith x -> EVERY (fun r => ODD r) (arithReads x).
Proof.
  intros x H; destruct x; cbn [can_mem_arith] in H; try discriminate H;
    try (destruct r); cbn [can_mem_arith] in H; try discriminate H; cbn [arithReads EVERY]; bsplit;
    auto.
Qed.

(** Galette-only: the canonical register of a read, after [register_read]. *)
Lemma canon_read data r x :
  wf_data a data -> lookup r (to_canonical data) = None -> ~ is_true (EVEN x) -> x <> r ->
  is_true (ODD (canonicalRegs' r data x)) /\ canonicalRegs' r data x <> r /\
  lookup (canonicalRegs' r data x) (to_canonical (register_read data (canonicalRegs' r data x))) =
    Some (canonicalRegs' r data x) /\
  lookup r (to_canonical (register_read data (canonicalRegs' r data x))) = None.
Proof.
  intros W Hr Ex Nx. unfold canonicalRegs', canonicalRegs, lookup_any; cbn zeta.
  destruct (lookup x (to_canonical data)) as [v|] eqn:Ev.
  - destruct (wf_tc _ _ W _ _ Ev) as (Vv & _ & Ov).
    assert (Nv : v <> r) by (intros ->; congruence).
    rewrite (proj2 (N.eqb_neq v r) Nv).
    rewrite !lookup_register_read.
    destruct (decide (v = v /\ _ /\ _)) as [(_ & _ & Hd)|_]; [congruence|].
    destruct (decide (r = v /\ _ /\ _)) as [(Hd & _)|_]; [congruence|]. auto.
  - rewrite (proj2 (N.eqb_neq x r) Nx). rewrite !lookup_register_read.
    split; [apply (proj1 (ODD_not_EVEN x)), Ex|split; [exact Nx|]].
    destruct (decide (x = x /\ _ /\ _)) as [_|Hd]; [split; [reflexivity|]|].
    + destruct (decide (r = x /\ _ /\ _)) as [(Hd & _)|_]; [congruence|exact Hr].
    + exfalso; apply Hd; auto.
Qed.

Lemma lookup_insert_same {A} (t : num_map A) x (y : A) : lookup x (insert x y t) = Some y.
Proof. rewrite lookup_insert; destruct (decide (x = x)); [reflexivity|congruence]. Qed.

Lemma lookup_insert_other {A} (t : num_map A) x (y : A) r : r <> x -> lookup r (insert x y t) = lookup r t.
Proof. intros H; rewrite lookup_insert; destruct (decide (r = x)); [contradiction|reflexivity]. Qed.

Lemma get_var_set_var_same r (w : word_loc a) s : get_var r (set_var r w s) = Some w.
Proof. rewrite get_var_set_var; destruct (decide (r = r)); [reflexivity|congruence]. Qed.

Lemma get_var_set_var_other r r' (w : word_loc a) s : r' <> r -> get_var r' (set_var r w s) = get_var r' s.
Proof. intros H; rewrite get_var_set_var; destruct (decide (r' = r)); [contradiction|reflexivity]. Qed.

(** Galette-only: the hit arm shared by [add_to_data_aux], [add_to_data_const]
    and [add_to_load_aux]. *)
Lemma data_inv_hit data s r r' w :
  data_inv data s -> lookup r (to_canonical data) = None -> ~ is_true (EVEN r) ->
  lookup r' (to_canonical data) = Some r' -> get_var r' s = Some w ->
  data_inv {| to_canonical := insert r r' (to_canonical data);
              to_latest := insert r' r (to_latest data);
              gets_mem := gets_mem data; instrs_mem := instrs_mem data;
              loads_mem := loads_mem data |} (set_var r w s).
Proof.
  intros H Hr Er Hr' Gr'. destruct H as [W S].
  destruct (wf_tc _ _ W _ _ Hr') as (_ & _ & Or').
  assert (Ne : r' <> r) by (intros ->; congruence).
  assert (H1 : data_inv (with_to_canonical (insert r r' (to_canonical data)) data) (set_var r w s)).
  { apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto; split; auto|].
    split; [exact Hr|]. split; [rewrite lookup_insert_other by exact Ne; exact Hr'|].
    split; [apply (proj1 (ODD_not_EVEN r)), Er|]. split; [exact Or'|].
    rewrite get_var_set_var_same, get_var_set_var_other by exact Ne. symmetry; exact Gr'. }
  apply (data_inv_insert_to_latest (with_to_canonical (insert r r' (to_canonical data)) data) _ r' r).
  split; [exact H1|]. cbn [with_to_canonical to_canonical].
  split; [apply domain_lookup; exists r'; rewrite lookup_insert_other by exact Ne; exact Hr'|].
  split; [apply domain_lookup; exists r'; apply lookup_insert_same|].
  rewrite get_var_set_var_same, get_var_set_var_other by exact Ne. exact Gr'.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_const_correct" *)
Theorem add_to_data_const_correct : forall data s r (w : word a) data' p',
  data_inv data s /\ lookup r (to_canonical data) = None /\ ~ is_true (EVEN r) /\
  add_to_data_const data r w = (data', p') ->
  evaluate (p', s) = (None, set_var r (Word w) s) /\ data_inv data' (set_var r (Word w) s).
Proof.
  intros data s r w data' p' (H & Hr & Er & Ha); unfold add_to_data_const in Ha.
  assert (Ev : evaluate (Inst (asm.Const r w), s) = (None, set_var r (Word w) s))
    by (rewrite evaluate_Inst_eq; reflexivity).
  destruct (balanced_map.lookup listCmp _ (instrs_mem data)) as [r'|] eqn:El; inv_eqs;
    (split; [exact Ev|]).
  - pose proof (bm_lookup_mem _ _ _ El) as M.
    destruct H as [W S]. pose proof (wf_instrs _ _ W _ _ M) as Hr'.
    pose proof (si_const _ _ S _ _ _ M) as Gr'.
    apply data_inv_hit; auto; split; auto.
  - assert (Or : is_true (ODD r)) by (apply (proj1 (ODD_not_EVEN r)), Er).
    assert (H1 : data_inv (with_to_canonical (insert r r (to_canonical data)) data) (set_var r (Word w) s)).
    { apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto|].
      split; [exact Hr|]. split; [apply lookup_insert_same|]. split; [exact Or|]. split; [exact Or|].
      reflexivity. }
    assert (H2 : data_inv (with_instrs_mem (balanced_map.insert listCmp (instToNumList (asm.Const r w)) r
                   (instrs_mem (with_to_canonical (insert r r (to_canonical data)) data)))
                   (with_to_canonical (insert r r (to_canonical data)) data)) (set_var r (Word w) s)).
    { apply data_inv_insert_instrs_Const; split; [exact H1|]. split; [apply lookup_insert_same|].
      unfold set_var; cbn [locals set_locals]; apply lookup_insert_same. }
    assert (D : r IN domain (insert r r (to_canonical data)))
      by (apply domain_lookup; exists r; apply lookup_insert_same).
    exact (data_inv_insert_to_latest _ _ r r (conj H2 (conj D (conj D eq_refl)))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_LocValue_correct" *)
Theorem add_to_data_LocValue_correct : forall data s r l data' p',
  data_inv data s /\ lookup r (to_canonical data) = None /\ l IN domain (code s) /\
  add_to_data_aux data r [48; l] (LocValue r l) = (data', p') ->
  evaluate (p', s) = (None, set_var r (Loc l 0) s) /\ data_inv data' (set_var r (Loc l 0) s).
Proof.
  intros data s r l data' p' (H & Hr & Hl & Ha).
  apply (add_to_data_aux_correct data s r [48; l] (LocValue r l) (Loc l 0) data' p').
  split; [exact H|]. split; [exact Hr|]. split; [exact Ha|]. split.
  { rewrite evaluate_eqn; cbn [evaluate_body].
    destruct (classical_dec _) as [_|n]; [reflexivity|contradiction]. }
  split.
  { intros v Hv. destruct H as [_ S]. apply (si_loc _ _ S), bm_lookup_mem, Hv. }
  intros Er. apply data_inv_insert_instrs_LocValue; split.
  - apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto|].
    split; [exact Hr|]. split; [apply lookup_insert_same|].
    split; [apply (proj1 (ODD_not_EVEN r)), Er|]. split; [apply (proj1 (ODD_not_EVEN r)), Er|].
    reflexivity.
  - split; [apply lookup_insert_same|]. unfold set_var; cbn [locals set_locals];
      apply lookup_insert_same.
Qed.

Lemma word_exp_och_cong b x y s :
  get_var x s = get_var y s ->
  word_exp s (Op b [Var x; Lookup stackLang.CurrHeap]) = word_exp s (Op b [Var y; Lookup stackLang.CurrHeap]).
Proof. intros G; cbn [word_exp MAP List.map]; rewrite G; reflexivity. Qed.

Lemma word_exp_och_set_var b x r u s :
  x <> r ->
  word_exp (set_var r u s) (Op b [Var x; Lookup stackLang.CurrHeap]) =
  word_exp s (Op b [Var x; Lookup stackLang.CurrHeap]).
Proof.
  intros H; cbn [word_exp MAP List.map]; rewrite get_var_set_var_other by exact H; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_OpCurrHeap_correct" *)
Theorem add_to_data_OpCurrHeap_correct : forall data s b r1 r2 r2' w data' p',
  data_inv data s /\ lookup r1 (to_canonical data) = None /\ r2' = canonicalRegs' r1 data r2 /\
  ~ is_true (EVEN r2) /\ r2 <> r1 /\
  word_exp s (Op b [Var r2; Lookup stackLang.CurrHeap]) = Some w /\
  add_to_data_aux (register_read data r2') r1 (OpCurrHeapToNumList b r2') (OpCurrHeap b r1 r2) =
    (data', p') ->
  evaluate (p', s) = (None, set_var r1 w s) /\ data_inv data' (set_var r1 w s).
Proof.
  intros data s b r1 r2 r2' w data' p' (H & Hr1 & -> & Er2 & Ne & He & Ha).
  destruct (canon_read data r1 r2 (proj1 H) Hr1 Er2 Ne) as (O2 & Ne' & Hs & Hr1').
  set (r2' := canonicalRegs' r1 data r2) in *.
  assert (G2 : get_var r2' s = get_var r2 s) by (apply canonicalRegs'_correct, H).
  apply (add_to_data_aux_correct (register_read data r2') s r1 (OpCurrHeapToNumList b r2') (OpCurrHeap b r1 r2) w data' p').
  split; [apply data_inv_register_read, H|]. split; [exact Hr1'|]. split; [exact Ha|]. split.
  { rewrite evaluate_eqn; cbn [evaluate_body]. rewrite He; reflexivity. }
  split.
  { intros v Hv. destruct H as [_ S]. destruct (register_read_simps data r2') as (E1 & _).
    rewrite E1 in Hv. destruct (si_och _ _ S _ _ _ (bm_lookup_mem _ _ _ Hv)) as [w' [Hw' Hg]].
    rewrite (word_exp_och_cong b r2' r2 s G2), He in Hw'. inv_eqs; exact Hg. }
  intros Er1.
  assert (O1 : is_true (ODD r1)) by (apply (proj1 (ODD_not_EVEN r1)), Er1).
  apply (data_inv_insert_instrs_OpCurrHeap _ _ r1 b r2' w).
  split; [apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto;
          apply data_inv_register_read, H|]|].
  - split; [exact Hr1'|]. split; [apply lookup_insert_same|]. repeat (split; [exact O1|]).
    reflexivity.
  - cbn [with_to_canonical to_canonical]. split; [apply lookup_insert_same|].
    split; [rewrite lookup_insert_other by exact Ne'; exact Hs|].
    split; [rewrite word_exp_och_set_var by exact Ne'; rewrite (word_exp_och_cong b r2' r2 s G2); exact He|].
    apply get_var_set_var_same.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_load_aux_correct" *)
Theorem add_to_load_aux_correct : forall data s r i (p : prog a) w data' p',
  data_inv data s /\ lookup r (to_canonical data) = None /\
  add_to_load_aux data r i p = (data', p') /\
  evaluate (p, s) = (None, set_var r w s) /\
  (forall v, balanced_map.lookup listCmp i (loads_mem data) = Some v -> get_var v s = Some w) /\
  (~ is_true (EVEN r) ->
     data_inv (with_loads_mem (balanced_map.insert listCmp i r
                 (loads_mem (with_to_canonical (insert r r (to_canonical data)) data)))
                 (with_to_canonical (insert r r (to_canonical data)) data)) (set_var r w s)) ->
  evaluate (p', s) = (None, set_var r w s) /\ data_inv data' (set_var r w s).
Proof.
  intros data s r i p w data' p' (H & Hr & Ha & He & Hv & Hn); unfold add_to_load_aux in Ha.
  destruct (balanced_map.lookup listCmp i (loads_mem data)) as [r'|] eqn:El.
  - pose proof (Hv r' eq_refl) as Gr'. pose proof (get_var_lookup_any data s r' w H Gr') as Gk.
    destruct (EVEN r) eqn:Er; inv_eqs.
    + split; [apply evaluate_Move1, Gk|apply data_inv_set_var; auto].
    + split; [apply evaluate_Move1, Gk|].
      apply data_inv_hit; [exact H|exact Hr|unfold is_true; rewrite Er; intros Hf; discriminate Hf
                          |apply (wf_loads _ _ (proj1 H) _ _ (bm_lookup_mem _ _ _ El))|exact Gr'].
  - destruct (EVEN r) eqn:Er; inv_eqs.
    + split; [exact He|apply data_inv_set_var; auto].
    + split; [exact He|].
      specialize (Hn ltac:(intros Hf; discriminate Hf)).
      assert (D : r IN domain (insert r r (to_canonical data)))
        by (apply domain_lookup; exists r; apply lookup_insert_same).
      exact (data_inv_insert_to_latest _ _ r r (conj Hn (conj D (conj D eq_refl)))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_load_correct" *)
Theorem add_to_load_correct : forall data s op r a0 a' (ofs : word a) w data' p',
  data_inv data s /\ lookup r (to_canonical data) = None /\ a' = canonicalRegs' r data a0 /\
  ~ is_store op /\ ~ is_true (EVEN r) /\ ~ is_true (EVEN a0) /\ a0 <> r /\
  evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s) /\
  add_to_load_aux (register_read data a') r (loadToNumList op a' ofs)
    (Inst (Mem op r (Addr a0 ofs))) = (data', p') ->
  evaluate (p', s) = (None, set_var r w s) /\ data_inv data' (set_var r w s).
Proof.
  intros data s op r a0 a' ofs w data' p' (H & Hr & -> & Hs & Er & Ea & Ne & He & Ha).
  destruct (canon_read data r a0 (proj1 H) Hr Ea Ne) as (Oa & Ne' & Hself & Hr').
  set (a' := canonicalRegs' r data a0) in *.
  assert (G : lookup a' (locals s) = lookup a0 (locals s)) by (apply canonicalRegs'_correct, H).
  assert (He' : evaluate (Inst (Mem op r (Addr a' ofs)), s) = (None, set_var r w s))
    by (apply (evaluate_load_change_addr op r a0 a' ofs w s); auto).
  assert (Hall : forall r2, evaluate (Inst (Mem op r2 (Addr a' ofs)), s) = (None, set_var r2 w s))
    by (intros r2; apply (evaluate_load_any_dest op r a' ofs w s r2); auto).
  apply (add_to_load_aux_correct (register_read data a') s r (loadToNumList op a' ofs) (Inst (Mem op r (Addr a0 ofs))) w data' p').
  split; [apply data_inv_register_read, H|]. split; [exact Hr'|]. split; [exact Ha|].
  split; [exact He|]. split.
  { intros v Hv. destruct H as [_ S]. destruct (register_read_simps data a') as (_ & _ & _ & E1).
    rewrite E1 in Hv. destruct (si_loads _ _ S _ _ _ _ Hs (bm_lookup_mem _ _ _ Hv)) as [w' [Hw' Hl]].
    specialize (Hl r). rewrite He' in Hl. apply pair_equal_spec in Hl as [_ Hl].
    apply set_var_inj in Hl. subst; exact Hw'. }
  intros Er'.
  assert (O1 : is_true (ODD r)) by (apply (proj1 (ODD_not_EVEN r)), Er').
  apply (data_inv_insert_loads _ _ r op a' ofs w).
  split; [apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto;
          apply data_inv_register_read, H|]|].
  - split; [exact Hr'|]. split; [apply lookup_insert_same|]. repeat (split; [exact O1|]).
    reflexivity.
  - cbn [with_to_canonical to_canonical]. split; [apply lookup_insert_same|].
    split; [rewrite lookup_insert_other by exact Ne'; exact Hself|].
    split; [exact Hs|]. split; [apply get_var_set_var_same|].
    intros r2. apply (evaluate_load_set_var op r2 a' ofs r w w s); auto.
Qed.

Lemma EVERY_iff {A} (P : A -> bool) l : EVERY P l <-> forall x, In x l -> P x.
Proof.
  unfold is_true; rewrite EVERY_Forall, Forall_forall; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "in_names_set_insert_self" *)
Theorem in_names_set_insert_self : forall (x0 : arith a) tc x,
  in_names_set x0 tc -> in_names_set x0 (insert x x tc).
Proof.
  intros x0 tc x H; rewrite in_names_set_iff in *; intros r Hr.
  rewrite lookup_insert; destruct (decide (r = x)); [subst; reflexivity|auto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "in_names_set_register_reads" *)
Theorem in_names_set_register_reads : forall (x : arith a) data,
  EVERY (fun r => ODD r) (arithReads x) /\
  EVERY (fun w => bool_decide (lookup w (to_canonical data) = None \/
                               lookup w (to_canonical data) = Some w)) (arithReads x) ->
  in_names_set x (to_canonical (register_reads data (arithReads x))).
Proof.
  intros x data [H1 H2]; rewrite EVERY_iff in H1, H2. apply in_names_set_iff; intros r Hr.
  rewrite lookup_register_reads. specialize (H2 r Hr). apply bool_decide_spec in H2.
  destruct (decide _) as [_|Hd]; [reflexivity|].
  destruct H2 as [H2|H2]; [|exact H2]. exfalso; apply Hd. split; [unfold is_true; rewrite MEM_In; exact Hr|].
  split; [apply ODD_not_EVEN, H1, Hr|exact H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalArith_reads_self_or_fresh" *)
Theorem canonicalArith_reads_self_or_fresh : forall data (x : arith a),
  wf_data a data /\ can_mem_arith (canonicalArith data x) /\
  lookup (firstRegOfArith x) (to_canonical data) = None ->
  EVERY (fun w => bool_decide (lookup w (to_canonical data) = None \/
                               lookup w (to_canonical data) = Some w))
        (arithReads (canonicalArith data x)).
Proof.
  intros data x (W & Hc & Hr); apply EVERY_iff; intros w Hw; apply bool_decide_spec.
  destruct x; cbn [canonicalArith firstRegOfArith] in *; cbn [can_mem_arith] in Hc;
    try discriminate Hc; try (destruct r); cbn [canonicalImmReg' arithReads In] in *;
    try discriminate Hc;
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H end;
    subst;
    match goal with
    | |- context [canonicalRegs' ?r1 _ ?y] =>
        destruct (canonicalRegs'_self_or_fresh_wf data r1 y (conj W Hr)); auto
    | |- context [canonicalRegs _ ?y] => destruct (canonicalRegs_self_or_fresh_wf data y W); auto
    end.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "add_to_data_Arith_correct" *)
Theorem add_to_data_Arith_correct : forall data s (x x' : arith a) r w data' p',
  data_inv data s /\ lookup r (to_canonical data) = None /\ x' = canonicalArith data x /\
  can_mem_arith x' /\ ~ MEM r (arithReads x') /\ r = firstRegOfArith x /\
  evaluate (Inst (Arith x), s) = (None, set_var r w s) /\
  add_to_data (register_reads data (arithReads x')) r (Arith x') (Arith x) = (data', p') ->
  evaluate (p', s) = (None, set_var r w s) /\ data_inv data' (set_var r w s).
Proof.
  intros data s x x' r w data' p' (H & Hr & -> & Hc & Hm & -> & He & Ha). unfold add_to_data in Ha.
  set (x' := canonicalArith data x) in *.
  assert (E1 : evaluate (Inst (Arith x'), s) = (None, set_var (firstRegOfArith x') w s)).
  { unfold x'; rewrite firstRegOfArith_canonicalArith, !evaluate_Inst_eq, canonicalArith_correct
      by exact H. rewrite evaluate_Inst_eq in He; exact He. }
  pose proof (canonicalArith_reads_self_or_fresh data x (conj (proj1 H) (conj Hc Hr))) as SF.
  fold x' in SF.
  set (D := register_reads data (arithReads x')).
  assert (HD : data_inv D s) by (apply data_inv_register_reads, H).
  assert (Hin : in_names_set x' (to_canonical D))
    by (apply in_names_set_register_reads; split; [apply can_mem_arith_ODD_reads, Hc|exact SF]).
  assert (HrD : lookup (firstRegOfArith x) (to_canonical D) = None).
  { unfold D; rewrite lookup_register_reads. destruct (decide _) as [(Hd & _)|_]; [|exact Hr].
    exfalso; apply Hm; exact Hd. }
  assert (Fx : firstRegOfArith x' = firstRegOfArith x) by apply firstRegOfArith_canonicalArith.
  set (r := firstRegOfArith x) in *.
  apply (add_to_data_aux_correct D s r (instToNumList (Arith x')) (Inst (Arith x)) w data' p').
  split; [exact HD|]. split; [exact HrD|]. split; [exact Ha|]. split; [exact He|]. split.
  { intros v Hv. destruct H as [_ S]. destruct (register_reads_simps (arithReads x') data) as (E2 & _).
    unfold D in Hv; rewrite E2 in Hv. destruct (si_arith _ _ S _ _ (bm_lookup_mem _ _ _ Hv)) as [w' [Hw' Ea]].
    rewrite E1, Fx in Ea. apply pair_equal_spec in Ea as [_ Ea]. apply set_var_inj in Ea. subst; exact Hw'. }
  intros Er.
  assert (O1 : is_true (ODD r)) by (apply (proj1 (ODD_not_EVEN r)), Er).
  apply (data_inv_insert_instrs_Arith _ _ r x' w).
  split; [apply data_inv_insert_to_canonical; split; [apply data_inv_set_var; auto|]|].
  - split; [exact HrD|]. split; [apply lookup_insert_same|]. repeat (split; [exact O1|]).
    reflexivity.
  - cbn [with_to_canonical to_canonical]. split; [apply lookup_insert_same|].
    split; [exact Hc|]. split; [apply in_names_set_insert_self, Hin|].
    split; [apply get_var_set_var_same|].
    rewrite <- Fx. apply evaluate_arith_set_var; [split; [exact Hc|rewrite Fx; exact Hm]|].
    rewrite Fx in *; exact E1.
Qed.

(** *** Moves *)

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "MAP_FST_lemma" *)
Theorem MAP_FST_lemma : forall data (moves : list (N * N)),
  MAP FST (MAP (fun '(a0, b) => (a0, canonicalRegs data b)) moves) = MAP FST moves.
Proof. intros data moves; induction moves as [|[x y] l IH]; cbn; [reflexivity|]; cbn in IH; rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "MAP_SND_lemma" *)
Theorem MAP_SND_lemma : forall data s (moves : list (N * N)) x,
  get_vars (MAP SND moves) s = Some x /\ data_inv data s ->
  get_vars (MAP SND (MAP (fun '(a0, b) => (a0, canonicalRegs data b)) moves)) s = Some x.
Proof.
  intros data s moves; induction moves as [|[y z] l IH]; intros x [Hg H]; cbn in *; [exact Hg|].
  rewrite canonicalRegs_correct by exact H.
  destruct (get_var z s); [|discriminate Hg]. destruct (get_vars _ s) eqn:E; [|discriminate Hg].
  cbn in IH; rewrite (IH _ (conj eq_refl H)); exact Hg.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_map_insert0" *)
Theorem lookup_map_insert0 : forall {A} (m : num_map A) xs r,
  lookup r (map_insert xs m) = match ALOOKUP xs r with None => lookup r m | Some r' => Some r' end.
Proof.
  intros A m xs r; induction xs as [|[x y] xs IH]; cbn [map_insert ALOOKUP]; [reflexivity|].
  rewrite lookup_insert. destruct (decide (r = x)), (decide (x = r)); subst; try congruence; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_lemma" *)
Theorem get_set_vars_lemma : forall xs xs' x y s,
  ~ MEM x xs /\ ~ MEM y xs -> get_var x s = get_var y s ->
  get_var x (set_vars xs xs' s) = get_var y (set_vars xs xs' s).
Proof.
  induction xs as [|z xs IH]; intros [|v vs] x y s [Hx Hy] G; unfold set_vars in *;
    cbn [alist_insert] in *; try exact G.
  unfold get_var in *; cbn [locals set_locals] in *.
  rewrite MEM_iff in Hx, Hy; cbn [In] in Hx, Hy.
  rewrite !lookup_insert. destruct (decide (x = z)); [exfalso; auto|].
  destruct (decide (y = z)); [exfalso; auto|].
  pose proof (IH vs x y s) as T. cbn [locals set_locals] in T. apply T; [|exact G].
  split; apply MEM_iff; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_not_in" *)
Theorem get_set_vars_not_in : forall rs vs r s,
  ~ MEM r rs -> get_var r (set_vars rs vs s) = get_var r s.
Proof.
  induction rs as [|z rs IH]; intros [|v vs] r s H; unfold set_vars in *; cbn [alist_insert] in *;
    try (destruct s; reflexivity).
  unfold get_var in *; cbn [locals set_locals] in *. rewrite MEM_iff in H; cbn [In] in H.
  rewrite lookup_insert. destruct (decide (r = z)); [exfalso; auto|].
  pose proof (IH vs r s) as T; cbn [locals set_locals] in T. apply T, MEM_iff; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "MEM_FST_reduc" *)
Theorem MEM_FST_reduc : forall (moves : list (N * N)) r p_2,
  MEM (r, p_2) moves -> MEM r (MAP FST moves).
Proof.
  intros moves r p_2; unfold is_true; rewrite !MEM_In; intros H.
  apply in_map_iff; exists (r, p_2); auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_in" *)
Theorem get_set_vars_in : forall (moves : list (N * N)) r p_2 x s,
  MEM (r, p_2) moves -> ALL_DISTINCT (MAP FST moves) ->
  get_vars (MAP SND moves) s = Some x ->
  get_var r (set_vars (MAP FST moves) x s) = get_var p_2 s.
Proof.
  induction moves as [|[q w] moves IH]; intros r p_2 x s Hm Hd Hg; [discriminate Hm|].
  cbn [MAP List.map fst snd get_vars] in Hg.
  destruct (get_var w s) as [v|] eqn:Gw; [|discriminate Hg].
  destruct (get_vars (MAP SND moves) s) as [vs|] eqn:Gs; [|discriminate Hg]. inv_eqs.
  unfold set_vars, get_var in *; cbn [MAP List.map fst snd alist_insert locals set_locals] in *.
  rewrite lookup_insert. cbn [ALL_DISTINCT] in Hd; bsplit.
  unfold is_true in Hm; rewrite MEM_In in Hm; destruct Hm as [Hm|Hm].
  - injection Hm as -> ->. destruct (decide (r = r)); [congruence|congruence].
  - destruct (decide (r = q)) as [->|n].
    + exfalso. apply negb_true_iff in H. rewrite (MEM_FST_reduc moves q p_2) in H; [discriminate H|].
      unfold is_true; rewrite MEM_In; exact Hm.
    + pose proof (IH r p_2 vs s) as T; cbn [locals set_locals] in T.
      apply T; auto. unfold is_true; rewrite MEM_In; exact Hm.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "get_set_vars_in_2" *)
Theorem get_set_vars_in_2 : forall (moves : list (N * N)) r p_2 x' x data s,
  MEM (r, p_2) moves -> ALL_DISTINCT (MAP FST moves) ->
  lookup p_2 (to_canonical data) = Some x' ->
  get_vars (MAP SND (MAP (fun '(a0, b) => (a0, canonicalRegs data b)) moves)) s = Some x ->
  get_var r (set_vars (MAP FST moves) x s) = get_var x' s.
Proof.
  intros moves r p_2 x' x data s Hm Hd Hl Hg.
  rewrite <- (MAP_FST_lemma data moves).
  rewrite (get_set_vars_in _ r (canonicalRegs data p_2) x s); auto.
  - unfold canonicalRegs, lookup_any; rewrite Hl; reflexivity.
  - unfold is_true in *; rewrite MEM_In in *. apply in_map_iff; exists (r, p_2); auto.
  - rewrite MAP_FST_lemma; exact Hd.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "lookup_set_vars_not_in" *)
Theorem lookup_set_vars_not_in : forall (moves : list (N * N)) v (c0 : word a) x s,
  ~ MEM v (MAP FST moves) -> lookup v (locals s) = Some (Word c0) ->
  lookup v (locals (set_vars (MAP FST moves) x s)) = Some (Word c0).
Proof.
  intros moves v c0 x s H1 H2. pose proof (get_set_vars_not_in (MAP FST moves) x v s H1) as T.
  unfold get_var in T; rewrite T; exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "list_insert_insert" *)
Theorem list_insert_insert : forall l n (an : num_set),
  list_insert l (insert n tt an) = insert n tt (list_insert l an).
Proof.
  induction l as [|h l IH]; intros n an; cbn [list_insert]; [reflexivity|].
  rewrite <- IH. f_equal. rewrite insert_insert. destruct (decide (h = n)); subst;
    [rewrite insert_shadow|]; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_canonical_pair" *)
Theorem data_inv_insert_canonical_pair : forall data s x y tc tl,
  data_inv (with_to_latest tl (with_to_canonical tc data)) s /\ lookup x tc = None /\
  lookup y (insert x y tc) = Some y /\ is_true (ODD x) /\ is_true (ODD y) /\
  get_var x s = get_var y s ->
  data_inv (with_to_latest tl (with_to_canonical (insert x y tc) data)) s.
Proof.
  intros data s x y tc tl (H & H1 & H2 & H3 & H4 & H5).
  exact (data_inv_insert_to_canonical _ _ x y (conj H (conj H1 (conj H2 (conj H3 (conj H4 H5)))))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_insert_pair" *)
Theorem data_inv_insert_pair : forall data s x y tc tl,
  data_inv (with_to_latest tl (with_to_canonical tc data)) s /\ lookup x tc = None /\
  lookup y tc = Some y /\ is_true (ODD x) /\ is_true (ODD y) /\ get_var x s = get_var y s ->
  data_inv (with_to_latest (insert y x tl) (with_to_canonical (insert x y tc) data)) s.
Proof.
  intros data s x y tc tl (H & H1 & H2 & H3 & H4 & H5).
  assert (Ne : y <> x) by (intros ->; congruence).
  assert (H2' : lookup y (insert x y tc) = Some y) by (rewrite lookup_insert_other by exact Ne; exact H2).
  pose proof (data_inv_insert_canonical_pair data s x y tc tl
    (conj H (conj H1 (conj H2' (conj H3 (conj H4 H5)))))) as T.
  refine (data_inv_insert_to_latest _ _ y x (conj T (conj _ (conj _ (eq_sym H5)))));
    cbn [with_to_latest with_to_canonical to_canonical].
  - apply domain_lookup; exists y; rewrite lookup_insert_other by exact Ne; exact H2.
  - apply domain_lookup; exists y; apply lookup_insert_same.
Qed.

Lemma with_tl_tc_eta data :
  with_to_latest (to_latest data) (with_to_canonical (to_canonical data) data) = data.
Proof. destruct data; reflexivity. Qed.

Lemma ALOOKUP_None_In {B} (ps : list (N * B)) x : ~ In x (MAP FST ps) -> ALOOKUP ps x = None.
Proof.
  intros H; apply ALOOKUP_NONE. intros Hm; apply H. unfold is_true in Hm; rewrite MEM_In in Hm; exact Hm.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_move_pairs" *)
Theorem data_inv_move_pairs : forall (ps : list (N * N)) data s,
  data_inv data s /\ ALL_DISTINCT (MAP FST ps) /\
  EVERY (fun '(x, y) => bool_decide (lookup x (to_canonical data) = None /\
                                     lookup y (to_canonical data) = Some y /\
                                     is_true (ODD x) /\ get_var x s = get_var y s)) ps ->
  data_inv (with_to_latest (map_insert (MAP (fun '(a0, b) => (b, a0)) ps) (to_latest data))
              (with_to_canonical (map_insert ps (to_canonical data)) data)) s.
Proof.
  induction ps as [|[x y] ps IH]; intros data s (H & Hd & He).
  - cbn [map_insert MAP List.map]. rewrite with_tl_tc_eta; exact H.
  - cbn [map_insert MAP List.map] in *. cbn [ALL_DISTINCT EVERY] in Hd, He.
    apply andb_prop in Hd as [H3 H2]. apply andb_prop in He as [H0 H1].
    apply bool_decide_spec in H0 as (Hx & Hy & Ox & Gx).
    pose proof (IH data s (conj H (conj H2 H1))) as T.
    assert (Oy : is_true (ODD y)) by apply (wf_tc _ _ (proj1 H) _ _ Hy).
    assert (Nx : ~ In x (MAP FST ps)).
    { intros Hin; apply negb_true_iff in H3. cbn [FST fst] in H3. rewrite <- MEM_In in Hin. unfold is_true in Hin.
      rewrite Hin in H3; discriminate H3. }
    assert (Ny : ~ In y (MAP FST ps)).
    { intros Hin. apply in_map_iff in Hin as [[x' y'] [Ex Hin]]. cbn in Ex; subst x'.
      pose proof (proj1 (EVERY_iff _ _) H1 _ Hin) as H1'. cbn beta iota in H1'.
      apply bool_decide_spec in H1' as (Hy' & _). congruence. }
    apply data_inv_insert_pair; split; [exact T|].
    split; [rewrite lookup_map_insert0, ALOOKUP_None_In by exact Nx; exact Hx|].
    split; [rewrite lookup_map_insert0, ALOOKUP_None_In by exact Ny; exact Hy|].
    repeat (split; [assumption|]). exact Gx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "canonicalMoveRegs_lemma" *)
Theorem canonicalMoveRegs_lemma : forall data s (rs : list (N * N)) vs,
  data_inv data s /\ ALL_DISTINCT (MAP FST rs) /\ get_vars (MAP SND rs) s = Some vs ->
  data_inv (canonicalMoveRegs data rs) (set_vars (MAP FST rs) vs s).
Proof.
  intros data s rs vs (H & Hd & Hg); unfold canonicalMoveRegs; cbn zeta.
  set (D := register_reads data (MAP SND rs)).
  destruct (EVERY (keep_data (to_canonical D)) (MAP FST rs)) eqn:Ek; [|apply data_inv_empty].
  assert (HD : data_inv D s) by apply data_inv_register_reads, H.
  assert (Unt : forall x, In x (MAP FST rs) -> lookup x (to_canonical D) = None).
  { intros x Hx. pose proof (proj1 (EVERY_iff _ _) Ek x Hx) as Ek'. unfold keep_data in Ek'.
    destruct (lookup x (to_canonical D)); [discriminate Ek'|reflexivity]. }
  assert (HD' : data_inv D (set_vars (MAP FST rs) vs s)).
  { apply data_inv_set_vars; [|exact HD]. apply EVERY_iff; intros x Hx; apply bool_decide_spec; auto. }
  set (xs := FILTER (fun '(a0, b) => negb (EVEN a0) && negb (EVEN b)) rs).
  set (ys := MAP (fun '(a0, b) => (a0, canonicalRegs D b)) xs).
  assert (Hxs : forall x y, In (x, y) xs -> In (x, y) rs /\ is_true (ODD x) /\ is_true (ODD y)).
  { intros x y Hin. unfold xs in Hin; apply filter_In in Hin as [Hin Hp].
    apply andb_prop in Hp as [P1 P2]. rewrite <- N.negb_even in *. auto. }
  assert (Self : forall y, In y (MAP SND rs) -> is_true (ODD y) ->
                 lookup (canonicalRegs D y) (to_canonical D) = Some (canonicalRegs D y)).
  { intros y Hy Oy. unfold canonicalRegs, lookup_any.
    destruct (lookup y (to_canonical D)) as [v|] eqn:E; [exact (proj1 (wf_tc _ _ (proj1 HD) _ _ E))|].
    exfalso. unfold D in E; rewrite lookup_register_reads in E.
    destruct (decide _) as [_|Hn]; [discriminate E|]. apply Hn.
    split; [unfold is_true; rewrite MEM_In; exact Hy|]. split; [apply ODD_not_EVEN, Oy|].
    exact E. }
  pose proof (data_inv_move_pairs ys D (set_vars (MAP FST rs) vs s)) as T.
  apply T; clear T. split; [exact HD'|]. split.
  - unfold ys; rewrite MAP_FST_lemma. unfold xs. apply ALL_DISTINCT_MAP_FST_FILTER, Hd.
  - apply EVERY_iff; intros [x y'] Hin. unfold ys in Hin. apply in_map_iff in Hin as [[x0 y] [Ex Hin]].
    injection Ex as <- <-. apply bool_decide_spec.
    destruct (Hxs x0 y Hin) as (Hr & Ox & Oy).
    assert (Inx : In x0 (MAP FST rs)) by (apply in_map_iff; exists (x0, y); auto).
    assert (Iny : In y (MAP SND rs)) by (apply in_map_iff; exists (x0, y); auto).
    pose proof (Self y Iny Oy) as Sy.
    assert (Ny : ~ In (canonicalRegs D y) (MAP FST rs)) by (intros Hc; rewrite (Unt _ Hc) in Sy; discriminate Sy).
    split; [apply Unt, Inx|]. split; [exact Sy|]. split; [exact Ox|].
    rewrite (get_set_vars_in rs x0 y vs s); [|unfold is_true; rewrite MEM_In; exact Hr|exact Hd|exact Hg].
    rewrite get_set_vars_not_in by (apply MEM_iff; exact Ny).
    symmetry; apply canonicalRegs_correct, HD.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "if_eq_rw" *)
Theorem if_eq_rw : forall {A} (x y : A), (if decide (x = y) then y else x) = x.
Proof. intros A x y; destruct (decide (x = y)); auto. Qed.

Lemma set_var_clock r w c0 td s :
  set_termdep td (set_clock c0 (set_var r w s)) = set_var r w (set_termdep td (set_clock c0 s)).
Proof. destruct s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_clock" *)
Theorem evaluate_arith_clock : forall (x : arith a) w s c0 td,
  can_mem_arith x ->
  (evaluate (Inst (Arith x), set_termdep td (set_clock c0 s)) =
     (None, set_termdep td (set_clock c0 (set_var (firstRegOfArith x) w s))) <->
   evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s)).
Proof.
  intros x w s c0 td H; rewrite set_var_clock, !eval_arith_iff by exact H.
  rewrite (arith_val_agree x (set_termdep td (set_clock c0 s)) s H); [reflexivity|].
  intros; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_clock" *)
Theorem evaluate_load_clock : forall op r a0 ofs w s c0 td,
  ~ is_store op ->
  (evaluate (Inst (Mem op r (Addr a0 ofs)), set_termdep td (set_clock c0 s)) =
     (None, set_termdep td (set_clock c0 (set_var r w s))) <->
   evaluate (Inst (Mem op r (Addr a0 ofs)), s) = (None, set_var r w s)).
Proof.
  intros op r a0 ofs w s c0 td H; rewrite set_var_clock, !eval_load_iff by exact H.
  rewrite (load_val_agree op a0 ofs (set_termdep td (set_clock c0 s)) s); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "data_inv_clock" *)
Theorem data_inv_clock : forall data s c0 td,
  data_inv data s -> data_inv data (set_termdep td (set_clock c0 s)).
Proof.
  intros data s c0 td H; eapply data_inv_state_agree; split; [exact H|]; repeat split.
Qed.

End DataInv.

(** ** Well-formedness of the knowledge [word_cse] computes *)

Section WF2.
Context {a : N}.

Lemma wf_hit data r r' :
  wf_data a data -> lookup r (to_canonical data) = None -> ~ is_true (EVEN r) ->
  lookup r' (to_canonical data) = Some r' ->
  wf_data a {| to_canonical := insert r r' (to_canonical data);
               to_latest := insert r' r (to_latest data);
               gets_mem := gets_mem data; instrs_mem := instrs_mem data;
               loads_mem := loads_mem data |}.
Proof.
  intros W Hr Er Hr'. destruct (wf_tc _ _ W _ _ Hr') as (_ & _ & Or').
  assert (Ne : r' <> r) by (intros ->; congruence).
  assert (W1 : wf_data a (with_to_canonical (insert r r' (to_canonical data)) data)).
  { apply wf_data_insert_to_canonical; split; [exact W|]. split; [exact Hr|].
    split; [rewrite lookup_insert_other by exact Ne; exact Hr'|].
    split; [apply (proj1 (ODD_not_EVEN r)), Er|exact Or']. }
  refine (wf_data_insert_to_latest _ r' r (conj W1 (conj _ _))); cbn [with_to_canonical to_canonical].
  - apply domain_lookup; exists r'; rewrite lookup_insert_other by exact Ne; exact Hr'.
  - apply domain_lookup; exists r'; apply lookup_insert_same.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_add_to_data_aux" *)
Theorem wf_add_to_data_aux : forall data r i (p : prog a) data' p',
  wf_data a data /\ lookup r (to_canonical data) = None /\
  add_to_data_aux data r i p = (data', p') /\
  (~ is_true (EVEN r) ->
     wf_data a (with_instrs_mem (balanced_map.insert listCmp i r
                 (instrs_mem (with_to_canonical (insert r r (to_canonical data)) data)))
                 (with_to_canonical (insert r r (to_canonical data)) data))) ->
  wf_data a data'.
Proof.
  intros data r i p data' p' (W & Hr & Ha & Hn); unfold add_to_data_aux in Ha.
  destruct (balanced_map.lookup listCmp i (instrs_mem data)) as [r'|] eqn:El;
    destruct (EVEN r) eqn:Er; inv_eqs; try exact W.
  - apply wf_hit; [exact W|exact Hr|unfold is_true; rewrite Er; intros Hf; discriminate Hf|].
    apply (wf_instrs _ _ W _ _ (bm_lookup_mem _ _ _ El)).
  - specialize (Hn ltac:(intros Hf; discriminate Hf)).
    assert (D : r IN domain (insert r r (to_canonical data)))
      by (apply domain_lookup; exists r; apply lookup_insert_same).
    exact (wf_data_insert_to_latest _ r r (conj Hn (conj D D))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_add_to_data_const" *)
Theorem wf_add_to_data_const : forall data r (w : word a) data' p',
  wf_data a data /\ lookup r (to_canonical data) = None /\ ~ is_true (EVEN r) /\
  add_to_data_const data r w = (data', p') ->
  wf_data a data'.
Proof.
  intros data r w data' p' (W & Hr & Er & Ha); unfold add_to_data_const in Ha.
  destruct (balanced_map.lookup listCmp _ (instrs_mem data)) as [r'|] eqn:El; inv_eqs.
  - apply wf_hit; auto. apply (wf_instrs _ _ W _ _ (bm_lookup_mem _ _ _ El)).
  - assert (Or : is_true (ODD r)) by (apply (proj1 (ODD_not_EVEN r)), Er).
    assert (W1 : wf_data a (with_to_canonical (insert r r (to_canonical data)) data))
      by (apply wf_data_insert_to_canonical; repeat (split; [eauto|]); [apply lookup_insert_same|]; exact Or).
    assert (W2 := wf_data_insert_instrs_Const _ r r w (conj W1 (lookup_insert_same _ _ _))).
    assert (D : r IN domain (insert r r (to_canonical data)))
      by (apply domain_lookup; exists r; apply lookup_insert_same).
    exact (wf_data_insert_to_latest _ r r (conj W2 (conj D D))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_add_to_load_aux" *)
Theorem wf_add_to_load_aux : forall data r i (p : prog a) data' p',
  wf_data a data /\ lookup r (to_canonical data) = None /\
  add_to_load_aux data r i p = (data', p') /\
  (~ is_true (EVEN r) ->
     wf_data a (with_loads_mem (balanced_map.insert listCmp i r
                 (loads_mem (with_to_canonical (insert r r (to_canonical data)) data)))
                 (with_to_canonical (insert r r (to_canonical data)) data))) ->
  wf_data a data'.
Proof.
  intros data r i p data' p' (W & Hr & Ha & Hn); unfold add_to_load_aux in Ha.
  destruct (balanced_map.lookup listCmp i (loads_mem data)) as [r'|] eqn:El;
    destruct (EVEN r) eqn:Er; inv_eqs; try exact W.
  - apply wf_hit; [exact W|exact Hr|unfold is_true; rewrite Er; intros Hf; discriminate Hf|].
    apply (wf_loads _ _ W _ _ (bm_lookup_mem _ _ _ El)).
  - specialize (Hn ltac:(intros Hf; discriminate Hf)).
    assert (D : r IN domain (insert r r (to_canonical data)))
      by (apply domain_lookup; exists r; apply lookup_insert_same).
    exact (wf_data_insert_to_latest _ r r (conj Hn (conj D D))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_data_move_pairs" *)
Theorem wf_data_move_pairs : forall (ps : list (N * N)) data,
  wf_data a data /\
  EVERY (fun '(x, y) => bool_decide (lookup x (to_canonical data) = None /\
                                     lookup y (to_canonical data) = Some y /\
                                     is_true (ODD x) /\ is_true (ODD y))) ps ->
  wf_data a (with_to_latest (map_insert (MAP (fun '(a0, b) => (b, a0)) ps) (to_latest data))
               (with_to_canonical (map_insert ps (to_canonical data)) data)).
Proof.
  intros ps data [W He].
  assert (P : forall x y, In (x, y) ps -> lookup x (to_canonical data) = None /\
                lookup y (to_canonical data) = Some y /\ is_true (ODD x) /\ is_true (ODD y)).
  { intros x y Hin. pose proof (proj1 (EVERY_iff _ _) He _ Hin) as T. cbn beta iota in T.
    apply bool_decide_spec in T; exact T. }
  assert (Mono : forall r v, lookup r (to_canonical data) = Some v ->
                 lookup r (map_insert ps (to_canonical data)) = Some v).
  { intros r v Hr. rewrite lookup_map_insert0. destruct (ALOOKUP ps r) as [v'|] eqn:E; [|exact Hr].
    apply ALOOKUP_In, P in E as (E & _). congruence. }
  assert (Snd : forall x y, In (x, y) ps -> lookup y (map_insert ps (to_canonical data)) = Some y)
    by (intros x y Hin; apply Mono, (P x y Hin)).
  assert (Dom : forall r, r IN domain (to_canonical data) -> r IN domain (map_insert ps (to_canonical data))).
  { intros r Hr; apply domain_lookup in Hr as [v Hv]; apply domain_lookup; eauto. }
  destruct W; constructor; cbn [with_to_latest with_to_canonical to_canonical to_latest gets_mem
    instrs_mem loads_mem]; auto.
  - intros r v Hr. rewrite lookup_map_insert0 in Hr. destruct (ALOOKUP ps r) as [v'|] eqn:E.
    + inv_eqs. apply ALOOKUP_In in E. destruct (P _ _ E) as (_ & _ & O1 & O2). split; eauto.
    + destruct (wf_tc0 _ _ Hr) as (A & B & C). auto.
  - intros r v Hr. rewrite lookup_map_insert0 in Hr.
    destruct (ALOOKUP (MAP (fun '(a0, b) => (b, a0)) ps) r) as [v'|] eqn:E.
    + inv_eqs. apply ALOOKUP_In, in_map_iff in E as [[x y] [Ex Hin]]. injection Ex as <- <-.
      split; apply domain_lookup; [exists y; eapply Snd; eauto|].
      rewrite lookup_map_insert0. destruct (ALOOKUP ps x) as [z|] eqn:Ez; [eauto|].
      exfalso. apply ALOOKUP_NONE in Ez. apply Ez. unfold is_true; rewrite MEM_In.
      apply in_map_iff; exists (x, y); auto.
    + destruct (wf_tl0 _ _ Hr); auto.
  - intros k v Hk; apply Mono; eauto.
  - intros x0 v Hk. destruct (wf_arith0 _ _ Hk) as [Hn Hc]; split; [|exact Hc].
    apply in_names_set_iff; intros r Hr. apply Mono, (proj1 (in_names_set_iff _ _) Hn), Hr.
  - intros op src v Hk; apply Mono; eauto.
  - intros x0 v Hk; apply Mono; eauto.
  - intros k v Hk; apply Mono; eauto.
  - intros op a0 ofs v Hk; apply Mono; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "wf_canonicalMoveRegs" *)
Theorem wf_canonicalMoveRegs : forall data (rs : list (N * N)),
  wf_data a data -> wf_data a (canonicalMoveRegs data rs).
Proof.
  intros data rs W; unfold canonicalMoveRegs; cbn zeta.
  set (D := register_reads data (MAP SND rs)).
  destruct (EVERY (keep_data (to_canonical D)) (MAP FST rs)) eqn:Ek; [|apply wf_data_empty].
  assert (WD : wf_data a D) by apply wf_data_register_reads, W.
  assert (Unt : forall x, In x (MAP FST rs) -> lookup x (to_canonical D) = None).
  { intros x Hx. pose proof (proj1 (EVERY_iff _ _) Ek x Hx) as Ek'. unfold keep_data in Ek'.
    destruct (lookup x (to_canonical D)); [discriminate Ek'|reflexivity]. }
  apply wf_data_move_pairs; split; [exact WD|].
  apply EVERY_iff; intros [x y'] Hin. apply in_map_iff in Hin as [[x0 y] [Ex Hin]].
  injection Ex as <- <-. apply filter_In in Hin as [Hin Hp]. apply andb_prop in Hp as [P1 P2].
  rewrite <- !N.negb_even in *. apply bool_decide_spec.
  assert (Iny : In y (MAP SND rs)) by (apply in_map_iff; exists (x0, y); auto).
  assert (Sy : lookup (canonicalRegs D y) (to_canonical D) = Some (canonicalRegs D y)).
  { unfold canonicalRegs, lookup_any.
    destruct (lookup y (to_canonical D)) as [v|] eqn:E; [exact (proj1 (wf_tc _ _ WD _ _ E))|].
    exfalso. unfold D in E; rewrite lookup_register_reads in E.
    destruct (decide _) as [_|Hn]; [discriminate E|]. apply Hn.
    split; [unfold is_true; rewrite MEM_In; exact Iny|]. split; [apply ODD_not_EVEN; exact P2|].
    exact E. }
  split; [apply Unt; apply in_map_iff; exists (x0, y); auto|]. split; [exact Sy|].
  split; [exact P1|]. exact (proj2 (proj2 (wf_tc _ _ WD _ _ Sy))).
Qed.

Lemma lookup_invalidate_data data n : lookup n (to_canonical (invalidate_data data n)) = None.
Proof.
  unfold invalidate_data, keep_data. destruct (lookup n (to_canonical data)) eqn:E; cbn [IS_NONE];
    [reflexivity|exact E].
Qed.

Lemma ALOOKUP_FILTER' (l : list (stackLang.store_name * N)) x :
  ALOOKUP (FILTER (fun '(m, n) => negb (bool_decide (m = x))) l) x = None.
Proof.
  induction l as [|[m n] l IH]; cbn [FILTER filter]; [reflexivity|].
  destruct (bool_decide (m = x)) eqn:E; cbn [negb]; [exact IH|].
  cbn [ALOOKUP]. destruct (decide (m = x)) as [->|]; [rewrite bd_true in E by reflexivity; discriminate E|exact IH].
Qed.

Lemma firstRegOfArith_writes (x : arith a) : In (firstRegOfArith x) (arithWrites x).
Proof. destruct x; cbn; auto. Qed.

(** Galette-only: [word_cseInst] keeps the knowledge well formed. *)
Lemma wf_word_cseInst data (i : asm.inst a) :
  wf_data a data -> wf_data a (FST (word_cseInst data i)).
Proof.
  intros W; destruct i as [|r w|x|m r [a0 ofs]|f]; cbn [word_cseInst]; cbn zeta.
  - exact W.
  - pose proof (wf_data_invalidate data r W) as W0.
    destruct (EVEN r) eqn:Er; [exact W0|].
    destruct (add_to_data_const (invalidate_data data r) r w) as [d' p'] eqn:E; cbn [FST].
    apply (wf_add_to_data_const (invalidate_data data r) r w d' p').
    split; [exact W0|]. split; [apply lookup_invalidate_data|].
    split; [unfold is_true; rewrite Er; intros Hf; discriminate Hf|exact E].
  - set (D0 := invalidate_regs data (arithWrites x)).
    assert (W0 : wf_data a D0) by apply wf_data_invalidate_regs, W.
    assert (H0 : lookup (firstRegOfArith x) (to_canonical D0) = None)
      by (apply lookup_invalidate_regs; unfold is_true; rewrite MEM_In; apply firstRegOfArith_writes).
    set (x' := canonicalArith D0 x).
    destruct (can_mem_arith x' && negb (MEM (firstRegOfArith x) (arithReads x'))) eqn:G; [|exact W0].
    apply andb_prop in G as [Gc Gm]. apply negb_true_iff in Gm.
    unfold add_to_data. set (D1 := register_reads D0 (arithReads x')).
    assert (W1 : wf_data a D1) by apply wf_data_register_reads, W0.
    assert (H1 : lookup (firstRegOfArith x) (to_canonical D1) = None).
    { unfold D1; rewrite lookup_register_reads. destruct (decide _) as [(Hd & _)|_]; [|exact H0].
      rewrite Gm in Hd; discriminate Hd. }
    assert (N1 : in_names_set x' (to_canonical D1)).
    { apply in_names_set_register_reads; split; [apply can_mem_arith_ODD_reads, Gc|].
      apply canonicalArith_reads_self_or_fresh; repeat (split; auto). }
    destruct (add_to_data_aux D1 (firstRegOfArith x) (instToNumList (Arith x')) (Inst (Arith x)))
      as [d' p'] eqn:E; cbn [FST].
    apply (wf_add_to_data_aux D1 (firstRegOfArith x) (instToNumList (Arith x')) (Inst (Arith x)) d' p').
    split; [exact W1|]. split; [exact H1|]. split; [exact E|]. intros Er.
    apply wf_data_insert_instrs_Arith. split.
    + apply wf_data_insert_to_canonical. split; [exact W1|]. split; [exact H1|].
      split; [apply lookup_insert_same|]. split; apply (proj1 (ODD_not_EVEN _)), Er.
    + cbn [with_to_canonical to_canonical]. split; [apply lookup_insert_same|].
      split; [exact Gc|apply in_names_set_insert_self, N1].
  - destruct (is_store m) eqn:Es; [apply wf_data_loads_wipe, W|].
    set (D0 := invalidate_data data r).
    assert (W0 : wf_data a D0) by apply wf_data_invalidate, W.
    assert (H0 : lookup r (to_canonical D0) = None) by apply lookup_invalidate_data.
    destruct (EVEN r || EVEN a0 || (a0 =? r)) eqn:G; [exact W0|].
    apply orb_false_iff in G as [G G3]. apply orb_false_iff in G as [G1 G2].
    apply N.eqb_neq in G3.
    destruct (canon_read D0 r a0 W0 H0 ltac:(rewrite G2; intros Hf; discriminate Hf) G3)
      as (Oa & Ne & Hs & Hr).
    set (a' := canonicalRegs' r D0 a0) in *.
    assert (W1 : wf_data a (register_read D0 a')) by apply wf_data_register_read, W0.
    destruct (add_to_load_aux (register_read D0 a') r (loadToNumList m a' ofs) (Inst (Mem m r (Addr a0 ofs))))
      as [d' p'] eqn:E; cbn [FST].
    apply (wf_add_to_load_aux (register_read D0 a') r (loadToNumList m a' ofs) (Inst (Mem m r (Addr a0 ofs))) d' p').
    split; [exact W1|]. split; [exact Hr|]. split; [exact E|]. intros Er.
    apply wf_data_insert_loads. split.
    + apply wf_data_insert_to_canonical. split; [exact W1|]. split; [exact Hr|].
      split; [apply lookup_insert_same|]. split; apply (proj1 (ODD_not_EVEN _)), Er.
    + cbn [with_to_canonical to_canonical]. split; [apply lookup_insert_same|].
      rewrite lookup_insert_other by exact Ne; exact Hs.
  - apply wf_data_invalidate_regs, W.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_wf_data" *)
Theorem word_cse_wf_data : forall (p : prog a) data,
  wf_data a data -> wf_data a (FST (word_cse data p)).
Proof.
  intros p; induction p using prog_nested_ind; intros data W; cbn [word_cse]; cbn zeta;
    try exact W; try apply wf_data_empty.
  - (* Move *) apply wf_canonicalMoveRegs, W.
  - (* Inst *) pose proof (wf_word_cseInst data i W) as T.
    destruct (word_cseInst data i); exact T.
  - (* Get *)
    set (D0 := invalidate_data data v).
    assert (W0 : wf_data a D0) by apply wf_data_invalidate, W.
    assert (H0 : lookup v (to_canonical D0) = None) by apply lookup_invalidate_data.
    destruct (ALOOKUP (gets_mem D0) n) as [k|] eqn:Ek; destruct (EVEN v) eqn:Ev; cbn [FST];
      try exact W0.
    + apply wf_hit; [exact W0|exact H0|unfold is_true; rewrite Ev; intros Hf; discriminate Hf|].
      apply (wf_gets _ _ W0 _ _ Ek).
    + apply wf_data_insert_gets. split; [exact W0|]. split; [exact H0|].
      split; [apply (proj1 (ODD_not_EVEN v)); unfold is_true; rewrite Ev; intros Hf; discriminate Hf|exact Ek].
  - (* Set *)
    destruct (decide (v = stackLang.CurrHeap)); cbn [FST]; [apply wf_data_empty|].
    pose proof (wf_data_filter_gets data v W) as WF. unfold with_gets_mem in WF.
    destruct (dest_Var e) as [v0|] eqn:Ed; [destruct (EVEN v0) eqn:Ev|]; cbn [FST];
      try exact WF.
    assert (O0 : is_true (ODD v0))
      by (apply (proj1 (ODD_not_EVEN v0)); unfold is_true; rewrite Ev; intros Hf; discriminate Hf).
    pose proof (wf_data_reinsert_canonical data v0 (conj W O0)) as W1.
    pose proof (wf_data_filter_gets _ v W1) as W2.
    refine (wf_data_cons_gets _ v (canonicalRegs data v0) (conj W2 (conj _ _)));
      cbn [with_gets_mem with_to_canonical to_canonical gets_mem].
    + rewrite ALOOKUP_FILTER'. reflexivity.
    + unfold canonicalRegs, lookup_any. destruct (lookup v0 (to_canonical data)) as [k|] eqn:E0.
      * rewrite lookup_insert. destruct (decide (k = v0)); [subst; first [reflexivity|apply lookup_insert_same]|].
        exact (proj1 (wf_tc _ _ W _ _ E0)).
      * apply lookup_insert_same.
  - (* Store *) apply wf_data_loads_wipe, W.
  - (* MustTerminate *)
    specialize (IHp data W). destruct (word_cse data p); exact IHp.
  - (* Seq *)
    specialize (IHp1 data W). destruct (word_cse data p1) as [d1 q1]; cbn [FST] in IHp1.
    specialize (IHp2 d1 IHp1). destruct (word_cse d1 p2); exact IHp2.
  - (* If *)
    specialize (IHp1 data W). specialize (IHp2 data W).
    destruct (word_cse data p1) as [d1 q1], (word_cse data p2) as [d2 q2]; cbn [FST] in *.
    apply wf_data_merge; auto.
  - (* Loop *) destruct (word_cse empty_data p); apply wf_data_empty.
  - (* StoreConsts *) apply wf_data_loads_wipe, wf_data_invalidate_regs, W.
  - (* OpCurrHeap *)
    set (D0 := invalidate_data data n1).
    assert (W0 : wf_data a D0) by apply wf_data_invalidate, W.
    assert (H0 : lookup n1 (to_canonical D0) = None) by apply lookup_invalidate_data.
    destruct (EVEN n2 || (n2 =? n1)) eqn:G; [exact W0|].
    apply orb_false_iff in G as [G1 G2]. apply N.eqb_neq in G2.
    destruct (canon_read D0 n1 n2 W0 H0 ltac:(rewrite G1; intros Hf; discriminate Hf) G2)
      as (O2 & Ne & Hs & Hr).
    set (r2' := canonicalRegs' n1 D0 n2) in *.
    destruct (add_to_data_aux (register_read D0 r2') n1 (OpCurrHeapToNumList b r2') (OpCurrHeap b n1 n2))
      as [d' p'] eqn:E; cbn [FST].
    apply (wf_add_to_data_aux (register_read D0 r2') n1 (OpCurrHeapToNumList b r2') (OpCurrHeap b n1 n2) d' p').
    split; [apply wf_data_register_read, W0|]. split; [exact Hr|]. split; [exact E|]. intros Er.
    apply wf_data_insert_instrs_OpCurrHeap. split.
    + apply wf_data_insert_to_canonical. split; [apply wf_data_register_read, W0|]. split; [exact Hr|].
      split; [apply lookup_insert_same|]. split; apply (proj1 (ODD_not_EVEN _)), Er.
    + cbn [with_to_canonical to_canonical]. split; [apply lookup_insert_same|].
      rewrite lookup_insert_other by exact Ne; exact Hs.
  - (* LocValue *)
    set (D0 := invalidate_data data r).
    assert (W0 : wf_data a D0) by apply wf_data_invalidate, W.
    assert (H0 : lookup r (to_canonical D0) = None) by apply lookup_invalidate_data.
    destruct (add_to_data_aux D0 r [48; l] (LocValue r l)) as [d' p'] eqn:E; cbn [FST].
    apply (wf_add_to_data_aux D0 r [48; l] (LocValue r l) d' p').
    split; [exact W0|]. split; [exact H0|]. split; [exact E|]. intros Er.
    apply wf_data_insert_instrs_LocValue. split.
    + apply wf_data_insert_to_canonical. split; [exact W0|]. split; [exact H0|].
      split; [apply lookup_insert_same|]. split; apply (proj1 (ODD_not_EVEN _)), Er.
    + apply lookup_insert_same.
  - (* ShareInst *)
    destruct (is_store op); cbn [FST]; [exact W|apply wf_data_invalidate, W].
Qed.

End WF2.

(** ** Correctness *)

Section Correct.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types s : state.

(** Galette-only: an update of untracked registers (and nothing that the
    invariant reads) preserves it. *)
Lemma data_inv_frame data s s' (ws : list N) :
  data_inv data s -> (forall w, In w ws -> lookup w (to_canonical data) = None) ->
  (forall r, ~ In r ws -> lookup r (locals s') = lookup r (locals s)) ->
  store s' = store s -> memory s' = memory s -> mdomain s' = mdomain s -> be s' = be s ->
  data_inv data s'.
Proof.
  intros [W S] Hw Hl Hs Hm Hd Hb; split; [exact W|].
  eapply sem_inv_agree; eauto.
  - intros r Hr; apply Hl. intros Hin; apply (not_in_dom _ _ (Hw r Hin) Hr).
  - rewrite Hs; reflexivity.
  - intros; rewrite Hs; reflexivity.
Qed.

(** Galette-only: the registers an instruction may write. *)
Definition inst_writes (i : asm.inst a) : list N :=
  match i with
  | asm.Const r _ => [r]
  | Arith x => arithWrites x
  | Mem op r _ => if is_store op then [] else [r]
  | FP x => fpWrites x
  | _ => []
  end.

Definition is_mem_store (i : asm.inst a) : bool :=
  match i with Mem op _ _ => is_store op | _ => false end.

Ltac st_simp :=
  unfold set_var, set_fp_var, set_memory, set_locals, set_fp_regs in *;
  cbn [locals store memory mdomain be] in *.

Lemma inst_frame (i : asm.inst a) s s' :
  inst i s = Some s' ->
  (forall r, ~ In r (inst_writes i) -> lookup r (locals s') = lookup r (locals s)) /\
  store s' = store s /\ mdomain s' = mdomain s /\ be s' = be s /\
  (is_mem_store i = false -> memory s' = memory s).
Proof.
  intros H; destruct i as [|r w|x|m r [a0 ofs]|f]; cbn [inst] in H; unfold assign in H;
    try destruct x; try destruct f; try destruct m; cbn zeta in H;
    repeat (case_split; inv_eqs); inv_eqs; try discriminate.
  all: unfold mem_store in *; repeat (case_split; inv_eqs); inv_eqs; try discriminate.
  all: st_simp; cbn [inst_writes arithWrites fpWrites is_mem_store is_store In];
    repeat split; try reflexivity; try (intros; discriminate).
  all: intros r' Hr'; rewrite ?lookup_insert;
    repeat (destruct (decide _); [exfalso; apply Hr'; subst; cbn; tauto|]); reflexivity.
Qed.

Lemma inst_store_frame (i : asm.inst a) s s' :
  inst i s = Some s' -> is_mem_store i = true -> exists m, s' = set_memory m s.
Proof.
  intros H Hs; destruct i as [| | |m r [a0 ofs]|]; try discriminate Hs; cbn [is_mem_store] in Hs.
  destruct m; try discriminate Hs; cbn [inst] in H; unfold mem_store in H;
    repeat (case_split; inv_eqs); inv_eqs; try discriminate; eauto.
Qed.

Lemma data_inv_invalidate_data data s r : data_inv data s -> data_inv (invalidate_data data r) s.
Proof. intros H; apply (data_inv_invalidate_regs [r] data s H). Qed.

Lemma inst_arith_val' (x : arith a) s :
  match x with Binop _ _ _ _ | asm.Shift _ _ _ _ | Div _ _ _ => True | _ => False end ->
  inst (Arith x) s = option_map (fun w => set_var (firstRegOfArith x) w s) (arith_val x s).
Proof.
  intros H; destruct x; try contradiction H; cbn [inst arith_val firstRegOfArith]; unfold assign.
  - destruct r; cbn [ri_exp]; destruct (word_exp _ _); reflexivity.
  - destruct r; cbn [ri_exp]; destruct (word_exp _ _); reflexivity.
  - cbn zeta. repeat case_split; reflexivity.
Qed.

Lemma can_mem_canonical_shape d (x : arith a) :
  can_mem_arith (canonicalArith d x) ->
  match x with Binop _ _ _ _ | asm.Shift _ _ _ _ | Div _ _ _ => True | _ => False end.
Proof. destruct x; cbn [canonicalArith can_mem_arith]; auto; intros H; discriminate H. Qed.

(** Galette-only: correctness of [word_cseInst]. *)
Lemma word_cseInst_correct data s (i : asm.inst a) res s' data' p' :
  evaluate (Inst i, s) = (res, s') -> data_inv data s -> res <> Some Error ->
  word_cseInst data i = (data', p') ->
  evaluate (p', s) = (res, s') /\ (res = None -> data_inv data' s').
Proof.
  intros He H Hr Hc. rewrite evaluate_Inst_eq in He.
  destruct (inst i s) as [s1|] eqn:Ei; [|inv_eqs; congruence].
  apply pair_equal_spec in He as [<- <-].
  assert (Ev : evaluate (Inst i, s) = (None, s1)) by (rewrite evaluate_Inst_eq, Ei; reflexivity).
  destruct i as [|r w|x|m r [a0 ofs]|f]; cbn [word_cseInst] in Hc; cbn zeta in Hc.
  - inv_eqs. cbn [inst] in Ei; inv_eqs. auto.
  - cbn [inst] in Ei; unfold assign in Ei; cbn [word_exp] in Ei; inv_eqs.
    pose proof (data_inv_invalidate_data data s r H) as H0.
    destruct (EVEN r) eqn:Er; inv_eqs.
    + split; [exact Ev|intros _; apply data_inv_set_var; [apply lookup_invalidate_data|exact H0]].
    + assert (NE : ~ is_true (EVEN r)) by (unfold is_true; rewrite Er; intros Hf; discriminate Hf).
      destruct (add_to_data_const_correct (invalidate_data data r) s r w data' p'
        (conj H0 (conj (lookup_invalidate_data data r) (conj NE Hc)))) as [A B].
      auto.
  - set (D0 := invalidate_regs data (arithWrites x)) in *.
    assert (H0 : data_inv D0 s) by apply data_inv_invalidate_regs, H.
    assert (L0 : lookup (firstRegOfArith x) (to_canonical D0) = None)
      by (apply lookup_invalidate_regs; unfold is_true; rewrite MEM_In; apply firstRegOfArith_writes).
    destruct (can_mem_arith (canonicalArith D0 x) && negb (MEM (firstRegOfArith x)
               (arithReads (canonicalArith D0 x)))) eqn:G.
    + apply andb_prop in G as [Gc Gm]. apply negb_true_iff in Gm.
      pose proof (inst_arith_val' x s (can_mem_canonical_shape D0 x Gc)) as Ia.
      rewrite Ia in Ei. destruct (arith_val x s) as [w|] eqn:Av; cbn [option_map] in Ei; inv_eqs.
      assert (Ex : evaluate (Inst (Arith x), s) = (None, set_var (firstRegOfArith x) w s))
        by (rewrite evaluate_Inst_eq, Ia; reflexivity).
      destruct (add_to_data_Arith_correct D0 s x (canonicalArith D0 x) (firstRegOfArith x) w data' p')
        as [A B].
      { split; [exact H0|]. split; [exact L0|]. split; [reflexivity|]. split; [exact Gc|].
        split; [rewrite Gm; intros Hf; discriminate Hf|]. split; [reflexivity|]. split; [exact Ex|exact Hc]. }
      auto.
    + inv_eqs. split; [exact Ev|intros _].
      destruct (inst_frame _ _ _ Ei) as (F1 & F2 & F3 & F4 & F5).
      apply (data_inv_frame D0 s s1 (arithWrites x)); auto.
      intros w Hw; apply lookup_invalidate_regs; unfold is_true; rewrite MEM_In; exact Hw.
  - destruct (is_store m) eqn:Es.
    + inv_eqs. split; [exact Ev|intros _].
      destruct (inst_store_frame _ _ _ Ei ltac:(cbn [is_mem_store]; exact Es)) as [mm ->].
      apply data_inv_memory, H.
    + assert (Ns : ~ is_store m) by (unfold is_true; rewrite Es; intros Hf; discriminate Hf).
      rewrite inst_load_val in Ei by exact Ns.
      destruct (load_val m a0 ofs s) as [w|] eqn:Lv; cbn [option_map] in Ei; inv_eqs.
      assert (Ex : evaluate (Inst (Mem m r (Addr a0 ofs)), s) = (None, set_var r w s))
        by (apply eval_load_iff; auto).
      pose proof (data_inv_invalidate_data data s r H) as H0.
      destruct (EVEN r || EVEN a0 || (a0 =? r)) eqn:G.
      * inv_eqs. split; [exact Ex|intros _; apply data_inv_set_var; [apply lookup_invalidate_data|exact H0]].
      * apply orb_false_iff in G as [G G3]. apply orb_false_iff in G as [G1 G2].
        apply N.eqb_neq in G3.
        destruct (add_to_load_correct (invalidate_data data r) s m r a0
          (canonicalRegs' r (invalidate_data data r) a0) ofs w data' p') as [A B].
        { split; [exact H0|]. split; [apply lookup_invalidate_data|]. split; [reflexivity|].
          split; [exact Ns|]. split; [rewrite G1; intros Hf; discriminate Hf|].
          split; [rewrite G2; intros Hf; discriminate Hf|]. split; [exact G3|].
          split; [exact Ex|exact Hc]. }
        auto.
  - inv_eqs. split; [exact Ev|intros _].
    destruct (inst_frame _ _ _ Ei) as (F1 & F2 & F3 & F4 & F5).
    apply (data_inv_frame (invalidate_regs data (fpWrites f)) s s1 (fpWrites f)); auto.
    + apply data_inv_invalidate_regs, H.
    + intros w Hw; apply lookup_invalidate_regs; unfold is_true; rewrite MEM_In; exact Hw.
Qed.

(** Galette-only: [Loop] bodies may be replaced by bodies that agree on all
    non-error runs (as in [word_copyProof]). *)
Lemma evaluate_Loop_body_cong_err : forall (st : state) names (p p' : prog a) exit_names res s',
  (forall (v : state) res s', evaluate (p, v) = (res, s') /\ res <> SOME Error ->
     evaluate (p', v) = (res, s')) /\
  evaluate (Loop names p exit_names, st) = (res, s') /\ res <> SOME Error ->
  evaluate (Loop names p' exit_names, st) = (res, s').
Proof.
  intros st names p p' exit_names res s' (Hs & H & Hr).
  revert res s' H Hr.
  remember (N.to_nat (clock st)) as n eqn:Hn. revert st Hn.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros st Hn res s' H Hr.
  rewrite evaluate_eqn in H |- *; cbn [evaluate_body] in H |- *.
  destruct (cut_state (names, LN) st) as [s0|] eqn:Ec; [|exact H].
  rewrite fix_clock_evaluate in H |- *.
  destruct (evaluate (p, s0)) as [r t] eqn:E1.
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

Lemma evaluate_Seq_eq (p1 p2 : prog a) (st : state) :
  evaluate (Seq p1 p2, st) =
  let '(res, s1) := evaluate (p1, st) in
  if bool_decide (res = NONE) then evaluate (p2, s1) else (res, s1).
Proof. rewrite (evaluate_eqn (Seq p1 p2) st); cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "comp_correct" *)
Theorem comp_correct : forall (v : prog a) (v1 : state) res s' data p' data',
  evaluate (v, v1) = (res, s') /\ flat_exp_conventions v /\ data_inv data v1 /\
  res <> Some Error /\ word_cse data v = (data', p') ->
  evaluate (p', v1) = (res, s') /\ (res = None -> data_inv data' s').
Proof.
  intros v.
  induction v as [ |pri moves|i|x ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                  |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                  |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                  |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op x ex]
    using prog_nested_ind;
    intros st res s' data p' data' (He & Hf & H & Hr & Hc); cbn [word_cse] in Hc; cbn zeta in Hc;
    cbn [flat_exp_conventions] in Hf.
  - (* Skip *)
    inv_eqs. rewrite evaluate_eqn in He; cbn [evaluate_body] in He; inv_eqs. auto.
  - (* Move *)
    inv_eqs. split; [exact He|intros ->].
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (ALL_DISTINCT (MAP FST moves)) eqn:Hd; [|inv_eqs; congruence].
    destruct (get_vars (MAP SND moves) st) as [vs|] eqn:Hg; inv_eqs; try congruence.
    apply canonicalMoveRegs_lemma; auto.
  - (* Inst *)
    destruct (word_cseInst data i) as [d1 q1] eqn:Ei; inv_eqs.
    eapply word_cseInst_correct; eauto.
  - (* Assign *) discriminate Hf.
  - (* Get *)
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (get_store gn st) as [w|] eqn:Gs; [|inv_eqs; congruence]. inv_eqs.
    set (D0 := invalidate_data data gv) in *.
    pose proof (data_inv_invalidate_data data st gv H) as H0.
    pose proof (lookup_invalidate_data data gv) as L0. fold D0 in H0, L0.
    destruct (ALOOKUP (gets_mem D0) gn) as [k|] eqn:Ek.
    + destruct (si_gets _ _ (proj2 H0) _ _ Ek) as [w' [Fw Gk]].
      unfold get_store in Gs; rewrite Gs in Fw; apply Some_eq_inv in Fw; subst w'.
      pose proof (get_var_lookup_any D0 st k w H0 Gk) as Gk'.
      assert (Ev : evaluate (Move 1 [(gv, lookup_any k (to_latest D0) k)], st) = (None, set_var gv w st))
        by (apply evaluate_Move1, Gk').
      destruct (EVEN gv) eqn:Eg; inv_eqs; (split; [exact Ev|intros _]).
      * apply data_inv_set_var; auto.
      * apply data_inv_hit; [exact H0|exact L0|unfold is_true; rewrite Eg; intros Hf'; discriminate Hf'|
          apply (wf_gets _ _ (proj1 H0) _ _ Ek)|exact Gk].
    + assert (Ev : evaluate (Get gv gn, st) = (None, set_var gv w st))
        by (rewrite evaluate_eqn; cbn [evaluate_body]; rewrite Gs; reflexivity).
      destruct (EVEN gv) eqn:Eg; inv_eqs; (split; [exact Ev|intros _]).
      * apply data_inv_set_var; auto.
      * apply (data_inv_insert_gets _ _ gn gv w). split; [apply data_inv_set_var; auto|]. split; [exact L0|].
        split; [apply (proj1 (ODD_not_EVEN gv)); unfold is_true; rewrite Eg; intros Hf'; discriminate Hf'|].
        split; [exact Ek|]. split; [unfold set_var; exact Gs|apply get_var_set_var_same].
  - (* Set *)
    destruct sexp; try discriminate Hf.
    rewrite evaluate_eqn in He; cbn [evaluate_body word_exp] in He.
    destruct (bool_decide (sn = stackLang.Handler) || bool_decide (sn = stackLang.BitmapBase)) eqn:Hb; [inv_eqs; congruence|].
    destruct (get_var n st) as [w|] eqn:Gn; [|inv_eqs; congruence]. inv_eqs.
    assert (Ev : evaluate (Set_ sn (Var n), st) = (None, set_store sn w st))
      by (rewrite evaluate_eqn; cbn [evaluate_body word_exp]; rewrite Hb, Gn; reflexivity).
    destruct (decide (sn = stackLang.CurrHeap)) as [Ecur|Ncur]; inv_eqs;
      [split; [exact Ev|intros _; apply data_inv_empty]|].
    cbn [dest_Var] in Hc. pose proof (data_inv_filter_gets data st sn H) as H1.
    assert (A1 : ALOOKUP (FILTER (fun '(m, n) => negb (bool_decide (m = sn))) (gets_mem data)) sn = None)
      by apply ALOOKUP_FILTER'.
    destruct (EVEN n) eqn:En; inv_eqs; (split; [exact Ev|intros _]).
    + apply data_inv_set_store. split; [exact H1|]. split; [exact Ncur|exact A1].
    + assert (On : is_true (ODD n)) by (apply (proj1 (ODD_not_EVEN n)); unfold is_true; rewrite En;
        intros Hf'; discriminate Hf').
      pose proof (data_inv_reinsert_canonical data st n (conj H On)) as H2.
      pose proof (data_inv_filter_gets _ st sn H2) as H3.
      pose proof (data_inv_set_store _ st sn w (conj H3 (conj Ncur A1))) as H4.
      refine (data_inv_cons_gets _ _ sn (canonicalRegs data n) w (conj H4 (conj A1 (conj _ (conj _ _)))));
        cbn [with_gets_mem with_to_canonical to_canonical gets_mem].
      * unfold canonicalRegs, lookup_any. destruct (lookup n (to_canonical data)) as [k|] eqn:E0.
        -- rewrite lookup_insert. destruct (decide (k = n)); [subst; first [reflexivity|apply lookup_insert_same]|].
           exact (proj1 (wf_tc _ _ (proj1 H) _ _ E0)).
        -- apply lookup_insert_same.
      * unfold set_store; cbn [store set_store_field]. rewrite FLOOKUP_UPDATE.
        destruct (decide _); [reflexivity|congruence].
      * rewrite get_var_set_store, canonicalRegs_correct by exact H. exact Gn.
  - (* Store *) discriminate Hf.
  - (* MustTerminate *)
    destruct (word_cse data q) as [d1 q1] eqn:Eq; apply pair_equal_spec in Hc as [<- <-].
    rewrite evaluate_eqn in He |- *; cbn [evaluate_body] in He |- *.
    destruct (termdep st =? 0); [inv_eqs; congruence|].
    destruct (evaluate (q, set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)))
      as [r1 t1] eqn:E1.
    destruct (bool_decide (r1 = SOME TimeOut)) eqn:Et; [inv_eqs; congruence|].
    apply pair_equal_spec in He as [<- <-].
    assert (Hr1 : r1 <> Some Error) by exact Hr.
    destruct (IHq _ r1 t1 data q1 d1 (conj E1 (conj Hf (conj (data_inv_clock _ _ _ _ H) (conj Hr1 Eq)))))
      as [A B].
    rewrite A, Et. split; [reflexivity|]. intros ->. apply data_inv_clock, B; reflexivity.
  - (* Call *) inv_eqs. split; [exact He|intros _; apply data_inv_empty].
  - (* Seq *)
    destruct (word_cse data q1) as [d1 p1] eqn:E1c; destruct (word_cse d1 q2) as [d2 p2] eqn:E2c;
      apply pair_equal_spec in Hc as [<- <-].
    apply andb_prop in Hf as [H0 H1].
    rewrite evaluate_Seq_eq in He |- *. destruct (evaluate (q1, st)) as [r1 s1] eqn:E1.
    assert (Hr1 : r1 <> SOME Error).
    { intros ->. rewrite bd_false in He by discriminate. inv_eqs. congruence. }
    destruct (IH1 st r1 s1 data p1 d1 (conj E1 (conj H0 (conj H (conj Hr1 E1c))))) as [A1 B1].
    rewrite A1. destruct (bool_decide (r1 = NONE)) eqn:En.
    + apply bool_decide_spec in En; subst r1.
      exact (IH2 s1 res s' d1 p2 d2 (conj He (conj H1 (conj (B1 eq_refl) (conj Hr E2c))))).
    + inv_eqs. split; [reflexivity|]. intros ->. rewrite bd_true in En by reflexivity. discriminate.
  - (* If *)
    destruct (word_cse data q1) as [d1 p1] eqn:E1c; destruct (word_cse data q2) as [d2 p2] eqn:E2c;
      apply pair_equal_spec in Hc as [<- <-].
    apply andb_prop in Hf as [H0 H1].
    pose proof (word_cse_wf_data q1 data (proj1 H)) as W1. rewrite E1c in W1; cbn [FST] in W1.
    pose proof (word_cse_wf_data q2 data (proj1 H)) as W2. rewrite E2c in W2; cbn [FST] in W2.
    rewrite evaluate_eqn in He |- *; cbn [evaluate_body] in He |- *.
    destruct (get_var r st), (get_var_imm ri st); try (inv_eqs; congruence).
    destruct (word_cmp cmp w w0) as [[]|]; [| |inv_eqs; congruence].
    + destruct (IH1 st res s' data p1 d1 (conj He (conj H0 (conj H (conj Hr E1c))))) as [A B].
      split; [exact A|intros Hn]. apply data_inv_merge_l. split; [exact W1|]. split; [exact W2|].
      apply (B Hn).
    + destruct (IH2 st res s' data p2 d2 (conj He (conj H1 (conj H (conj Hr E2c))))) as [A B].
      split; [exact A|intros Hn]. apply data_inv_merge_r. split; [exact W1|]. split; [exact W2|].
      apply (B Hn).
  - (* Loop *)
    destruct (word_cse empty_data q) as [d1 q1] eqn:Eq; apply pair_equal_spec in Hc as [<- <-].
    split; [|intros _; apply data_inv_empty].
    apply (evaluate_Loop_body_cong_err st names q q1 exit_names res s'). split; [|split; assumption].
    intros v0 r0 s0 [Hv Hr0].
    exact (proj1 (IHq v0 r0 s0 empty_data q1 d1 (conj Hv (conj Hf (conj (data_inv_empty v0) (conj Hr0 Eq)))))).
  - (* Alloc *) inv_eqs. split; [exact He|intros _; apply data_inv_empty].
  - (* StoreConsts *)
    inv_eqs. split; [exact He|intros ->].
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He. cbn zeta in He.
    destruct (get_var ad st) as [[w1|]|], (get_var off st) as [[w2|]|]; try (inv_eqs; congruence).
    destruct (negb _); inv_eqs; try congruence.
    set (D := invalidate_regs data [t1; t2; ad; off]).
    assert (HD : data_inv D st) by apply data_inv_invalidate_regs, H.
    assert (U : forall x, In x [t1; t2; ad; off] -> lookup x (to_canonical D) = None)
      by (intros x Hx; apply lookup_invalidate_regs; unfold is_true; rewrite MEM_In; exact Hx).
    pose proof (data_inv_memory D st (const_writes w1 w2 ws (memory st)) HD) as HM.
    unfold set_loads_mem.
    apply (data_inv_set_var (with_loads_mem balanced_map.empty D)); [apply U; cbn; auto|].
    apply (data_inv_set_var (with_loads_mem balanced_map.empty D)); [apply U; cbn; auto|].
    apply (data_inv_unset_var (with_loads_mem balanced_map.empty D)); [apply U; cbn; auto|].
    apply (data_inv_unset_var (with_loads_mem balanced_map.empty D)); [apply U; cbn; auto|exact HM].
  - (* Raise *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    repeat (case_split; inv_eqs); inv_eqs; discriminate.
  - (* Return *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    repeat (case_split; inv_eqs); inv_eqs; discriminate.
  - (* Break *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    inv_eqs; discriminate.
  - (* Continue *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    inv_eqs; discriminate.
  - (* Tick *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (clock st =? 0); inv_eqs; try discriminate.
    eapply data_inv_state_agree; split; [exact H|]; repeat split.
  - (* OpCurrHeap *)
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (word_exp st (Op b [Var src; Lookup stackLang.CurrHeap])) as [w|] eqn:Ew; [|inv_eqs; congruence].
    inv_eqs.
    assert (Ev : evaluate (OpCurrHeap b dst src, st) = (None, set_var dst w st))
      by (rewrite evaluate_eqn; cbn [evaluate_body]; rewrite Ew; reflexivity).
    pose proof (data_inv_invalidate_data data st dst H) as H0.
    destruct (EVEN src || (src =? dst)) eqn:G.
    + inv_eqs. split; [exact Ev|intros _; apply data_inv_set_var; [apply lookup_invalidate_data|exact H0]].
    + apply orb_false_iff in G as [G1 G2]. apply N.eqb_neq in G2.
      destruct (add_to_data_OpCurrHeap_correct (invalidate_data data dst) st b dst src
        (canonicalRegs' dst (invalidate_data data dst) src) w data' p') as [A B].
      { split; [exact H0|]. split; [apply lookup_invalidate_data|]. split; [reflexivity|].
        split; [rewrite G1; intros Hf'; discriminate Hf'|]. split; [exact G2|]. split; [exact Ew|exact Hc]. }
      auto.
  - (* LocValue *)
    rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (classical_dec _) as [Hl|Hl]; [|inv_eqs; congruence]. inv_eqs.
    destruct (add_to_data_LocValue_correct (invalidate_data data lr) st lr ll data' p') as [A B].
    { split; [apply data_inv_invalidate_data, H|]. split; [apply lookup_invalidate_data|].
      split; [exact Hl|exact Hc]. }
    auto.
  - (* Install *) inv_eqs. split; [exact He|intros _; apply data_inv_empty].
  - (* CodeBufferWrite *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    repeat (case_split; inv_eqs); inv_eqs; try discriminate.
    eapply data_inv_state_agree; split; [exact H|]; repeat split.
  - (* DataBufferWrite *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    repeat (case_split; inv_eqs); inv_eqs; try discriminate.
    eapply data_inv_state_agree; split; [exact H|]; repeat split.
  - (* FFI *) inv_eqs. split; [exact He|intros _; apply data_inv_empty].
  - (* ShareInst *)
    inv_eqs. split; [exact He|intros ->]. rewrite evaluate_eqn in He; cbn [evaluate_body] in He.
    destruct (word_exp st ex) as [[ad|]|]; [|inv_eqs; congruence|inv_eqs; congruence].
    assert (SA : forall d f, data_inv d st -> data_inv d (set_ffi f st))
      by (intros d f Hd; eapply data_inv_state_agree; split; [exact Hd|]; repeat split).
    pose proof (data_inv_invalidate_data data st x H) as H0.
    destruct op; cbn [is_store share_inst] in *;
      unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
        sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in He;
      repeat (case_split; inv_eqs); inv_eqs; try discriminate.
    all: first [ apply SA, H
               | apply data_inv_set_var; [apply lookup_invalidate_data|apply SA, H0] ].
Qed.

End Correct.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_common_subexp_elim_correct" *)
Theorem word_common_subexp_elim_correct : forall {a c ffi_t} (p : prog a) (s : state a c ffi_t) res s1,
  evaluate (p, s) = (res, s1) /\ flat_exp_conventions p /\ res <> Some Error ->
  evaluate (word_common_subexp_elim p, s) = (res, s1).
Proof.
  intros a c ffi_t p s res s1 (He & Hf & Hr); unfold word_common_subexp_elim.
  destruct (word_cse empty_data p) as [d q] eqn:E.
  exact (proj1 (comp_correct p s res s1 empty_data q d (conj He (conj Hf (conj (data_inv_empty s) (conj Hr E)))))).
Qed.

(** ** Syntactic conventions *)

Section Syntax.
Context {a : N}.

Lemma add_to_data_aux_shape' : forall data r i (x : prog a) d' p,
  add_to_data_aux data r i x = (d', p) -> p = x \/ exists k, p = Move 0 [(r, k)].
Proof.
  intros data r i x d' p H; unfold add_to_data_aux in H;
    repeat (case_split; inv_eqs); inv_eqs; eauto.
Qed.

Lemma word_cseInst_shape' : forall data (i : asm.inst a) d' p,
  word_cseInst data i = (d', p) -> p = Inst i \/ exists r k, p = Move 0 [(r, k)].
Proof.
  intros data i d' p H; unfold word_cseInst in H; repeat (case_split; inv_eqs); inv_eqs; eauto.
  all: try (unfold add_to_data in *; match goal with
         | E : add_to_data_aux _ _ _ _ = _ |- _ =>
             apply add_to_data_aux_shape' in E as [->|[? ->]]; eauto
         end).
  all: try (unfold add_to_load_aux in *; repeat (case_split; inv_eqs); inv_eqs; eauto).
  all: try (unfold add_to_data_const in *; repeat (case_split; inv_eqs); inv_eqs; eauto).
Qed.

Ltac cse_shape :=
  repeat match goal with
  | E : word_cseInst _ _ = (_, _) |- _ =>
      apply word_cseInst_shape' in E as [->|[? [? ->]]]
  | E : add_to_data_aux _ _ _ _ = (_, _) |- _ =>
      apply add_to_data_aux_shape' in E as [->|[? ->]]
  end.

Ltac use_ih2 :=
  repeat match goal with
  | IH : forall d x y, _ -> word_cse d ?q = (x, y) -> _, E : word_cse ?d0 ?q = (?x0, ?y0) |- _ =>
      specialize (IH _ _ _ ltac:(eassumption) E)
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_full_inst_ok_less" *)
Theorem word_cse_full_inst_ok_less : forall (p : prog a) data c data' q,
  full_inst_ok_less c p /\ word_cse data p = (data', q) -> full_inst_ok_less c q.
Proof.
  intros p data c0; revert data; induction p using prog_nested_ind;
    intros data data' q [Hp Hc]; cbn [word_cse] in Hc;
    repeat (case_split; inv_eqs); inv_eqs; cse_shape;
    cbn [full_inst_ok_less] in *; bsplit; eauto.
Qed.

Lemma word_cse_esv : forall P (p : prog a) data data' q,
  every_stack_var P p /\ word_cse data p = (data', q) -> every_stack_var P q.
Proof.
  intros P p; induction p using prog_nested_ind;
    intros data data' q [Hp Hc]; cbn [word_cse] in Hc;
    repeat (case_split; inv_eqs); inv_eqs; cse_shape;
    cbn [every_stack_var] in *; bsplit; eauto.
Qed.

Lemma word_cse_cac : forall (p : prog a) data data' q,
  call_arg_convention p /\ word_cse data p = (data', q) -> call_arg_convention q.
Proof.
  intros p; induction p using prog_nested_ind;
    intros data data' q [Hp Hc]; cbn [word_cse] in Hc;
    repeat (case_split; inv_eqs); inv_eqs; cse_shape;
    cbn [call_arg_convention] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_pre_alloc_conventions" *)
Theorem word_cse_pre_alloc_conventions : forall (p : prog a) data data' q,
  pre_alloc_conventions p /\ word_cse data p = (data', q) -> pre_alloc_conventions q.
Proof.
  intros p data data' q [Hp Hc]; unfold pre_alloc_conventions in *; bsplit;
    [eapply word_cse_esv|eapply word_cse_cac]; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_every_inst_distinct_tar_reg" *)
Theorem word_cse_every_inst_distinct_tar_reg : forall (p : prog a) data data' q,
  every_inst distinct_tar_reg p /\ word_cse data p = (data', q) -> every_inst distinct_tar_reg q.
Proof.
  intros p; induction p using prog_nested_ind;
    intros data data' q [Hp Hc]; cbn [word_cse] in Hc;
    repeat (case_split; inv_eqs); inv_eqs; cse_shape;
    cbn [every_inst] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "word_cse_every_inst_two_reg" *)
Theorem word_cse_every_inst_two_reg : forall (p : prog a) data data' q,
  every_inst two_reg_inst p /\ word_cse data p = (data', q) -> every_inst two_reg_inst q.
Proof.
  intros p; induction p using prog_nested_ind;
    intros data data' q [Hp Hc]; cbn [word_cse] in Hc;
    repeat (case_split; inv_eqs); inv_eqs; cse_shape;
    cbn [every_inst] in *; bsplit; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "every_inst_distinct_tar_reg_word_common_subexp_elim" *)
Theorem every_inst_distinct_tar_reg_word_common_subexp_elim : forall (p : prog a),
  every_inst distinct_tar_reg p -> every_inst distinct_tar_reg (word_common_subexp_elim p).
Proof.
  intros p H; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_every_inst_distinct_tar_reg; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "pre_alloc_conventions_word_common_subexp_elim" *)
Theorem pre_alloc_conventions_word_common_subexp_elim : forall (p : prog a),
  pre_alloc_conventions p -> pre_alloc_conventions (word_common_subexp_elim p).
Proof.
  intros p H; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_pre_alloc_conventions; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "full_inst_ok_less_word_common_subexp_elim" *)
Theorem full_inst_ok_less_word_common_subexp_elim : forall ac (p : prog a),
  full_inst_ok_less ac p -> full_inst_ok_less ac (word_common_subexp_elim p).
Proof.
  intros ac p H; unfold word_common_subexp_elim; destruct (word_cse empty_data p) eqn:E.
  eapply word_cse_full_inst_ok_less; eauto.
Qed.

End Syntax.

