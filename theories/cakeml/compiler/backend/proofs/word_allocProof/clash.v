(** * CakeML [word_allocProof]: clash trees and [word_alloc_correct]

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    2385-3480, "3. connect check_clash_tree to colouring_ok" and
    "4. word_alloc_correct").

    Notes:
    - HOL's commented-out [get_clash_sets] development (lines 2272-2383
      and 2398-2589) is not ported.
    - HOL's predicate [λx. x ∈ domain ...] given to the boolean
      [every_var_exp] is [fun x => ⌜x IN domain ...⌝].
    - [clash_tree_colouring_ok] is proved by structural induction on the
      program (HOL: [get_clash_tree_ind]); the Galette-only lemmas below
      ([delta_case], ...) factor out HOL's repeated [start_tac]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc linear_scan.
From Galette.cakeml.compiler.backend.reg_alloc.proofs Require Import reg_allocProof.
From Galette.cakeml.compiler.backend.reg_alloc.proofs Require linear_scanProof.
From Galette.cakeml.compiler.backend.reg_alloc.proofs.linear_scanProof Require Import intervals.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import wordLang word_alloc.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.proofs.word_allocProof Require Import colouring.
Open Scope N_scope.

Section Clash.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "every_var_exp_get_live_exp" *)
Theorem every_var_exp_get_live_exp : forall (exp : exp a),
  every_var_exp (fun x => ⌜x IN domain (get_live_exp exp)⌝) exp.
Proof.
  intros exp. induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [every_var_exp get_live_exp]; try reflexivity.
  - apply bd_true'. rewrite domain_insert. left; reflexivity.
  - exact IH.
  - unfold is_true. rewrite EVERY_Forall, Forall_forall. rewrite Forall_forall in IH.
    intros e He. apply (every_var_exp_mono (fun x => ⌜x IN domain (get_live_exp e)⌝) e). split; [|apply IH, He].
    intros x Hx. apply bool_decide_spec in Hx. apply bd_true'.
    apply (domain_big_union_subset es e); [apply MEM_iff', He|exact Hx].
  - unfold is_true; rewrite andb_true_iff; split.
    + apply (every_var_exp_mono (fun x => ⌜x IN domain (get_live_exp e1)⌝) e1); split; [|exact IH1].
      intros x Hx; apply bool_decide_spec in Hx; apply bd_true'; rewrite domain_union; left; exact Hx.
    + apply (every_var_exp_mono (fun x => ⌜x IN domain (get_live_exp e2)⌝) e2); split; [|exact IH2].
      intros x Hx; apply bool_decide_spec in Hx; apply bd_true'; rewrite domain_union; right; exact Hx.
Qed.

(** Galette-only: well-formed [num_set]s with the same domain are equal. *)
Lemma num_set_eq (t1 t2 : num_set) :
  wf t1 -> wf t2 -> (forall x, x IN domain t1 <-> x IN domain t2) -> t1 = t2.
Proof.
  intros W1 W2 H. apply spt_eq_thm; [split; assumption|]. intros n.
  specialize (H n). rewrite !IN_domain_iff in H.
  destruct (lookup n t1) as [[]|], (lookup n t2) as [[]|]; try reflexivity.
  - exfalso. destruct (proj1 H (ex_intro _ tt eq_refl)) as [v Hv]; discriminate.
  - exfalso. destruct (proj2 H (ex_intro _ tt eq_refl)) as [v Hv]; discriminate.
Qed.

Lemma lookup_num_set (t : num_set) x : lookup x t = if decide (x IN domain t) then Some tt else None.
Proof.
  destruct (decide _) as [H|H].
  - apply IN_domain_iff in H as [[] Hv]; exact Hv.
  - destruct (lookup x t) as [[]|] eqn:E; [|reflexivity]. exfalso; apply H; apply IN_domain_iff; eauto.
Qed.

Lemma NoDup_map_In_inj {A B} (g : A -> B) l x y :
  NoDup (List.map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  induction l as [|z l IH]; intros Hd Hx Hy E; [destruct Hx|].
  cbn in Hd; inversion Hd as [|? ? Hz Hd']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hz; rewrite E; apply in_map, Hy.
  - exfalso; apply Hz; rewrite <- E; apply in_map, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "check_col_INJ" *)
Theorem check_col_INJ : forall (f : N -> N) (numset : num_set) q r,
  check_col f numset = Some (q, r) ->
  q = numset /\ INJ f (domain q) UNIV /\ domain r = IMAGE f (domain q).
Proof.
  intros f numset q r H. unfold check_col in H.
  destruct (ALL_DISTINCT _) eqn:Ed; [|discriminate]. injection H as <- <-.
  apply ALL_DISTINCT_iff' in Ed. split; [reflexivity|split].
  - split; [intros; exact Logic.I|]. intros x y [Hx Hy] E.
    apply IN_domain_iff in Hx as [[] Hx], Hy as [[] Hy].
    apply ALOOKUP_toAList_In in Hx, Hy.
    assert (Exy : (x, tt) = (y, tt)) by (eapply (NoDup_map_In_inj (fun p => f (FST p))); eauto).
    injection Exy as ->; reflexivity.
  - rewrite domain_fromAList. apply set_ext; intros z. unfold pred_set.IMAGE, pred_set.IN.
    rewrite MEM_iff', List.map_map. cbn. rewrite List.map_id. split.
    + intros Hz. apply in_map_iff in Hz as [[k []] [<- Hk]]. exists k; split; [reflexivity|].
      apply IN_domain_iff; exists tt; apply ALOOKUP_toAList_In, Hk.
    + intros [k [-> Hk]]. apply IN_domain_iff in Hk as [[] Hk]. apply in_map_iff.
      exists (k, tt); split; [reflexivity|apply ALOOKUP_toAList_In, Hk].
Qed.

Lemma wf_numset_list_insert ls (t : num_set) : wf t -> wf (numset_list_insert ls t).
Proof. induction ls as [|x ls IH]; intros W; cbn [numset_list_insert]; [exact W|apply wf_insert, IH, W]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lookup_numset_list_insert" *)
Theorem lookup_numset_list_insert : forall ls n (t : num_set),
  lookup n (numset_list_insert ls t) = if MEM n ls then SOME tt else lookup n t.
Proof.
  induction ls as [|x ls IH]; intros n t; [reflexivity|]. cbn [numset_list_insert MEM].
  rewrite lookup_insert, IH. unfold bool_decide. destruct (decide (n = x)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_insert_swap" *)
Theorem wf_insert_swap : forall (t : num_set) a0 c0,
  wf t -> insert a0 tt (insert c0 tt t) = insert c0 tt (insert a0 tt t).
Proof.
  intros t a0 c0 W. apply spt_eq_thm; [split; repeat apply wf_insert; exact W|].
  intros n; rewrite !lookup_insert. destruct (decide (n = a0)), (decide (n = c0)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "numset_list_insert_swap" *)
Theorem numset_list_insert_swap : forall ls h (live : num_set),
  wf live ->
  wf (numset_list_insert ls live) /\
  numset_list_insert ls (insert h tt live) = insert h tt (numset_list_insert ls live).
Proof.
  intros ls h live W. split; [apply wf_numset_list_insert, W|].
  apply spt_eq_thm; [split; [apply wf_numset_list_insert, wf_insert, W|apply wf_insert, wf_numset_list_insert, W]|].
  intros n; rewrite lookup_numset_list_insert, !lookup_insert, lookup_numset_list_insert.
  destruct (MEM n ls), (decide (n = h)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "check_partial_col_INJ" *)
Theorem check_partial_col_INJ : forall ls f (live flive live' flive' : num_set),
  wf live /\
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV /\
  check_partial_col f ls live flive = Some (live', flive') ->
  wf live' /\
  live' = numset_list_insert ls live /\
  INJ f (domain live') UNIV /\
  domain flive' = IMAGE f (domain live').
Proof.
  induction ls as [|h ls IH]; intros f live flive live' flive' (W & Hd & Hi & H); cbn [check_partial_col] in H.
  - injection H as <- <-. auto.
  - destruct (lookup h live) as [[]|] eqn:Eh.
    + destruct (IH f live flive live' flive' (conj W (conj Hd (conj Hi H)))) as (W' & -> & Hi' & Hd').
      split; [exact W'|split; [|auto]].
      cbn [numset_list_insert]. apply spt_eq_thm; [split; [exact W'|apply wf_insert, W']|].
      intros n. rewrite lookup_insert, !lookup_numset_list_insert. destruct (decide (n = h)) as [->|]; [|reflexivity].
      destruct (MEM h ls); [reflexivity|exact Eh].
    + destruct (lookup (f h) flive) as [[]|] eqn:Ef; [discriminate|].
      assert (Hh : ~ h IN domain live) by (intros Hin; apply IN_domain_iff in Hin as [v Hv]; congruence).
      destruct (IH f (insert h tt live) (insert (f h) tt flive) live' flive') as (W' & -> & Hi' & Hd').
      { split; [apply wf_insert, W|split; [|split; [|exact H]]].
        - rewrite !domain_insert, Hd. apply set_ext; intros z; unfold pred_set.IMAGE, pred_set.IN; split.
          + intros [->|[x [-> Hx]]]; [exists h; auto|exists x; auto].
          + intros [x [-> [->|Hx]]]; [left; reflexivity|right; exists x; auto].
        - rewrite domain_insert. split; [intros; exact Logic.I|]. intros x y [Hx Hy] E.
          destruct Hi as [_ Hi].
          assert (Hn : forall z, z IN domain live -> f z <> f h).
          { intros z Hz Ez. assert (Hfz : f h IN domain flive) by (rewrite Hd; exists z; auto).
            apply IN_domain_iff in Hfz as [v Hv]. congruence. }
          destruct Hx as [->|Hx], Hy as [->|Hy];
            [reflexivity|exfalso; apply (Hn y Hy); congruence|exfalso; apply (Hn x Hx); congruence
            |apply Hi; [split; assumption|exact E]]. }
      split; [exact W'|split; [|auto]]. cbn [numset_list_insert].
      apply (proj2 (numset_list_insert_swap ls h live W)).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_insert_eq_union" *)
Theorem domain_insert_eq_union : forall num (live : num_set),
  domain (insert num tt live) = domain (union (insert num tt LN) live).
Proof. intros; rewrite <- insert_union; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_numset_list_insert_eq_union" *)
Theorem domain_numset_list_insert_eq_union : forall ls (live : num_set),
  domain (numset_list_insert ls live) = domain (union (numset_list_insert ls LN) live).
Proof.
  intros ls live. rewrite domain_union, !domain_numset_list_insert. apply set_ext; intros x.
  unfold pred_set.UNION, pred_set.IN; cbn [domain]. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_reads_exp_get_live_exp" *)
Theorem get_reads_exp_get_live_exp : forall (exp : exp a),
  set (get_reads_exp exp) = domain (get_live_exp exp).
Proof.
  intros exp. apply set_ext; intros x. change (x IN set (get_reads_exp exp) <-> x IN domain (get_live_exp exp)).
  rewrite IN_set. revert x.
  induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind; intros x;
    cbn [get_reads_exp get_live_exp].
  - unfold pred_set.IN; cbn; tauto.
  - rewrite domain_insert; unfold pred_set.IN; cbn; intuition congruence.
  - unfold pred_set.IN; cbn; tauto.
  - apply IH.
  - rewrite in_concat. rewrite Forall_forall in IH. unfold big_union. split.
    + intros [l [Hl Hx]]. apply in_map_iff in Hl as [e [<- He]]. apply IH in Hx; [|exact He].
      apply (domain_big_union_subset es e); [apply MEM_iff', He|exact Hx].
    + intros Hx. induction es as [|e es IHes]; cbn [MAP List.map FOLDR] in Hx |- *.
      * unfold pred_set.IN in Hx; cbn in Hx; contradiction.
      * rewrite domain_union in Hx. destruct Hx as [Hx|Hx].
        -- exists (get_reads_exp e); split; [left; reflexivity|apply IH; [left; reflexivity|exact Hx]].
        -- assert (IH' : forall x0, In x0 es -> forall x, In x (get_reads_exp x0) <-> x IN domain (get_live_exp x0))
             by (intros e' He'; apply IH; right; exact He').
           destruct (IHes IH' Hx) as [l [Hl Hx']]. exists l; split; [right; exact Hl|exact Hx'].
  - rewrite in_app_iff, IH1, IH2, domain_union. unfold pred_set.IN; tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "numset_list_insert_eq_UNION" *)
Theorem numset_list_insert_eq_UNION : forall (t t' : num_set) ls,
  wf t /\ wf t' /\ domain t' = set ls -> numset_list_insert ls t = union t' t.
Proof.
  intros t t' ls (W & W' & Hd). apply num_set_eq; [apply wf_numset_list_insert, W|apply wf_union; auto|].
  intros x. rewrite domain_numset_list_insert, domain_union, Hd. unfold pred_set.UNION, pred_set.IN. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_delete_swap" *)
Theorem wf_delete_swap : forall {A} (t : num_map A) a0 c0,
  wf t -> delete a0 (delete c0 t) = delete c0 (delete a0 t).
Proof.
  intros A t a0 c0 W. apply spt_eq_thm; [split; repeat apply wf_delete; exact W|].
  intros n; rewrite !lookup_delete. destruct (decide (n = a0)), (decide (n = c0)); reflexivity.
Qed.

Lemma wf_numset_list_delete {A} ls (t : num_map A) : wf t -> wf (numset_list_delete ls t).
Proof. revert t; induction ls as [|x ls IH]; intros t W; cbn [numset_list_delete]; [exact W|apply IH, wf_delete, W]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "numset_list_delete_swap" *)
Theorem numset_list_delete_swap : forall {A} ls h (live : num_map A),
  wf live ->
  wf (numset_list_delete ls live) /\
  numset_list_delete ls (delete h live) = delete h (numset_list_delete ls live).
Proof.
  intros A ls h live W. split; [apply wf_numset_list_delete, W|].
  apply spt_eq_thm; [split; [apply wf_numset_list_delete, wf_delete, W|apply wf_delete, wf_numset_list_delete, W]|].
  intros n. rewrite lookup_numset_list_delete, !lookup_delete, lookup_numset_list_delete.
  destruct (MEM n ls), (decide (n = h)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_numset_list_delete_eq" *)
Theorem wf_numset_list_delete_eq : forall {A} ls (t : num_map A),
  wf t -> FOLDR delete t ls = numset_list_delete ls t.
Proof.
  intros A ls t W. apply spt_eq_thm.
  { split; [|apply wf_numset_list_delete, W]. induction ls as [|x ls IH]; [exact W|apply wf_delete, IH]. }
  intros n. rewrite lookup_numset_list_delete. induction ls as [|x ls IH]; [reflexivity|].
  cbn [FOLDR MEM]. rewrite lookup_delete, IH. unfold bool_decide. destruct (decide (n = x)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_get_live_exp" *)
Theorem wf_get_live_exp : forall (exp : exp a), wf (get_live_exp exp).
Proof.
  intros exp; induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [get_live_exp]; try reflexivity.
  - apply wf_insert; reflexivity.
  - exact IH.
  - unfold big_union. induction es as [|e es IHes]; [reflexivity|]. inversion IH; subst.
    cbn [MAP List.map FOLDR]. apply wf_union; split; [assumption|apply IHes; assumption].
  - apply wf_union; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "IMAGE_DIFF" *)
Theorem IMAGE_DIFF : forall {B} (f : N -> B) s t,
  INJ f (s UNION t) UNIV -> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t.
Proof. intros; apply INJ_IMP_IMAGE_DIFF; assumption. Qed.

(** ** Galette-only: the [Delta] steps of [check_clash_tree] *)

Lemma delta_spec f w r (live flive livein flivein : num_set) :
  wf live -> domain flive = IMAGE f (domain live) -> INJ f (domain live) UNIV ->
  check_clash_tree f (Delta w r) live flive = Some (livein, flivein) ->
  INJ f (set w UNION domain live) UNIV /\ wf livein /\ INJ f (domain livein) UNIV /\
  domain flivein = IMAGE f (domain livein) /\
  domain livein = set r UNION (domain live DIFF set w).
Proof.
  intros W Hd Hi H. cbn [check_clash_tree] in H.
  destruct (check_partial_col f w live flive) as [[l1 fl1]|] eqn:E1; [|discriminate].
  destruct (check_partial_col_INJ w f live flive l1 fl1 (conj W (conj Hd (conj Hi E1)))) as (W1 & -> & I1 & D1).
  pose proof (numset_list_delete_IMAGE f w live flive _ Hd Hi E1) as Hdel.
  destruct (check_partial_col_INJ r f (numset_list_delete w live) (numset_list_delete (MAP f w) flive) livein flivein)
    as (W2 & -> & I2 & D2).
  { split; [apply wf_numset_list_delete, W|split; [exact Hdel|split; [|exact H]]].
    eapply INJ_less; split; [exact Hi|]. rewrite domain_numset_list_delete. intros x [Hx _]; exact Hx. }
  split; [|split; [exact W2|split; [exact I2|split; [exact D2|]]]].
  - rewrite domain_numset_list_insert in I1. eapply INJ_less; split; [exact I1|].
    intros x [Hx|Hx]; [right|left]; exact Hx.
  - rewrite domain_numset_list_insert, domain_numset_list_delete. apply set_ext; intros x.
    unfold pred_set.UNION, pred_set.IN; tauto.
Qed.

Lemma delta_case (p : prog a) lt f (live flive livein flivein : num_set) w r :
  get_clash_tree p lt = Delta w r ->
  (colouring_ok f p live lt <->
   INJ f (domain (get_live p live lt)) UNIV /\ INJ f (domain (union (get_writes p) live)) UNIV) ->
  wf (get_live p live lt) ->
  domain (get_live p live lt) = set r UNION (domain live DIFF set w) ->
  domain (get_writes p) SUBSET set w ->
  wf live -> domain flive = IMAGE f (domain live) -> INJ f (domain live) UNIV ->
  check_clash_tree f (get_clash_tree p lt) live flive = Some (livein, flivein) ->
  hide (wf livein /\ INJ f (domain livein) UNIV /\ colouring_ok f p live lt /\
        livein = get_live p live lt /\ domain flivein = IMAGE f (domain livein)).
Proof.
  intros Ht Hc Wg Dg Hw W Hd Hi H. rewrite Ht in H.
  destruct (delta_spec f w r live flive livein flivein W Hd Hi H) as (Hiw & W' & I' & D' & Dl).
  assert (E : livein = get_live p live lt) by (apply num_set_eq; [exact W'|exact Wg|]; rewrite Dl, Dg; tauto).
  subst livein. unfold hide. split; [exact W'|split; [exact I'|split; [|split; [reflexivity|exact D']]]].
  apply Hc. split; [exact I'|]. eapply INJ_less; split; [exact Hiw|].
  rewrite domain_union. intros x [Hx|Hx]; [left; apply Hw, Hx|right; exact Hx].
Qed.

Lemma wf_list_insert' ls (t : num_set) : wf t -> wf (list_insert ls t).
Proof. revert t; induction ls as [|x ls IH]; intros t W; cbn [list_insert]; [exact W|apply IH, wf_insert, W]. Qed.

Lemma wf_FOLDR_delete {A} ls (t : num_map A) : wf t -> wf (FOLDR delete t ls).
Proof. intros W; rewrite wf_numset_list_delete_eq by exact W; apply wf_numset_list_delete, W. Qed.

Ltac wf_solve :=
  repeat first [ assumption | reflexivity
               | apply wf_insert | apply wf_delete | apply wf_numset_list_insert
               | apply wf_list_insert' | apply wf_FOLDR_delete | apply wf_get_live_exp
               | apply wf_union; split ].

Ltac eq_cases :=
  repeat match goal with
  | |- context [?u = ?v] =>
      lazymatch type of u with
      | N => assert_fails (constr_eq u v);
             lazymatch goal with
             | _ : u <> v |- _ => fail
             | _ : v <> u |- _ => fail
             | _ => destruct (N.eq_dec u v) as [?E|?E]; [try subst u|]
             end
      end
  end.

Lemma domain_list_insert_eq xs (t : num_set) : domain (list_insert xs t) = set xs UNION domain t.
Proof.
  apply set_ext; intros x. unfold pred_set.UNION. change (set xs x) with (x IN set xs).
  rewrite domain_list_insert, IN_set, MEM_iff'. unfold pred_set.IN; tauto.
Qed.

Ltac head_constructor p := match p with ?h _ _ _ _ _ _ => h | ?h _ _ _ _ _ => h | ?h _ _ _ _ => h | ?h _ _ _ => h | ?h _ _ => h | ?h _ => h | ?h => h end.

Ltac dom_solve :=
  apply set_ext; let x := fresh "x" in intros x;
  rewrite ?get_reads_exp_get_live_exp, ?domain_list_insert_eq;
  set_simp; cbn [LIST_TO_SET] in *; rewrite ?get_reads_exp_get_live_exp; set_simp;
  eq_cases; first [tauto | intuition congruence].

Lemma set_spec f t (live flive livein flivein : num_set) :
  check_clash_tree f (reg_alloc.Set_ t) live flive = Some (livein, flivein) ->
  livein = t /\ INJ f (domain t) UNIV /\ domain flivein = IMAGE f (domain t).
Proof.
  intros H. cbn [check_clash_tree] in H. destruct (check_col_INJ f t livein flivein H) as (-> & I & D). auto.
Qed.

Lemma check_clash_tree_Seq f t1 t2 (live flive : num_set) :
  check_clash_tree f (reg_alloc.Seq t1 t2) live flive =
  match check_clash_tree f t2 live flive with
  | None => None
  | Some (t2_out, ft2_out) => check_clash_tree f t1 t2_out ft2_out
  end.
Proof. reflexivity. Qed.

Ltac dom_eq Dom :=
  let x := fresh "x" in intros x; rewrite Dom; cbn [get_live]; set_simp; eq_cases; first [tauto | intuition congruence].

Lemma EVERY_oEL {A} (P : A -> bool) l n x : EVERY P l -> oEL n l = Some x -> P x.
Proof.
  revert n; induction l as [|y l IH]; intros n He Ho; [discriminate|].
  cbn [EVERY oEL] in *. apply andb_prop in He as [Hy Hl].
  destruct (n =? 0); [injection Ho as <-; exact Hy|exact (IH _ Hl Ho)].
Qed.

Lemma INJ_union_LN (f : N -> N) (live : num_set) : INJ f (domain live) UNIV -> INJ f (domain (union LN live)) UNIV.
Proof. intros H; exact H. Qed.

Lemma clash_tree_colouring_ok_aux : forall (prog : prog a) lt f (live flive livein flivein : num_set),
  wf_cutsets prog -> wf live -> EVERY (fun '(n, e) => wf n && wf e) lt ->
  domain flive = IMAGE f (domain live) -> INJ f (domain live) UNIV ->
  check_clash_tree f (get_clash_tree prog lt) live flive = Some (livein, flivein) ->
  hide (wf livein /\ INJ f (domain livein) UNIV /\ colouring_ok f prog live lt /\
        livein = get_live prog live lt /\ domain flivein = IMAGE f (domain livein)).
Proof.
  intros prog.
  induction prog as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind; intros lt f live flive livein flivein Hwc W Hlt Hd Hi H.
  all: try (eapply delta_case; [reflexivity|cbn [colouring_ok]; reflexivity|cbn [get_live]; wf_solve
           |cbn [get_live]; dom_solve|cbn [get_writes]; set_solve
           |exact W|exact Hd|exact Hi|exact H]).
  { (* Move *)
    eapply delta_case; [reflexivity|cbn [colouring_ok]; reflexivity|cbn [get_live]; wf_solve| | |exact W|exact Hd|exact Hi|exact H].
    + cbn [get_live]. rewrite domain_numset_list_insert, domain_FOLDR_delete. apply set_ext; intros x.
      unfold pred_set.UNION, pred_set.DIFF, pred_set.IN. change (set (MAP SND moves) x) with (x IN set (MAP SND moves)).
      change (set (MAP FST moves) x) with (x IN set (MAP FST moves)). rewrite !IN_set, MEM_iff'. tauto.
    + cbn [get_writes]. rewrite domain_numset_list_insert. intros x [Hx|Hx]; [destruct Hx|exact Hx]. }
  { (* Inst *)
    destruct_inst i; destruct (dimindex a =? 64) eqn:E64;
      (eapply delta_case; [cbn [get_clash_tree get_delta_inst]; rewrite ?E64; reflexivity
        | cbn [colouring_ok]; reflexivity
        | cbn [get_live get_live_inst]; rewrite ?E64; wf_solve
        | cbn [get_live get_live_inst]; rewrite ?E64; dom_solve
        | cbn [get_writes get_writes_inst]; rewrite ?E64; set_solve
        | exact W|exact Hd|exact Hi|exact H]). }
  - (* MustTerminate *)
    cbn [get_clash_tree] in H. cbn [wf_cutsets] in Hwc. exact (IHq lt f live flive livein flivein Hwc W Hlt Hd Hi H).
  - (* Call *)
    destruct ret as [[vs [cs [rh [l1 l2]]]]|].
    2:{ cbn [get_clash_tree] in H. destruct (set_spec _ _ _ _ _ _ H) as (-> & I & D).
        unfold hide; cbn [colouring_ok get_live]; cbv zeta.
        split; [apply wf_numset_list_insert; reflexivity|split; [exact I|split; [split; [exact I|apply INJ_union_LN, Hi]|split; [reflexivity|exact D]]]]. }
    cbn [wf_cutsets] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [Hwc Hwh]. apply andb_prop in Hwc as [Hwn Hwr].
    unfold wf_names in Hwn. apply andb_prop in Hwn as [Wc1 Wc2]. destruct cs as [c1 c2]. cbn [FST SND fst snd] in *.
    cbn [get_clash_tree] in H. cbv zeta in H.
    destruct h as [[hv [hp [hl1 hl2]]]|].
    + cbn [check_clash_tree FST SND fst snd] in H.
      destruct (check_clash_tree f (get_clash_tree rh lt) live flive) as [[lr flr]|] eqn:Er; [|discriminate].
      destruct (IHret lt f live flive lr flr Hwr W Hlt Hd Hi Er) as (Wr & Ir & Cr & -> & Dr).
      destruct (check_col f (numset_list_insert vs (union c1 c2))) as [[lv flv]|] eqn:Ev; [|discriminate].
      destruct (check_col_INJ _ _ _ _ Ev) as (-> & Iv & Dv).
      destruct (check_clash_tree f (get_clash_tree hp lt) live flive) as [[lh flh]|] eqn:Eh; [|discriminate].
      destruct (IHh lt f live flive lh flh Hwh W Hlt Hd Hi Eh) as (Wh & Ih & Ch & -> & Dh).
      destruct (check_col f (insert hv tt (union c1 c2))) as [[lh2 flh2]|] eqn:Eh2; [|discriminate].
      destruct (check_col_INJ _ _ _ _ Eh2) as (-> & Ih2 & Dh2).
      destruct (check_col_INJ f _ livein flivein H) as (-> & I & D).
      unfold hide; cbn [colouring_ok get_live]; cbv zeta.
      split; [apply wf_union; split; [apply wf_union; split; assumption|apply wf_numset_list_insert; reflexivity]|].
      split; [exact I|]. split; [|split; [reflexivity|exact D]].
      rewrite union_num_set_sym with (t1 := c2).
      split; [exact I|split; [exact Iv|split; [exact Cr|split; [exact Ih2|exact Ch]]]].
    + cbn [check_clash_tree FST SND fst snd] in H.
      destruct (check_clash_tree f (get_clash_tree rh lt) live flive) as [[lr flr]|] eqn:Er; [|discriminate].
      destruct (IHret lt f live flive lr flr Hwr W Hlt Hd Hi Er) as (Wr & Ir & Cr & -> & Dr).
      destruct (check_col f (numset_list_insert vs (union c1 c2))) as [[lv flv]|] eqn:Ev; [|discriminate].
      destruct (check_col_INJ _ _ _ _ Ev) as (-> & Iv & Dv).
      destruct (check_col_INJ _ _ _ _ H) as (-> & I & D).
      unfold hide; cbn [colouring_ok get_live]; cbv zeta.
      split; [apply wf_union; split; [apply wf_union; split; assumption|apply wf_numset_list_insert; reflexivity]|].
      split; [exact I|]. split; [|split; [reflexivity|exact D]].
      rewrite union_num_set_sym with (t1 := c2).
      split; [exact I|split; [exact Iv|split; [exact Cr|exact Logic.I]]].
  - (* Seq *)
    cbn [wf_cutsets] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [Hw1 Hw2].
    cbn [get_clash_tree check_clash_tree] in H.
    destruct (check_clash_tree f (get_clash_tree q2 lt) live flive) as [[l2 fl2]|] eqn:E2; [|discriminate].
    destruct (IH2 lt f live flive l2 fl2 Hw2 W Hlt Hd Hi E2) as (W2 & I2 & C2 & -> & D2).
    destruct (IH1 lt f _ fl2 livein flivein Hw1 W2 Hlt D2 I2 H) as (W1 & I1 & C1 & -> & D1).
    unfold hide; cbn [colouring_ok get_live]; cbv zeta. auto 10.
  - (* If *)
    cbn [wf_cutsets] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [Hw1 Hw2].
    assert (HB : forall livein flivein,
      check_clash_tree f (reg_alloc.Branch None (get_clash_tree q1 lt) (get_clash_tree q2 lt)) live flive = Some (livein, flivein) ->
      livein = union (get_live q1 live lt) (get_live q2 live lt) /\ wf livein /\ INJ f (domain livein) UNIV /\
      domain flivein = IMAGE f (domain livein) /\ colouring_ok f q1 live lt /\ colouring_ok f q2 live lt).
    { intros li fli HBr. cbn [check_clash_tree] in HBr.
      destruct (check_clash_tree f (get_clash_tree q1 lt) live flive) as [[l1 fl1]|] eqn:E1; [|discriminate].
      destruct (IH1 lt f live flive l1 fl1 Hw1 W Hlt Hd Hi E1) as (W1 & I1 & C1 & -> & D1).
      destruct (check_clash_tree f (get_clash_tree q2 lt) live flive) as [[l2 fl2]|] eqn:E2; [|discriminate].
      destruct (IH2 lt f live flive l2 fl2 Hw2 W Hlt Hd Hi E2) as (W2 & I2 & C2 & -> & D2).
      destruct (check_partial_col_INJ _ f _ _ li fli (conj W1 (conj D1 (conj I1 HBr)))) as (Wm & -> & Im & Dm).
      assert (Hm : numset_list_insert (MAP fst (toAList (difference (get_live q2 live lt) (get_live q1 live lt))))
                     (get_live q1 live lt) = union (get_live q1 live lt) (get_live q2 live lt)).
      2:{ split; [exact Hm|split; [exact Wm|split; [exact Im|split; [exact Dm|split; assumption]]]]. }
      apply num_set_eq; [exact Wm|apply wf_union; split; assumption|].
      intros x. rewrite domain_numset_list_insert, domain_union, IN_UNION, IN_set, in_map_iff.
      unfold pred_set.IN. split.
      - intros [Hx|[[k []] [<- Hk]]]; [left; exact Hx|]. apply ALOOKUP_toAList_In in Hk.
        rewrite lookup_difference in Hk. destruct (decide _); [|discriminate].
        right. apply IN_domain_iff; eauto.
      - intros [Hx|Hx]; [left; exact Hx|].
        destruct (lookup x (get_live q1 live lt)) as [v|] eqn:E; [left; apply IN_domain_iff; eauto|right].
        apply IN_domain_iff in Hx as [[] Hx]. exists (x, tt); split; [reflexivity|].
        apply ALOOKUP_toAList_In. rewrite lookup_difference. rewrite decide_True' by exact E. exact Hx. }
    cbn [get_clash_tree] in H.
    destruct ri as [r2|w]; rewrite check_clash_tree_Seq in H;
    (destruct (check_clash_tree f (reg_alloc.Branch None (get_clash_tree q1 lt) (get_clash_tree q2 lt)) live flive)
      as [[lb flb]|] eqn:EB; [|discriminate]);
    destruct (HB lb flb eq_refl) as (-> & Wb & Ib & Db & C1 & C2).
    + destruct (delta_spec f [] [r; r2] _ _ livein flivein Wb Db Ib H) as (_ & Wl & Il & Dl & Dom).
      assert (E : livein = get_live (If cmp r (Reg r2) q1 q2) live lt).
      { apply num_set_eq; [exact Wl|cbn [get_live]; wf_solve|]. dom_eq Dom. }
      subst livein. unfold hide. split; [exact Wl|split; [exact Il|split; [|split; [reflexivity|exact Dl]]]].
      cbn [colouring_ok]; cbv zeta. split; [exact Il|split; assumption].
    + destruct (delta_spec f [] [r] _ _ livein flivein Wb Db Ib H) as (_ & Wl & Il & Dl & Dom).
      assert (E : livein = get_live (If cmp r (Imm w) q1 q2) live lt).
      { apply num_set_eq; [exact Wl|cbn [get_live]; wf_solve|]. dom_eq Dom. }
      subst livein. unfold hide. split; [exact Wl|split; [exact Il|split; [|split; [reflexivity|exact Dl]]]].
      cbn [colouring_ok]; cbv zeta. split; [exact Il|split; assumption].
  - (* Loop *)
    cbn [wf_cutsets] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [Hwc Hwq]. apply andb_prop in Hwc as [Wn We].
    cbn [get_clash_tree] in H. rewrite !check_clash_tree_Seq in H.
    destruct (check_col f names) as [[n0 fn0]|] eqn:E0; cbn [check_clash_tree] in H; rewrite ?E0 in H; [|discriminate].
    destruct (check_col_INJ _ _ _ _ E0) as (-> & In & Dn).
    destruct (check_clash_tree f (get_clash_tree q ((names, exit_names) :: lt)) names fn0) as [[lb flb]|] eqn:Eb;
      [|discriminate].
    destruct (IHq ((names, exit_names) :: lt) f names fn0 lb flb Hwq Wn) as (Wb & Ib & Cb & -> & Db);
      [cbn [EVERY]; rewrite Wn, We; exact Hlt|exact Dn|exact In|exact Eb|].
    cbn [check_clash_tree] in H.
    destruct (check_col f exit_names) as [[e0 fe0]|] eqn:Ee; [|discriminate].
    destruct (check_col_INJ _ _ _ _ Ee) as (-> & Ie & De).
    injection H as <- <-.
    unfold hide; cbn [colouring_ok get_live]. auto 10.
  - (* Alloc *)
    cbn [wf_cutsets wf_names] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [W1 W2].
    cbn [get_clash_tree] in H. rewrite check_clash_tree_Seq in H.
    destruct (check_clash_tree f (reg_alloc.Set_ (union (FST anames) (SND anames))) live flive)
      as [[l0 fl0]|] eqn:E0; [|discriminate].
    destruct (set_spec _ _ _ _ _ _ E0) as (-> & I0 & D0).
    assert (Wu : wf (union (FST anames) (SND anames))) by (apply wf_union; split; assumption).
    destruct (delta_spec f [] [an] _ _ livein flivein Wu D0 I0 H) as (_ & Wl & Il & Dl & Dom).
    assert (E : livein = get_live (@Alloc a an anames) live lt).
    { apply num_set_eq; [exact Wl|cbn [get_live]; wf_solve|]. dom_eq Dom. }
    subst livein. unfold hide. split; [exact Wl|split; [exact Il|split; [|split; [reflexivity|exact Dl]]]].
    cbn [colouring_ok]; cbv zeta. split; [exact Il|apply INJ_union_LN, Hi].
  - (* Break *)
    cbn [get_clash_tree] in H. destruct (oEL k lt) as [[nm ex]|] eqn:Eo.
    + destruct (set_spec _ _ _ _ _ _ H) as (-> & I & D).
      pose proof (EVERY_oEL _ _ _ _ Hlt Eo) as Wx. cbn beta iota in Wx. apply andb_prop in Wx as [_ Wx].
      unfold hide; cbn [colouring_ok get_live]; cbv zeta; rewrite Eo.
      split; [exact Wx|split; [exact I|split; [split; [exact I|apply INJ_union_LN, Hi]|split; [reflexivity|exact D]]]].
    + destruct (set_spec _ _ _ _ _ _ H) as (-> & I & D).
      unfold hide; cbn [colouring_ok get_live]; cbv zeta; rewrite Eo.
      split; [reflexivity|split; [exact I|split; [split; [exact I|apply INJ_union_LN, Hi]|split; [reflexivity|exact D]]]].
  - (* Continue *)
    cbn [get_clash_tree] in H. destruct (oEL k lt) as [[nm ex]|] eqn:Eo.
    + destruct (set_spec _ _ _ _ _ _ H) as (-> & I & D).
      pose proof (EVERY_oEL _ _ _ _ Hlt Eo) as Wx. cbn beta iota in Wx. apply andb_prop in Wx as [Wx _].
      unfold hide; cbn [colouring_ok get_live]; cbv zeta; rewrite Eo.
      split; [exact Wx|split; [exact I|split; [split; [exact I|apply INJ_union_LN, Hi]|split; [reflexivity|exact D]]]].
    + destruct (set_spec _ _ _ _ _ _ H) as (-> & I & D).
      unfold hide; cbn [colouring_ok get_live]; cbv zeta; rewrite Eo.
      split; [reflexivity|split; [exact I|split; [split; [exact I|apply INJ_union_LN, Hi]|split; [reflexivity|exact D]]]].
  - (* Install *)
    cbn [wf_cutsets wf_names] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [W1 W2].
    cbn [get_clash_tree] in H. rewrite !check_clash_tree_Seq in H.
    destruct (check_clash_tree f (Delta [r1] []) live flive) as [[l0 fl0]|] eqn:E0; [|discriminate].
    destruct (delta_spec f [r1] [] _ _ _ _ W Hd Hi E0) as (Iw & _ & _ & _ & _).
    destruct (check_clash_tree f (reg_alloc.Set_ (union (FST inames) (SND inames))) l0 fl0)
      as [[l1 fl1]|] eqn:E1; [|discriminate].
    destruct (set_spec _ _ _ _ _ _ E1) as (-> & I1 & D1).
    assert (Wu : wf (union (FST inames) (SND inames))) by (apply wf_union; split; assumption).
    destruct (delta_spec f [] [r4; r3; r2; r1] _ _ livein flivein Wu D1 I1 H) as (_ & Wl & Il & Dl & Dom).
    assert (E : livein = get_live (@Install a r1 r2 r3 r4 inames) live lt).
    { apply num_set_eq; [exact Wl|cbn [get_live]; wf_solve|]. intros x; rewrite Dom; cbn [get_live].
      rewrite domain_list_insert_eq. set_simp; eq_cases; first [tauto | intuition congruence]. }
    subst livein. unfold hide. split; [exact Wl|split; [exact Il|split; [|split; [reflexivity|exact Dl]]]].
    cbn [colouring_ok get_writes]; cbv zeta. split; [exact Il|].
    eapply INJ_less; split; [exact Iw|]. set_solve.
  - (* FFI *)
    cbn [wf_cutsets wf_names] in Hwc. unfold is_true in Hwc. apply andb_prop in Hwc as [W1 W2].
    cbn [get_clash_tree] in H. rewrite check_clash_tree_Seq in H.
    destruct (check_clash_tree f (reg_alloc.Set_ (union (FST fnames) (SND fnames))) live flive)
      as [[l0 fl0]|] eqn:E0; [|discriminate].
    destruct (set_spec _ _ _ _ _ _ E0) as (-> & I0 & D0).
    assert (Wu : wf (union (FST fnames) (SND fnames))) by (apply wf_union; split; assumption).
    destruct (delta_spec f [] [r1; r2; r3; r4] _ _ livein flivein Wu D0 I0 H) as (_ & Wl & Il & Dl & Dom).
    assert (E : livein = get_live (@FFI a fi r1 r2 r3 r4 fnames) live lt).
    { apply num_set_eq; [exact Wl|cbn [get_live]; wf_solve|]. dom_eq Dom. }
    subst livein. unfold hide. split; [exact Wl|split; [exact Il|split; [|split; [reflexivity|exact Dl]]]].
    cbn [colouring_ok]; cbv zeta. split; [exact Il|apply INJ_union_LN, Hi].
  - (* ShareInst *)
    destruct op;
    (let E := fresh "Eso" in
     match goal with |- context [ShareInst ?o _ _] =>
       assert (E : is_store_op o = ltac:(let b := eval vm_compute in (is_store_op o) in exact b)) by reflexivity
     end;
     eapply delta_case; [cbn [get_clash_tree]; rewrite E; reflexivity
       | cbn [colouring_ok]; reflexivity
       | cbn [get_live]; rewrite E; wf_solve
       | cbn [get_live]; rewrite E; dom_solve
       | cbn [get_writes]; set_solve
       | exact W|exact Hd|exact Hi|exact H]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok" *)
Theorem clash_tree_colouring_ok : forall (prog : prog a) lt f (live flive livein flivein : num_set),
  wf_cutsets prog /\
  wf live /\
  EVERY (fun '(n, e) => wf n && wf e) lt /\
  domain flive = IMAGE f (domain live) /\
  INJ f (domain live) UNIV /\
  check_clash_tree f (get_clash_tree prog lt) live flive = Some (livein, flivein) ->
  hide (wf livein /\
        INJ f (domain livein) UNIV /\
        colouring_ok f prog live lt /\
        livein = get_live prog live lt /\
        domain flivein = IMAGE f (domain livein)).
Proof.
  intros prog lt f live flive livein flivein (Hwc & W & Hlt & Hd & Hi & H).
  exact (clash_tree_colouring_ok_aux prog lt f live flive livein flivein Hwc W Hlt Hd Hi H).
Qed.

End Clash.

(** ** [word_alloc_correct] *)

(** Actually, it should probably be exactly 0, 2, 4, 6, ... (HOL's comment). *)
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "even_starting_locals_def" *)
Definition even_starting_locals {a} (locs : num_map (word_loc a)) : Prop :=
  forall x, x IN domain locs -> is_phy_var x.

Section Forced.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_forced_tail_split" *)
Theorem get_forced_tail_split : forall (c0 : asm_config a) (p : prog a) ls ls',
  get_forced c0 p (ls ++ ls') = get_forced c0 p ls ++ ls'.
Proof.
  intros c0 p; induction p as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind; intros ls ls'; cbn [get_forced]; try reflexivity.
  - destruct_inst i; try reflexivity; repeat (destruct (_ : bool)); rewrite ?app_assoc; reflexivity.
  - apply IHq.
  - destruct ret as [[x1 [x2 [rh [l1 l2]]]]|]; [|reflexivity]. cbn in IHret.
    destruct h as [[hv [hp [hl1 hl2]]]|]; cbn in IHh; [rewrite IHret, IHh; reflexivity|apply IHret].
  - rewrite IH2, IH1; reflexivity.
  - rewrite IH2, IH1; reflexivity.
  - apply IHq.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "EVERY_get_forced" *)
Theorem EVERY_get_forced : forall (P : N * N -> bool) (c0 : asm_config a) (p : prog a) ls,
  EVERY P (get_forced c0 p ls) = EVERY P (get_forced c0 p []) && EVERY P ls.
Proof.
  intros P c0 p ls. rewrite <- (app_nil_l ls) at 1. rewrite get_forced_tail_split.
  apply eq_true_iff_eq. unfold is_true. rewrite andb_true_iff, !EVERY_Forall, Forall_app. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_forced_pairwise_distinct" *)
Theorem get_forced_pairwise_distinct : forall (c0 : asm_config a) (prog : prog a) ls,
  EVERY (fun '(x, y) => negb (x =? y)) ls ->
  EVERY (fun '(x, y) => negb (x =? y)) (get_forced c0 prog ls).
Proof.
  intros c0 p; induction p as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind; intros ls Hls; cbn [get_forced]; try exact Hls.
  - destruct_inst i; try exact Hls;
      repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
      cbn [EVERY APPEND app]; rewrite ?Hls; try reflexivity;
      repeat match goal with H : (_ =? _) = _ |- _ => rewrite H end; cbn; rewrite ?Hls; try reflexivity;
      repeat match goal with H : (_ && negb _) = true |- _ => apply andb_prop in H as [_ ?] end;
      repeat match goal with H : negb _ = true |- _ => rewrite H end; cbn; rewrite ?Hls; reflexivity.
  - apply IHq, Hls.
  - destruct ret as [[x1 [x2 [rh [l1 l2]]]]|]; [|exact Hls]. cbn in IHret.
    destruct h as [[hv [hp [hl1 hl2]]]|]; cbn in IHh; [apply IHh, IHret, Hls|apply IHret, Hls].
  - apply IH1, IH2, Hls.
  - apply IH1, IH2, Hls.
  - apply IHq, Hls.
Qed.

Lemma EVERY_pair_iff (P : N -> Prop) (l : list (N * N)) :
  is_true (EVERY (fun '(x, y) => ⌜P x /\ P y⌝) l) <-> (forall x y, In (x, y) l -> P x /\ P y).
Proof.
  unfold is_true; rewrite EVERY_Forall, Forall_forall. split.
  - intros H x y Hin. specialize (H (x, y) Hin). apply bool_decide_spec in H. exact H.
  - intros H [x y] Hin. apply bool_decide_spec, H, Hin.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "get_forced_in_get_clash_tree" *)
Theorem get_forced_in_get_clash_tree : forall (prog : prog a) lt (c0 : asm_config a),
  EVERY (fun '(x, y) => ⌜in_clash_tree (get_clash_tree prog lt) x /\ in_clash_tree (get_clash_tree prog lt) y⌝)
    (get_forced c0 prog []).
Proof.
  intros p; induction p as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind; intros lt c0; cbn [get_forced]; try reflexivity.
  - apply EVERY_pair_iff. intros x y Hin.
    destruct_inst i; cbn [get_clash_tree get_delta_inst in_clash_tree] in *; try destruct Hin;
      repeat match goal with H : context [if ?b then _ else _] |- _ => destruct b eqn:? end;
      repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
      try (match goal with H1 : (dimindex a =? 64) = true, H2 : ((dimindex a =? 32) && _) = true |- _ =>
             apply andb_prop in H2 as [H2 _]; apply N.eqb_eq in H1, H2; rewrite H1 in H2; discriminate end);
      cbn [app In] in Hin; try contradiction;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H as [H|H]
             | H : (_, _) = (_, _) |- _ => injection H as <- <-
             end; try contradiction;
      cbn [in_clash_tree]; unfold is_true; rewrite ?MEM_In; cbn [In]; tauto.
  - exact (IHq lt c0).
  - destruct ret as [[x1 [cs [rh [l1 l2]]]]|]; [|reflexivity]. cbn in IHret.
    apply EVERY_pair_iff. intros x y Hin. cbn [get_clash_tree].
    destruct h as [[hv [hp [hl1 hl2]]]|]; cbn in IHh.
    + rewrite <- (app_nil_l (get_forced c0 rh [])), get_forced_tail_split in Hin. apply in_app_iff in Hin as [Hin|Hin].
      * pose proof (proj1 (EVERY_pair_iff _ _) (IHh lt c0) x y Hin) as [Hx Hy].
        cbn [in_clash_tree]. split; right; left; right; assumption.
      * pose proof (proj1 (EVERY_pair_iff _ _) (IHret lt c0) x y Hin) as [Hx Hy].
        cbn [in_clash_tree]. split; left; right; assumption.
    + pose proof (proj1 (EVERY_pair_iff _ _) (IHret lt c0) x y Hin) as [Hx Hy].
      cbn [in_clash_tree]. split; right; right; assumption.
  - apply EVERY_pair_iff. intros x y Hin.
    rewrite <- (app_nil_l (get_forced c0 q2 [])), get_forced_tail_split in Hin. apply in_app_iff in Hin as [Hin|Hin].
    + pose proof (proj1 (EVERY_pair_iff _ _) (IH1 lt c0) x y Hin) as [Hx Hy]. cbn [get_clash_tree in_clash_tree]. auto.
    + pose proof (proj1 (EVERY_pair_iff _ _) (IH2 lt c0) x y Hin) as [Hx Hy]. cbn [get_clash_tree in_clash_tree]. auto.
  - apply EVERY_pair_iff. intros x y Hin.
    rewrite <- (app_nil_l (get_forced c0 q2 [])), get_forced_tail_split in Hin. apply in_app_iff in Hin as [Hin|Hin].
    + pose proof (proj1 (EVERY_pair_iff _ _) (IH1 lt c0) x y Hin) as [Hx Hy].
      cbn [get_clash_tree]; destruct ri; cbn [in_clash_tree]; auto.
    + pose proof (proj1 (EVERY_pair_iff _ _) (IH2 lt c0) x y Hin) as [Hx Hy].
      cbn [get_clash_tree]; destruct ri; cbn [in_clash_tree]; auto.
  - apply EVERY_pair_iff. intros x y Hin.
    pose proof (proj1 (EVERY_pair_iff _ _) (IHq ((names, exit_names) :: lt) c0) x y Hin) as [Hx Hy].
    cbn [get_clash_tree in_clash_tree]. auto.
Qed.

End Forced.



(** ** Selecting the allocator *)

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "select_reg_alloc_correct" *)
Theorem select_reg_alloc_correct : forall alg spillcosts k heu_moves tree forced fs,
  EVERY (fun '(r1, r2) => ⌜in_clash_tree tree r1 /\ in_clash_tree tree r2⌝) forced ->
  exists spcol livein flivein,
    select_reg_alloc alg spillcosts k heu_moves tree forced fs = M_success spcol /\
    check_clash_tree (sp_default spcol) tree LN LN = Some (livein, flivein) /\
    (forall r, in_clash_tree tree r ->
       r IN domain spcol /\
       (if is_phy_var r then sp_default spcol r = r DIV 2
        else if is_stack_var r then k <= sp_default spcol r
        else True)) /\
    (forall r, r IN domain spcol -> in_clash_tree tree r) /\
    EVERY (fun '(r1, r2) => ⌜sp_default spcol r1 = sp_default spcol r2 -> r1 = r2⌝) forced.
Proof.
  intros alg spillcosts k heu_moves tree forced fs Hf. unfold select_reg_alloc.
  destruct (4 <=? alg).
  - exact (linear_scanProof.linear_scan_reg_alloc_correct k heu_moves tree forced Hf).
  - exact (reg_alloc_correct _ spillcosts k heu_moves tree forced fs Hf).
Qed.

(** HOL's [word_allocTheory.total_colour_alt] (not ported in [word_alloc.v];
    Galette-only restatement). *)
Lemma total_colour_alt' (col : num_map N) : total_colour col = (fun x => 2 * x) ∘ sp_default col.
Proof.
  apply functional_extensionality; intros x. unfold total_colour, sp_default.
  destruct (lookup x col); [reflexivity|]. destruct (is_phy_var x) eqn:E; [|reflexivity].
  unfold is_phy_var in E. apply N.eqb_eq in E. pose proof (N.div_mod x 2 ltac:(lia)). lia.
Qed.

Lemma domain_LN_IMAGE (f : N -> N) : domain (LN : num_set) = IMAGE f (domain (LN : num_set)).
Proof. apply set_ext; intros x; unfold pred_set.IMAGE, pred_set.IN; cbn; split; [intros []|intros [y [_ []]]]. Qed.

Lemma INJ_LN (f : N -> N) : INJ f (domain (LN : num_set)) UNIV.
Proof. split; [intros; exact Logic.I|intros x y [[] _]]. Qed.

Section WordAllocCorrect.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma apply_colour_correct_LN (prog : prog a) (st : state) f q r :
  wf_cutsets prog ->
  check_clash_tree f (get_clash_tree prog []) LN LN = Some (q, r) ->
  (forall n, n IN domain (locals st) -> f n = n) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res', rcst) := evaluate (apply_colour f prog, st) in
    res = res' /\ word_state_eq_rel rst rcst /\
    match res with
    | NONE => True
    | SOME (Break _) => True
    | SOME (Continue _) => True
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros Hwc Hc Hf.
  destruct (clash_tree_colouring_ok prog [] f LN LN q r) as (_ & _ & Cq & _ & _).
  { repeat split; try reflexivity; try exact Hwc; [apply domain_LN_IMAGE|apply INJ_LN|exact Hc]. }
  destruct (evaluate_apply_colour prog st st f LN []) as [perm Hp].
  { split; [exact Cq|split; [apply word_state_eq_rel_refl|]].
    intros n v [_ Hl]. rewrite Hf; [exact Hl|apply IN_domain_iff; eauto]. }
  exists perm. destruct (evaluate (prog, set_permute perm st)) as [res rst].
  destruct (bool_decide _); [exact Logic.I|].
  destruct (evaluate (apply_colour f prog, st)) as [res' rcst].
  destruct Hp as (<- & Hw & Hpost). split; [reflexivity|split; [exact Hw|]].
  destruct res as [[]|]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "word_alloc_correct" *)
Theorem word_alloc_correct : forall fc (c0 : asm_config a) alg (prog : prog a) k col_opt (st : state),
  even_starting_locals (locals st) /\ wf_cutsets prog ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res', rcst) := evaluate (word_alloc fc c0 alg k prog col_opt, st) in
    res = res' /\ word_state_eq_rel rst rcst /\
    match res with
    | NONE => True
    | SOME (Break _) => True
    | SOME (Continue _) => True
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros fc c0 alg prog k col_opt st [He Hwc]. unfold word_alloc. cbv zeta.
  destruct (oracle_colour_ok k col_opt (get_clash_tree prog []) prog (get_forced c0 prog [])) as [cp|] eqn:Eo.
  - unfold oracle_colour_ok in Eo. destruct col_opt as [col|]; [|discriminate].
    destruct (every_even_colour col) eqn:Ee; [|discriminate].
    destruct (check_clash_tree (total_colour col) (get_clash_tree prog []) LN LN) as [[q r]|] eqn:Ec;
      [|discriminate]. cbn [andb] in Eo. cbv zeta in Eo.
    destruct (_ && _); [|discriminate]. injection Eo as <-.
    apply (apply_colour_correct_LN prog st _ q r Hwc Ec).
    intros n Hn. pose proof (He n Hn) as Hp. unfold total_colour.
    destruct (lookup n col) as [x|] eqn:Ex; [|rewrite Hp; reflexivity].
    unfold every_even_colour in Ee. unfold is_true in Ee. rewrite EVERY_Forall, Forall_forall in Ee.
    specialize (Ee (n, x) (proj2 (ALOOKUP_toAList_In _ _ _) Ex)). cbn beta iota in Ee. rewrite Hp in Ee.
    apply N.eqb_eq in Ee. unfold is_phy_var in Hp. apply N.eqb_eq in Hp. pose proof (N.div_mod n 2 ltac:(lia)). lia.
  - destruct (get_heuristics alg fc prog) as [heu_moves spillcosts].
    destruct (select_reg_alloc_correct alg spillcosts k heu_moves (get_clash_tree prog [])
                (get_forced c0 prog []) (get_stack_only prog) (get_forced_in_get_clash_tree prog [] c0))
      as (spcol & livein & flivein & Es & Hc & Hin & Hdom & _).
    rewrite Es.
    pose proof (check_clash_tree_INJ (get_clash_tree prog []) (sp_default spcol) (fun x => 2 * x) LN LN LN) as Hg.
    rewrite Hc in Hg. destruct Hg as (gl & Eg & _).
    { split; [|apply domain_LN_IMAGE]. split; [intros; exact Logic.I|]. intros x y _ E; lia. }
    rewrite <- total_colour_alt' in Eg.
    apply (apply_colour_correct_LN prog st _ livein gl Hwc Eg).
    intros n Hn. pose proof (He n Hn) as Hp. unfold total_colour.
    destruct (lookup n spcol) as [x|] eqn:Ex; [|rewrite Hp; reflexivity].
    assert (Hd : n IN domain spcol) by (apply IN_domain_iff; eauto).
    destruct (Hin n (Hdom n Hd)) as [_ Hs]. rewrite Hp in Hs. unfold sp_default in Hs. rewrite Ex in Hs.
    unfold is_phy_var in Hp. apply N.eqb_eq in Hp. pose proof (N.div_mod n 2 ltac:(lia)). lia.
Qed.

End WordAllocCorrect.
