(** * CakeML Pancake [pan_structsProof]: correctness of [pan_structs]

    Port of [cakeml/pancake/proofs/pan_structsProofScript.sml].

    Carrier and statement notes:
    - [pan_structs]'s [context] has fields [structs]/[locals]/[globals],
      as does [panSem]'s [state]; the context fields are written qualified
      ([pan_structs.structs ctxt]).  HOL's [ctxt with locals := l] is a
      record construction.
    - [v_flds_ok] is a [bool] (as in HOL); [struct_infos_ok] is a [Prop]
      (HOL defines it by [<=>] with a quantified conjunct).
    - [compile_shape_n] terminates in HOL by the lexicographic measure
      (context length minus [n], shape size); here it runs on a fuel
      bounding [LENGTH sctxt - n] ([compile_shape_n_f]) and HOL's equations
      are the tagged [compile_shape_n_def].  HOL's generated induction
      theorem [compile_shape_n_ind] is the Galette-only
      [compile_shape_n_ind'].  It is typed at [pan_structs]'s context type
      [sctxt_ty] (HOL infers a type polymorphic in the field-name type).
    - HOL's [mem_load_rec1], [mem_load_rec] (instances of [mem_load_def]),
      [convert_res_eq_case1], [convert_res_eq_case], [convert_res_eq_NONE],
      [compile_shape_n_eq_rev], [mem_load_conversion_inst] and
      [shape_of_convert_v_rev] are [local] rewriting forms of other
      theorems; they are ported as plain theorems with HOL's statements.
    - In [compile_top_semantics_decls], HOL's record literal
      [<| structs := [] |>] (other fields [ARB]) is written with [ARB]
      for [locals] and [globals].
    - [semantics_eq] is proved directly from [compile_correct] by comparing
      the clocked runs (HOL goes through [panProps]'s [semantics_wrapper],
      not ported).

    Proof method: HOL's [recInduct evaluate_ind] is well-founded induction
    on [eval_lt] ([panSem]); a case of [evaluate] is unfolded with
    [evaluate_eqn]/[evaluate_def].  Galette-only helpers (list lemmas
    bridging [N]-indexed HOL list operations and [Stdlib.List], nested
    inductions) carry no tag. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.pancake Require Import panLang pan_structs.
From Galette.cakeml.pancake.semantics Require Import panSem pan_commonProps panProps.
Open Scope N_scope.
Local Open Scope fmap_scope.

(** Equality on HOL types in statements ([MEM], [ALL_DISTINCT]) without a
    computable decision procedure. *)
#[local] Instance eq_dec_cl {A} : EqDecision A | 1000 := fun x y => classical_dec (x = y).

#[local] Instance struct_info_inhabited : Inhabited struct_info := {| fields := []; size := 0 |}.

(** ** Galette-only list helpers *)

Lemma EL_nth_any {A} `{Inhabited A} n (l : list A) : EL n l = List.nth (N.to_nat n) l ARB.
Proof.
  destruct (N.lt_ge_cases n (LENGTH l)) as [Hl|Hl]; [apply EL_nth, Hl|].
  rewrite nth_overflow by (rewrite LENGTH_length in Hl; lia).
  assert (Hnil : forall m, EL m (@nil A) = ARB).
  { intros m; induction m as [|m IHm] using N.peano_ind; [reflexivity|]. rewrite EL_SUC; exact IHm. }
  revert l Hl; induction n as [|n IH] using N.peano_ind; intros [|h t] Hl.
  - reflexivity.
  - cbn in Hl; lia.
  - apply Hnil.
  - rewrite EL_SUC; cbn [TL]. apply IH. rewrite LENGTH_cons in Hl; lia.
Qed.

Section ListHelpers.
Context {A B : Type}.

Lemma LENGTH_MAP_ (f : A -> B) l : LENGTH (MAP f l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_map; reflexivity. Qed.

Lemma EL_MAP_ `{Inhabited A} `{Inhabited B} (f : A -> B) n l :
  n < LENGTH l -> EL n (MAP f l) = f (EL n l).
Proof.
  intros Hn; rewrite !EL_nth_any. rewrite LENGTH_length in Hn.
  rewrite nth_indep with (d' := f ARB) by (rewrite length_map; lia).
  apply map_nth.
Qed.

Lemma MEM_In_ `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

Lemma OPT_MMAP_length_ (f : A -> option B) xs ys :
  OPT_MMAP f xs = SOME ys -> length ys = length xs.
Proof. intros H; symmetry; eapply OPT_MMAP_LENGTH, H. Qed.

Lemma OPT_MMAP_Forall2 (f : A -> option B) xs ys :
  OPT_MMAP f xs = SOME ys <-> Forall2 (fun x y => f x = SOME y) xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys; cbn.
  - split; [intros H; injection H as <-; constructor|intros H; inversion H; reflexivity].
  - split.
    + destruct (f x) as [y|] eqn:Ef; [|discriminate]; cbn.
      destruct (OPT_MMAP f xs) as [zs|] eqn:Eo; [|discriminate]; cbn.
      intros H; injection H as <-. constructor; [exact Ef|apply IH; reflexivity].
    + intros H; inversion H as [|x' y ? zs Hxy Hr]; subst.
      rewrite Hxy; cbn. apply IH in Hr. rewrite Hr; reflexivity.
Qed.

Lemma Forall2_nth_iff (R : A -> B -> Prop) xs ys d1 d2 :
  Forall2 R xs ys <-> length xs = length ys /\ (forall n, (n < length xs)%nat -> R (nth n xs d1) (nth n ys d2)).
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn.
  - split; [intros _; split; [reflexivity|intros; lia]|constructor].
  - split; [intros H; inversion H|intros [H _]; discriminate].
  - split; [intros H; inversion H|intros [H _]; discriminate].
  - split.
    + intros H; inversion H as [|? ? ? ? Hxy Hr]; subst. apply IH in Hr as [Hl Hn].
      split; [lia|]. intros [|n] Hlt; [exact Hxy|apply Hn; lia].
    + intros [Hl Hn]; constructor; [apply (Hn 0%nat); lia|].
      apply IH; split; [lia|]. intros n Hlt; apply (Hn (Datatypes.S n)); lia.
Qed.

Lemma OPT_MMAP_map_ext (f : A -> option B) (g : B -> B) (h : A -> option B) xs ys :
  OPT_MMAP f xs = SOME ys -> (forall x y, In x xs -> f x = SOME y -> h x = SOME (g y)) ->
  OPT_MMAP h xs = SOME (MAP g ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys H Hfh; cbn in H |- *.
  - injection H as <-; reflexivity.
  - destruct (f x) as [y|] eqn:Ef; [|discriminate]; cbn in H.
    destruct (OPT_MMAP f xs) as [zs|] eqn:Eo; [|discriminate]; cbn in H. injection H as <-.
    rewrite (Hfh x y (or_introl eq_refl) Ef); cbn.
    rewrite (IH zs eq_refl (fun x' y' Hx => Hfh x' y' (or_intror Hx))); reflexivity.
Qed.

Lemma DROP_DROP_ (m n : N) (l : list A) : DROP m (DROP n l) = DROP (n + m) l.
Proof. rewrite !DROP_skipn, skipn_skipn. f_equal. lia. Qed.

Lemma DROP_nth_cons `{Inhabited A} (n : N) (l : list A) :
  n < LENGTH l -> DROP n l = EL n l :: DROP (n + 1) l.
Proof.
  intros Hn; rewrite !DROP_skipn, EL_nth_any. rewrite LENGTH_length in Hn.
  replace (N.to_nat (n + 1)) with (Datatypes.S (N.to_nat n)) by lia.
  assert (Hk : (N.to_nat n < length l)%nat) by lia. clear Hn. revert Hk.
  generalize (N.to_nat n) as k. intros k.
  revert l; induction k as [|k IH]; intros [|x l] Hl; cbn in Hl |- *; try lia.
  - reflexivity.
  - apply IH; lia.
Qed.

End ListHelpers.

Section Defs.
Context {a : N}.

(** ** Basic lemmas *)

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exps_eq_map" *)
Theorem compile_exps_eq_map : forall ctxt, @compile_exps a ctxt = MAP (compile_exp ctxt).
Proof.
  intros ctxt; apply functional_extensionality; intros x.
  induction x as [|e es IH]; cbn; [reflexivity|]. rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_some_el" *)
Theorem opt_mmap_eq_some_el : forall {A B} `{Inhabited A} `{Inhabited B} (f : A -> option B) xs ys,
  OPT_MMAP f xs = SOME ys <->
  LENGTH xs = LENGTH ys /\ (forall n, n < LENGTH ys -> f (EL n xs) = SOME (EL n ys)).
Proof.
  intros A B HA HB f xs ys; rewrite OPT_MMAP_Forall2, Forall2_nth_iff with (d1 := ARB) (d2 := ARB).
  rewrite !LENGTH_length. split.
  - intros [Hl Hn]; split; [lia|]. intros n Hlt. rewrite !EL_nth_any. apply Hn; lia.
  - intros [Hl Hn]; split; [lia|]. intros n Hlt.
    specialize (Hn (N.of_nat n) ltac:(lia)). rewrite !EL_nth_any, Nat2N.id in Hn. exact Hn.
Qed.

(** ** Value conversion and invariants *)

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_v_def" *)
Fixpoint convert_v (x : v a) : v a :=
  match x with
  | Val w => Val w
  | RStruct xs => RStruct (MAP convert_v xs)
  | NStruct nm flds =>
      let vs := MAP (fun '(nm, v0) => convert_v v0) flds in
      RStruct vs
  end.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_def" *)
Fixpoint v_flds_ok (ctxt : list (stcname * struct_info)) (x : v a) : bool :=
  match x with
  | Val w => true
  | RStruct vs => EVERY (v_flds_ok ctxt) vs
  | NStruct nm flds =>
      EVERY (fun '(nm, v0) => v_flds_ok ctxt v0) flds &&
      match ALOOKUP ctxt nm with
      | NONE => false
      | SOME info =>
          bool_decide (MAP FST flds = MAP FST (fields info)) &&
          bool_decide (MAP (shape_of ∘ SND) flds = MAP SND (fields info))
      end
  end.

End Defs.

Section Defs2.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_eshapes_def" *)
Definition convert_eshapes (str_ctxt : sctxt_ty) : fmap eid shape -> fmap eid shape :=
  FMAP_MAP2 (fun '(eid, sh) => compile_shape str_ctxt sh).

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_code_def" *)
Definition convert_code (ctxt : context)
    : fmap funname (list (varname * shape) * (prog a * shape)) ->
      fmap funname (list (varname * shape) * (prog a * shape)) :=
  FMAP_MAP2 (fun '(nm, (params, (prog, rshape))) =>
    (MAP (I ## compile_shape (pan_structs.structs ctxt)) params,
     (compile {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := params;
                 pan_structs.globals := pan_structs.globals ctxt |} prog,
      compile_shape (pan_structs.structs ctxt) rshape))).

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_s_def" *)
Definition convert_s {ffi_t} (ctxt : context) (s : state a ffi_t) : state a ffi_t :=
  mk_state (FMAP_MAP2 (fun '(nm, v0) => convert_v v0) (locals s))
    (FMAP_MAP2 (fun '(nm, v0) => convert_v v0) (globals s))
    []
    (convert_code ctxt (code s))
    (convert_eshapes (pan_structs.structs ctxt) (eshapes s))
    (memory s) (memaddrs s) (sh_memaddrs s) (clock s) (be s) (ffi s) (base_addr s) (top_addr s).

End Defs2.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "struct_infos_ok_def" *)
Definition struct_infos_ok (sh_ctxt : list (stcname * struct_info)) : Prop :=
  is_true (EVERY (fun '(nm, info) => ALL_DISTINCT (MAP FST (fields info))) sh_ctxt) /\
  is_true (ALL_DISTINCT (MAP FST sh_ctxt)) /\
  (forall i nm info, i < LENGTH sh_ctxt /\ EL i sh_ctxt = (nm, info) ->
     is_true (EVERY (is_wf_shape (DROP (i + 1) sh_ctxt)) (MAP SND (fields info)))) /\
  is_true (EVERY (fun '(nm, info) =>
     bool_decide (size info = size_of_sh_with_ctxt sh_ctxt (Comb (MAP SND (fields info))))) sh_ctxt).

(** ** Galette-only helpers on struct contexts *)

Section CtxtHelpers.
Context {A : Type}.

Lemma EL_DROP_split `{Inhabited A} (l : list A) i :
  i < LENGTH l -> l = TAKE i l ++ EL i l :: DROP (i + 1) l.
Proof.
  intros Hi. rewrite <- DROP_nth_cons by exact Hi. rewrite TAKE_firstn, DROP_skipn.
  symmetry; apply firstn_skipn.
Qed.

Lemma app_cons_EL_DROP `{Inhabited A} (pre post : list A) x :
  EL (LENGTH pre) (pre ++ x :: post) = x /\ DROP (LENGTH pre + 1) (pre ++ x :: post) = post /\
  LENGTH pre < LENGTH (pre ++ x :: post).
Proof.
  rewrite EL_nth_any, DROP_skipn, !LENGTH_length, length_app; cbn [length].
  rewrite Nat2N.id. split; [|split; [|lia]].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag; reflexivity.
  - replace (N.to_nat (N.of_nat (length pre) + 1)) with (length pre + 1)%nat by lia.
    rewrite skipn_app. rewrite skipn_all2 by lia. cbn.
    replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity.
Qed.

(** The third conjunct of [struct_infos_ok], over decompositions. *)
Lemma EL_DROP_iff_split `{Inhabited A} (l : list A) (P : A -> list A -> Prop) :
  (forall i x, i < LENGTH l /\ EL i l = x -> P x (DROP (i + 1) l)) <->
  (forall pre x post, l = pre ++ x :: post -> P x post).
Proof.
  split.
  - intros Hl pre x post ->. destruct (app_cons_EL_DROP pre post x) as (E1 & E2 & E3).
    rewrite <- E2. apply Hl; split; [exact E3|exact E1].
  - intros Hs i x [Hi <-]. apply (Hs (TAKE i l) (EL i l) (DROP (i + 1) l)). apply EL_DROP_split, Hi.
Qed.

End CtxtHelpers.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "alookup_drop_helper" *)
Theorem alookup_drop_helper : forall {K V} `{EqDecision K} n (xs : list (K * V)) k v,
  ALOOKUP (DROP n xs) k = SOME v /\ ALL_DISTINCT (MAP FST xs) ->
  ~ is_true (MEM k (MAP FST (TAKE n xs))) /\ ALOOKUP xs k = SOME v.
Proof.
  intros K V HK n xs k v [H1 H2].
  rewrite DROP_skipn in H1. rewrite TAKE_firstn, MEM_In_.
  apply ALL_DISTINCT_iff in H2. rewrite <- (firstn_skipn (N.to_nat n) xs) in H2.
  rewrite map_app in H2. pose proof (NoDup_app_disj _ _ H2) as Hd.
  pose proof (ALOOKUP_In _ _ _ H1) as Hin.
  assert (Hk : In k (map fst (skipn (N.to_nat n) xs))) by (apply in_map_iff; exists (k, v); auto).
  split.
  - intros Hm. exact (Hd k Hm Hk).
  - rewrite <- (firstn_skipn (N.to_nat n) xs) at 1.
    rewrite ALOOKUP_app. destruct (ALOOKUP (firstn (N.to_nat n) xs) k) eqn:E; [|exact H1].
    exfalso. apply (Hd k); [|exact Hk]. apply ALOOKUP_In in E. apply in_map_iff; exists (k, v0); auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_sh_with_ctxt_drop" *)
Theorem size_of_sh_with_ctxt_drop : forall n sh_ctxt sh,
  is_true (is_wf_shape (DROP n sh_ctxt) sh) /\ is_true (ALL_DISTINCT (MAP FST sh_ctxt)) ->
  size_of_sh_with_ctxt (DROP n sh_ctxt) sh = size_of_sh_with_ctxt sh_ctxt sh.
Proof.
  intros n sh_ctxt sh; induction sh as [| l Hl | nm] using shape_nested_ind; intros [H1 H2].
  - reflexivity.
  - cbn [size_of_sh_with_ctxt is_wf_shape] in *. f_equal.
    unfold is_true in H1; rewrite EVERY_Forall in H1.
    induction Hl as [|x xs Hx Hxs IHl]; [reflexivity|]. inversion H1; subst.
    cbn [MAP List.map]; rewrite Hx, IHl by (try split; assumption); reflexivity.
  - cbn [size_of_sh_with_ctxt is_wf_shape] in *.
    destruct (ALOOKUP (DROP n sh_ctxt) nm) as [info|] eqn:E; [|discriminate].
    destruct (alookup_drop_helper n sh_ctxt nm info (conj E H2)) as [_ ->]. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_wf_shape_drop" *)
Theorem is_wf_shape_drop : forall {B} (sh_ctxt : list (stcname * B)) sh n,
  is_true (is_wf_shape (DROP n sh_ctxt) sh) -> is_true (is_wf_shape sh_ctxt sh).
Proof.
  intros B sh_ctxt sh n; induction sh as [| l Hl | nm] using shape_nested_ind; intros H.
  - reflexivity.
  - cbn [is_wf_shape] in *. unfold is_true in *; rewrite EVERY_Forall in *.
    rewrite Forall_forall in *. intros x Hx. apply (Hl x Hx), H, Hx.
  - cbn [is_wf_shape] in *. destruct (ALOOKUP (DROP n sh_ctxt) nm) eqn:E; [|discriminate].
    destruct (ALOOKUP sh_ctxt nm) eqn:E'; [reflexivity|].
    apply ALOOKUP_None_iff in E'. apply ALOOKUP_In in E. rewrite DROP_skipn in E.
    exfalso; apply E'. apply in_map_iff. exists (nm, b); split; [reflexivity|].
    eapply In_skipn, E.
Qed.

Lemma DROP_1_cons {A} (x : A) l : DROP 1 (x :: l) = l.
Proof. cbn; destruct l; reflexivity. Qed.

Lemma is_wf_shape_Comb {B} (c : list (stcname * B)) shs :
  is_wf_shape c (Comb shs) = EVERY (is_wf_shape c) shs.
Proof. reflexivity. Qed.

Lemma EVERY_Forall_ {A} (P : A -> bool) l : is_true (EVERY P l) <-> Forall (fun x => is_true (P x)) l.
Proof. apply EVERY_Forall. Qed.

Lemma struct_infos_ok_split (c : list (stcname * struct_info)) :
  struct_infos_ok c <->
  Forall (fun '(nm, info) => NoDup (map fst (fields info))) c /\
  NoDup (map fst c) /\
  (forall pre nm info post, c = pre ++ (nm, info) :: post ->
     Forall (fun sh => is_true (is_wf_shape post sh)) (map snd (fields info))) /\
  Forall (fun '(nm, info) => size info = size_of_sh_with_ctxt c (Comb (MAP SND (fields info)))) c.
Proof.
  unfold struct_infos_ok. rewrite !EVERY_Forall_, ALL_DISTINCT_iff.
  assert (E1 : Forall (fun x => is_true ((fun '(nm, info) => ALL_DISTINCT (MAP FST (fields info))) x)) c <->
               Forall (fun '(nm, info) => NoDup (map fst (fields info))) c).
  { split; intros HF; eapply Forall_impl; try exact HF; intros [nm info]; cbn; apply ALL_DISTINCT_iff. }
  assert (E4 : Forall (fun x => is_true ((fun '(nm, info) => bool_decide (size info =
                  size_of_sh_with_ctxt c (Comb (MAP SND (fields info))))) x)) c <->
               Forall (fun '(nm, info) => size info = size_of_sh_with_ctxt c (Comb (MAP SND (fields info)))) c).
  { split; intros HF; eapply Forall_impl; try exact HF; intros [nm info]; cbn; apply bool_decide_spec. }
  rewrite E1, E4. clear E1 E4.
  pose proof (EL_DROP_iff_split c (fun x post => let '(nm, info) := x in
                 Forall (fun sh => is_true (is_wf_shape post sh)) (map snd (fields info)))) as E3.
  assert (E3' : (forall i nm info, i < LENGTH c /\ EL i c = (nm, info) ->
                  is_true (EVERY (is_wf_shape (DROP (i + 1) c)) (MAP SND (fields info)))) <->
                (forall i x, i < LENGTH c /\ EL i c = x -> (let '(nm, info) := x in
                   Forall (fun sh => is_true (is_wf_shape (DROP (i + 1) c) sh)) (map snd (fields info))))).
  { split.
    - intros Hl i [nm info] Hi. apply EVERY_Forall_, (Hl i nm info Hi).
    - intros Hl i nm info Hi. apply EVERY_Forall_, (Hl i (nm, info) Hi). }
  rewrite E3', E3. clear E3 E3'.
  split; intros (H1 & H2 & H3 & H4); (split; [exact H1|split; [exact H2|split; [|exact H4]]]).
  - intros pre nm info post Hc. exact (H3 pre (nm, info) post Hc).
  - intros pre [nm info] post Hc. exact (H3 pre nm info post Hc).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "struct_infos_ok_cons" *)
Theorem struct_infos_ok_cons : forall xs info nm,
  struct_infos_ok xs /\
  is_true (ALL_DISTINCT (MAP FST (fields info))) /\
  ~ is_true (MEM nm (MAP FST xs)) /\
  is_true (EVERY (is_wf_shape xs) (MAP SND (fields info))) /\
  size info = size_of_sh_with_ctxt xs (Comb (MAP SND (fields info))) ->
  struct_infos_ok ((nm, info) :: xs).
Proof.
  intros xs info nm (Hok & Hd & Hm & Hw & Hs).
  pose proof Hok as Hok'. apply struct_infos_ok_split in Hok as (H1 & H2 & H3 & H4).
  rewrite MEM_In_ in Hm. apply ALL_DISTINCT_iff in Hd. apply EVERY_Forall_ in Hw.
  assert (Hnd : NoDup (map fst ((nm, info) :: xs))) by (cbn; constructor; assumption).
  assert (Hsz : forall sh, is_true (is_wf_shape xs sh) ->
                 size_of_sh_with_ctxt ((nm, info) :: xs) sh = size_of_sh_with_ctxt xs sh).
  { intros sh Hsh. rewrite <- (size_of_sh_with_ctxt_drop 1 ((nm, info) :: xs) sh);
      rewrite DROP_1_cons; [reflexivity|].
    split; [exact Hsh|apply ALL_DISTINCT_iff, Hnd]. }
  assert (HszC : forall shs, Forall (fun sh => is_true (is_wf_shape xs sh)) shs ->
                 size_of_sh_with_ctxt ((nm, info) :: xs) (Comb shs) = size_of_sh_with_ctxt xs (Comb shs)).
  { intros shs Hf. apply Hsz. cbn [is_wf_shape]. apply EVERY_Forall_, Hf. }
  apply struct_infos_ok_split. split; [constructor; assumption|]. split; [exact Hnd|]. split.
  - intros [|[nm0 info0] pre] nm' info' post Hc; cbn in Hc; injection Hc as Hc1 Hc2 Hc3.
    + subst. exact Hw.
    + subst. apply (H3 pre nm' info' post eq_refl).
  - constructor.
    + rewrite HszC; [exact Hs|exact Hw].
    + apply Forall_forall. intros [nm' info'] Hin.
      rewrite Forall_forall in H4. specialize (H4 _ Hin). cbn in H4. rewrite H4.
      symmetry; apply HszC. apply in_split in Hin as (pre & post & Hc).
      specialize (H3 pre nm' info' post Hc). eapply Forall_impl; [|exact H3].
      intros sh Hsh. apply (is_wf_shape_drop xs sh (LENGTH pre + 1)).
      rewrite Hc. rewrite (proj1 (proj2 (app_cons_EL_DROP pre post (nm', info')))). exact Hsh.
Qed.

Lemma DROP_app_cons_split {A} n (c pre post : list A) x :
  DROP n c = pre ++ x :: post -> c = (TAKE n c ++ pre) ++ x :: post.
Proof.
  intros H. rewrite <- app_assoc, <- H, TAKE_firstn, DROP_skipn. symmetry; apply firstn_skipn.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "struct_infos_ok_drop" *)
Theorem struct_infos_ok_drop : forall n sh_ctxt,
  struct_infos_ok sh_ctxt -> struct_infos_ok (DROP n sh_ctxt).
Proof.
  intros n c Hok. apply struct_infos_ok_split in Hok as (H1 & H2 & H3 & H4).
  assert (Hsub : forall x, In x (DROP n c) -> In x c) by (intros x Hx; rewrite DROP_skipn in Hx; eapply In_skipn, Hx).
  apply struct_infos_ok_split. split; [|split; [|split]].
  - apply Forall_forall; intros x Hx. apply (proj1 (Forall_forall _ _) H1), Hsub, Hx.
  - rewrite DROP_skipn. rewrite <- (firstn_skipn (N.to_nat n) c), map_app in H2.
    apply NoDup_app_remove_l in H2. exact H2.
  - intros pre nm info post Hc. apply DROP_app_cons_split in Hc. exact (H3 _ _ _ _ Hc).
  - apply Forall_forall. intros [nm info] Hin.
    pose proof (proj1 (Forall_forall _ _) H4 _ (Hsub _ Hin)) as Hs; cbn in Hs. rewrite Hs.
    symmetry. apply size_of_sh_with_ctxt_drop. split; [|apply ALL_DISTINCT_iff, H2].
    apply in_split in Hin as (pre & post & Hc).
    specialize (H3 _ _ _ _ (DROP_app_cons_split n c pre post _ Hc)).
    cbn [is_wf_shape]. apply EVERY_Forall_. eapply Forall_impl; [|exact H3].
    intros sh Hsh. apply (is_wf_shape_drop (DROP n c) sh (LENGTH pre + 1)).
    rewrite Hc. rewrite (proj1 (proj2 (app_cons_EL_DROP pre post (nm, info)))). exact Hsh.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "struct_infos_ok_append" *)
Theorem struct_infos_ok_append : forall xs ys,
  struct_infos_ok (xs ++ ys) -> struct_infos_ok ys.
Proof.
  intros xs ys H. apply (struct_infos_ok_drop (LENGTH xs)) in H.
  rewrite DROP_skipn, LENGTH_length, Nat2N.id, skipn_app, skipn_all, Nat.sub_diag in H. exact H.
Qed.

(** ** Expressions: list helpers *)

Section ExpHelpers.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct_mmap_helper" *)
Theorem compile_exp_correct_mmap_helper : forall (s : state a ffi_t) ctxt es vs,
  OPT_MMAP (eval s) es = SOME vs /\
  (forall e, is_true (MEM e es) -> forall v0, eval s e = SOME v0 ->
     eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v0)) ->
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt es) = SOME (MAP convert_v vs).
Proof.
  intros s ctxt es vs [H1 H2]. rewrite compile_exps_eq_map, OPT_MMAP_MAP.
  eapply OPT_MMAP_map_ext; [exact H1|]. intros x y Hx Hy. apply H2; [apply MEM_In_, Hx|exact Hy].
Qed.

Lemma compile_fields_map (ctxt : context) (l : list (fldname * exp a)) :
  compile_fields ctxt l = MAP (fun '(f, e) => (f, compile_exp ctxt e)) l.
Proof. induction l as [|[f e] l IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

Lemma FLAT_ALOOKUP_reorder {B C} (ifs : list (fldname * B)) (L : list (fldname * C)) :
  MAP FST ifs = MAP FST L -> NoDup (MAP FST L) ->
  FLAT (MAP (fun '(nm', sh) => match ALOOKUP L nm' with None => [] | Some e => [e] end) ifs) =
  MAP SND L.
Proof.
  revert L; induction ifs as [|[k b] ifs IH]; intros [|[k' c] L] Hk Hd; cbn in Hk |- *;
    try discriminate; [reflexivity|].
  injection Hk as -> Hk. inversion Hd as [|? ? Hn Hd']; subst.
  destruct (decide (k' = k')) as [_|C0]; [|exfalso; apply C0; reflexivity]. cbn.
  f_equal. rewrite <- (IH L Hk Hd'). f_equal. apply map_ext_in. intros [k2 b2] Hin.
  destruct (decide (k' = k2)) as [<-|]; [|reflexivity].
  exfalso; apply Hn. rewrite <- Hk. apply in_map_iff; exists (k', b2); auto.
Qed.

End ExpHelpers.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "fields_in_order_reorder_noop" *)
Theorem fields_in_order_reorder_noop : forall {a B} (ctxt : context) (eflds : list (fldname * exp a))
    (info_fields : list (fldname * B)),
  MAP FST info_fields = MAP FST eflds /\ is_true (ALL_DISTINCT (MAP FST info_fields)) ->
  FLAT (MAP (fun '(nm', sh) => match ALOOKUP (compile_fields ctxt eflds) nm' with
                              | NONE => [] | SOME e => [e] end) info_fields) =
  MAP (compile_exp ctxt ∘ SND) eflds.
Proof.
  intros a B ctxt eflds ifs [Hk Hd]. apply ALL_DISTINCT_iff in Hd.
  rewrite FLAT_ALOOKUP_reorder.
  - rewrite compile_fields_map, map_map. apply map_ext; intros [f e]; reflexivity.
  - rewrite compile_fields_map, map_map, Hk. apply map_ext; intros [f e]; reflexivity.
  - rewrite compile_fields_map, map_map. rewrite Hk in Hd.
    erewrite map_ext; [exact Hd|]. intros [f e]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "alookup_map_structs_ok" *)
Theorem alookup_map_structs_ok : forall s_ctxt nm info,
  ALOOKUP s_ctxt nm = SOME info /\ struct_infos_ok s_ctxt ->
  is_true (ALL_DISTINCT (MAP FST (fields info))).
Proof.
  intros s_ctxt nm info [H1 H2]. apply struct_infos_ok_split in H2 as (H2 & _).
  apply ALOOKUP_In in H1. apply ALL_DISTINCT_iff. exact (proj1 (Forall_forall _ _) H2 _ H1).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_every" *)
Theorem opt_mmap_eq_every : forall {A B} `{EqDecision A} (f : A -> option B) xs ys (P : B -> bool),
  OPT_MMAP f xs = SOME ys /\
  (forall x y, is_true (MEM x xs) /\ f x = SOME y -> is_true (P y)) ->
  is_true (EVERY P ys).
Proof.
  intros A B HA f xs ys P [H1 H2]. apply EVERY_Forall_, Forall_forall. intros y Hy.
  destruct (OPT_MMAP_In _ _ _ _ H1 Hy) as (x & Hx & Hf). apply (H2 x y); split; [apply MEM_In_, Hx|exact Hf].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "every_convert_v_eq" *)
Theorem every_convert_v_eq : forall {a} (vs : list (v a)),
  is_true (EVERY (fun w => match w with Val _ => true | _ => false end) vs) ->
  MAP convert_v vs = vs.
Proof.
  intros a vs H; apply EVERY_Forall_ in H. induction H as [|[w| |] vs Hx _ IH]; cbn in *;
    try discriminate; [reflexivity|]. rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_fst_eq_alookup" *)
Theorem map_fst_eq_alookup : forall {K V W} `{EqDecision K} `{Inhabited K} `{Inhabited V} `{Inhabited W}
    (nm : K) (v0 : V) (xs : list (K * V)) (ys : list (K * W)),
  MAP FST xs = MAP FST ys /\ ALOOKUP xs nm = SOME v0 ->
  exists i, afindi nm xs = SOME i /\ afindi nm ys = SOME i /\
    i < LENGTH xs /\ i < LENGTH ys /\
    v0 = SND (EL i xs) /\ ALOOKUP ys nm = SOME (SND (EL i ys)).
Proof.
  intros K V W HK HiK HiV HiW nm v0 xs ys. revert xs.
  induction ys as [|[k w] ys IH]; intros [|[k' v'] xs] [Hk Hl]; cbn in Hk; try discriminate.
  injection Hk as -> Hk. cbn [ALOOKUP afindi] in Hl |- *. destruct (decide (k = nm)) as [->|Hne].
  - injection Hl as <-. destruct (decide (nm = nm)) as [_|C0]; [|exfalso; apply C0; reflexivity].
    exists 0. rewrite !LENGTH_cons. repeat split; try reflexivity; lia.
  - destruct (decide (nm = k)) as [->|_]; [exfalso; apply Hne; reflexivity|].
    destruct (IH xs (conj Hk Hl)) as (i & H1 & H2 & H3 & H4 & H5 & H6).
    exists (1 + i). rewrite H1, H2, !LENGTH_cons.
    rewrite !EL_cons_pos by lia. replace (1 + i - 1) with i by lia.
    repeat split; try assumption; lia.
Qed.

(** ** Shapes *)

Lemma afindi_lt {K V} `{EqDecision K} (kx : K) (xs : list (K * V)) n :
  afindi kx xs = SOME n -> n < LENGTH xs.
Proof.
  revert n; induction xs as [|[k v0] xs IH]; intros n Hf; cbn [afindi] in Hf; [discriminate|].
  rewrite LENGTH_cons. destruct (decide (kx = k)); [injection Hf as <-; lia|].
  destruct (afindi kx xs) eqn:E; [|discriminate]. specialize (IH _ eq_refl).
  assert (Hn : n = 1 + n1) by (injection Hf; intros Hx; rewrite <- Hx; reflexivity). lia.
Qed.

(** [compile_shape_n] with a fuel bounding [LENGTH sctxt - n]. *)
Fixpoint compile_shape_n_f (fuel : nat) (sctxt : sctxt_ty) (n : N) (sh : shape) {struct fuel} : shape :=
  match fuel with
  | O => One
  | Datatypes.S fuel' =>
      (fix cs (sh : shape) : shape :=
         match sh with
         | One => One
         | Comb shs =>
             Comb ((fix css (l : list shape) : list shape :=
                      match l with [] => [] | sh :: shs => cs sh :: css shs end) shs)
         | Named nm =>
             match afindi nm (DROP n sctxt) with
             | NONE => One
             | SOME j =>
                 let '(nm', flds) := EL (n + j) sctxt in
                 Comb (MAP (compile_shape_n_f fuel' sctxt (n + j + 1)) (MAP SND flds))
             end
         end) sh
  end.

Definition compile_shape_n (sctxt : sctxt_ty) (n : N) (sh : shape) : shape :=
  compile_shape_n_f (Datatypes.S (N.to_nat (LENGTH sctxt - n))) sctxt n sh.

Lemma compile_shape_n_f_Comb f sctxt n shs :
  compile_shape_n_f (Datatypes.S f) sctxt n (Comb shs) = Comb (MAP (compile_shape_n_f (Datatypes.S f) sctxt n) shs).
Proof. reflexivity. Qed.

Lemma compile_shape_n_f_Named f sctxt n nm :
  compile_shape_n_f (Datatypes.S f) sctxt n (Named nm) =
  match afindi nm (DROP n sctxt) with
  | NONE => One
  | SOME j => let '(nm', flds) := EL (n + j) sctxt in
              Comb (MAP (compile_shape_n_f f sctxt (n + j + 1)) (MAP SND flds))
  end.
Proof. reflexivity. Qed.

Lemma afindi_DROP_bound (sctxt : sctxt_ty) n nm j :
  afindi nm (DROP n sctxt) = SOME j -> n + j < LENGTH sctxt.
Proof.
  intros H. apply afindi_lt in H. rewrite DROP_skipn, !LENGTH_length, length_skipn in H.
  rewrite LENGTH_length. lia.
Qed.

Lemma compile_shape_n_f_fuel : forall f1 f2 sctxt n sh,
  (N.to_nat (LENGTH sctxt - n) < f1)%nat -> (N.to_nat (LENGTH sctxt - n) < f2)%nat ->
  compile_shape_n_f f1 sctxt n sh = compile_shape_n_f f2 sctxt n sh.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] sctxt n sh H1 H2; try lia.
  induction sh as [| l Hl | nm] using shape_nested_ind.
  - reflexivity.
  - rewrite !compile_shape_n_f_Comb. f_equal. apply map_ext_in. intros x Hx.
    apply (proj1 (Forall_forall _ _) Hl x Hx).
  - rewrite !compile_shape_n_f_Named. destruct (afindi nm (DROP n sctxt)) as [j|] eqn:E; [|reflexivity].
    apply afindi_DROP_bound in E. destruct (EL (n + j) sctxt) as [nm' flds].
    f_equal. apply map_ext; intros sh. apply IH; lia.
Qed.

Lemma compile_shape_n_f_eq f sctxt n sh :
  (N.to_nat (LENGTH sctxt - n) < f)%nat -> compile_shape_n_f f sctxt n sh = compile_shape_n sctxt n sh.
Proof. intros H; apply compile_shape_n_f_fuel; [exact H|lia]. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_def" *)
Theorem compile_shape_n_def :
  (forall sctxt n, compile_shape_n sctxt n One = One) /\
  (forall sctxt n shs, compile_shape_n sctxt n (Comb shs) = Comb (MAP (compile_shape_n sctxt n) shs)) /\
  (forall sctxt n nm, compile_shape_n sctxt n (Named nm) =
     match afindi nm (DROP n sctxt) with
     | NONE => One
     | SOME j =>
         let '(nm', flds) := EL (n + j) sctxt in
         Comb (MAP (compile_shape_n sctxt (n + j + 1)) (MAP SND flds))
     end).
Proof.
  split; [reflexivity|split].
  - intros sctxt n shs; unfold compile_shape_n at 1; rewrite compile_shape_n_f_Comb. reflexivity.
  - intros sctxt n nm; unfold compile_shape_n at 1; rewrite compile_shape_n_f_Named.
    destruct (afindi nm (DROP n sctxt)) as [j|] eqn:E; [|reflexivity].
    apply afindi_DROP_bound in E. destruct (EL (n + j) sctxt) as [nm' flds].
    f_equal. apply map_ext; intros sh. apply compile_shape_n_f_eq; lia.
Qed.

(** HOL's [compile_shape_n_ind]. *)
Lemma compile_shape_n_ind' (P : sctxt_ty -> N -> shape -> Prop) :
  (forall sctxt n, P sctxt n One) ->
  (forall sctxt n shs, (forall sh, In sh shs -> P sctxt n sh) -> P sctxt n (Comb shs)) ->
  (forall sctxt n nm,
     (forall j nm' flds sh, afindi nm (DROP n sctxt) = SOME j -> EL (n + j) sctxt = (nm', flds) ->
        In sh (MAP SND flds) -> P sctxt (n + j + 1) sh) ->
     P sctxt n (Named nm)) ->
  forall sctxt n sh, P sctxt n sh.
Proof.
  intros H1 H2 H3 sctxt.
  enough (G : forall m n, N.to_nat (LENGTH sctxt - n) = m -> forall sh, P sctxt n sh)
    by (intros n sh; exact (G _ n eq_refl sh)).
  intros m; induction m as [m IHm] using (well_founded_induction lt_wf). intros n Hm sh.
  induction sh as [| l Hl | nm] using shape_nested_ind.
  - apply H1.
  - apply H2. intros sh Hsh. apply (proj1 (Forall_forall _ _) Hl sh Hsh).
  - apply H3. intros j nm' flds sh Hj _ _. apply afindi_DROP_bound in Hj.
    apply (IHm (N.to_nat (LENGTH sctxt - (n + j + 1)))); [lia|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shapes_eq_map" *)
Theorem compile_shapes_eq_map : forall sctxt shs, compile_shapes sctxt shs = MAP (compile_shape sctxt) shs.
Proof. intros sctxt shs; induction shs as [|x xs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_afindi" *)
Theorem dropWhile_afindi : forall {K V} `{EqDecision K} (kx : K) (xs : list (K * V)),
  dropWhile (fun '(k, v0) => negb (bool_decide (k = kx))) xs =
  match afindi kx xs with NONE => [] | SOME n => DROP n xs end.
Proof.
  intros K V HK kx xs; induction xs as [|[k v0] xs IH]; cbn [dropWhile afindi]; [reflexivity|].
  destruct (decide (kx = k)) as [->|Hne].
  - rewrite (bool_decide_eq_true_2 _ eq_refl); reflexivity.
  - rewrite bool_decide_eq_false_2 by (intros ->; apply Hne; reflexivity). cbn [negb]. rewrite IH.
    destruct (afindi kx xs) as [n|]; [|reflexivity]. cbn [DROP].
    replace (1 + n =? 0) with false by (symmetry; apply N.eqb_neq; lia).
    f_equal. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_less_length" *)
Theorem afindi_less_length : forall {K V} `{EqDecision K} (kx : K) (xs : list (K * V)) n,
  afindi kx xs = SOME n -> n < LENGTH xs.
Proof. intros; eapply afindi_lt; eassumption. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_MAP_eq" *)
Theorem afindi_MAP_eq : forall {K V W} `{EqDecision K} (kx : K) (f : K * V -> K * W) (xs : list (K * V)),
  (forall x y, is_true (MEM (x, y) xs) -> FST (f (x, y)) = x) ->
  afindi kx (MAP f xs) = afindi kx xs.
Proof.
  intros K V W HK kx f xs; induction xs as [|[k v0] xs IH]; intros H; cbn; [reflexivity|].
  destruct (f (k, v0)) as [k' w] eqn:Ef.
  assert (Hk : k' = k).
  { pose proof (H k v0) as Hh. rewrite Ef in Hh. apply Hh, MEM_In_. left; reflexivity. }
  subst k'. rewrite IH; [reflexivity|]. intros x y Hm. apply H. apply MEM_In_. right. apply MEM_In_, Hm.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_eq" *)
Theorem compile_shape_n_eq : forall sctxt n sh, compile_shape_n sctxt n sh = compile_shape (DROP n sctxt) sh.
Proof.
  apply compile_shape_n_ind'.
  - intros; rewrite (proj1 compile_shape_n_def), (proj1 compile_shape_def); reflexivity.
  - intros sctxt n shs IH. rewrite (proj1 (proj2 compile_shape_n_def)),
      (proj1 (proj2 compile_shape_def)), compile_shapes_eq_map.
    f_equal. apply map_ext_in, IH.
  - intros sctxt n nm IH. rewrite (proj2 (proj2 compile_shape_n_def)),
      (proj1 (proj2 (proj2 compile_shape_def))), dropWhile_afindi.
    destruct (afindi nm (DROP n sctxt)) as [j|] eqn:E; [|reflexivity].
    pose proof (afindi_DROP_bound _ _ _ _ E) as Hb.
    rewrite DROP_DROP_, DROP_nth_cons by exact Hb.
    destruct (EL (n + j) sctxt) as [nm' flds] eqn:Eel.
    rewrite compile_shapes_eq_map. f_equal. apply map_ext_in. intros sh Hsh.
    apply (IH j nm' flds sh eq_refl Eel Hsh).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_eq_rev" *)
Theorem compile_shape_n_eq_rev : forall sctxt sh, compile_shape sctxt sh = compile_shape_n sctxt 0 sh.
Proof. intros sctxt sh; rewrite compile_shape_n_eq, DROP_skipn; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_wf_shape_compile_shape" *)
Theorem is_wf_shape_compile_shape : forall {B} (str_ctxt : list (stcname * B)),
  (forall sh_ctxt sh, is_true (is_wf_shape str_ctxt (compile_shape sh_ctxt sh))) /\
  (forall sh_ctxt shs, is_true (EVERY (is_wf_shape str_ctxt) (compile_shapes sh_ctxt shs))).
Proof.
  intros B str_ctxt.
  assert (G : forall sh_ctxt n sh, is_true (is_wf_shape str_ctxt (compile_shape_n sh_ctxt n sh))).
  { apply compile_shape_n_ind'.
    - intros; rewrite (proj1 compile_shape_n_def); reflexivity.
    - intros sctxt n shs IH. rewrite (proj1 (proj2 compile_shape_n_def)). cbn [is_wf_shape].
      apply EVERY_Forall_, Forall_forall. intros x Hx. apply in_map_iff in Hx as (y & <- & Hy). apply IH, Hy.
    - intros sctxt n nm IH. rewrite (proj2 (proj2 compile_shape_n_def)).
      destruct (afindi nm (DROP n sctxt)) as [j|] eqn:E; [|reflexivity].
      destruct (EL (n + j) sctxt) as [nm' flds] eqn:Eel. cbn [is_wf_shape].
      apply EVERY_Forall_, Forall_forall. intros x Hx. apply in_map_iff in Hx as (y & <- & Hy).
      apply (IH j nm' flds y eq_refl Eel Hy). }
  split.
  - intros sh_ctxt sh; rewrite compile_shape_n_eq_rev; apply G.
  - intros sh_ctxt shs. rewrite compile_shapes_eq_map. apply EVERY_Forall_, Forall_forall.
    intros x Hx. apply in_map_iff in Hx as (y & <- & Hy). rewrite compile_shape_n_eq_rev; apply G.
Qed.

Section MemLoadHelpers.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_flds_eq" *)
Theorem mem_load_flds_eq : forall (madd : word a -> Prop) memry stcs fld_shs vflds (x : word a),
  mem_load_flds fld_shs x madd memry stcs = SOME vflds ->
  exists vs, mem_loads (MAP SND fld_shs) x madd memry stcs = SOME vs /\
    LENGTH vs = LENGTH fld_shs /\ vflds = ZIP (MAP FST fld_shs, vs).
Proof.
  intros madd memry stcs fld_shs; induction fld_shs as [|[fld sh] fl IH]; intros vflds x H.
  - rewrite (proj1 (proj2 (proj2 (proj2 mem_load_def)))) in H. injection H as <-.
    exists []. cbn [MAP List.map]. rewrite (proj1 (proj2 mem_load_def)). repeat split.
  - rewrite (proj2 (proj2 (proj2 (proj2 mem_load_def)))) in H.
    destruct (mem_load sh x madd memry stcs) as [v0|] eqn:E1; [|discriminate].
    destruct (mem_load_flds fl _ madd memry stcs) as [vf|] eqn:E2; [|discriminate].
    injection H as <-. destruct (IH _ _ E2) as (vs & H1 & H2 & H3).
    exists (v0 :: vs). cbn [MAP List.map fst snd]. rewrite (proj1 (proj2 (proj2 mem_load_def))).
    rewrite E1, H1. rewrite !LENGTH_cons, H2, H3. split; [reflexivity|split; [reflexivity|]].
    reflexivity.
Qed.

End MemLoadHelpers.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "ALOOKUP_eq_afindi" *)
Theorem ALOOKUP_eq_afindi : forall {K V} `{EqDecision K} `{Inhabited K} `{Inhabited V} (xs : list (K * V)) nm,
  ALOOKUP xs nm = OPTION_MAP (fun i => SND (EL i xs)) (afindi nm xs).
Proof.
  intros K V HK HiK HiV xs nm; induction xs as [|[k v0] xs IH]; cbn [ALOOKUP afindi]; [reflexivity|].
  destruct (decide (k = nm)) as [->|Hne].
  - destruct (decide (nm = nm)) as [_|C0]; [reflexivity|exfalso; apply C0; reflexivity].
  - destruct (decide (nm = k)) as [->|_]; [exfalso; apply Hne; reflexivity|].
    rewrite IH. destruct (afindi nm xs) as [i|]; cbn [option_map]; [|reflexivity].
    rewrite EL_cons_pos by lia. f_equal. f_equal. f_equal. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_append" *)
Theorem afindi_append : forall {K V} `{EqDecision K} (k : K) (xs ys : list (K * V)),
  afindi k (xs ++ ys) =
  match afindi k xs with
  | NONE => OPTION_MAP (N.add (LENGTH xs)) (afindi k ys)
  | SOME i => SOME i
  end.
Proof.
  intros K V HK k xs ys; induction xs as [|[k' v0] xs IH]; cbn [afindi List.app].
  - destruct (afindi k ys); cbn [option_map]; [f_equal; lia|reflexivity].
  - destruct (decide (k = k')); [reflexivity|]. rewrite IH.
    destruct (afindi k xs); cbn [option_map]; [reflexivity|]. destruct (afindi k ys); cbn [option_map]; [|reflexivity].
    f_equal. rewrite LENGTH_cons. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_EL" *)
Theorem afindi_EL : forall {K V} `{EqDecision K} `{Inhabited K} `{Inhabited V} (k : K) (xs : list (K * V)) i,
  afindi k xs = SOME i -> FST (EL i xs) = k.
Proof.
  intros K V HK HiK HiV k xs; induction xs as [|[k' v0] xs IH]; intros i Hf; cbn [afindi] in Hf; [discriminate|].
  destruct (decide (k = k')) as [->|Hne]; [injection Hf as <-; reflexivity|].
  destruct (afindi k xs) as [j|] eqn:E; [|discriminate].
  assert (Hi : i = 1 + j) by (injection Hf; intros Hx; rewrite <- Hx; reflexivity). subst i.
  rewrite EL_cons_pos by lia. replace (1 + j - 1) with j by lia. apply IH; reflexivity.
Qed.

(** ** Sizes and struct contexts *)

Lemma afindi_None_iff {K V} `{EqDecision K} (k : K) (xs : list (K * V)) :
  afindi k xs = NONE <-> ~ In k (map fst xs).
Proof.
  induction xs as [|[k' v0] xs IH]; cbn [afindi map fst]; [split; [intros _ []|reflexivity]|].
  destruct (decide (k = k')) as [->|Hne];
    [split; [discriminate|intros Hn; exfalso; apply Hn; left; reflexivity]|].
  split.
  - intros Hf [Hk|Hk]; [apply Hne; symmetry; exact Hk|].
    destruct (afindi k xs) eqn:E; [discriminate|]. apply (proj1 IH eq_refl), Hk.
  - intros Hn. destruct (afindi k xs) eqn:E; [|reflexivity].
    exfalso. assert (Hc : SOME n <> NONE) by congruence.
    apply Hc, IH. intros Hk; apply Hn; right; exact Hk.
Qed.

Lemma MAP_DROP_ {A B} (f : A -> B) n l : MAP f (DROP n l) = DROP n (MAP f l).
Proof. rewrite !DROP_skipn, skipn_map. reflexivity. Qed.

Lemma EL_DROP_ {A} `{Inhabited A} (n i : N) (l : list A) : EL i (DROP n l) = EL (n + i) l.
Proof. rewrite !EL_nth_any, DROP_skipn, nth_skipn. f_equal. lia. Qed.

Lemma LENGTH_DROP_ {A} n (l : list A) : LENGTH (DROP n l) = LENGTH l - n.
Proof. rewrite DROP_skipn, !LENGTH_length, length_skipn. lia. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "wf_shape_struct_infos_ok_helper" *)
Theorem wf_shape_struct_infos_ok_helper : forall n ctxt nm info,
  ALOOKUP (DROP n ctxt) nm = SOME info /\ struct_infos_ok ctxt ->
  exists i,
    afindi nm (DROP n ctxt) = SOME i /\
    i + n < LENGTH ctxt /\
    EL (i + n) ctxt = (nm, info) /\
    afindi nm ctxt = SOME (i + n) /\
    (forall sh, is_true (MEM sh (MAP SND (fields info))) ->
       is_true (is_wf_shape (DROP (i + n + 1) ctxt) sh)).
Proof.
  intros n ctxt nm info [H1 Hok]. pose proof Hok as (_ & Hd & H3 & _).
  rewrite ALOOKUP_eq_afindi in H1. destruct (afindi nm (DROP n ctxt)) as [i|] eqn:E; [|discriminate].
  injection H1 as H1. pose proof (afindi_EL _ _ _ E) as Hf. pose proof (afindi_lt _ _ _ E) as Hl.
  rewrite LENGTH_DROP_ in Hl. rewrite EL_DROP_ in Hf, H1.
  assert (Hel : EL (i + n) ctxt = (nm, info)).
  { rewrite N.add_comm. destruct (EL (n + i) ctxt); cbn in *; subst; reflexivity. }
  exists i. split; [reflexivity|]. split; [lia|]. split; [exact Hel|]. split.
  - assert (Hc : ctxt = TAKE n ctxt ++ DROP n ctxt)
      by (rewrite TAKE_firstn, DROP_skipn; symmetry; apply firstn_skipn).
    rewrite Hc at 1. rewrite afindi_append, E.
    assert (Hn : afindi nm (TAKE n ctxt) = NONE).
    { apply afindi_None_iff. intros Hin. apply ALL_DISTINCT_iff in Hd.
      rewrite Hc, map_app in Hd. apply (NoDup_app_disj _ _ Hd nm Hin).
      pose proof (afindi_lt _ _ _ E) as Hlt. pose proof (afindi_EL _ _ _ E) as Hf'.
      rewrite EL_nth_any in Hf'. rewrite <- Hf'. apply in_map, nth_In.
      rewrite LENGTH_length in Hlt. lia. }
    rewrite Hn. cbn [option_map]. f_equal. rewrite TAKE_firstn, LENGTH_length, length_firstn. rewrite LENGTH_length in Hl. lia.
  - intros sh Hsh. assert (Hb : i + n < LENGTH ctxt) by lia. specialize (H3 (i + n) nm info (conj Hb Hel)).
    apply EVERY_Forall_ in H3. apply MEM_In_ in Hsh. exact (proj1 (Forall_forall _ _) H3 sh Hsh).
Qed.

Lemma afindi_DROP_MAP_fields (ctxt : list (stcname * struct_info)) n nm :
  afindi nm (DROP n (MAP (fun '(nm, info) => (nm, fields info)) ctxt)) = afindi nm (DROP n ctxt).
Proof.
  rewrite <- MAP_DROP_. apply afindi_MAP_eq. intros x y _; reflexivity.
Qed.

Lemma EL_MAP_fields (ctxt : list (stcname * struct_info)) i nm info :
  EL i ctxt = (nm, info) -> i < LENGTH ctxt ->
  EL i (MAP (fun '(nm, info) => (nm, fields info)) ctxt) = (nm, fields info).
Proof. intros H Hi. rewrite EL_MAP_ by exact Hi. rewrite H. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_compile_shape_n" *)
Theorem size_of_compile_shape_n : forall ctxt sh_ctxt n sh,
  sh_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt /\
  is_true (is_wf_shape (DROP n ctxt) sh) /\
  struct_infos_ok ctxt ->
  size_of_sh_with_ctxt [] (compile_shape_n sh_ctxt n sh) = size_of_sh_with_ctxt ctxt sh.
Proof.
  intros ctxt.
  enough (G : forall sh_ctxt n sh, sh_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt ->
            is_true (is_wf_shape (DROP n ctxt) sh) -> struct_infos_ok ctxt ->
            size_of_sh_with_ctxt [] (compile_shape_n sh_ctxt n sh) = size_of_sh_with_ctxt ctxt sh)
    by (intros sh_ctxt n sh (H1 & H2 & H3); exact (G sh_ctxt n sh H1 H2 H3)).
  apply (compile_shape_n_ind' (fun sh_ctxt n sh => sh_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt ->
            is_true (is_wf_shape (DROP n ctxt) sh) -> struct_infos_ok ctxt ->
            size_of_sh_with_ctxt [] (compile_shape_n sh_ctxt n sh) = size_of_sh_with_ctxt ctxt sh)).
  - intros; rewrite (proj1 compile_shape_n_def); reflexivity.
  - intros sctxt n shs IH Hs Hw Hok. rewrite (proj1 (proj2 compile_shape_n_def)).
    cbn [size_of_sh_with_ctxt]. rewrite map_map. f_equal. apply map_ext_in. intros sh Hsh.
    apply IH; try assumption. cbn [is_wf_shape] in Hw. apply EVERY_Forall_ in Hw.
    exact (proj1 (Forall_forall _ _) Hw sh Hsh).
  - intros sctxt n nm IH Hs Hw Hok. cbn [is_wf_shape] in Hw.
    destruct (ALOOKUP (DROP n ctxt) nm) as [info|] eqn:Ea; [|discriminate].
    destruct (wf_shape_struct_infos_ok_helper n ctxt nm info (conj Ea Hok))
      as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
    rewrite (proj2 (proj2 compile_shape_n_def)). subst sctxt. rewrite afindi_DROP_MAP_fields, Hi1.
    rewrite (N.add_comm n i), (EL_MAP_fields _ _ _ _ Hi3 Hi2).
    cbn [size_of_sh_with_ctxt]. rewrite (ALOOKUP_eq_afindi ctxt nm), Hi4. cbn [option_map].
    rewrite Hi3. cbn [snd].
    pose proof Hok as (_ & _ & _ & H4). apply EVERY_Forall_ in H4.
    assert (Hin : In (nm, info) ctxt) by (rewrite <- Hi3, EL_nth_any; apply nth_In; rewrite LENGTH_length in Hi2; lia).
    pose proof (proj1 (Forall_forall _ _) H4 _ Hin) as Hsz. cbn in Hsz. apply bool_decide_spec in Hsz.
    rewrite Hsz. cbn [size_of_sh_with_ctxt]. rewrite map_map. f_equal. apply map_ext_in. intros sh Hsh.
    rewrite (N.add_comm i n) in Hi5 |- *.
    apply (IH (i) nm (fields info) sh); try reflexivity.
    + rewrite <- afindi_DROP_MAP_fields in Hi1. exact Hi1.
    + rewrite (N.add_comm n i). apply EL_MAP_fields; assumption.
    + exact Hsh.
    + apply Hi5, MEM_In_, Hsh.
    + exact Hok.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_compile_shape" *)
Theorem size_of_compile_shape : forall ctxt sh,
  is_true (is_wf_shape ctxt sh) /\ struct_infos_ok ctxt ->
  size_of_sh_with_ctxt [] (compile_shape (MAP (fun '(nm, info) => (nm, fields info)) ctxt) sh) =
  size_of_sh_with_ctxt ctxt sh.
Proof.
  intros ctxt sh [H1 H2]. rewrite compile_shape_n_eq_rev. apply size_of_compile_shape_n.
  split; [reflexivity|split; [|exact H2]]. rewrite DROP_skipn; exact H1.
Qed.

Section VHelpers.
Context {a : N}.

Lemma v_flds_ok_RStruct ctxt (vs : list (v a)) :
  is_true (v_flds_ok ctxt (RStruct vs)) <-> Forall (fun x => is_true (v_flds_ok ctxt x)) vs.
Proof. cbn [v_flds_ok]. apply EVERY_Forall_. Qed.

Lemma v_flds_ok_NStruct ctxt nm (flds : list (fldname * v a)) :
  is_true (v_flds_ok ctxt (NStruct nm flds)) <->
  Forall (fun p => is_true (v_flds_ok ctxt (snd p))) flds /\
  exists info, ALOOKUP ctxt nm = SOME info /\ MAP FST flds = MAP FST (fields info) /\
    MAP (shape_of ∘ SND) flds = MAP SND (fields info).
Proof.
  cbn [v_flds_ok]. unfold is_true. rewrite Bool.andb_true_iff, EVERY_Forall.
  assert (E : Forall (fun x => (fun '(_, v0) => v_flds_ok ctxt v0) x = true) flds <->
              Forall (fun p => v_flds_ok ctxt (snd p) = true) flds)
    by (split; intros HF; eapply Forall_impl; try exact HF; intros [? ?]; exact id).
  rewrite E. split.
  - intros [HF Hm]; split; [exact HF|]. destruct (ALOOKUP ctxt nm) as [info|]; [|discriminate].
    apply Bool.andb_true_iff in Hm as [Hm1 Hm2]. apply bool_decide_spec in Hm1, Hm2.
    exists info; auto.
  - intros [HF (info & Ha & Hm1 & Hm2)]; split; [exact HF|]. rewrite Ha.
    apply Bool.andb_true_iff; split; apply bool_decide_spec; assumption.
Qed.

End VHelpers.

(** Induction on values with induction hypotheses for the nested lists. *)
Definition v_nested_ind' {a} := @v_nested_ind a.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "v_flds_ok_append" *)
Theorem v_flds_ok_append : forall {a} (pfx : list (stcname * struct_info)) ctxt (x : v a),
  is_true (v_flds_ok ctxt x) /\ is_true (ALL_DISTINCT (MAP FST pfx ++ MAP FST ctxt)) ->
  is_true (v_flds_ok (pfx ++ ctxt) x).
Proof.
  intros a pfx ctxt x; induction x as [w|vs IH|nm vs IH] using v_nested_ind; intros [H1 H2].
  - reflexivity.
  - apply v_flds_ok_RStruct in H1. apply v_flds_ok_RStruct. rewrite Forall_forall in *. intros y Hy.
    apply (IH y Hy); split; [apply H1, Hy|exact H2].
  - apply v_flds_ok_NStruct in H1 as [HF (info & Ha & Hm1 & Hm2)]. apply v_flds_ok_NStruct.
    split.
    + rewrite Forall_forall in *. intros y Hy. apply (IH y Hy); split; [apply HF, Hy|exact H2].
    + exists info. split; [|split; assumption]. rewrite ALOOKUP_app.
      destruct (ALOOKUP pfx nm) as [i'|] eqn:Ep; [|exact Ha]. exfalso.
      apply ALL_DISTINCT_iff in H2. apply ALOOKUP_In in Ep, Ha.
      apply (NoDup_app_disj _ _ H2 nm); apply in_map_iff; [exists (nm, i')|exists (nm, info)]; auto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_MAP_helper" *)
Theorem dropWhile_MAP_helper : forall {A B} (P : A -> bool) (Q : B -> bool) (f : A -> B) xs ys,
  dropWhile P xs = ys /\ (forall x, In x xs -> P x = Q (f x)) ->
  dropWhile Q (MAP f xs) = MAP f ys.
Proof.
  intros A B P Q f xs; induction xs as [|x xs IH]; intros ys [H1 H2]; cbn in H1 |- *.
  - subst; reflexivity.
  - rewrite <- (H2 x (or_introl eq_refl)). destruct (P x).
    + apply IH; split; [exact H1|]. intros y Hy; apply H2; right; exact Hy.
    + subst; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "UNCURRY_EQ_o_SND" *)
Theorem UNCURRY_EQ_o_SND : forall {A B C} (f : B -> C), UNCURRY (fun (x : A) => f) = f ∘ SND.
Proof. intros; apply functional_extensionality; intros [x y]; reflexivity. Qed.

Section MemLoad.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_rec1" *)
Theorem mem_load_rec1 : forall stcs sh (addr : word a) dm m,
  mem_load sh addr dm m stcs =
  match sh with
  | One => if classical_dec (addr IN dm) then SOME (Val (m addr)) else NONE
  | Comb shapes =>
      match mem_loads shapes addr dm m stcs with SOME vs => SOME (RStruct vs) | NONE => NONE end
  | Named nm =>
      match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
      | (nm, info) :: stcs' =>
          match mem_load_flds (fields info) addr dm m stcs' with
          | SOME vflds => SOME (NStruct nm vflds)
          | NONE => NONE
          end
      | _ => NONE
      end
  end.
Proof. intros; apply (proj1 mem_load_def). Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_rec" *)
Theorem mem_load_rec :
  (forall stcs (addr : word a) dm m,
     mem_load One addr dm m stcs =
     if classical_dec (addr IN dm) then SOME (Val (m addr)) else NONE) /\
  (forall stcs shs (addr : word a) dm m,
     mem_load (Comb shs) addr dm m stcs =
     match mem_loads shs addr dm m stcs with SOME vs => SOME (RStruct vs) | NONE => NONE end) /\
  (forall stcs nm (addr : word a) dm m,
     mem_load (Named nm) addr dm m stcs =
     match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
     | (nm, info) :: stcs' =>
         match mem_load_flds (fields info) addr dm m stcs' with
         | SOME vflds => SOME (NStruct nm vflds)
         | NONE => NONE
         end
     | _ => NONE
     end).
Proof. repeat split; intros; rewrite mem_load_rec1; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_loads_convert_helper" *)
Theorem mem_loads_convert_helper : forall (madd : word a -> Prop) memry stcs stcs2 (f : shape -> shape)
    shs vs (x : word a),
  mem_loads shs x madd memry stcs = SOME vs /\
  (forall sh y v0, is_true (MEM sh shs) /\ mem_load sh y madd memry stcs = SOME v0 ->
     size_of_sh_with_ctxt stcs2 (f sh) = size_of_sh_with_ctxt stcs sh /\
     mem_load (f sh) y madd memry stcs2 = SOME (convert_v v0)) ->
  mem_loads (MAP f shs) x madd memry stcs2 = SOME (MAP convert_v vs).
Proof.
  intros madd memry stcs stcs2 f shs; induction shs as [|sh shs IH]; intros vs x [H1 H2].
  - rewrite (proj1 (proj2 mem_load_def)) in H1. injection H1 as <-.
    cbn [MAP List.map]. apply (proj1 (proj2 mem_load_def)).
  - rewrite (proj1 (proj2 (proj2 mem_load_def))) in H1.
    destruct (mem_load sh x madd memry stcs) as [v0|] eqn:E1; [|discriminate].
    destruct (mem_loads shs _ madd memry stcs) as [vs'|] eqn:E2; [|discriminate].
    injection H1 as <-. cbn [MAP List.map]. rewrite (proj1 (proj2 (proj2 mem_load_def))).
    assert (Hm : is_true (MEM sh (sh :: shs))) by (apply MEM_In_; left; reflexivity).
    destruct (H2 sh x v0 (conj Hm E1)) as [Hs Hl]. rewrite Hl, Hs.
    erewrite IH; [reflexivity|]. split; [exact E2|]. intros sh' y v' [Hm' Hl']. apply H2.
    split; [|exact Hl']. apply MEM_In_; right; apply MEM_In_, Hm'.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_loads_EL" *)
Theorem mem_loads_EL : forall (madd : word a -> Prop) memry stcs shs vs (x : word a) i,
  mem_loads shs x madd memry stcs = SOME vs /\ i < LENGTH shs ->
  exists y, mem_load (EL i shs) y madd memry stcs = SOME (EL i vs).
Proof.
  intros madd memry stcs shs; induction shs as [|sh shs IH]; intros vs x i [H1 H2].
  - cbn in H2; lia.
  - rewrite (proj1 (proj2 (proj2 mem_load_def))) in H1.
    destruct (mem_load sh x madd memry stcs) as [v0|] eqn:E1; [|discriminate].
    destruct (mem_loads shs _ madd memry stcs) as [vs'|] eqn:E2; [|discriminate].
    injection H1 as <-. destruct (N.eq_dec i 0) as [->|Hi].
    + exists x; exact E1.
    + rewrite !EL_cons_pos by lia. eapply (IH vs' _ (i - 1)). split; [exact E2|].
      rewrite LENGTH_cons in H2; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_loads_mem" *)
Theorem mem_loads_mem : forall (madd : word a -> Prop) memry stcs (v0 : v a) shs vs (x : word a),
  mem_loads shs x madd memry stcs = SOME vs /\ is_true (MEM v0 vs) ->
  exists sh y, is_true (MEM sh shs) /\ mem_load sh y madd memry stcs = SOME v0.
Proof.
  intros madd memry stcs v0 shs; induction shs as [|sh shs IH]; intros vs x [H1 H2].
  - rewrite (proj1 (proj2 mem_load_def)) in H1. injection H1 as <-. discriminate.
  - rewrite (proj1 (proj2 (proj2 mem_load_def))) in H1.
    destruct (mem_load sh x madd memry stcs) as [v1|] eqn:E1; [|discriminate].
    destruct (mem_loads shs _ madd memry stcs) as [vs'|] eqn:E2; [|discriminate].
    injection H1 as <-. apply MEM_In_ in H2. destruct H2 as [<-|H2].
    + exists sh, x. split; [apply MEM_In_; left; reflexivity|exact E1].
    + destruct (IH vs' _ (conj E2 (proj2 (MEM_In_ _ _) H2))) as (sh' & y & Hm & Hl).
      exists sh', y. split; [|exact Hl]. apply MEM_In_; right; apply MEM_In_, Hm.
Qed.

Lemma mem_loads_In (madd : word a -> Prop) memry stcs (v0 : v a) shs vs (x : word a) :
  mem_loads shs x madd memry stcs = SOME vs -> In v0 vs ->
  exists sh y, In sh shs /\ mem_load sh y madd memry stcs = SOME v0.
Proof.
  intros H1 H2. destruct (mem_loads_mem madd memry stcs v0 shs vs x (conj H1 (proj2 (MEM_In_ _ _) H2)))
    as (sh & y & Hm & Hl). exists sh, y. split; [apply MEM_In_, Hm|exact Hl].
Qed.

End MemLoad.

Section ZipHelpers.
Context {A B : Type}.

Lemma ZIP_combine (xs : list A) (ys : list B) : ZIP (xs, ys) = combine xs ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity.
  all: rewrite (proj2 (proj2 ZIP_eqns)); cbn [combine]; rewrite IH; reflexivity.
Qed.

Lemma MAP_FST_ZIP (xs : list A) (ys : list B) :
  length xs = length ys -> MAP FST (ZIP (xs, ys)) = xs.
Proof.
  rewrite ZIP_combine. revert ys; induction xs as [|x xs IH]; intros [|y ys] Hl; cbn in *;
    try discriminate; [reflexivity|]. rewrite IH by congruence. reflexivity.
Qed.

Lemma MAP_SND_ZIP (xs : list A) (ys : list B) :
  length xs = length ys -> MAP SND (ZIP (xs, ys)) = ys.
Proof.
  rewrite ZIP_combine. revert ys; induction xs as [|x xs IH]; intros [|y ys] Hl; cbn in *;
    try discriminate; [reflexivity|]. rewrite IH by congruence. reflexivity.
Qed.

End ZipHelpers.

Section MemLoadConv.
Context {a : N}.

Lemma afindi_DROP_bound' {V} (c : list (stcname * V)) n nm j :
  afindi nm (DROP n c) = SOME j -> n + j < LENGTH c.
Proof.
  intros H. apply afindi_lt in H. rewrite LENGTH_DROP_ in H. lia.
Qed.

Lemma dropWhile_DROP_afindi (c : list (stcname * struct_info)) n nm i :
  afindi nm (DROP n c) = SOME i ->
  dropWhile (fun '(k, v0) => negb (bool_decide (k = nm))) (DROP n c) =
  EL (n + i) c :: DROP (n + i + 1) c.
Proof.
  intros E. rewrite dropWhile_afindi, E, DROP_DROP_. apply DROP_nth_cons.
  apply (afindi_DROP_bound' _ _ _ _ E).
Qed.

Lemma MAP_convert_v_ZIP (ks : list fldname) (vs : list (v a)) :
  length ks = length vs ->
  MAP (fun '(nm, v0) => convert_v v0) (ZIP (ks, vs)) = MAP convert_v vs.
Proof.
  intros Hl. rewrite <- (MAP_SND_ZIP ks vs Hl) at 2. rewrite map_map.
  apply map_ext; intros [k v0]; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_conversion" *)
Theorem mem_load_conversion : forall (madd : word a -> Prop) memry str_ctxt str2 n shape (x : word a) v0,
  mem_load shape x madd memry (DROP n str_ctxt) = SOME v0 /\
  str2 = MAP (fun '(nm, info) => (nm, fields info)) str_ctxt /\
  is_true (is_wf_shape (DROP n str_ctxt) shape) /\
  struct_infos_ok str_ctxt ->
  mem_load (compile_shape_n str2 n shape) x madd memry [] = SOME (convert_v v0) /\
  is_true (v_flds_ok str_ctxt v0).
Proof.
  intros madd memry c.
  enough (G : forall str2 n shape, forall (x : word a) v0,
            mem_load shape x madd memry (DROP n c) = SOME v0 ->
            str2 = MAP (fun '(nm, info) => (nm, fields info)) c ->
            is_true (is_wf_shape (DROP n c) shape) -> struct_infos_ok c ->
            mem_load (compile_shape_n str2 n shape) x madd memry [] = SOME (convert_v v0) /\
            is_true (v_flds_ok c v0))
    by (intros str2 n shape x v0 (H1 & H2 & H3 & H4); exact (G str2 n shape x v0 H1 H2 H3 H4)).
  apply (compile_shape_n_ind' (fun str2 n shape => forall (x : word a) v0,
            mem_load shape x madd memry (DROP n c) = SOME v0 ->
            str2 = MAP (fun '(nm, info) => (nm, fields info)) c ->
            is_true (is_wf_shape (DROP n c) shape) -> struct_infos_ok c ->
            mem_load (compile_shape_n str2 n shape) x madd memry [] = SOME (convert_v v0) /\
            is_true (v_flds_ok c v0))).
  - intros str2 n x v0 H Hs Hw Hok. rewrite (proj1 compile_shape_n_def).
    rewrite (proj1 mem_load_rec) in H |- *.
    destruct (classical_dec _); [|discriminate]. injection H as <-. split; reflexivity.
  - intros str2 n shs IH x v0 H Hs Hw Hok. rewrite (proj1 (proj2 compile_shape_n_def)).
    rewrite (proj1 (proj2 mem_load_rec)) in H |- *.
    destruct (mem_loads shs x madd memry (DROP n c)) as [vs|] eqn:E; [|discriminate].
    injection H as <-. cbn [is_wf_shape] in Hw. apply EVERY_Forall_ in Hw.
    pose proof Hok as (_ & Hd & _).
    assert (IH' : forall sh y v', In sh shs -> mem_load sh y madd memry (DROP n c) = SOME v' ->
              mem_load (compile_shape_n str2 n sh) y madd memry [] = SOME (convert_v v') /\
              is_true (v_flds_ok c v'))
      by (intros sh y v' Hsh Hl; apply (IH sh Hsh y v' Hl Hs); [exact (proj1 (Forall_forall _ _) Hw sh Hsh)|exact Hok]).
    split.
    + erewrite mem_loads_convert_helper; [reflexivity|]. split; [exact E|].
      intros sh y v' [Hm Hl]. apply MEM_In_ in Hm. split.
      * rewrite (size_of_compile_shape_n c).
        -- symmetry; apply size_of_sh_with_ctxt_drop. split; [exact (proj1 (Forall_forall _ _) Hw sh Hm)|exact Hd].
        -- split; [exact Hs|split; [exact (proj1 (Forall_forall _ _) Hw sh Hm)|exact Hok]].
      * exact (proj1 (IH' sh y v' Hm Hl)).
    + apply v_flds_ok_RStruct, Forall_forall. intros v' Hv.
      destruct (mem_loads_In _ _ _ _ _ _ _ E Hv) as (sh & y & Hsh & Hl).
      exact (proj2 (IH' sh y v' Hsh Hl)).
  - intros str2 n nm IH x v0 H Hs Hw Hok. cbn [is_wf_shape] in Hw.
    destruct (ALOOKUP (DROP n c) nm) as [info|] eqn:Ea; [|discriminate].
    destruct (wf_shape_struct_infos_ok_helper n c nm info (conj Ea Hok))
      as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
    pose proof Hok as (_ & Hd & _).
    rewrite (proj2 (proj2 mem_load_rec)), (dropWhile_DROP_afindi _ _ _ _ Hi1) in H.
    rewrite (N.add_comm n i), Hi3 in H.
    destruct (mem_load_flds (fields info) x madd memry (DROP (i + n + 1) c)) as [vflds|] eqn:Ef;
      [|discriminate]. injection H as <-.
    destruct (mem_load_flds_eq _ _ _ _ _ _ Ef) as (vs & Hvs & Hlen & ->).
    rewrite (proj2 (proj2 compile_shape_n_def)). subst str2. rewrite afindi_DROP_MAP_fields, Hi1.
    rewrite (N.add_comm n i), (EL_MAP_fields _ _ _ _ Hi3 Hi2).
    rewrite (proj1 (proj2 mem_load_rec)).
    assert (IH' : forall sh y v', In sh (MAP SND (fields info)) ->
              mem_load sh y madd memry (DROP (i + n + 1) c) = SOME v' ->
              mem_load (compile_shape_n (MAP (fun '(nm, info) => (nm, fields info)) c) (i + n + 1) sh)
                y madd memry [] = SOME (convert_v v') /\ is_true (v_flds_ok c v')).
    { intros sh y v' Hsh Hl. rewrite (N.add_comm i n) in Hl |- *.
      apply (IH i nm (fields info) sh); try reflexivity; try assumption.
      - rewrite afindi_DROP_MAP_fields. exact Hi1.
      - replace (n + i) with (i + n) by lia. apply EL_MAP_fields; assumption.
      - replace (n + i + 1) with (i + n + 1) by lia. apply Hi5, MEM_In_, Hsh. }
    assert (Hlen' : length (MAP FST (fields info)) = length vs)
      by (rewrite LENGTH_length, LENGTH_length in Hlen; rewrite length_map; lia).
    split.
    + erewrite mem_loads_convert_helper; [|split; [exact Hvs|]].
      * cbn [convert_v]. rewrite MAP_convert_v_ZIP by exact Hlen'. reflexivity.
      * intros sh y v' [Hm Hl]. apply MEM_In_ in Hm. split.
        -- rewrite (size_of_compile_shape_n c).
           ++ symmetry; apply size_of_sh_with_ctxt_drop. split; [apply Hi5, MEM_In_, Hm|exact Hd].
           ++ split; [reflexivity|split; [apply Hi5, MEM_In_, Hm|exact Hok]].
        -- exact (proj1 (IH' sh y v' Hm Hl)).
    + apply v_flds_ok_NStruct. split.
      * apply Forall_forall. intros [k v'] Hkv. cbn [snd].
        rewrite ZIP_combine in Hkv. apply in_combine_r in Hkv.
        destruct (mem_loads_In _ _ _ _ _ _ _ Hvs Hkv) as (sh & y & Hsh & Hl).
        exact (proj2 (IH' sh y v' Hsh Hl)).
      * exists info. split; [|split].
        -- rewrite ALOOKUP_eq_afindi, Hi4. cbn [option_map]. rewrite Hi3. reflexivity.
        -- apply MAP_FST_ZIP, Hlen'.
        -- rewrite <- map_map, MAP_SND_ZIP by exact Hlen'.
           exact (proj1 (proj2 mem_loads_some_shape_eq) _ _ _ _ _ _ Hvs).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "mem_load_conversion_inst" *)
Theorem mem_load_conversion_inst : forall (madd : word a -> Prop) memry str_ctxt shape (x : word a) v0,
  mem_load shape x madd memry str_ctxt = SOME v0 /\
  is_true (is_wf_shape str_ctxt shape) /\
  struct_infos_ok str_ctxt ->
  mem_load (compile_shape (MAP (fun '(nm, info) => (nm, fields info)) str_ctxt) shape) x madd memry [] =
    SOME (convert_v v0) /\
  is_true (v_flds_ok str_ctxt v0).
Proof.
  intros madd memry c shape x v0 (H1 & H2 & H3). rewrite compile_shape_n_eq_rev.
  apply (mem_load_conversion madd memry c _ 0 shape x v0). rewrite DROP_skipn. cbn [N.to_nat skipn].
  split; [exact H1|split; [reflexivity|split; assumption]].
Qed.

End MemLoadConv.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "old_exp_shapes_eq" *)
Theorem old_exp_shapes_eq : forall {a} ctxt (es : list (exp a)),
  old_exp_shapes ctxt es = MAP (old_exp_shape ctxt) es.
Proof. intros a ctxt es; induction es as [|e es IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

(** ** Expressions *)

Lemma Forall2_map_eq {A B C} (f : A -> C) (g : B -> C) xs ys :
  Forall2 (fun x y => f x = g y) xs ys -> MAP f xs = MAP g ys.
Proof. induction 1 as [|x y xs ys Hxy _ IH]; cbn; [reflexivity|]. rewrite Hxy, IH; reflexivity. Qed.

Lemma Forall2_impl_In' {A B} (R R' : A -> B -> Prop) xs ys :
  (forall x y, In x xs -> In y ys -> R x y -> R' x y) -> Forall2 R xs ys -> Forall2 R' xs ys.
Proof.
  intros Himp HF; induction HF as [|x y xs ys Hxy _ IH]; constructor.
  - apply Himp; [left|left|]; auto.
  - apply IH. intros x' y' Hx Hy; apply Himp; right; assumption.
Qed.

Lemma EVERY_ZIP_shape {a} (fs : list shape) (vals : list (v a)) :
  length fs = length vals ->
  is_true (EVERY (fun '(s, v0) => bool_decide (s = shape_of v0)) (ZIP (fs, vals))) ->
  fs = MAP shape_of vals.
Proof.
  rewrite ZIP_combine. revert vals; induction fs as [|f fs IH]; intros [|v0 vals] Hl H;
    cbn in *; try discriminate; [reflexivity|].
  unfold is_true in H; apply Bool.andb_true_iff in H as [H1 H2]. apply bool_decide_spec in H1.
  rewrite H1, (IH vals) by (congruence || exact H2). reflexivity.
Qed.

Lemma EVERY_Val_Word {a} (ws : list (v a)) :
  is_true (EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws) ->
  is_true (EVERY (fun w => match w with Val _ => true | _ => false end) ws).
Proof.
  intros H; apply EVERY_Forall_ in H; apply EVERY_Forall_.
  eapply Forall_impl; [|exact H]. intros [[w]| |]; cbn; tauto.
Qed.

Lemma MAP_convert_v_Words {a} (ws : list (v a)) :
  is_true (EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws) ->
  MAP convert_v ws = ws.
Proof. intros H; apply every_convert_v_eq, EVERY_Val_Word, H. Qed.

Section CompileExp.
Context {a : N} {ffi_t : Type}.

Lemma eval_convert_s_Var (ctxt : context) (s : state a ffi_t) vk v0 :
  eval (convert_s ctxt s) (Var vk v0) = OPTION_MAP convert_v (eval s (Var vk v0)).
Proof. destruct vk; cbn [eval convert_s locals globals]; rewrite FLOOKUP_FMAP_MAP2; reflexivity. Qed.

Lemma ALOOKUP_shape_of (l : list (varname * shape)) (m : fmap varname (v a)) k v0 :
  alist_to_fmap l = FMAP_MAP2 (shape_of ∘ SND) m -> FLOOKUP m k = SOME v0 ->
  ALOOKUP l k = SOME (shape_of v0).
Proof.
  intros Hl Hm. rewrite <- FLOOKUP_alist_to_fmap, Hl, FLOOKUP_FMAP_MAP2, Hm. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct" *)
Theorem compile_exp_correct : forall (s : state a ffi_t) e v0 ctxt,
  eval s e = SOME v0 /\
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (locals s) /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (globals s) /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s) /\
  struct_infos_ok (structs s) ->
  old_exp_shape ctxt e = shape_of v0 /\
  is_true (v_flds_ok (structs s) v0) /\
  eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v0).
Proof.
  intros s e v0 ctxt (H & Hl & Hg & Hst & Hfl & Hfg & Hok). revert v0 H.
  induction e as [w|vk vn|es IH|i e IH|nm eflds IH|fld e IH|sh e IH|e IH|e IH|bop es IH|pop es IH
                  |c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| | | ] using exp_nested_ind; intros v0 H;
    cbn [eval] in H.
  - (* Const *)
    injection H as <-. repeat split.
  - (* Var *)
    cbn [compile_exp]. rewrite eval_convert_s_Var. cbn [eval]. destruct vk.
    + rewrite H. cbn [option_map]. split; [|split; [exact (Hfl _ _ H)|reflexivity]].
      cbn [old_exp_shape]. rewrite (ALOOKUP_shape_of _ _ _ _ Hl H). reflexivity.
    + rewrite H. cbn [option_map]. split; [|split; [exact (Hfg _ _ H)|reflexivity]].
      cbn [old_exp_shape]. rewrite (ALOOKUP_shape_of _ _ _ _ Hg H). reflexivity.
  - (* RStruct *)
    destruct (OPT_MMAP (eval s) es) as [vs|] eqn:E; [|discriminate]. injection H as <-.
    pose proof E as E2. apply OPT_MMAP_Forall2 in E2.
    assert (IH' : forall e v', In e es -> eval s e = SOME v' ->
              old_exp_shape ctxt e = shape_of v' /\ is_true (v_flds_ok (structs s) v') /\
              eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v'))
      by (intros e v' He Hv; exact (proj1 (Forall_forall _ _) IH e He v' Hv)).
    split; [|split].
    + rewrite (proj1 (proj2 (proj2 old_exp_shape_def))), old_exp_shapes_eq. cbn [shape_of].
      f_equal. apply Forall2_map_eq. eapply Forall2_impl_In'; [|exact E2].
      intros e v' He _ Hv. exact (proj1 (IH' e v' He Hv)).
    + apply v_flds_ok_RStruct, Forall_forall. intros v' Hv.
      destruct (OPT_MMAP_In _ _ _ _ E Hv) as (e & He & Hev). exact (proj1 (proj2 (IH' e v' He Hev))).
    + rewrite (proj1 compile_exp_def). cbn [eval convert_v].
      rewrite (compile_exp_correct_mmap_helper s ctxt es vs); [reflexivity|].
      split; [exact E|]. intros e He v' Hv. apply MEM_In_ in He. exact (proj2 (proj2 (IH' e v' He Hv))).
  - (* RField *)
    destruct (eval s e) as [[w|vs|nm vf]|] eqn:E; try discriminate.
    destruct (i <? LENGTH vs) eqn:Ei; [|discriminate]. injection H as <-. apply N.ltb_lt in Ei.
    destruct (IH _ eq_refl) as (H1 & H2 & H3). apply v_flds_ok_RStruct in H2.
    split; [|split].
    + rewrite (proj1 (proj2 (proj2 (proj2 old_exp_shape_def)))), H1. cbn [shape_of].
      rewrite oEL_THM, LENGTH_MAP_. destruct (N.ltb_spec i (LENGTH vs)); [|lia].
      rewrite EL_MAP_ by exact Ei. reflexivity.
    + rewrite Forall_forall in H2. apply H2. rewrite EL_nth_any. apply nth_In.
      rewrite LENGTH_length in Ei; lia.
    + rewrite (proj1 (proj2 compile_exp_def)). cbn [eval]. rewrite H3. cbn [convert_v].
      rewrite LENGTH_MAP_. destruct (N.ltb_spec i (LENGTH vs)); [|lia].
      rewrite EL_MAP_ by exact Ei. reflexivity.
  - (* NStruct *)
    destruct (ALOOKUP (structs s) nm) as [info|] eqn:Ea; [|discriminate].
    rewrite UNZIP_MAP in H.
    destruct (bool_decide _) eqn:Ek; [|discriminate]. apply bool_decide_spec in Ek.
    destruct (OPT_MMAP _ eflds) as [vals|] eqn:Ev; [|discriminate].
    destruct (EVERY _ _) eqn:Es; [|discriminate].
    assert (Hv : v0 = NStruct nm (ZIP (MAP fst eflds, vals)))
      by (injection H; intros Hx; rewrite <- Hx; reflexivity).
    clear H. subst v0.
    pose proof (OPT_MMAP_length_ _ _ _ Ev) as Hlv.
    assert (Hlf : length (MAP fst (fields info)) = length eflds)
      by (rewrite Ek, length_map; reflexivity).
    assert (Hsh : MAP snd (fields info) = MAP shape_of vals).
    { apply EVERY_ZIP_shape; [|exact Es]. rewrite length_map in Hlf |- *. lia. }
    assert (IH' : forall p v', In p eflds -> eval s (snd p) = SOME v' ->
              old_exp_shape ctxt (snd p) = shape_of v' /\ is_true (v_flds_ok (structs s) v') /\
              eval (convert_s ctxt s) (compile_exp ctxt (snd p)) = SOME (convert_v v'))
      by (intros p v' Hp Hv; exact (proj1 (Forall_forall _ _) IH p Hp v' Hv)).
    split; [|split].
    + reflexivity.
    + apply v_flds_ok_NStruct. split.
      * apply Forall_forall. intros [k v'] Hkv. cbn [snd].
        rewrite ZIP_combine in Hkv. apply in_combine_r in Hkv.
        destruct (OPT_MMAP_In _ _ _ _ Ev Hkv) as (p & Hp & Hpv). exact (proj1 (proj2 (IH' p v' Hp Hpv))).
      * exists info. split; [exact Ea|split].
        -- rewrite MAP_FST_ZIP by (rewrite length_map; lia). symmetry; exact Ek.
        -- rewrite <- map_map, MAP_SND_ZIP by (rewrite length_map; lia). symmetry; exact Hsh.
    + rewrite (proj1 (proj2 (proj2 compile_exp_def))). cbv zeta.
      rewrite Hst, ALOOKUP_MAP. cbn [option_map]. rewrite Ea. cbn [option_map].
      rewrite fields_in_order_reorder_noop.
      * cbn [eval]. rewrite OPT_MMAP_MAP.
        erewrite OPT_MMAP_map_ext; [|exact Ev|].
        -- cbn [convert_v]. rewrite MAP_convert_v_ZIP by (rewrite length_map; lia). reflexivity.
        -- intros p v' Hp Hv. exact (proj2 (proj2 (IH' p v' Hp Hv))).
      * split; [exact Ek|]. apply (alookup_map_structs_ok (structs s) nm). split; assumption.
  - (* NField *)
    destruct (eval s e) as [[w|vs|nm vflds]|] eqn:E; try discriminate.
    destruct (negb _) eqn:Ea; [|discriminate].
    destruct (IH _ eq_refl) as (H1 & H2 & H3).
    apply v_flds_ok_NStruct in H2 as [HF (info & Hi & Hk & Hs)].
    destruct (map_fst_eq_alookup fld v0 vflds (fields info) (conj Hk H))
      as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6).
    assert (Hsh : shape_of v0 = SND (EL i (fields info))).
    { rewrite Hi5. rewrite <- (EL_MAP_ (shape_of ∘ SND)) by exact Hi3. rewrite Hs.
      rewrite EL_MAP_ by exact Hi4. reflexivity. }
    split; [|split].
    + rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 old_exp_shape_def)))))), H1. cbn [shape_of].
      rewrite Hst, ALOOKUP_MAP. cbn [option_map]. rewrite Hi. cbn [option_map]. rewrite Hi6.
      symmetry; exact Hsh.
    + rewrite Hi5. rewrite Forall_forall in HF. apply HF. rewrite EL_nth_any. apply nth_In.
      rewrite LENGTH_length in Hi3; lia.
    + rewrite (proj1 (proj2 (proj2 (proj2 compile_exp_def)))). cbv zeta.
      rewrite H1. cbn [shape_of]. rewrite Hst, ALOOKUP_MAP. cbn [option_map]. rewrite Hi.
      cbn [option_map]. rewrite Hi2. cbn [eval]. rewrite H3. cbn [convert_v].
      rewrite LENGTH_MAP_. destruct (N.ltb_spec i (LENGTH vflds)); [|lia].
      rewrite EL_MAP_ by exact Hi3. rewrite Hi5. destruct (EL i vflds); reflexivity.
  - (* Load *)
    destruct (is_wf_shape (structs s) sh) eqn:Ew; [|discriminate].
    destruct (eval s e) as [[[w]| |]|] eqn:E; try discriminate.
    destruct (IH _ eq_refl) as (_ & _ & H3).
    destruct (mem_load_conversion_inst (memaddrs s) (memory s) (structs s) sh w v0 (conj H (conj Ew Hok)))
      as [M1 M2].
    split; [|split; [exact M2|]].
    + rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 old_exp_shape_def))))))).
      symmetry; exact (mem_load_some_shape_eq _ _ _ _ _ _ H).
    + rewrite (proj1 (proj2 (proj2 (proj2 (proj2 compile_exp_def))))). cbn [eval].
      rewrite (proj1 (is_wf_shape_compile_shape _)). rewrite H3. cbn [convert_v].
      cbn [convert_s structs memaddrs memory]. rewrite Hst. exact M1.
  - (* Load32 *)
    destruct (eval s e) as [[[w]| |]|] eqn:E; try discriminate.
    destruct (IH _ eq_refl) as (_ & _ & H3).
    destruct (mem_load_32 _ _ _ _) as [w'|] eqn:Em; [|discriminate]. injection H as <-.
    split; [reflexivity|split; [reflexivity|]].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 compile_exp_def))))))).
    cbn [eval]. rewrite H3. cbn [convert_v convert_s memory memaddrs be]. rewrite Em. reflexivity.
  - (* LoadByte *)
    destruct (eval s e) as [[[w]| |]|] eqn:E; try discriminate.
    destruct (IH _ eq_refl) as (_ & _ & H3).
    destruct (mem_load_byte _ _ _ _) as [w'|] eqn:Em; [|discriminate]. injection H as <-.
    split; [reflexivity|split; [reflexivity|]].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 compile_exp_def)))))).
    cbn [eval]. rewrite H3. cbn [convert_v convert_s memory memaddrs be]. rewrite Em. reflexivity.
  - (* Op *)
    destruct (OPT_MMAP (eval s) es) as [ws|] eqn:E; [|discriminate].
    destruct (EVERY _ ws) eqn:Ew; [|discriminate].
    destruct (wordLang.word_op _ _) as [w|] eqn:Eo; [|discriminate]. injection H as <-.
    split; [reflexivity|split; [reflexivity|]].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 compile_exp_def)))))))).
    cbn [eval]. rewrite (compile_exp_correct_mmap_helper s ctxt es ws).
    + rewrite MAP_convert_v_Words by exact Ew. rewrite Ew, Eo. reflexivity.
    + split; [exact E|]. intros e He v' Hv. apply MEM_In_ in He.
      exact (proj2 (proj2 (proj1 (Forall_forall _ _) IH e He v' Hv))).
  - (* Panop *)
    destruct (OPT_MMAP (eval s) es) as [ws|] eqn:E; [|discriminate].
    destruct (EVERY _ ws) eqn:Ew; [|discriminate].
    destruct (pan_op _ _) as [w|] eqn:Eo; [|discriminate]. injection H as <-.
    split; [reflexivity|split; [reflexivity|]].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 compile_exp_def))))))))).
    cbn [eval]. rewrite (compile_exp_correct_mmap_helper s ctxt es ws).
    + rewrite MAP_convert_v_Words by exact Ew. rewrite Ew, Eo. reflexivity.
    + split; [exact E|]. intros e He v' Hv. apply MEM_In_ in He.
      exact (proj2 (proj2 (proj1 (Forall_forall _ _) IH e He v' Hv))).
  - (* Cmp *)
    destruct (eval s e1) as [[[w1]| |]|] eqn:E1; try discriminate.
    destruct (eval s e2) as [[[w2]| |]|] eqn:E2; try discriminate. injection H as <-.
    destruct (IH1 _ eq_refl) as (_ & _ & H1). destruct (IH2 _ eq_refl) as (_ & _ & H2).
    split; [reflexivity|split; [reflexivity|]].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 compile_exp_def)))))))))).
    cbn [eval]. rewrite H1, H2. reflexivity.
  - (* Shift *)
    destruct (eval s e1) as [[[w1]| |]|] eqn:E1; try discriminate.
    destruct (eval s e2) as [[[w2]| |]|] eqn:E2; try discriminate.
    destruct (wordLang.word_sh _ _ _) as [w|] eqn:Eo; [|discriminate]. injection H as <-.
    destruct (IH1 _ eq_refl) as (_ & _ & H1). destruct (IH2 _ eq_refl) as (_ & _ & H2).
    split; [reflexivity|split; [reflexivity|]].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 compile_exp_def))))))))))).
    cbn [eval]. rewrite H1, H2. cbn [convert_v]. rewrite Eo. reflexivity.
  - injection H as <-. repeat split.
  - injection H as <-. repeat split.
  - injection H as <-. repeat split.
Qed.

End CompileExp.

(** ** Programs: helpers *)

Section ProgHelpers.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "evaluate_structs_code_inv" *)
Theorem evaluate_structs_code_inv : forall (p : prog a) (s : state a ffi_t) res s',
  evaluate (p, s) = (res, s') -> structs s' = structs s /\ code s' = code s.
Proof.
  intros p s res s' H. pose proof (evaluate_invariants _ _ _ _ H) as (_ & _ & _ & _ & _ & H1 & H2 & _).
  split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "eval_upd_code_eq2" *)
Theorem eval_upd_code_eq2 : forall (t : state a ffi_t) code0, eval (set_code code0 t) = eval t.
Proof. intros; apply eval_set_code. Qed.

End ProgHelpers.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "res_var_FMAP_MAP2" *)
Theorem res_var_FMAP_MAP2 : forall {K V W} `{EqDecision K} (f : K * V -> W) (g : V -> W) fmap nm x,
  (forall y, x = SOME y -> f (nm, y) = g y) ->
  res_var (FMAP_MAP2 f fmap) (nm, OPTION_MAP g x) = FMAP_MAP2 f (res_var fmap (nm, x)).
Proof.
  intros K V W HK f g fm nm [y|] H; cbn [option_map res_var].
  - rewrite FMAP_MAP2_FUPDATE, (H y eq_refl). reflexivity.
  - apply DOMSUB_FMAP_MAP2.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "res_var_FMAP_MAP2_rev" *)
Theorem res_var_FMAP_MAP2_rev : forall {K V W} `{EqDecision K} (f : K * V -> W) fmap nm x,
  FMAP_MAP2 f (res_var fmap (nm, x)) = res_var (FMAP_MAP2 f fmap) (nm, OPTION_MAP (fun y => f (nm, y)) x).
Proof.
  intros K V W HK f fm nm [y|]; cbn [option_map res_var].
  - apply FMAP_MAP2_FUPDATE.
  - symmetry; apply DOMSUB_FMAP_MAP2.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "FEVERY_res_var" *)
Theorem FEVERY_res_var : forall {K V} `{EqDecision K} (P : K * V -> Prop) fmap k opt_v,
  FEVERY P (res_var fmap (k, opt_v)) <->
  FEVERY P (DRESTRICT fmap (COMPL (k INSERT {}))) /\ (forall v0, opt_v = SOME v0 -> P (k, v0)).
Proof.
  intros K V HK P fm k [v0|]; cbn [res_var].
  - rewrite FEVERY_FUPDATE. split; [intros [H1 H2]; split; [exact H2|intros v' Hv; injection Hv as <-; exact H1]|].
    intros [H1 H2]; split; [apply H2; reflexivity|exact H1].
  - split.
    + intros H; split; [|intros v' Hv; discriminate]. intros k' v' Hk.
      rewrite FLOOKUP_DRESTRICT in Hk. destruct (classical_dec _) as [Hin|]; [|discriminate].
      apply H. rewrite DOMSUB_FLOOKUP_THM. destruct (decide (k = k')) as [->|]; [|exact Hk].
      exfalso. rewrite IN_COMPL in Hin. apply Hin. rewrite IN_INSERT. left; reflexivity.
    + intros [H _] k' v' Hk. rewrite DOMSUB_FLOOKUP_THM in Hk.
      destruct (decide (k = k')) as [->|Hne]; [discriminate|]. apply H.
      rewrite FLOOKUP_DRESTRICT. destruct (classical_dec _) as [|Hn]; [exact Hk|].
      exfalso; apply Hn. rewrite IN_COMPL. intros Hin. rewrite IN_INSERT in Hin.
      destruct Hin as [Hin|Hin]; [congruence|]. exact Hin.
Qed.

Section ShapeConv.
Context {a : N}.

Lemma shape_of_One (x : v a) : shape_of x = One -> exists w, x = Val w.
Proof. destruct x; cbn; try discriminate. intros _; eexists; reflexivity. Qed.

Lemma shape_of_Comb (x : v a) shs : shape_of x = Comb shs -> exists vs, x = RStruct vs /\ shs = MAP shape_of vs.
Proof. destruct x; cbn; try discriminate. intros H; injection H as <-; eexists; split; reflexivity. Qed.

Lemma shape_of_Named (x : v a) nm : shape_of x = Named nm -> exists flds, x = NStruct nm flds.
Proof. destruct x; cbn; try discriminate. intros H; injection H as <-; eexists; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "shape_of_convert_v_ind" *)
Theorem shape_of_convert_v_ind : forall ctxt str_ctxt n sh (x : v a),
  struct_infos_ok ctxt /\
  is_true (is_wf_shape (DROP n ctxt) sh) /\
  is_true (v_flds_ok ctxt x) /\
  str_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt /\
  shape_of x = sh ->
  compile_shape_n str_ctxt n sh = shape_of (convert_v x).
Proof.
  intros ctxt.
  enough (G : forall str_ctxt n sh, forall x : v a, struct_infos_ok ctxt ->
            is_true (is_wf_shape (DROP n ctxt) sh) -> is_true (v_flds_ok ctxt x) ->
            str_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt -> shape_of x = sh ->
            compile_shape_n str_ctxt n sh = shape_of (convert_v x))
    by (intros str_ctxt n sh x (H1 & H2 & H3 & H4 & H5); exact (G _ _ _ x H1 H2 H3 H4 H5)).
  apply (compile_shape_n_ind' (fun str_ctxt n sh => forall x : v a, struct_infos_ok ctxt ->
            is_true (is_wf_shape (DROP n ctxt) sh) -> is_true (v_flds_ok ctxt x) ->
            str_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt -> shape_of x = sh ->
            compile_shape_n str_ctxt n sh = shape_of (convert_v x))).
  - intros str n x _ _ _ _ Hs. apply shape_of_One in Hs as [w ->]. reflexivity.
  - intros str n shs IH x Hok Hw Hf Hst Hs. apply shape_of_Comb in Hs as (vs & -> & ->).
    rewrite (proj1 (proj2 compile_shape_n_def)). cbn [convert_v shape_of]. f_equal.
    rewrite !map_map. apply map_ext_in. intros x Hx.
    apply v_flds_ok_RStruct in Hf. cbn [is_wf_shape] in Hw. apply EVERY_Forall_ in Hw.
    apply IH; try assumption.
    + apply in_map, Hx.
    + apply (proj1 (Forall_forall _ _) Hw), in_map, Hx.
    + apply (proj1 (Forall_forall _ _) Hf), Hx.
    + reflexivity.
  - intros str n nm IH x Hok Hw Hf Hst Hs. apply shape_of_Named in Hs as [flds ->].
    cbn [is_wf_shape] in Hw. destruct (ALOOKUP (DROP n ctxt) nm) as [info|] eqn:Ea; [|discriminate].
    destruct (wf_shape_struct_infos_ok_helper n ctxt nm info (conj Ea Hok))
      as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
    apply v_flds_ok_NStruct in Hf as [HF (info' & Hi & Hk & Hsh)].
    assert (Hii : info' = info).
    { rewrite ALOOKUP_eq_afindi, Hi4 in Hi. cbn [option_map] in Hi. rewrite Hi3 in Hi.
      injection Hi as <-; reflexivity. }
    subst info'.
    rewrite (proj2 (proj2 compile_shape_n_def)). subst str. rewrite afindi_DROP_MAP_fields, Hi1.
    rewrite (N.add_comm n i), (EL_MAP_fields _ _ _ _ Hi3 Hi2). cbn [convert_v shape_of]. f_equal.
    rewrite <- Hsh, !map_map. apply map_ext_in. intros [k x] Hx. cbn [snd].
    replace (i + n + 1) with (n + i + 1) by lia.
    apply (IH i nm (fields info) (shape_of x)); try reflexivity; try assumption.
    + rewrite afindi_DROP_MAP_fields. exact Hi1.
    + replace (n + i) with (i + n) by lia. apply EL_MAP_fields; assumption.
    + rewrite <- Hsh. apply in_map_iff. exists (k, x); split; [reflexivity|exact Hx].
    + replace (n + i + 1) with (i + n + 1) by lia. apply Hi5, MEM_In_. rewrite <- Hsh.
      apply in_map_iff. exists (k, x); split; [reflexivity|exact Hx].
    + exact (proj1 (Forall_forall _ _) HF _ Hx).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "shape_of_convert_v" *)
Theorem shape_of_convert_v : forall ctxt (x : v a) str_ctxt (n : N),
  is_true (v_flds_ok ctxt x) /\
  str_ctxt = MAP (fun '(nm, info) => (nm, fields info)) ctxt /\
  is_true (is_wf_shape_v ctxt x) /\
  struct_infos_ok ctxt ->
  compile_shape str_ctxt (shape_of x) = shape_of (convert_v x).
Proof.
  intros ctxt x str_ctxt n (H1 & H2 & H3 & H4). rewrite compile_shape_n_eq_rev.
  apply (shape_of_convert_v_ind ctxt str_ctxt 0 (shape_of x) x).
  split; [exact H4|split; [|split; [exact H1|split; [exact H2|reflexivity]]]].
  rewrite DROP_skipn. cbn [N.to_nat skipn]. apply is_wf_shape_of_v, H3.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "shape_of_convert_v_rev" *)
Theorem shape_of_convert_v_rev : forall ctxt (x : v a),
  is_true (v_flds_ok ctxt x) /\ is_true (is_wf_shape_v ctxt x) /\ struct_infos_ok ctxt ->
  shape_of (convert_v x) = compile_shape (MAP (fun '(nm, info) => (nm, fields info)) ctxt) (shape_of x).
Proof.
  intros ctxt x (H1 & H2 & H3). symmetry. apply (shape_of_convert_v ctxt x _ 0).
  split; [exact H1|split; [reflexivity|split; assumption]].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "flatten_convert_v" *)
Theorem flatten_convert_v : forall x : v a, flatten (convert_v x) = flatten x.
Proof.
  intros x; induction x as [w|vs IH|nm vs IH] using v_nested_ind; [reflexivity| |].
  - cbn [convert_v flatten]. rewrite map_map. f_equal. apply map_ext_in. intros y Hy.
    exact (proj1 (Forall_forall _ _) IH y Hy).
  - cbn [convert_v flatten]. rewrite map_map. f_equal. apply map_ext_in. intros [k y] Hy.
    exact (proj1 (Forall_forall _ _) IH _ Hy).
Qed.

End ShapeConv.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_uncurry_zip_again" *)
Theorem map_uncurry_zip_again : forall {A B C D} (f : A -> C) (g : B -> D) xs ys,
  LENGTH xs = LENGTH ys ->
  MAP (fun '(x, y) => (f x, g y)) (ZIP (xs, ys)) = ZIP (MAP f xs, MAP g ys).
Proof.
  intros A B C D f g xs ys H. rewrite !ZIP_combine. rewrite !LENGTH_length in H.
  assert (Hl : length xs = length ys) by lia. clear H. revert ys Hl.
  induction xs as [|x xs IH]; intros [|y ys] Hl; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by congruence. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "fupdate_elim2" *)
Theorem fupdate_elim2 : forall {K V} `{EqDecision K} (fm : fmap K V) x y,
  FLOOKUP fm x = SOME y -> FUPDATE fm (x, y) = fm.
Proof.
  intros K V HK fm x y H. apply fmap_ext; intros k. rewrite FLOOKUP_UPDATE.
  destruct (decide (x = k)) as [<-|]; [symmetry; exact H|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_cont_res_def" *)
Definition is_cont_res {a} (res : option (result a)) : bool :=
  match res with
  | NONE => true
  | SOME Break => true
  | SOME Continue => true
  | _ => false
  end.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "is_cont_res_eq_disj" *)
Theorem is_cont_res_eq_disj : forall {a} (res : option (result a)),
  is_true (is_cont_res res) <-> res = NONE \/ res = SOME Break \/ res = SOME Continue.
Proof.
  intros a [[]|]; cbn; split; intros H; try discriminate; try reflexivity; auto;
    destruct H as [H|[H|H]]; discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_res_def" *)
Definition convert_res {a} (res : option (result a)) : option (result a) :=
  match res with
  | SOME Break => SOME Break
  | SOME (Return v0) => SOME (Return (convert_v v0))
  | SOME (Exception eid ev) => SOME (Exception eid (convert_v ev))
  | res => res
  end.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_res_eq_case1" *)
Theorem convert_res_eq_case1 : forall {a} (res : option (result a)),
  convert_res res =
  match res with
  | SOME Break => convert_res (SOME Break)
  | SOME x => convert_res (SOME x)
  | NONE => NONE
  end.
Proof. intros a [[]|]; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_res_eq_case" *)
Theorem convert_res_eq_case : forall {a} (res : option (result a)),
  convert_res res =
  match res with
  | SOME Break => SOME Break
  | SOME x => convert_res (SOME x)
  | NONE => NONE
  end.
Proof. intros a [[]|]; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_res_eq_NONE" *)
Theorem convert_res_eq_NONE : forall {a} (res : option (result a)), convert_res res = NONE <-> res = NONE.
Proof. intros a [[]|]; cbn; split; intros H; try discriminate; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "res_vs_def" *)
Definition res_vs {a} (res : option (result a)) : list (v a) :=
  match res with
  | SOME (Return v0) => [v0]
  | SOME (Exception eid ev) => [ev]
  | _ => []
  end.

(** ** Function calls *)

Lemma FLOOKUP_FEMPTY_FUPDATE_LIST {K V} `{EqDecision K} (l : list (K * V)) k :
  FLOOKUP (FEMPTY |++ l) k = ALOOKUP (REVERSE l) k.
Proof. rewrite FLOOKUP_FUPDATE_LIST. destruct (ALOOKUP (REVERSE l) k); reflexivity. Qed.

Lemma ALOOKUP_ZIP_In {K V} `{EqDecision K} (ks : list K) (vs : list V) k x :
  ALOOKUP (REVERSE (ZIP (ks, vs))) k = SOME x -> In x vs.
Proof.
  intros Hz. apply ALOOKUP_In, in_rev in Hz. rewrite ZIP_combine in Hz. apply in_combine_r in Hz. exact Hz.
Qed.

Lemma LIST_REL_ALOOKUP_shape {a} (vshs : list (varname * shape)) (args : list (v a)) k :
  LIST_REL (fun vshape arg => snd vshape = shape_of arg) vshs args ->
  ALOOKUP vshs k = OPTION_MAP shape_of (ALOOKUP (ZIP (MAP fst vshs, args)) k).
Proof.
  induction 1 as [|[k' sh] arg l1 l2 Hr _ IH]; [reflexivity|].
  cbn [MAP List.map fst]. rewrite (proj2 (proj2 ZIP_eqns)). cbn [ALOOKUP snd] in *.
  destruct (decide (k' = k)); [subst; reflexivity|exact IH].
Qed.

Lemma LIST_REL_length {A B} (R : A -> B -> Prop) xs ys : LIST_REL R xs ys -> length xs = length ys.
Proof. induction 1; cbn; congruence. Qed.

Lemma LIST_REL_impl {A B} (R R' : A -> B -> Prop) xs ys :
  LIST_REL R xs ys -> (forall x y, In x xs -> In y ys -> R x y -> R' x y) -> LIST_REL R' xs ys.
Proof.
  induction 1 as [|x y l1 l2 Hr _ IH]; intros Himp; constructor.
  - apply Himp; [left|left|]; auto.
  - apply IH. intros x' y' Hx Hy; apply Himp; right; assumption.
Qed.

Lemma LIST_REL_map {A B C D} (R : C -> D -> Prop) (f : A -> C) (g : B -> D) xs ys :
  LIST_REL (fun x y => R (f x) (g y)) xs ys -> LIST_REL R (MAP f xs) (MAP g ys).
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma ZIP_MAP_snd {K V W} (f : V -> W) (ks : list K) (vs : list V) :
  ZIP (ks, MAP f vs) = MAP (fun '(k, v0) => (k, f v0)) (ZIP (ks, vs)).
Proof.
  rewrite !ZIP_combine. revert vs; induction ks as [|k ks IH]; intros [|x vs]; cbn; try reflexivity.
  rewrite IH; reflexivity.
Qed.

Lemma ALOOKUP_map_snd {K V W} `{EqDecision K} (f : V -> W) (l : list (K * V)) k :
  ALOOKUP (MAP (fun '(k, v0) => (k, f v0)) l) k = OPTION_MAP f (ALOOKUP l k).
Proof.
  induction l as [|[k' x] l IH]; cbn [MAP List.map ALOOKUP]; [reflexivity|].
  destruct (decide (k' = k)); [reflexivity|exact IH].
Qed.

Section LookupCode.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "lookup_code_flds_ok" *)
Theorem lookup_code_flds_ok : forall (s : state a ffi_t) argexps args fname prog0 newlocals rshape ctxt,
  OPT_MMAP (eval s) argexps = SOME args /\
  lookup_code (code s) fname args = SOME (prog0, (newlocals, rshape)) /\
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (locals s) /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (globals s) /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) /\
  struct_infos_ok (structs s) ->
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt argexps) = SOME (MAP convert_v args) /\
  is_true (EVERY (fun v0 => v_flds_ok (structs s) v0) args) /\
  (exists new_l,
     lookup_code (code (convert_s ctxt s)) fname (MAP convert_v args) =
       SOME (compile {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := new_l;
                        pan_structs.globals := pan_structs.globals ctxt |} prog0,
             (FMAP_MAP2 (fun '(nm, v0) => convert_v v0) newlocals,
              compile_shape (pan_structs.structs ctxt) rshape)) /\
     alist_to_fmap new_l = FMAP_MAP2 (shape_of ∘ SND) newlocals) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) newlocals /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) newlocals.
Proof.
  intros s argexps args fname prog0 newlocals rshape ctxt
    (Ha & Hlc & Hl & Hg & Hst & Hfl & Hfg & Hwl & Hwg & Hok).
  assert (Hargs : forall v0, In v0 args ->
            is_true (v_flds_ok (structs s) v0) /\ is_true (is_wf_shape_v (structs s) v0)).
  { intros v0 Hv. destruct (OPT_MMAP_In _ _ _ _ Ha Hv) as (e & _ & He). split.
    - exact (proj1 (proj2 (compile_exp_correct s e v0 ctxt (conj He (conj Hl (conj Hg (conj Hst
               (conj Hfl (conj Hfg Hok))))))))).
    - apply (eval_is_wf_shape_v s e v0). split; [exact He|split; assumption]. }
  unfold lookup_code in Hlc.
  destruct (FLOOKUP (code s) fname) as [[vshs [p rs]]|] eqn:Ef; [|discriminate].
  destruct (ALL_DISTINCT (MAP fst vshs)) eqn:Ed; [|discriminate].
  destruct (bool_decide (LIST_REL _ vshs args)) eqn:Er; [|discriminate].
  apply bool_decide_spec in Er. cbn [andb] in Hlc.
  assert (E1 : prog0 = p) by (injection Hlc; intros; congruence).
  assert (E2 : newlocals = FEMPTY |++ ZIP (MAP fst vshs, args))
    by (injection Hlc; intros _ Hx _; rewrite <- Hx; reflexivity).
  assert (E3 : rshape = rs) by (injection Hlc; intros; congruence).
  subst prog0 newlocals rshape. clear Hlc.
  split; [|split; [|split; [|split]]].
  - rewrite (compile_exp_correct_mmap_helper s ctxt argexps args); [reflexivity|].
    split; [exact Ha|]. intros e _ v0 He.
    exact (proj2 (proj2 (compile_exp_correct s e v0 ctxt (conj He (conj Hl (conj Hg (conj Hst
               (conj Hfl (conj Hfg Hok))))))))).
  - apply EVERY_Forall_, Forall_forall. intros v0 Hv; exact (proj1 (Hargs v0 Hv)).
  - exists vshs. split.
    + unfold lookup_code. cbn [convert_s code]. unfold convert_code. rewrite FLOOKUP_FMAP_MAP2, Ef.
      cbn [option_map].
      replace (MAP fst (MAP (I ## compile_shape (pan_structs.structs ctxt)) vshs)) with (MAP fst vshs)
        by (rewrite map_map; apply map_ext; intros [k sh]; reflexivity).
      rewrite Ed. rewrite bool_decide_eq_true_2.
      * cbn [andb]. f_equal. f_equal. f_equal.
        apply fmap_ext; intros k. rewrite FLOOKUP_FMAP_MAP2, !FLOOKUP_FEMPTY_FUPDATE_LIST.
        rewrite ZIP_MAP_snd, <- map_rev, ALOOKUP_map_snd.
        destruct (ALOOKUP (REVERSE _) k); reflexivity.
      * apply LIST_REL_map. eapply LIST_REL_impl; [exact Er|]. intros [k sh] arg _ Hin Hr.
        cbn [snd I] in *. rewrite Hr, Hst. symmetry. apply shape_of_convert_v_rev.
        destruct (Hargs arg Hin) as [H1 H2]. split; [exact H1|split; [exact H2|exact Hok]].
    + apply fmap_ext; intros k. rewrite FLOOKUP_alist_to_fmap, FLOOKUP_FMAP_MAP2,
        FLOOKUP_FEMPTY_FUPDATE_LIST, alookup_distinct_reverse.
      * rewrite (LIST_REL_ALOOKUP_shape _ _ _ Er). reflexivity.
      * rewrite MAP_FST_ZIP; [exact Ed|]. rewrite length_map. exact (LIST_REL_length _ _ _ Er).
  - intros k v0 Hk. rewrite FLOOKUP_FEMPTY_FUPDATE_LIST in Hk. apply ALOOKUP_ZIP_In in Hk.
    exact (proj1 (Hargs v0 Hk)).
  - intros k v0 Hk. rewrite FLOOKUP_FEMPTY_FUPDATE_LIST in Hk. apply ALOOKUP_ZIP_In in Hk.
    exact (proj2 (Hargs v0 Hk)).
Qed.

End LookupCode.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_code_locals_upd" *)
Theorem convert_code_locals_upd : forall {a} ctxt (f : list (varname * shape) -> list (varname * shape))
    (code0 : fmap funname (list (varname * shape) * (prog a * shape))),
  convert_code {| pan_structs.structs := pan_structs.structs ctxt;
                  pan_structs.locals := f (pan_structs.locals ctxt);
                  pan_structs.globals := pan_structs.globals ctxt |} code0 = convert_code ctxt code0.
Proof. reflexivity. Qed.

Lemma convert_s_locals_upd {a ffi_t} ctxt l (s : state a ffi_t) :
  convert_s {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := l;
               pan_structs.globals := pan_structs.globals ctxt |} s = convert_s ctxt s.
Proof. reflexivity. Qed.

(** ** Programs *)

Abbreviation cvf := (fun '(nm, v0) => convert_v v0).
Abbreviation shp := (shape_of ∘ SND).

Section CompileCorrect.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma convert_s_set_locals ctxt l s : convert_s ctxt (set_locals l s) = set_locals (FMAP_MAP2 cvf l) (convert_s ctxt s).
Proof. reflexivity. Qed.
Lemma convert_s_set_globals ctxt g s : convert_s ctxt (set_globals g s) = set_globals (FMAP_MAP2 cvf g) (convert_s ctxt s).
Proof. reflexivity. Qed.
Lemma convert_s_set_memory ctxt m s : convert_s ctxt (set_memory m s) = set_memory m (convert_s ctxt s).
Proof. reflexivity. Qed.
Lemma convert_s_set_ffi ctxt f s : convert_s ctxt (set_ffi f s) = set_ffi f (convert_s ctxt s).
Proof. reflexivity. Qed.
Lemma convert_s_set_clock ctxt k s : convert_s ctxt (set_clock k s) = set_clock k (convert_s ctxt s).
Proof. reflexivity. Qed.
Lemma convert_s_dec_clock ctxt s : convert_s ctxt (dec_clock s) = dec_clock (convert_s ctxt s).
Proof. reflexivity. Qed.
Lemma convert_s_empty_locals ctxt s : convert_s ctxt (empty_locals s) = empty_locals (convert_s ctxt s).
Proof. unfold empty_locals. rewrite convert_s_set_locals, FMAP_MAP2_FEMPTY. reflexivity. Qed.
Lemma convert_s_set_var ctxt x v0 s : convert_s ctxt (set_var x v0 s) = set_var x (convert_v v0) (convert_s ctxt s).
Proof. unfold set_var. rewrite convert_s_set_locals, FMAP_MAP2_FUPDATE. reflexivity. Qed.
Lemma convert_s_set_global ctxt x v0 s : convert_s ctxt (set_global x v0 s) = set_global x (convert_v v0) (convert_s ctxt s).
Proof. unfold set_global. rewrite convert_s_set_globals, FMAP_MAP2_FUPDATE. reflexivity. Qed.
Lemma convert_s_set_kvar ctxt vk x v0 s :
  convert_s ctxt (set_kvar vk x v0 s) = set_kvar vk x (convert_v v0) (convert_s ctxt s).
Proof. destruct vk; [apply convert_s_set_var|apply convert_s_set_global]. Qed.
Lemma lookup_kvar_convert_s ctxt vk x s :
  lookup_kvar vk x (convert_s ctxt s) = OPTION_MAP convert_v (lookup_kvar vk x s).
Proof. destruct vk; cbn [lookup_kvar convert_s locals globals]; apply FLOOKUP_FMAP_MAP2. Qed.

Ltac cs_rw := repeat first [ rewrite convert_s_set_locals | rewrite convert_s_set_globals
  | rewrite convert_s_set_memory | rewrite convert_s_set_ffi | rewrite convert_s_set_clock
  | rewrite convert_s_dec_clock | rewrite convert_s_empty_locals | rewrite convert_s_set_var
  | rewrite convert_s_set_global | rewrite convert_s_set_kvar ].

(** The invariants of [compile_correct]'s states. *)
Definition sok s : Prop :=
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) /\
  struct_infos_ok (structs s).

Definition vok sc (x : v a) : Prop := is_true (v_flds_ok sc x) /\ is_true (is_wf_shape_v sc x).

Lemma sok_lookup_local s k x : sok s -> FLOOKUP (locals s) k = SOME x -> vok (structs s) x.
Proof. intros (H1 & _ & H3 & _) Hk; split; [exact (H1 _ _ Hk)|exact (H3 _ _ Hk)]. Qed.
Lemma sok_lookup_global s k x : sok s -> FLOOKUP (globals s) k = SOME x -> vok (structs s) x.
Proof. intros (_ & H2 & _ & H4 & _) Hk; split; [exact (H2 _ _ Hk)|exact (H4 _ _ Hk)]. Qed.

Lemma FEVERY_update {K V} `{EqDecision K} (P : K * V -> Prop) m k x :
  FEVERY P m -> P (k, x) -> FEVERY P (m |+ (k, x)).
Proof.
  intros Hm Hx k' v' Hk. rewrite FLOOKUP_UPDATE in Hk.
  destruct (decide (k = k')) as [<-|]; [injection Hk as <-; exact Hx|exact (Hm _ _ Hk)].
Qed.

Lemma sok_set_var s k x : sok s -> vok (structs s) x -> sok (set_var k x s).
Proof.
  intros (H1 & H2 & H3 & H4 & H5) [Hx1 Hx2]. unfold set_var; state_cbn.
  split; [apply FEVERY_update; assumption|split; [exact H2|split; [apply FEVERY_update; assumption|split; assumption]]].
Qed.

Lemma sok_set_global s k x : sok s -> vok (structs s) x -> sok (set_global k x s).
Proof.
  intros (H1 & H2 & H3 & H4 & H5) [Hx1 Hx2]. unfold set_global; state_cbn.
  split; [exact H1|split; [apply FEVERY_update; assumption|split; [exact H3|split; [apply FEVERY_update; assumption|exact H5]]]].
Qed.

Lemma sok_set_kvar s vk k x : sok s -> vok (structs s) x -> sok (set_kvar vk k x s).
Proof. destruct vk; [apply sok_set_var|apply sok_set_global]. Qed.

Lemma shp_update (m : fmap varname (v a)) k x w :
  FLOOKUP m k = SOME w -> shape_of x = shape_of w ->
  FMAP_MAP2 shp (m |+ (k, x)) = FMAP_MAP2 shp m.
Proof.
  intros Hk Hs. rewrite FMAP_MAP2_FUPDATE. apply fupdate_elim2.
  rewrite FLOOKUP_FMAP_MAP2, Hk. cbn. rewrite Hs. reflexivity.
Qed.

Lemma vok_convert_shape ctxt s x :
  sok s -> vok (structs s) x -> pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  shape_of (convert_v x) = compile_shape (pan_structs.structs ctxt) (shape_of x).
Proof.
  intros (_ & _ & _ & _ & Hok) [H1 H2] Hst. rewrite Hst. apply shape_of_convert_v_rev.
  split; [exact H1|split; assumption].
Qed.

Lemma is_valid_value_convert ctxt s vk k x :
  sok s -> vok (structs s) x -> pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  is_true (is_valid_value s vk k x) ->
  is_valid_value (convert_s ctxt s) vk k (convert_v x) = true /\
  exists w, lookup_kvar vk k s = SOME w /\ shape_of x = shape_of w /\ vok (structs s) w.
Proof.
  intros Hs Hx Hst Hv. unfold is_valid_value in *. rewrite lookup_kvar_convert_s.
  destruct (lookup_kvar vk k s) as [w|] eqn:Ew; [|discriminate]. apply bool_decide_spec in Hv.
  assert (Hw : vok (structs s) w)
    by (destruct vk; [exact (sok_lookup_local _ _ _ Hs Ew)|exact (sok_lookup_global _ _ _ Hs Ew)]).
  split; [|exists w; split; [reflexivity|split; assumption]].
  cbn [option_map]. apply bool_decide_spec.
  rewrite (vok_convert_shape ctxt s x Hs Hx Hst), (vok_convert_shape ctxt s w Hs Hw Hst), Hv. reflexivity.
Qed.

(** Expressions under the invariants. *)
Lemma ecorrect ctxt s e x :
  eval s e = SOME x -> sok s ->
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s) ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  old_exp_shape ctxt e = shape_of x /\ vok (structs s) x /\
  eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v x).
Proof.
  intros He Hs Hl Hg Hst. pose proof Hs as (H1 & H2 & H3 & H4 & H5).
  destruct (compile_exp_correct s e x ctxt (conj He (conj Hl (conj Hg (conj Hst (conj H1 (conj H2 H5)))))))
    as (A & B & C).
  split; [exact A|split; [split; [exact B|]|exact C]].
  apply (eval_is_wf_shape_v s e x). split; [exact He|split; assumption].
Qed.

Lemma ecorrects ctxt s es xs :
  OPT_MMAP (eval s) es = SOME xs -> sok s ->
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s) ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt es) = SOME (MAP convert_v xs) /\
  Forall (vok (structs s)) xs.
Proof.
  intros He Hs Hl Hg Hst. split.
  - apply (compile_exp_correct_mmap_helper s ctxt es xs). split; [exact He|].
    intros e _ x Hx. exact (proj2 (proj2 (ecorrect ctxt s e x Hx Hs Hl Hg Hst))).
  - apply Forall_forall. intros x Hx. destruct (OPT_MMAP_In _ _ _ _ He Hx) as (e & _ & Hev).
    exact (proj1 (proj2 (ecorrect ctxt s e x Hev Hs Hl Hg Hst))).
Qed.

(** The statement of [compile_correct] for one program and state. *)
Definition cc_P (p : prog a) s : Prop :=
  forall res s' ctxt,
  evaluate (p, s) = (res, s') ->
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  sok s ->
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s) ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  res <> SOME Error ->
  evaluate (compile ctxt p, convert_s ctxt s) = (convert_res res, convert_s ctxt s') /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (locals s') /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (globals s') /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s') /\
  (is_true (is_cont_res res) -> alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s')) /\
  is_true (EVERY (v_flds_ok (structs s')) (res_vs res)) /\
  is_true (EVERY (is_wf_shape_v (structs s')) (res_vs res)).

Ltac cc_intro := intros ?res ?s' ?ctxt ?H ?Hst ?Hs ?Hl ?Hg ?Hne.

(** One step of [evaluate] in hypothesis [H] / in the goal. *)
Ltac sstep H := rewrite evaluate_unfold in H; cbn [evaluate_body] in H; rewrite ?fix_clock_evaluate in H.
Ltac tstep := rewrite evaluate_unfold; cbn [evaluate_body]; rewrite ?fix_clock_evaluate.

(** The post-condition for a result state [s'] whose locals and globals
    are those of [s]. *)
Lemma post_same ctxt s s' (res : option (result a)) :
  sok s -> structs s' = structs s -> locals s' = locals s -> globals s' = globals s ->
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s) ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  res_vs res = [] ->
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (locals s') /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (globals s') /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s') /\
  (is_true (is_cont_res res) -> alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s')) /\
  is_true (EVERY (v_flds_ok (structs s')) (res_vs res)) /\
  is_true (EVERY (is_wf_shape_v (structs s')) (res_vs res)).
Proof.
  intros (H1 & H2 & _) E1 E2 E3 Hl Hg Hr. rewrite E1, E2, E3, Hr.
  repeat split; try assumption. intros _; exact Hl.
Qed.

(** As [post_same] for an exit with empty locals (the result is not a
    continuation). *)
Lemma post_empty ctxt s s' (res : option (result a)) :
  sok s -> structs s' = structs s -> locals s' = FEMPTY -> globals s' = globals s ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  is_cont_res res = false ->
  Forall (vok (structs s)) (res_vs res) ->
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (locals s') /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (globals s') /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s') /\
  (is_true (is_cont_res res) -> alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s')) /\
  is_true (EVERY (v_flds_ok (structs s')) (res_vs res)) /\
  is_true (EVERY (is_wf_shape_v (structs s')) (res_vs res)).
Proof.
  intros (H1 & H2 & _) E1 E2 E3 Hg Hc Hv. rewrite E1, E2, E3.
  split; [apply FEVERY_FEMPTY|split; [exact H2|split; [exact Hg|split]]].
  - rewrite Hc; discriminate.
  - split; apply EVERY_Forall_; eapply Forall_impl; try exact Hv; intros x [Hx1 Hx2]; assumption.
Qed.

End CompileCorrect.

Section CompileCases.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Ltac cc_intro := intros ?res ?s' ?ctxt ?H ?Hst ?Hs ?Hl ?Hg ?Hne.
Ltac sstep H := rewrite evaluate_unfold in H; cbn [evaluate_body] in H; rewrite ?fix_clock_evaluate in H.
Ltac tstep := rewrite evaluate_unfold; cbn [evaluate_body]; rewrite ?fix_clock_evaluate.
Ltac cs_rw := repeat first [ rewrite convert_s_set_locals | rewrite convert_s_set_globals
  | rewrite convert_s_set_memory | rewrite convert_s_set_ffi | rewrite convert_s_set_clock
  | rewrite convert_s_dec_clock | rewrite convert_s_empty_locals | rewrite convert_s_set_var
  | rewrite convert_s_set_global | rewrite convert_s_set_kvar ].
Ltac err H := injection H as <- <-; exfalso; match goal with Hn : SOME Error <> SOME Error |- _ => apply Hn; reflexivity end.

Lemma cc_Skip s : cc_P Skip s.
Proof.
  cc_intro. sstep H. injection H as <- <-. cbn [compile]. tstep. split; [reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_Break s : cc_P panLang.Break s.
Proof.
  cc_intro. sstep H. injection H as <- <-. cbn [compile]. tstep. split; [reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_Continue s : cc_P panLang.Continue s.
Proof.
  cc_intro. sstep H. injection H as <- <-. cbn [compile]. tstep. split; [reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_Annot s m1 m2 : cc_P (Annot m1 m2) s.
Proof.
  cc_intro. sstep H. injection H as <- <-. cbn [compile]. tstep. split; [reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_Tick s : cc_P Tick s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep. cbn [convert_s clock].
  destruct (clock s =? 0); injection H as <- <-.
  - split; [cs_rw; reflexivity|].
    eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor].
  - split; [cs_rw; reflexivity|].
    eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_Assign s vk vn e : cc_P (Assign vk vn e) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e) as [value|] eqn:Ee; [|err H].
  destruct (is_valid_value s vk vn value) eqn:Ev; [|err H]. injection H as <- <-.
  destruct (ecorrect ctxt s e value Ee Hs Hl Hg Hst) as (_ & Hvok & Hce).
  destruct (is_valid_value_convert ctxt s vk vn value Hs Hvok Hst Ev) as (Hv' & w & Hw & Hsw & _).
  rewrite Hce, Hv'. split; [cs_rw; reflexivity|].
  pose proof (sok_set_kvar s vk vn value Hs Hvok) as (H1 & H2 & _).
  destruct vk; cbn [set_kvar lookup_kvar] in *; unfold set_var, set_global in *; state_cbn.
  - split; [exact H1|split; [exact H2|split; [exact Hg|split; [|split; reflexivity]]]].
    intros _. rewrite (shp_update _ _ _ _ Hw Hsw). exact Hl.
  - split; [exact H1|split; [exact H2|split; [|split; [intros _; exact Hl|split; reflexivity]]]].
    rewrite (shp_update _ _ _ _ Hw Hsw). exact Hg.
Qed.

Lemma pan_primop_words pop (vs : list (v a)) value :
  pan_primop pop vs = SOME value -> MAP convert_v vs = vs /\ convert_v value = value /\ is_true (v_flds_ok [] value).
Proof.
  destruct pop; unfold pan_primop. destruct (_ && _) eqn:E; [|discriminate].
  apply Bool.andb_true_iff in E as [_ E].
  destruct (backend_common.word_add_carry _ _ _). intros Hv; injection Hv as <-.
  split; [|split; reflexivity]. apply every_convert_v_eq. apply EVERY_Forall_ in E; apply EVERY_Forall_.
  eapply Forall_impl; [|exact E]. intros [[ww]| |]; cbn; tauto.
Qed.

Lemma cc_Primitive s vn pop es : cc_P (Primitive vn pop es) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (OPT_MMAP (eval s) es) as [vs|] eqn:Ee; [|err H].
  destruct (pan_primop pop vs) as [value|] eqn:Ep; [|err H].
  destruct (is_valid_value s Local vn value) eqn:Ev; [|err H]. injection H as <- <-.
  destruct (ecorrects ctxt s es vs Ee Hs Hl Hg Hst) as [Hce _].
  destruct (pan_primop_words _ _ _ Ep) as (Hm & Hc & _).
  assert (Hvok : vok (structs s) value).
  { split; [|exact (pan_primop_is_wf_shape_v _ _ _ _ Ep)].
    destruct pop; unfold pan_primop in Ep. destruct (_ && _); [|discriminate].
    destruct (backend_common.word_add_carry _ _ _). injection Ep as <-. reflexivity. }
  destruct (is_valid_value_convert ctxt s Local vn value Hs Hvok Hst Ev) as (Hv' & w & Hw & Hsw & _).
  rewrite Hce, Hm, Ep. rewrite Hc in Hv'. rewrite Hv'. split; [cs_rw; rewrite Hc; reflexivity|].
  pose proof (sok_set_var s vn value Hs Hvok) as (H1 & H2 & _).
  unfold set_var in *; state_cbn. cbn [lookup_kvar] in Hw.
  split; [exact H1|split; [exact H2|split; [exact Hg|split; [|split; reflexivity]]]].
  intros _. rewrite (shp_update _ _ _ _ Hw Hsw). exact Hl.
Qed.

Lemma cc_Store s e1 e2 : cc_P (Store e1 e2) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e1) as [x1|] eqn:E1; [|err H].
  destruct (ecorrect ctxt s e1 x1 E1 Hs Hl Hg Hst) as (_ & _ & C1). rewrite C1.
  destruct (eval s e2) as [x2|] eqn:E2; [|destruct x1 as [[w]| |]; err H].
  destruct (ecorrect ctxt s e2 x2 E2 Hs Hl Hg Hst) as (_ & _ & C2). rewrite C2.
  destruct x1 as [[w]| |]; try err H. cbn [convert_v]. rewrite flatten_convert_v. cbn [convert_s memaddrs memory].
  destruct (mem_stores _ _ _ _) as [m|]; [|err H]. injection H as <- <-.
  split; [cs_rw; reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_Store32 s e1 e2 : cc_P (Store32 e1 e2) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e1) as [x1|] eqn:E1; [|err H].
  destruct (ecorrect ctxt s e1 x1 E1 Hs Hl Hg Hst) as (_ & _ & C1). rewrite C1.
  destruct (eval s e2) as [x2|] eqn:E2; [|destruct x1 as [[w]| |]; err H].
  destruct (ecorrect ctxt s e2 x2 E2 Hs Hl Hg Hst) as (_ & _ & C2). rewrite C2.
  destruct x1 as [[w]| |]; try err H. destruct x2 as [[w2]| |]; try err H. cbn [convert_v].
  cbn [convert_s memaddrs memory be].
  destruct (mem_store_32 _ _ _ _ _) as [m|]; [|err H]. injection H as <- <-.
  split; [cs_rw; reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_StoreByte s e1 e2 : cc_P (StoreByte e1 e2) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e1) as [x1|] eqn:E1; [|err H].
  destruct (ecorrect ctxt s e1 x1 E1 Hs Hl Hg Hst) as (_ & _ & C1). rewrite C1.
  destruct (eval s e2) as [x2|] eqn:E2; [|destruct x1 as [[w]| |]; err H].
  destruct (ecorrect ctxt s e2 x2 E2 Hs Hl Hg Hst) as (_ & _ & C2). rewrite C2.
  destruct x1 as [[w]| |]; try err H. destruct x2 as [[w2]| |]; try err H. cbn [convert_v].
  cbn [convert_s memaddrs memory be].
  destruct (mem_store_byte _ _ _ _ _) as [m|]; [|err H]. injection H as <- <-.
  split; [cs_rw; reflexivity|].
  eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Ltac ec_all :=
  repeat match goal with
  | E : eval ?s ?e = SOME ?x, Hs : sok ?s |- context [eval (convert_s ?c ?s) (compile_exp ?c ?e)] =>
      let C := fresh "C" in
      destruct (ecorrect c s e x E Hs ltac:(assumption) ltac:(assumption) ltac:(assumption)) as (_ & _ & C);
      rewrite C; clear C
  end.

Ltac rw_ctx :=
  repeat match goal with
  | E : ?x = _ |- context [?x] =>
      tryif (is_var x) then fail else
      lazymatch x with
      | evaluate _ => fail
      | alist_to_fmap _ => fail
      | pan_structs.structs _ => fail
      | _ => rewrite E
      end
  end.

Lemma cc_ShMemLoad s op vk vn e : cc_P (ShMemLoad op vk vn e) s.
Proof.
  cc_intro. sstep H. cbn [compile]. unfold sh_mem_load in H.
  split_all H; leaf_subst H; try (exfalso; apply Hne; reflexivity).
  all: tstep; ec_all; cbn [convert_v]; rewrite lookup_kvar_convert_s; rw_ctx; cbn [option_map convert_v].
  all: unfold sh_mem_load; cbn [convert_s ffi sh_memaddrs]; rw_ctx; cbn beta iota.
  all: split; [cs_rw; reflexivity|].
  - assert (Hvok : forall w : word a, vok (structs s) (ValWord w)) by (intros; split; reflexivity).
    match goal with |- context [set_kvar vk vn ?x s] =>
      pose proof (sok_set_kvar s vk vn x Hs (Hvok _)) as (H1 & H2 & _) end.
    destruct vk; cbn [set_kvar lookup_kvar] in *; unfold set_var, set_global in *; state_cbn.
    + split; [exact H1|split; [exact H2|split; [exact Hg|split; [|split; reflexivity]]]].
      intros _. match goal with Ek : FLOOKUP (locals s) vn = SOME _ |- _ =>
        erewrite shp_update; [exact Hl|exact Ek|reflexivity] end.
    + split; [exact H1|split; [exact H2|split; [|split; [intros _; exact Hl|split; reflexivity]]]].
      match goal with Ek : FLOOKUP (globals s) vn = SOME _ |- _ =>
        erewrite shp_update; [exact Hg|exact Ek|reflexivity] end.
  - eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor].
  - assert (Hvok : forall w : word a, vok (structs s) (ValWord w)) by (intros; split; reflexivity).
    match goal with |- context [set_kvar vk vn ?x s] =>
      pose proof (sok_set_kvar s vk vn x Hs (Hvok _)) as (H1 & H2 & _) end.
    destruct vk; cbn [set_kvar lookup_kvar] in *; unfold set_var, set_global in *; state_cbn.
    + split; [exact H1|split; [exact H2|split; [exact Hg|split; [|split; reflexivity]]]].
      intros _. match goal with Ek : FLOOKUP (locals s) vn = SOME _ |- _ =>
        erewrite shp_update; [exact Hl|exact Ek|reflexivity] end.
    + split; [exact H1|split; [exact H2|split; [|split; [intros _; exact Hl|split; reflexivity]]]].
      match goal with Ek : FLOOKUP (globals s) vn = SOME _ |- _ =>
        erewrite shp_update; [exact Hg|exact Ek|reflexivity] end.
  - eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor].
Qed.

Lemma cc_ShMemStore s op e1 e2 : cc_P (ShMemStore op e1 e2) s.
Proof.
  cc_intro. sstep H. cbn [compile]. unfold sh_mem_store in H.
  split_all H; leaf_subst H; try (exfalso; apply Hne; reflexivity).
  all: tstep; ec_all; cbn [convert_v]; unfold sh_mem_store; cbn [convert_s ffi sh_memaddrs]; rw_ctx;
    cbn beta iota.
  all: split; [cs_rw; reflexivity|].
  all: eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity].
Qed.

Lemma cc_ExtCall s f e1 e2 e3 e4 : cc_P (ExtCall f e1 e2 e3 e4) s.
Proof.
  cc_intro. sstep H. cbn [compile].
  split_all H; leaf_subst H; try (exfalso; apply Hne; reflexivity).
  all: tstep; ec_all; cbn [convert_v convert_s memory memaddrs be ffi]; rw_ctx; cbn beta iota zeta.
  all: split; [cs_rw; reflexivity|].
  all: first
    [ eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity]
    | eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor] ].
Qed.

Lemma size_convert ctxt s (x : v a) :
  sok s -> vok (structs s) x -> pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  size_of_sh_with_ctxt (structs (convert_s ctxt s)) (shape_of (convert_v x)) =
  size_of_sh_with_ctxt (structs s) (shape_of x).
Proof.
  intros Hs Hx Hst. rewrite (vok_convert_shape ctxt s x Hs Hx Hst). cbn [convert_s structs]. rewrite Hst.
  apply size_of_compile_shape. split; [apply is_wf_shape_of_v, (proj2 Hx)|exact (proj2 (proj2 (proj2 (proj2 Hs))))].
Qed.

Lemma cc_Return s e : cc_P (panLang.Return e) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e) as [x|] eqn:Ee; [|err H].
  destruct (ecorrect ctxt s e x Ee Hs Hl Hg Hst) as (_ & Hvok & C). rewrite C.
  rewrite (size_convert ctxt s x Hs Hvok Hst).
  destruct (_ <=? 32) eqn:E32; [|err H]. injection H as <- <-.
  split; [cs_rw; reflexivity|].
  eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|].
  constructor; [exact Hvok|constructor].
Qed.

Lemma cc_Raise s eid e : cc_P (Raise eid e) s.
Proof.
  cc_intro. sstep H. cbn [compile]. tstep.
  destruct (FLOOKUP (eshapes s) eid) as [sh|] eqn:Esh; [|destruct (eval s e); err H].
  replace (eshapes (convert_s ctxt s)) with (convert_eshapes (pan_structs.structs ctxt) (eshapes s))
    by reflexivity.
  unfold convert_eshapes. rewrite FLOOKUP_FMAP_MAP2, Esh. cbn [option_map].
  destruct (eval s e) as [x|] eqn:Ee; [|err H].
  destruct (ecorrect ctxt s e x Ee Hs Hl Hg Hst) as (_ & Hvok & C). rewrite C.
  rewrite (size_convert ctxt s x Hs Hvok Hst).
  destruct (bool_decide (shape_of x = sh)) eqn:Eb; [|err H].
  destruct (_ <=? 32) eqn:E32; [|err H]. cbn [andb] in H. injection H as <- <-.
  apply bool_decide_spec in Eb.
  rewrite bool_decide_eq_true_2 by (rewrite (vok_convert_shape ctxt s x Hs Hvok Hst), Eb; reflexivity).
  cbn [andb]. split; [cs_rw; reflexivity|].
  eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|].
  constructor; [exact Hvok|constructor].
Qed.

Lemma sok_after (p : prog a) s r s1 :
  evaluate (p, s) = (r, s1) -> sok s ->
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s1) v0)) (locals s1) ->
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s1) v0)) (globals s1) ->
  sok s1.
Proof.
  intros E (H1 & H2 & H3 & H4 & H5) F1 F2.
  destruct (evaluate_is_wf_shape_invariant p s r s1 (conj E (conj H3 H4))) as (W1 & W2 & _).
  pose proof (evaluate_structs_code_inv _ _ _ _ E) as [Hs1 _].
  split; [exact F1|split; [exact F2|split; [exact W1|split; [exact W2|rewrite Hs1; exact H5]]]].
Qed.

Lemma convert_res_SOME (r : result a) : exists r', convert_res (SOME r) = SOME r'.
Proof. destruct r; eexists; reflexivity. Qed.

Lemma cc_Seq s p1 p2 :
  (forall p' s', eval_lt (p', s') (Seq p1 p2, s) -> cc_P p' s') -> cc_P (Seq p1 p2) s.
Proof.
  intros IH. cc_intro. sstep H. cbn [compile]. tstep.
  destruct (evaluate (p1, s)) as [r1 s1] eqn:E1.
  assert (Hr1 : r1 <> SOME Error) by (intros ->; injection H as <- <-; apply Hne; reflexivity).
  destruct (IH p1 s ltac:(prove_lt) r1 s1 ctxt E1 Hst Hs Hl Hg Hr1) as (T1 & F1 & F2 & G1 & L1 & V1 & W1).
  rewrite T1. pose proof (evaluate_structs_code_inv _ _ _ _ E1) as [Hs1 _].
  destruct r1 as [r1|].
  - injection H as <- <-. destruct (convert_res_SOME r1) as [r' Hr']. rewrite Hr'.
    split; [rewrite <- Hr'; reflexivity|]. repeat split; assumption.
  - cbn [convert_res].
    apply (IH p2 s1 ltac:(prove_lt) res s' ctxt H); try assumption.
    + rewrite Hs1; exact Hst.
    + exact (sok_after _ _ _ _ E1 Hs F1 F2).
    + exact (L1 eq_refl).
Qed.

Lemma cc_If s e p1 p2 :
  (forall p' s', eval_lt (p', s') (If e p1 p2, s) -> cc_P p' s') -> cc_P (If e p1 p2) s.
Proof.
  intros IH. cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e) as [x|] eqn:Ee; [|err H].
  destruct (ecorrect ctxt s e x Ee Hs Hl Hg Hst) as (_ & _ & C). rewrite C.
  destruct x as [[w]| |]; try err H. cbn [convert_v].
  destruct (negb _); [apply (IH p1 s ltac:(prove_lt))|apply (IH p2 s ltac:(prove_lt))]; assumption.
Qed.

Lemma FLOOKUP_res_var {V} (m : fmap varname V) k o k' :
  FLOOKUP (res_var m (k, o)) k' = if decide (k' = k) then o else FLOOKUP m k'.
Proof.
  destruct o; cbn [res_var]; [rewrite FLOOKUP_UPDATE|rewrite DOMSUB_FLOOKUP_THM];
    destruct (decide (k = k')), (decide (k' = k)); congruence.
Qed.

Lemma FEVERY_res_var' {V} (P : varname * V -> Prop) m k o :
  FEVERY P m -> (forall x, o = SOME x -> P (k, x)) -> FEVERY P (res_var m (k, o)).
Proof.
  intros Hm Ho k' x Hk. rewrite FLOOKUP_res_var in Hk.
  destruct (decide (k' = k)) as [->|]; [apply Ho, Hk|apply Hm, Hk].
Qed.

(** The locals' shapes after the scope of a declaration of [vn]. *)
Lemma dec_locals_shape (l : list (varname * shape)) (ls lst : fmap varname (v a)) vn sh :
  alist_to_fmap l = FMAP_MAP2 shp ls ->
  alist_to_fmap ((vn, sh) :: l) = FMAP_MAP2 shp lst ->
  alist_to_fmap l = FMAP_MAP2 shp (res_var lst (vn, FLOOKUP ls vn)).
Proof.
  intros H1 H2. apply fmap_ext; intros k.
  rewrite FLOOKUP_FMAP_MAP2, FLOOKUP_res_var.
  destruct (decide (k = vn)) as [->|Hne].
  - rewrite H1, FLOOKUP_FMAP_MAP2. reflexivity.
  - apply (f_equal (fun m => FLOOKUP m k)) in H2. rewrite FLOOKUP_FMAP_MAP2 in H2.
    rewrite <- H2. cbn [alist_to_fmap]. rewrite !FLOOKUP_alist_to_fmap. cbn [ALOOKUP].
    destruct (decide (vn = k)); [congruence|reflexivity].
Qed.

Lemma dec_locals_shape_in (l : list (varname * shape)) (ls : fmap varname (v a)) vn x :
  alist_to_fmap l = FMAP_MAP2 shp ls ->
  alist_to_fmap ((vn, shape_of x) :: l) = FMAP_MAP2 shp (ls |+ (vn, x)).
Proof.
  intros H. rewrite (proj2 (alist_to_fmap_thm vn (shape_of x) l)), H, FMAP_MAP2_FUPDATE. reflexivity.
Qed.

Lemma cc_Dec s vn sh e p :
  (forall p' s', eval_lt (p', s') (Dec vn sh e p, s) -> cc_P p' s') -> cc_P (Dec vn sh e p) s.
Proof.
  intros IH. cc_intro. sstep H. cbn [compile]. tstep.
  destruct (eval s e) as [x|] eqn:Ee; [|err H].
  destruct (ecorrect ctxt s e x Ee Hs Hl Hg Hst) as (_ & Hvok & C). rewrite C.
  destruct (bool_decide (sh = shape_of x)) eqn:Eb; [|err H]. apply bool_decide_spec in Eb. subst sh.
  rewrite bool_decide_eq_true_2 by (rewrite (vok_convert_shape ctxt s x Hs Hvok Hst); reflexivity).
  destruct (evaluate (p, set_locals (locals s |+ (vn, x)) s)) as [r1 st] eqn:E1.
  assert (Hres : res = r1) by (injection H; intros _ Hx; exact (eq_sym Hx)).
  assert (Hs' : s' = set_locals (res_var (locals st) (vn, FLOOKUP (locals s) vn)) st)
    by (injection H; intros Hx _; rewrite <- Hx; reflexivity).
  subst res s'. clear H.
  set (ctxt' := {| pan_structs.structs := pan_structs.structs ctxt;
                   pan_structs.locals := (vn, shape_of x) :: pan_structs.locals ctxt;
                   pan_structs.globals := pan_structs.globals ctxt |}).
  assert (Hr1 : r1 <> SOME Error) by exact Hne.
  destruct (IH p (set_locals (locals s |+ (vn, x)) s) ltac:(prove_lt) r1 st ctxt' E1)
    as (T1 & F1 & F2 & G1 & L1 & V1 & W1); try exact Hr1.
  - exact Hst.
  - exact (sok_set_var s vn x Hs Hvok).
  - exact (dec_locals_shape_in _ _ _ _ Hl).
  - exact Hg.
  - pose proof (evaluate_structs_code_inv _ _ _ _ E1) as [Hs1 _]. state_cbn.
    replace (set_locals (FMAP_MAP2 cvf (locals s) |+ (vn, convert_v x)) (convert_s ctxt s))
      with (convert_s ctxt' (set_locals (locals s |+ (vn, x)) s))
      by (rewrite convert_s_set_locals, FMAP_MAP2_FUPDATE; reflexivity).
    rewrite T1. split.
    + cs_rw. unfold ctxt'. rewrite convert_s_locals_upd, res_var_FMAP_MAP2_rev.
      reflexivity.
    + state_cbn. rewrite Hs1 in *. pose proof Hs as (H1 & _).
      split; [|split; [exact F2|split; [exact G1|split; [|split; assumption]]]].
      * apply FEVERY_res_var'; [exact F1|]. intros y Hy. exact (H1 _ _ Hy).
      * intros Hc. apply (dec_locals_shape _ (locals s) _ vn (shape_of x)); [exact Hl|exact (L1 Hc)].
Qed.

Lemma cc_While s e c :
  (forall p' s', eval_lt (p', s') (While e c, s) -> cc_P p' s') -> cc_P (While e c) s.
Proof.
  intros IH. cc_intro. pose proof H as H0. sstep H. cbn [compile]. tstep.
  destruct (eval s e) as [x|] eqn:Ee; [|err H].
  destruct (ecorrect ctxt s e x Ee Hs Hl Hg Hst) as (_ & _ & C). rewrite C.
  destruct x as [[w]| |]; try err H. cbn [convert_v].
  destruct (negb _); [|injection H as <- <-; split; [reflexivity|];
    eapply post_same; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hl|exact Hg|reflexivity]].
  cbn [convert_s clock]. destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. split; [cs_rw; reflexivity|].
    eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor]. }
  destruct (evaluate (c, dec_clock s)) as [r1 s1] eqn:E1.
  assert (Hr1 : r1 <> SOME Error) by (intros ->; injection H as <- <-; apply Hne; reflexivity).
  pose proof (evaluate_structs_code_inv _ _ _ _ E1) as [Hs1 _]. state_cbn.
  destruct (IH c (dec_clock s) ltac:(prove_lt) r1 s1 ctxt E1) as (T1 & F1 & F2 & G1 & L1 & V1 & W1);
    try assumption.
  replace (dec_clock (convert_s ctxt s)) with (convert_s ctxt (dec_clock s)) by reflexivity.
  rewrite T1.
  assert (Hok1 : sok s1).
  { apply (sok_after _ _ _ _ E1); [exact Hs|exact F1|exact F2]. }
  rewrite Hs1 in *.
  destruct r1 as [[| | | |rv|eid ev|ff]|]; cbn [convert_res]; try (exfalso; apply Hr1; reflexivity);
    try (injection H as <- <-; rewrite ?Hs1; split; [reflexivity|];
         split; [exact F1|split; [exact F2|split; [exact G1|split; [exact L1|split; assumption]]]]).
  - (* Continue *)
    exact (IH (While e c) s1 ltac:(prove_lt) res s' ctxt H ltac:(rewrite Hs1; exact Hst) Hok1 (L1 eq_refl) G1 Hne).
  - (* NONE *)
    exact (IH (While e c) s1 ltac:(prove_lt) res s' ctxt H ltac:(rewrite Hs1; exact Hst) Hok1 (L1 eq_refl) G1 Hne).
Qed.

(** The common part of [Call] and [DecCall]: the callee's run. *)
Lemma call_setup s ctxt argexps args fname prog0 nl rsh :
  OPT_MMAP (eval s) argexps = SOME args ->
  lookup_code (code s) fname args = SOME (prog0, (nl, rsh)) ->
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) -> sok s ->
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals s) ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  exists new_l,
    OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt argexps) = SOME (MAP convert_v args) /\
    lookup_code (code (convert_s ctxt s)) fname (MAP convert_v args) =
       SOME (compile {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := new_l;
                        pan_structs.globals := pan_structs.globals ctxt |} prog0,
             (FMAP_MAP2 cvf nl, compile_shape (pan_structs.structs ctxt) rsh)) /\
    alist_to_fmap new_l = FMAP_MAP2 shp nl /\
    sok (set_locals nl (dec_clock s)).
Proof.
  intros Ea El Hst Hs Hl Hg. pose proof Hs as (H1 & H2 & H3 & H4 & H5).
  destruct (lookup_code_flds_ok s argexps args fname prog0 nl rsh ctxt
              (conj Ea (conj El (conj Hl (conj Hg (conj Hst (conj H1 (conj H2 (conj H3 (conj H4 H5))))))))))
    as (A1 & _ & (new_l & A3 & A4) & A5 & A6).
  exists new_l. split; [exact A1|split; [exact A3|split; [exact A4|]]].
  split; [exact A5|split; [exact H2|split; [exact A6|split; [exact H4|exact H5]]]].
Qed.

Lemma globals_shape_after ctxt s (st : state a ffi_t) k w :
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals s) ->
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals st) ->
  FLOOKUP (globals s) k = SOME w ->
  exists w', FLOOKUP (globals st) k = SOME w' /\ shape_of w' = shape_of w.
Proof.
  intros Hg G1 Hk. apply (f_equal (fun m => FLOOKUP m k)) in Hg, G1.
  rewrite FLOOKUP_FMAP_MAP2, Hk in Hg. rewrite FLOOKUP_FMAP_MAP2, Hg in G1.
  destruct (FLOOKUP (globals st) k) as [w'|]; [|discriminate]. injection G1 as G1.
  exists w'; split; [reflexivity|exact (eq_sym G1)].
Qed.

Lemma cc_Call s ct fname argexps :
  (forall p' s', eval_lt (p', s') (Call ct fname argexps, s) -> cc_P p' s') -> cc_P (Call ct fname argexps) s.
Proof.
  intros IH. cc_intro. sstep H.
  destruct (OPT_MMAP (eval s) argexps) as [args|] eqn:Ea; [|err H].
  destruct (lookup_code (code s) fname args) as [[prog0 [nl rsh]]|] eqn:El; [|err H].
  destruct (call_setup s ctxt argexps args fname prog0 nl rsh Ea El Hst Hs Hl Hg)
    as (new_l & A1 & A3 & A4 & Hsok).
  set (nctxt := {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := new_l;
                   pan_structs.globals := pan_structs.globals ctxt |}) in *.
  assert (Ecomp : evaluate (compile ctxt (Call ct fname argexps), convert_s ctxt s) =
    match OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt argexps) with
    | SOME args0 =>
        match lookup_code (code (convert_s ctxt s)) fname args0 with
        | SOME (prog1, (newlocals, return_sh)) =>
            if (clock (convert_s ctxt s) =? 0)%N then (SOME TimeOut, empty_locals (convert_s ctxt s))
            else
              match evaluate (prog1, set_locals newlocals (dec_clock (convert_s ctxt s))) with
              | (NONE, st) => (SOME Error, st)
              | (SOME Break, st) => (SOME Error, st)
              | (SOME Continue, st) => (SOME Error, st)
              | (SOME (Return retv), st) =>
                  if negb (bool_decide (shape_of retv = return_sh)) then (SOME Error, st)
                  else
                    match (match ct with
                           | NONE => NONE
                           | SOME (tl, hdl) => SOME (tl, match hdl with
                                                         | NONE => NONE
                                                         | SOME (eid, (evar, p)) => SOME (eid, (evar, compile ctxt p))
                                                         end)
                           end) with
                    | NONE => (SOME (Return retv), empty_locals st)
                    | SOME (NONE, _) => (NONE, set_locals (locals (convert_s ctxt s)) st)
                    | SOME (SOME (rk, rt), _) =>
                        if is_valid_value (convert_s ctxt s) rk rt retv
                        then (NONE, set_kvar rk rt retv (set_locals (locals (convert_s ctxt s)) st))
                        else (SOME Error, st)
                    end
              | (SOME (Exception eid exn), st) =>
                  match (match ct with
                         | NONE => NONE
                         | SOME (tl, hdl) => SOME (tl, match hdl with
                                                       | NONE => NONE
                                                       | SOME (eid, (evar, p)) => SOME (eid, (evar, compile ctxt p))
                                                       end)
                         end) with
                  | NONE => (SOME (Exception eid exn), empty_locals st)
                  | SOME (_, NONE) => (SOME (Exception eid exn), empty_locals st)
                  | SOME (_, SOME (eid', (evar, p))) =>
                      if bool_decide (eid = eid') then
                        match FLOOKUP (eshapes (convert_s ctxt s)) eid with
                        | SOME sh =>
                            if andb (bool_decide (shape_of exn = sh))
                                    (is_valid_value (convert_s ctxt s) Local evar exn)
                            then evaluate (p, set_var evar exn (set_locals (locals (convert_s ctxt s)) st))
                            else (SOME Error, st)
                        | NONE => (SOME Error, st)
                        end
                      else (SOME (Exception eid exn), empty_locals st)
                  end
              | (res, st) => (res, empty_locals st)
              end
        | _ => (SOME Error, convert_s ctxt s)
        end
    | _ => (SOME Error, convert_s ctxt s)
    end).
  { cbn [compile]. destruct ct as [[tl [[eid' [evar hp]]|]]|]; cbv zeta;
      rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))))))))))))));
      reflexivity. }
  rewrite Ecomp. clear Ecomp. rewrite A1, A3. cbn [convert_s clock].
  destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. split; [cs_rw; reflexivity|].
    eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor]. }
  rewrite fix_clock_evaluate in H.
  destruct (evaluate (prog0, set_locals nl (dec_clock s))) as [r1 st] eqn:E1.
  assert (Hr1 : r1 <> SOME Error) by (intros ->; injection H as <- <-; apply Hne; reflexivity).
  destruct (IH prog0 (set_locals nl (dec_clock s)) ltac:(prove_lt) r1 st nctxt E1)
    as (T1 & F1 & F2 & G1 & L1 & V1 & W1); try exact Hr1.
  { exact Hst. }
  { exact Hsok. }
  { exact A4. }
  { exact Hg. }
  replace (set_locals (FMAP_MAP2 cvf nl) (dec_clock (convert_s ctxt s)))
    with (convert_s nctxt (set_locals nl (dec_clock s))) by reflexivity.
  rewrite T1. unfold nctxt in *. rewrite convert_s_locals_upd.
  pose proof (evaluate_structs_code_inv _ _ _ _ E1) as [Hs1 _]. state_cbn.
  pose proof (evaluate_is_wf_shape_invariant _ _ _ _ (conj E1 (conj (proj1 (proj2 (proj2 Hsok)))
                (proj1 (proj2 (proj2 (proj2 Hsok))))))) as (Wl & Wg & Wr). state_cbn.
  rewrite Hs1 in *.
  destruct r1 as [[| | | |rv|eid ev|ff]|]; cbn [convert_res];
    try (exfalso; apply Hr1; reflexivity); try (injection H as <- <-; exfalso; apply Hne; reflexivity).
  - (* TimeOut *)
    destruct ct as [[tl [[eid' [evar hp]]|]]|]; injection H as <- <-; (split; [cs_rw; reflexivity|]);
    state_cbn; rewrite ?Hs1;
    (split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|split; reflexivity]]]]).
  - (* Return *)
    cbn [res_vs] in V1, W1. apply EVERY_Forall_ in V1, W1. inversion V1 as [|? ? Vr _]; inversion W1 as [|? ? Wr' _].
    subst.
    assert (Hrv : vok (structs s) rv) by (split; assumption).
    destruct (bool_decide (shape_of rv = rsh)) eqn:Eb; [|cbn [negb] in H; err H].
    apply bool_decide_spec in Eb.
    rewrite (bool_decide_eq_true_2 (shape_of (convert_v rv) = compile_shape (pan_structs.structs ctxt) rsh))
      by (rewrite (vok_convert_shape ctxt s rv Hs Hrv Hst), Eb; reflexivity).
    cbn [negb] in H |- *.
    destruct ct as [[[[rk rt]|] hdl]|].
    + destruct (is_valid_value s rk rt rv) eqn:Ev; [|err H]. injection H as <- <-. rewrite ?Hs1.
      destruct (is_valid_value_convert ctxt s rk rt rv Hs Hrv Hst Ev) as (Ev' & w & Hw & Hsw & _).
      rewrite Ev'. split; [cs_rw; reflexivity|].
      pose proof Hs as (H1 & H2 & H3 & H4 & H5).
      destruct rk; cbn [set_kvar lookup_kvar] in *; unfold set_var, set_global; state_cbn; rewrite ?Hs1.
      * split; [apply FEVERY_update; [exact H1|exact (proj1 Hrv)]|].
        split; [exact F2|split; [exact G1|split; [|split; reflexivity]]].
        intros _. rewrite (shp_update _ _ _ _ Hw Hsw). exact Hl.
      * split; [exact H1|split; [apply FEVERY_update; [exact F2|exact (proj1 Hrv)]|]].
        destruct (globals_shape_after ctxt s st rt w Hg G1 Hw) as (w' & Hw' & Hsw').
        split; [erewrite shp_update; [exact G1|exact Hw'|rewrite Hsw', Hsw; reflexivity]|].
        split; [intros _; exact Hl|split; reflexivity].
    + injection H as <- <-. split; [cs_rw; reflexivity|].
      pose proof Hs as (H1 & H2 & _). state_cbn. rewrite ?Hs1.
      split; [exact H1|split; [exact F2|split; [exact G1|split; [intros _; exact Hl|split; reflexivity]]]].
    + injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1.
      split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|]]]].
      cbn [res_vs]. split; apply EVERY_Forall_; constructor; try constructor; assumption.
  - (* Exception *)
    cbn [res_vs] in V1, W1. apply EVERY_Forall_ in V1, W1. inversion V1 as [|? ? Vr _]; inversion W1 as [|? ? Wr' _].
    subst.
    assert (Hev : vok (structs s) ev) by (split; assumption).
    assert (Pexc : FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (locals (empty_locals st)) /\
       FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals (empty_locals st)) /\
       alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 shp (globals (empty_locals st)) /\
       (is_true (is_cont_res (SOME (Exception eid ev))) ->
          alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 shp (locals (empty_locals st))) /\
       is_true (EVERY (v_flds_ok (structs s)) (res_vs (SOME (Exception eid ev)))) /\
       is_true (EVERY (is_wf_shape_v (structs s)) (res_vs (SOME (Exception eid ev))))).
    { state_cbn. split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|]]]].
      cbn [res_vs]. split; apply EVERY_Forall_; constructor; try constructor; assumption. }
    destruct ct as [[tl [[eid' [evar hp]]|]]|].
    + destruct (bool_decide (eid = eid')) eqn:Eeid.
      * apply bool_decide_spec in Eeid. subst eid'.
        destruct (FLOOKUP (eshapes s) eid) as [sh|] eqn:Esh; [|err H].
        replace (eshapes (convert_s ctxt s)) with (convert_eshapes (pan_structs.structs ctxt) (eshapes s))
          by reflexivity.
        unfold convert_eshapes. rewrite FLOOKUP_FMAP_MAP2, Esh. cbn [option_map].
        destruct (bool_decide (shape_of ev = sh)) eqn:Esh2; [|cbn [andb] in H; err H].
        destruct (is_valid_value s Local evar ev) eqn:Ev; [|cbn [andb] in H; err H].
        cbn [andb] in H. apply bool_decide_spec in Esh2.
        destruct (is_valid_value_convert ctxt s Local evar ev Hs Hev Hst Ev) as (Ev' & w & Hw & Hsw & _).
        rewrite (bool_decide_eq_true_2 (shape_of (convert_v ev) = compile_shape (pan_structs.structs ctxt) sh))
          by (rewrite (vok_convert_shape ctxt s ev Hs Hev Hst), Esh2; reflexivity).
        rewrite Ev'. cbn [andb].
        replace (set_var evar (convert_v ev) (set_locals (locals (convert_s ctxt s)) (convert_s ctxt st)))
          with (convert_s ctxt (set_var evar ev (set_locals (locals s) st))) by (cs_rw; reflexivity).
        pose proof Hs as (H1 & H2 & H3 & H4 & H5).
        apply (IH hp (set_var evar ev (set_locals (locals s) st)) ltac:(prove_lt) res s' ctxt H);
          state_cbn; try assumption.
        all: first
          [ rewrite ?Hs1; exact Hst
          | unfold set_var, sok; state_cbn; rewrite ?Hs1;
            split; [apply FEVERY_update; [exact H1|exact (proj1 Hev)]|split; [exact F2|]];
            split; [apply FEVERY_update; [exact H3|exact (proj2 Hev)]|split; [exact Wg|exact H5]]
          | cbn [lookup_kvar] in Hw; rewrite (shp_update _ _ _ _ Hw Hsw); exact Hl ].
      * injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1. exact Pexc.
    + injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1. exact Pexc.
    + injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1. exact Pexc.
  - (* FinalFFI *)
    destruct ct as [[tl [[eid' [evar hp]]|]]|]; injection H as <- <-; (split; [cs_rw; reflexivity|]);
    state_cbn; rewrite ?Hs1;
    (split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|split; reflexivity]]]]).
Qed.

Lemma cc_DecCall s rt sh fname argexps p1 :
  (forall p' s', eval_lt (p', s') (DecCall rt sh fname argexps p1, s) -> cc_P p' s') ->
  cc_P (DecCall rt sh fname argexps p1) s.
Proof.
  intros IH. cc_intro. sstep H.
  destruct (OPT_MMAP (eval s) argexps) as [args|] eqn:Ea; [|err H].
  destruct (lookup_code (code s) fname args) as [[prog0 [nl rsh]]|] eqn:El; [|err H].
  destruct (call_setup s ctxt argexps args fname prog0 nl rsh Ea El Hst Hs Hl Hg)
    as (new_l & A1 & A3 & A4 & Hsok).
  set (nctxt := {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := new_l;
                   pan_structs.globals := pan_structs.globals ctxt |}) in *.
  set (dctxt := {| pan_structs.structs := pan_structs.structs ctxt;
                   pan_structs.locals := (rt, sh) :: pan_structs.locals ctxt;
                   pan_structs.globals := pan_structs.globals ctxt |}).
  cbn [compile]. fold dctxt. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))))))))))))))). rewrite A1, A3. cbn [convert_s clock].
  destruct (clock s =? 0) eqn:Ec.
  { injection H as <- <-. split; [cs_rw; reflexivity|].
    eapply post_empty; [exact Hs|reflexivity|reflexivity|reflexivity|exact Hg|reflexivity|constructor]. }
  rewrite fix_clock_evaluate in H.
  destruct (evaluate (prog0, set_locals nl (dec_clock s))) as [r1 st] eqn:E1.
  assert (Hr1 : r1 <> SOME Error) by (intros ->; injection H as <- <-; apply Hne; reflexivity).
  destruct (IH prog0 (set_locals nl (dec_clock s)) ltac:(prove_lt) r1 st nctxt E1)
    as (T1 & F1 & F2 & G1 & L1 & V1 & W1); try exact Hr1.
  { exact Hst. }
  { exact Hsok. }
  { exact A4. }
  { exact Hg. }
  replace (set_locals (FMAP_MAP2 cvf nl) (dec_clock (convert_s ctxt s)))
    with (convert_s nctxt (set_locals nl (dec_clock s))) by reflexivity.
  rewrite T1. unfold nctxt in *. rewrite convert_s_locals_upd.
  pose proof (evaluate_structs_code_inv _ _ _ _ E1) as [Hs1 _]. state_cbn.
  pose proof (evaluate_is_wf_shape_invariant _ _ _ _ (conj E1 (conj (proj1 (proj2 (proj2 Hsok)))
                (proj1 (proj2 (proj2 (proj2 Hsok))))))) as (Wl & Wg & Wr). state_cbn.
  rewrite Hs1 in *.
  destruct r1 as [[| | | |rv|eid ev|ff]|]; cbn [convert_res];
    try (exfalso; apply Hr1; reflexivity); try (injection H as <- <-; exfalso; apply Hne; reflexivity).
  - (* TimeOut *)
    injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1.
    split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|split; reflexivity]]]].
  - (* Return *)
    cbn [res_vs] in V1, W1. apply EVERY_Forall_ in V1, W1. inversion V1 as [|? ? Vr _]; inversion W1 as [|? ? Wr' _].
    subst.
    assert (Hrv : vok (structs s) rv) by (split; assumption).
    destruct (bool_decide (shape_of rv = sh)) eqn:Eb1; [|cbn [andb] in H; err H].
    destruct (bool_decide (shape_of rv = rsh)) eqn:Eb2; [|cbn [andb] in H; err H].
    apply bool_decide_spec in Eb1, Eb2. cbn [andb] in H.
    rewrite (bool_decide_eq_true_2 (shape_of (convert_v rv) = compile_shape (pan_structs.structs ctxt) sh))
      by (rewrite (vok_convert_shape ctxt s rv Hs Hrv Hst), Eb1; reflexivity).
    rewrite (bool_decide_eq_true_2 (shape_of (convert_v rv) = compile_shape (pan_structs.structs ctxt) rsh))
      by (rewrite (vok_convert_shape ctxt s rv Hs Hrv Hst), Eb2; reflexivity).
    cbn [andb].
    destruct (evaluate (p1, set_var rt rv (set_locals (locals s) st))) as [r2 st2] eqn:E2.
    assert (Hres : res = r2) by (injection H; intros _ Hx; exact (eq_sym Hx)).
    assert (Hs' : s' = set_locals (res_var (locals st2) (rt, FLOOKUP (locals s) rt)) st2)
      by (injection H; intros Hx _; rewrite <- Hx; reflexivity).
    subst res s'. clear H.
    pose proof Hs as (H1 & H2 & H3 & H4 & H5).
    assert (Hsok2 : sok (set_var rt rv (set_locals (locals s) st))).
    { unfold set_var, sok; state_cbn; rewrite ?Hs1.
      split; [apply FEVERY_update; [exact H1|exact (proj1 Hrv)]|split; [exact F2|]].
      split; [apply FEVERY_update; [exact H3|exact (proj2 Hrv)]|split; [exact Wg|exact H5]]. }
    subst sh.
    destruct (IH p1 (set_var rt rv (set_locals (locals s) st)) ltac:(prove_lt) r2 st2 dctxt E2)
      as (T2 & F3 & F4 & G2 & L2 & V2 & W2); try exact Hne.
    { unfold set_var; state_cbn. rewrite Hs1. exact Hst. }
    { exact Hsok2. }
    { exact (dec_locals_shape_in _ _ _ _ Hl). }
    { exact G1. }
    pose proof (evaluate_structs_code_inv _ _ _ _ E2) as [Hs2 _]. unfold set_var in Hs2. state_cbn.
    replace (set_var rt (convert_v rv) (set_locals (locals (convert_s ctxt s)) (convert_s ctxt st)))
      with (convert_s dctxt (set_var rt rv (set_locals (locals s) st))) by (cs_rw; reflexivity).
    rewrite T2. split.
    + cs_rw. unfold dctxt. rewrite convert_s_locals_upd, res_var_FMAP_MAP2_rev. reflexivity.
    + state_cbn. rewrite Hs2, Hs1 in *.
      split; [|split; [exact F4|split; [exact G2|split; [|split; assumption]]]].
      * apply FEVERY_res_var'; [exact F3|]. intros y Hy. exact (H1 _ _ Hy).
      * intros Hc. apply (dec_locals_shape _ (locals s) _ rt (shape_of rv)); [exact Hl|exact (L2 Hc)].
  - (* Exception *)
    injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1.
    split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|]]]].
    split; assumption.
  - (* FinalFFI *)
    injection H as <- <-. split; [cs_rw; reflexivity|]. state_cbn; rewrite ?Hs1.
    split; [apply FEVERY_FEMPTY|split; [exact F2|split; [exact G1|split; [discriminate|split; reflexivity]]]].
Qed.

Lemma cc_all : forall x : prog a * state a ffi_t, cc_P (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  assert (IH' : forall p' s', eval_lt (p', s') (p, s) -> cc_P p' s')
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  cbn [fst snd]. destruct p.
  - apply cc_Skip.
  - apply cc_Dec; exact IH'.
  - apply cc_Assign.
  - apply cc_Primitive.
  - apply cc_Store.
  - apply cc_Store32.
  - apply cc_StoreByte.
  - apply cc_Seq; exact IH'.
  - apply cc_If; exact IH'.
  - apply cc_While; exact IH'.
  - apply cc_Break.
  - apply cc_Continue.
  - apply cc_Call; exact IH'.
  - apply cc_DecCall; exact IH'.
  - apply cc_ExtCall.
  - apply cc_Raise.
  - apply cc_Return.
  - apply cc_ShMemLoad.
  - apply cc_ShMemStore.
  - apply cc_Tick.
  - apply cc_Annot.
Qed.

End CompileCases.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct" *)
Theorem compile_correct : forall {a ffi_t} (p : prog a) (s : state a ffi_t) res s' ctxt,
  evaluate (p, s) = (res, s') /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (locals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) /\
  struct_infos_ok (structs s) /\
  alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (locals s) /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (globals s) /\
  res <> SOME Error ->
  evaluate (compile ctxt p, convert_s ctxt s) = (convert_res res, convert_s ctxt s') /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (locals s') /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s') v0)) (globals s') /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (globals s') /\
  (is_true (is_cont_res res) ->
     alist_to_fmap (pan_structs.locals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (locals s')) /\
  is_true (EVERY (v_flds_ok (structs s')) (res_vs res)) /\
  is_true (EVERY (is_wf_shape_v (structs s')) (res_vs res)).
Proof.
  intros a ffi_t p s res s' ctxt (H & Hst & H1 & H2 & H3 & H4 & H5 & Hl & Hg & Hne).
  apply (cc_all (p, s) res s' ctxt H Hst); try assumption.
  split; [exact H1|split; [exact H2|split; [exact H3|split; [exact H4|exact H5]]]].
Qed.

(** ** Declarations *)

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decs_structs" *)
Theorem compile_decs_structs : forall {a} ctxt (decs : list (decl a)) decs' ctxt',
  compile_decs ctxt decs = (decs', ctxt') -> pan_structs.structs ctxt' = pan_structs.structs ctxt.
Proof.
  intros a ctxt decs; revert ctxt; induction decs as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    intros ctxt decs' ctxt' H; cbn [compile_decs] in H.
  - injection H as _ <-; reflexivity.
  - destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. injection H as _ <-. exact (IH _ _ _ E).
  - destruct (compile_decs _ ds) as [ds' c'] eqn:E. injection H as _ <-. exact (IH _ _ _ E).
  - destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. injection H as _ <-. exact (IH _ _ _ E).
  - exact (IH _ _ _ H).
Qed.

Section Decls.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma convert_s_set_code ctxt c s :
  convert_s ctxt (set_code c s) = set_code (convert_code ctxt c) (convert_s ctxt s).
Proof. reflexivity. Qed.

Lemma convert_s_set_eshapes ctxt e s :
  convert_s ctxt (set_eshapes e s) = set_eshapes (convert_eshapes (pan_structs.structs ctxt) e) (convert_s ctxt s).
Proof. reflexivity. Qed.

Lemma eval_convert_s_ctxt ctxt1 ctxt2 s :
  pan_structs.structs ctxt1 = pan_structs.structs ctxt2 ->
  eval (convert_s ctxt1 s) = eval (convert_s ctxt2 s).
Proof. intros H. apply eval_state_cong; reflexivity. Qed.

Lemma context_eta (c : context) :
  c = {| pan_structs.structs := pan_structs.structs c; pan_structs.locals := pan_structs.locals c;
         pan_structs.globals := pan_structs.globals c |}.
Proof. destruct c; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct" *)
Theorem compile_decls_correct : forall s' s (decs : list (decl a)) ctxt decs' ctxt',
  evaluate_decls s decs = SOME s' /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) /\
  pan_structs.locals ctxt = [] /\
  struct_infos_ok (structs s) /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (globals s) /\
  compile_decs ctxt decs = (decs', ctxt') ->
  evaluate_decls (convert_s ctxt' s) decs' = SOME (convert_s ctxt' s') /\
  (exists gb, ctxt' = {| pan_structs.structs := pan_structs.structs ctxt;
                         pan_structs.locals := pan_structs.locals ctxt; pan_structs.globals := gb |} /\
     FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s') /\
     FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s') /\
     structs s' = structs s /\
     locals s' = locals s /\
     alist_to_fmap gb = FMAP_MAP2 (shape_of ∘ SND) (globals s')).
Proof.
  intros s' s decs; revert s; induction decs as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    intros s ctxt decs' ctxt' (H & Hst & Hlc & Hok & Hf & Hw & Hg & Hc).
  - cbn [evaluate_decls compile_decs] in H, Hc. injection H as <-. injection Hc as <- <-.
    split; [reflexivity|]. exists (pan_structs.globals ctxt).
    split; [apply context_eta|repeat split; assumption].
  - (* Function *)
    cbn [evaluate_decls compile_decs] in H, Hc.
    destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. injection Hc as <- <-.
    destruct (_ && _) eqn:Ew; [|discriminate]. apply Bool.andb_true_iff in Ew as [Ew1 Ew2].
    destruct (IH _ ctxt ds' c' (conj H (conj Hst (conj Hlc (conj Hok (conj Hf (conj Hw (conj Hg E))))))))
      as [Ev (gb & Hc' & R)].
    split; [|exists gb; split; [exact Hc'|exact R]].
    pose proof (compile_decs_structs _ _ _ _ E) as Hs'.
    cbn [evaluate_decls]. cbn [params fun_decl_return name body].
    rewrite (proj2 (Bool.andb_true_iff _ _)).
    + rewrite <- Ev. f_equal. rewrite convert_s_set_code. f_equal.
      cbn [convert_s code]. unfold convert_code at 2. rewrite FMAP_MAP2_FUPDATE. f_equal.
      cbn beta iota zeta. rewrite Hs'. apply (f_equal2 pair); [reflexivity|]. apply (f_equal2 pair); [apply map_ext; intros [p sh]; reflexivity|reflexivity].
    + split.
      * apply EVERY_Forall_, Forall_forall. intros [p sh] Hp. apply in_map_iff in Hp as ([p' sh'] & Hx & _).
        injection Hx as <- <-. cbn. apply (proj1 (is_wf_shape_compile_shape _)).
      * apply (proj1 (is_wf_shape_compile_shape _)).
  - (* Decl *)
    cbn [evaluate_decls compile_decs] in H, Hc.
    destruct (eval (set_locals FEMPTY s) e) as [res|] eqn:Ee; [|discriminate].
    destruct (bool_decide (sh = shape_of res)) eqn:Eb; [|discriminate]. apply bool_decide_spec in Eb. subst sh.
    set (ctxt1 := {| pan_structs.structs := pan_structs.structs ctxt; pan_structs.locals := pan_structs.locals ctxt;
                     pan_structs.globals := (v0, shape_of res) :: pan_structs.globals ctxt |}) in Hc.
    destruct (compile_decs ctxt1 ds) as [ds' c'] eqn:E. injection Hc as <- <-.
    assert (Hsl : sok (set_locals FEMPTY s)).
    { split; [apply FEVERY_FEMPTY|split; [exact Hf|split; [apply FEVERY_FEMPTY|split; [exact Hw|exact Hok]]]]. }
    destruct (ecorrect ctxt (set_locals FEMPTY s) e res Ee Hsl) as (_ & Hvok & Hce);
      [rewrite Hlc; apply fmap_ext; intros; reflexivity|exact Hg|exact Hst|].
    destruct (IH (set_globals (globals s |+ (v0, res)) s) ctxt1 ds' c') as [Ev (gb & Hc' & R)].
    { split; [exact H|]. state_cbn. split; [exact Hst|split; [exact Hlc|split; [exact Hok|]]].
      split; [apply FEVERY_update; [exact Hf|exact (proj1 Hvok)]|].
      split; [apply FEVERY_update; [exact Hw|exact (proj2 Hvok)]|].
      split; [|exact E]. apply dec_locals_shape_in, Hg. }
    split.
    + cbn [evaluate_decls].
      rewrite (eval_state_cong (set_locals FEMPTY (convert_s c' s)) (convert_s ctxt (set_locals FEMPTY s)))
        by (cbn; try reflexivity; rewrite FMAP_MAP2_FEMPTY; reflexivity).
      rewrite Hce.
      rewrite bool_decide_eq_true_2
        by (rewrite (vok_convert_shape ctxt (set_locals FEMPTY s) res Hsl Hvok Hst); reflexivity).
      rewrite <- Ev. f_equal. rewrite convert_s_set_globals, FMAP_MAP2_FUPDATE. reflexivity.
    + exists gb. state_cbn. destruct R as (R1 & R2 & R3 & R4 & R5).
      split; [rewrite Hc'; reflexivity|]. repeat split; assumption.
  - (* ExnDecl *)
    cbn [evaluate_decls compile_decs] in H, Hc.
    destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. injection Hc as <- <-.
    destruct (_ && _) eqn:Ew; [|discriminate]. apply Bool.andb_true_iff in Ew as [Ew1 Ew2].
    apply bool_decide_spec in Ew1.
    destruct (IH _ ctxt ds' c' (conj H (conj Hst (conj Hlc (conj Hok (conj Hf (conj Hw (conj Hg E))))))))
      as [Ev (gb & Hc' & R)].
    split; [|exists gb; split; [exact Hc'|exact R]].
    pose proof (compile_decs_structs _ _ _ _ E) as Hs'.
    cbn [evaluate_decls]. rewrite (proj2 (Bool.andb_true_iff _ _)).
    + rewrite <- Ev. f_equal. rewrite convert_s_set_eshapes. f_equal. unfold convert_eshapes.
      rewrite FMAP_MAP2_FUPDATE. cbn [convert_s eshapes]. unfold convert_eshapes. rewrite Hs'. reflexivity.
    + split; [|apply (proj1 (is_wf_shape_compile_shape _))].
      apply bool_decide_spec. cbn [convert_s eshapes]. unfold convert_eshapes.
      rewrite FLOOKUP_FMAP_MAP2, Ew1. reflexivity.
  - (* Name *)
    cbn [evaluate_decls compile_decs] in H, Hc.
    exact (IH _ ctxt decs' ctxt' (conj H (conj Hst (conj Hlc (conj Hok (conj Hf (conj Hw (conj Hg Hc)))))))).
Qed.

End Decls.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "decs_stcnames_compile_decs" *)
Theorem decs_stcnames_compile_decs : forall {a} acc ctxt (decs : list (decl a)),
  decs_stcnames acc (FST (compile_decs ctxt decs)) = SOME acc.
Proof.
  intros a acc ctxt decs; revert ctxt; induction decs as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt;
    cbn [compile_decs].
  - reflexivity.
  - destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. cbn. specialize (IH ctxt). rewrite E in IH. exact IH.
  - destruct (compile_decs _ ds) as [ds' c'] eqn:E. cbn. specialize (IH (Build_context (pan_structs.structs ctxt)
      (pan_structs.locals ctxt) ((v0, sh) :: pan_structs.globals ctxt))). rewrite E in IH. exact IH.
  - destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. cbn. specialize (IH ctxt). rewrite E in IH. exact IH.
  - apply IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "decs_stcnames_to_get_names" *)
Theorem decs_stcnames_to_get_names : forall {a} acc (code : list (decl a)) res ctxt,
  decs_stcnames acc code = SOME res /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) acc ->
  get_names ctxt code = {| pan_structs.structs := MAP (fun '(nm, info) => (nm, fields info)) res;
                           pan_structs.locals := pan_structs.locals ctxt;
                           pan_structs.globals := pan_structs.globals ctxt |}.
Proof.
  intros a acc code; revert acc; induction code as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    intros acc res ctxt [H1 H2]; cbn [decs_stcnames get_names] in *.
  - injection H1 as <-. rewrite <- H2. apply context_eta.
  - exact (IH acc res ctxt (conj H1 H2)).
  - exact (IH acc res ctxt (conj H1 H2)).
  - exact (IH acc res ctxt (conj H1 H2)).
  - destruct (ALOOKUP acc nm); [discriminate|].
    destruct (ALL_DISTINCT (MAP fst flds)); [|discriminate].
    destruct (EVERY (is_wf_shape acc) (MAP snd flds)); [|discriminate].
    erewrite IH; [|split; [exact H1|cbn [pan_structs.structs MAP List.map]; rewrite H2; reflexivity]].
    cbn [pan_structs.locals pan_structs.globals pan_structs.structs].
    reflexivity.
Qed.

Lemma decs_stcnames_get_names_structs {a} acc (code : list (decl a)) res ctxt :
  decs_stcnames acc code = SOME res ->
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) acc ->
  pan_structs.structs (get_names ctxt code) = MAP (fun '(nm, info) => (nm, fields info)) res.
Proof. intros H1 H2. rewrite (decs_stcnames_to_get_names acc code res ctxt (conj H1 H2)). reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "decs_stcnames_infos_ok" *)
Theorem decs_stcnames_infos_ok : forall {a} acc (code : list (decl a)) res (ctxt : context),
  decs_stcnames acc code = SOME res /\ struct_infos_ok acc -> struct_infos_ok res.
Proof.
  intros a acc code; revert acc; induction code as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    intros acc res ctxt [H1 H2]; cbn [decs_stcnames] in H1.
  - injection H1 as <-. exact H2.
  - exact (IH acc res ctxt (conj H1 H2)).
  - exact (IH acc res ctxt (conj H1 H2)).
  - exact (IH acc res ctxt (conj H1 H2)).
  - destruct (ALOOKUP acc nm) eqn:Ea; [discriminate|].
    destruct (ALL_DISTINCT (MAP fst flds)) eqn:Ed; [|discriminate].
    destruct (EVERY (is_wf_shape acc) (MAP snd flds)) eqn:Ew; [|discriminate].
    eapply (IH _ res ctxt). split; [exact H1|].
    apply struct_infos_ok_cons. split; [exact H2|]. cbn [fields size].
    split; [exact Ed|split; [|split; [exact Ew|reflexivity]]].
    rewrite MEM_In_. intros Hin. apply ALOOKUP_None_iff in Ea. exact (Ea Hin).
Qed.

(** ** Observable semantics *)

Section Semantics.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

#[local] Instance behaviour_inhabited' : Inhabited behaviour := Fail.

(** Galette-only: two programs' clocked runs that agree up to [convert_res]
    and on the FFI state have the same observable semantics. *)
Lemma semantics_convert_res s t start :
  (forall k, fst (evaluate ((TailCall start [] : prog a), set_clock k t)) =
             convert_res (fst (evaluate ((TailCall start [] : prog a), set_clock k s))) /\
             ffi (snd (evaluate ((TailCall start [] : prog a), set_clock k t))) =
             ffi (snd (evaluate ((TailCall start [] : prog a), set_clock k s)))) ->
  semantics t start = semantics s start.
Proof.
  intros HF. unfold semantics. cbv zeta.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P1 with P2
  end.
  2: { apply propositional_extensionality. split; intros [k Hk]; exists k;
       rewrite (proj1 (HF k)) in *; destruct (fst (evaluate (_, set_clock k s))) as [[]|]; cbn in *; tauto. }
  destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q1 with Q2
  end.
  - destruct (some _); [reflexivity|]. f_equal. f_equal. f_equal.
    apply functional_extensionality; intros k. rewrite (proj2 (HF k)). reflexivity.
  - apply functional_extensionality; intros res; apply propositional_extensionality.
    split; intros (k & t' & r & out & H1 & H2 & H3); exists k.
    + destruct (HF k) as [Hf Hs]. rewrite H1 in Hf, Hs; cbn [fst snd] in Hf, Hs.
      exists (snd (evaluate (TailCall start [], set_clock k t))), (convert_res r), out.
      split; [rewrite <- Hf; destruct (evaluate (TailCall start [], set_clock k t)); reflexivity|].
      split; [destruct r as [[]|]; cbn in *; assumption|rewrite Hs; exact H3].
    + destruct (HF k) as [Hf Hs]. rewrite H1 in Hf, Hs; cbn [fst snd] in Hf, Hs.
      destruct (evaluate (TailCall start [], set_clock k s)) as [rs ts] eqn:Es. cbn [fst snd] in Hf, Hs.
      exists ts, rs, out. split; [reflexivity|].
      split; [subst r; destruct rs as [[]|]; cbn in *; assumption|rewrite <- Hs; exact H3].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "semantics_eq" *)
Theorem semantics_eq : forall s start ctxt,
  semantics s start <> Fail /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) /\
  locals s = FEMPTY /\
  FEVERY (fun '(nm, v0) => is_true (v_flds_ok (structs s) v0)) (globals s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) /\
  pan_structs.locals ctxt = [] /\
  alist_to_fmap (pan_structs.globals ctxt) = FMAP_MAP2 (shape_of ∘ SND) (globals s) /\
  struct_infos_ok (structs s) ->
  semantics (convert_s ctxt s) start = semantics s start.
Proof.
  intros s start ctxt (Hsem & Hst & Hl & Hf & Hw & Hcl & Hg & Hok).
  apply semantics_convert_res. intros k.
  destruct (evaluate (TailCall start [], set_clock k s)) as [r st] eqn:E.
  assert (Hr : r <> SOME Error).
  { intros ->. apply Hsem. unfold semantics. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
    exfalso; apply Hn. exists k. rewrite E. exact Logic.I. }
  destruct (compile_correct (TailCall start []) (set_clock k s) r st ctxt) as (T & _).
  { state_cbn. rewrite Hl. split; [exact E|split; [exact Hst|split; [apply FEVERY_FEMPTY|]]].
    split; [exact Hf|split; [apply FEVERY_FEMPTY|split; [exact Hw|split; [exact Hok|]]]].
    split; [rewrite Hcl, FMAP_MAP2_FEMPTY; apply fmap_ext; intros; reflexivity|split; [exact Hg|exact Hr]]. }
  cbn [compile compile_exps] in T. rewrite convert_s_set_clock in T. rewrite T. split; reflexivity.
Qed.

End Semantics.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_top_semantics_decls" *)
Theorem compile_top_semantics_decls : forall {a ffi_t} (s : state a ffi_t) start (code : list (decl a)),
  semantics_decls s start code <> Fail /\
  locals s = FEMPTY /\ panSem.code s = FEMPTY /\ globals s = FEMPTY ->
  semantics_decls s start code =
  semantics_decls
    (set_eshapes (FMAP_MAP2 (fun '(eid, sh) =>
       compile_shape (pan_structs.structs (get_names {| pan_structs.structs := []; pan_structs.locals := ARB;
                                                         pan_structs.globals := ARB |} code)) sh)
       (eshapes s)) s)
    start (compile_top code).
Proof.
  intros a ffi_t s start code (Hsem & Hl & Hc & Hg).
  unfold semantics_decls in *.
  destruct (decs_stcnames [] code) as [res|] eqn:Ed; [|contradiction].
  destruct (evaluate_decls (set_structs res s) code) as [s'|] eqn:Ev; [|contradiction].
  unfold compile_top. cbv zeta. rewrite decs_stcnames_compile_decs.
  set (nm_ctxt := get_names {| pan_structs.structs := []; pan_structs.locals := [];
                               pan_structs.globals := [] |} code).
  assert (Hnm : nm_ctxt = {| pan_structs.structs := MAP (fun '(nm, info) => (nm, fields info)) res;
                             pan_structs.locals := []; pan_structs.globals := [] |})
    by (apply (decs_stcnames_to_get_names [] code res); split; [exact Ed|reflexivity]).
  assert (Hok : struct_infos_ok res).
  { apply (decs_stcnames_infos_ok [] code res nm_ctxt). split; [exact Ed|].
    unfold struct_infos_ok; cbn. repeat split. intros i nm info [Hi _]. cbn in Hi; lia. }
  destruct (compile_decs nm_ctxt code) as [decs' ctxt'] eqn:Ec. cbn [FST fst].
  destruct (compile_decls_correct s' (set_structs res s) code nm_ctxt decs' ctxt') as [T (gb & Hc' & R)].
  { state_cbn. rewrite Hnm, Hg. cbn [pan_structs.structs pan_structs.locals pan_structs.globals].
    split; [exact Ev|split; [reflexivity|split; [reflexivity|split; [exact Hok|]]]].
    split; [apply FEVERY_FEMPTY|split; [apply FEVERY_FEMPTY|split; [|]]].
    - rewrite FMAP_MAP2_FEMPTY. apply fmap_ext; intros; reflexivity.
    - rewrite <- Hnm. exact Ec. }
  state_cbn. destruct R as (R1 & R2 & R3 & R4 & R5).
  replace (set_structs [] (set_eshapes _ s)) with (convert_s ctxt' (set_structs res s)).
  - rewrite T. symmetry.
    apply semantics_eq. rewrite R3, R4, Hc', Hnm. state_cbn. cbn [pan_structs.structs pan_structs.locals pan_structs.globals].
    split; [exact Hsem|split; [reflexivity|split; [exact Hl|split; [exact R1|]]]].
    split; [exact R2|split; [reflexivity|split; [exact R5|exact Hok]]].
  - pose proof (compile_decs_structs _ _ _ _ Ec) as Hs'. rewrite Hnm in Hs'. cbn in Hs'.
    assert (Hgn : pan_structs.structs (get_names {| pan_structs.structs := []; pan_structs.locals := ARB;
                    pan_structs.globals := ARB |} code) = MAP (fun '(nm, info) => (nm, fields info)) res)
      by (apply (decs_stcnames_get_names_structs [] code res); [exact Ed|reflexivity]).
    rewrite Hgn. unfold convert_s, set_structs, set_eshapes. state_cbn. rewrite Hl, Hg, Hc, Hs'.
    rewrite !FMAP_MAP2_FEMPTY. unfold convert_code. rewrite FMAP_MAP2_FEMPTY. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decs_no_names" *)
Theorem compile_decs_no_names : forall {a} ctxt (decs : list (decl a)),
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) (FST (compile_decs ctxt decs))).
Proof.
  intros a ctxt decs; revert ctxt; induction decs as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt;
    cbn [compile_decs].
  - reflexivity.
  - destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. specialize (IH ctxt). rewrite E in IH. exact IH.
  - destruct (compile_decs _ ds) as [ds' c'] eqn:E. specialize (IH (Build_context (pan_structs.structs ctxt)
      (pan_structs.locals ctxt) ((v0, sh) :: pan_structs.globals ctxt))). rewrite E in IH. exact IH.
  - destruct (compile_decs ctxt ds) as [ds' c'] eqn:E. specialize (IH ctxt). rewrite E in IH. exact IH.
  - apply IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_top_no_names" *)
Theorem compile_top_no_names : forall {a} (pan_code : list (decl a)),
  is_true (EVERY (fun d => is_function d || is_decl d || is_exn_decl d) (pan_structs.compile_top pan_code)).
Proof. intros a pan_code; unfold compile_top; apply compile_decs_no_names. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_n_no_name" *)
Theorem compile_shape_n_no_name : forall ctxt n sh, is_true (is_wf_shape_nil (compile_shape_n ctxt n sh)).
Proof. intros; rewrite compile_shape_n_eq. apply (proj1 (is_wf_shape_compile_shape [])). Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_shape_no_name" *)
Theorem compile_shape_no_name : forall ctxt sh, is_true (is_wf_shape_nil (compile_shape ctxt sh)).
Proof. intros ctxt sh; rewrite compile_shape_n_eq_rev; apply compile_shape_n_no_name. Qed.

(*! HOL "cakeml/pancake/proofs/pan_structsProofScript.sml" "size_of_shape_compile_pass_eq" *)
Theorem size_of_shape_compile_pass_eq : forall {a ffi_t} (s : state a ffi_t) shape str_ctxt,
  struct_infos_ok (structs s) /\
  is_true (is_wf_shape (structs s) shape) /\
  str_ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  size_of_shape (compile_shape str_ctxt shape) = size_of_sh_with_ctxt (structs s) shape.
Proof.
  intros a ffi_t s shape str_ctxt (H1 & H2 & ->).
  rewrite <- (size_of_sh_with_ctxt_eq _ [] (compile_shape_no_name _ _)).
  apply size_of_compile_shape. split; assumption.
Qed.
