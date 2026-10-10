(** * CakeML [word_allocProof]: applying a colouring

    Part of the port of
    [cakeml/compiler/backend/proofs/word_allocProofScript.sml] (HOL lines
    1-2270, "1. correctness theorem about colouring_ok"): [colouring_ok],
    [word_state_eq_rel], [strong_locals_rel], the lemmas on cutting and
    pushing environments, and [evaluate_apply_colour].

    Carrier notes:
    - HOL's free variables are quantified explicitly.  HOL
      [s with f := v] is [set_f v s]; HOL's [s.stack_size] is
      [state_stack_size s]; HOL [LLOOKUP lt n] is [oEL n lt].
    - HOL's [let (res,rst) = evaluate ... in if res = SOME Error then T
      else ...] is a [let '(res, rst)] pattern with
      [if bool_decide (res = SOME Error) then True else ...].
    - HOL's [sorting$PERM] is not ported: [list_rearrange_perm] is stated
      with Rocq's [Permutation] and is untagged (as [PERM_list_rearrange]
      in [wordProps.consts]).
    - Not ported: [LET_FORALL_ELIM'] (a rewrite on HOL's [LET] constant,
      proof automation) and the commented-out [stack_size_map_excp_const].
    - Proofs are by structural induction on programs ([prog_nested_ind])
      instead of HOL's complete induction on [prog_size]; the [Loop] case
      is [evaluate_apply_colour_Loop_helper] (induction on the clock, as in
      HOL).  The Galette-only helpers have no tag. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set extra.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang wordLang word_alloc.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import
  consts consts_with clock dec_clock locals_rel permute_swap stack_swap code.
From Stdlib Require Import Permutation.
From Stdlib Require FinFun.
Open Scope N_scope.

(** ** Galette-only list and set helpers *)

(** Decidable equality on wordLang expressions, classically (HOL
    equality); HOL's [MEM] on expression lists needs it. *)
#[export] Instance wexp_eq_dec_classical {a : N} : EqDecision (wordLang.exp a) :=
  fun x y => classical_dec (x = y).

Lemma bd_true' (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. apply bool_decide_spec. Qed.
Lemma bd_false' (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros HP; destruct (bool_decide P) eqn:E; [|reflexivity]. apply bool_decide_spec in E; tauto. Qed.

Lemma decide_True' {P : Prop} `{Decision P} {B} (x y : B) : P -> (if decide P then x else y) = x.
Proof. intros HP; destruct (decide P); [reflexivity|contradiction]. Qed.
Lemma decide_False' {P : Prop} `{Decision P} {B} (x y : B) : ~ P -> (if decide P then x else y) = y.
Proof. intros HP; destruct (decide P); [contradiction|reflexivity]. Qed.

Lemma IN_domain_iff {A} (t : spt A) k : k IN domain t <-> exists v, lookup k t = Some v.
Proof. apply domain_lookup. Qed.

Lemma MEM_iff' {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. unfold is_true; apply MEM_In. Qed.

Lemma IN_set {A} (x : A) l : x IN set l <-> In x l.
Proof.
  induction l as [|y l IH]; cbn; unfold pred_set.IN in *; cbn; [tauto|].
  rewrite <- IH. split; intros [H|H]; auto.
Qed.

Lemma ZIP_combine' {A B} (xs : list A) (ys : list B) : ZIP (xs, ys) = combine xs ys.
Proof. revert ys; induction xs as [|x xs IH]; intros [|y ys]; try reflexivity; cbn [combine]; rewrite <- IH; reflexivity. Qed.

Lemma map_fst_combine {A B} (l : list A) (l' : list B) :
  length l = length l' -> List.map fst (combine l l') = l.
Proof. revert l'; induction l as [|x l IH]; intros [|y l'] H; cbn in *; try lia; [reflexivity|]. f_equal; apply IH; lia. Qed.

Lemma map_snd_combine {A B} (l : list A) (l' : list B) :
  length l = length l' -> List.map snd (combine l l') = l'.
Proof. revert l'; induction l as [|x l IH]; intros [|y l'] H; cbn in *; try lia; [reflexivity|]. f_equal; apply IH; lia. Qed.

Lemma LENGTH_MAP' {A B} (f : A -> B) l : LENGTH (MAP f l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_map; reflexivity. Qed.

Lemma ALL_DISTINCT_iff' {A} `{EqDecision A} (l : list A) : is_true (ALL_DISTINCT l) <-> NoDup l.
Proof. unfold is_true; apply ALL_DISTINCT_NoDup. Qed.

Lemma NoDup_map_inj {A B} (f : A -> B) l :
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (List.map f l).
Proof.
  intros Hd Hi; apply NoDup_map_NoDup_ForallPairs; [|exact Hd].
  intros x y Hx Hy; apply Hi; assumption.
Qed.

Section Helpers.
Context {A : Type}.

Lemma INJ_less (f : N -> A) s s' : INJ f s' UNIV /\ s SUBSET s' -> INJ f s UNIV.
Proof.
  intros [[H1 H2] Hs]; split; [intros; exact Logic.I|].
  intros x y [Hx Hy] E; apply H2; [split; apply Hs; assumption|exact E].
Qed.

Lemma INJ_neq (f : N -> A) s x y : INJ f s UNIV -> x IN s -> y IN s -> x <> y -> f x <> f y.
Proof. intros [_ H] Hx Hy Hn E; apply Hn, H; [split; assumption|exact E]. Qed.

End Helpers.

Section Defs.
Context {a : N}.

(** ** Set lemmas (HOL lines 27-98) *)

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "SUBSET_OF_INSERT" *)
Theorem SUBSET_OF_INSERT : forall {A} (s : A -> Prop) x, s SUBSET x INSERT s.
Proof. intros A s x y Hy; right; exact Hy. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_UNION" *)
Theorem INJ_UNION : forall {B} (f : N -> B) A0 B0,
  INJ f (A0 UNION B0) UNIV -> INJ f A0 UNIV /\ INJ f B0 UNIV.
Proof.
  intros B f A0 B0 H; split; apply (INJ_less f _ (A0 UNION B0)); split; auto;
    intros x Hx; [left|right]; exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_less" *)
Theorem INJ_less_thm : forall {B} (f : N -> B) s s',
  INJ f s' UNIV /\ s SUBSET s' -> INJ f s UNIV.
Proof. intros B f s s'; apply INJ_less. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "hide_def" *)
Definition hide {A} (x : A) : A := x.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_IMP_IMAGE_DIFF" *)
Theorem INJ_IMP_IMAGE_DIFF : forall {B} (f : N -> B) s t,
  INJ f (s UNION t) UNIV -> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t.
Proof.
  intros B f s t [_ H]; apply set_ext; intros y; unfold pred_set.IMAGE, pred_set.DIFF, pred_set.IN; split.
  - intros [x [-> [Hs Ht]]]; split; [exists x; auto|].
    intros [x' [E Ht']]; apply Ht. replace x with x'; [exact Ht'|].
    apply H; [split; [right|left]; assumption|symmetry; exact E].
  - intros [[x [-> Hs]] Hn]; exists x; split; [reflexivity|split; [exact Hs|]].
    intros Ht; apply Hn; exists x; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_IMP_IMAGE_DIFF_single" *)
Theorem INJ_IMP_IMAGE_DIFF_single : forall {B} (f : N -> B) s n,
  INJ f (s UNION (n INSERT {})) UNIV -> IMAGE f s DIFF (f n INSERT {}) = IMAGE f (s DIFF (n INSERT {})).
Proof.
  intros B f s n H. rewrite (INJ_IMP_IMAGE_DIFF f s _ H). f_equal.
  apply set_ext; intros y; unfold pred_set.IMAGE, pred_set.INSERT, pred_set.EMPTY, pred_set.IN; split.
  - intros [->|[]]; exists n; auto.
  - intros [x [-> [->|[]]]]; left; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_ALL_DISTINCT_MAP" *)
Theorem INJ_ALL_DISTINCT_MAP : forall {B} `{EqDecision B} (f : N -> B) ls,
  ALL_DISTINCT (MAP f ls) -> INJ f (set ls) UNIV.
Proof.
  intros B EB f ls H; rewrite ALL_DISTINCT_iff' in H; split; [intros; exact Logic.I|].
  intros x y [Hx Hy] E; rewrite IN_set in Hx, Hy.
  induction ls as [|z ls IH]; [destruct Hx|]. cbn in H; inversion H as [|? ? Hz Hd]; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
  - exfalso; apply Hz; rewrite E; apply in_map, Hy.
  - exfalso; apply Hz; rewrite <- E; apply in_map, Hx.
Qed.

End Defs.

(** ** [colouring_ok] *)

Section Colouring.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "colouring_ok_def" *)
Fixpoint colouring_ok (f : N -> N) (p : prog a) (live : num_set)
    (lt : list (num_set * num_set)) {struct p} : Prop :=
  match p with
  | Seq s1 s2 =>
      let s2_live := get_live s2 live lt in
      let s1_live := get_live s1 s2_live lt in
      INJ f (domain s1_live) UNIV /\
      colouring_ok f s2 live lt /\ colouring_ok f s1 s2_live lt
  | If cmp r1 ri e2 e3 =>
      let e2_live := get_live e2 live lt in
      let e3_live := get_live e3 live lt in
      let union_live := union e2_live e3_live in
      let merged := match ri with
                    | Reg r2 => insert r2 tt (insert r1 tt union_live)
                    | _ => insert r1 tt union_live
                    end in
      INJ f (domain merged) UNIV /\
      colouring_ok f e2 live lt /\ colouring_ok f e3 live lt
  | Call (Some (v, (cutset, (ret_handler, (l1, l2))))) dest args h =>
      let args_set := numset_list_insert args LN in
      let all_names := union (SND cutset) (FST cutset) in
      INJ f (domain (union all_names args_set)) UNIV /\
      INJ f (domain (numset_list_insert v all_names)) UNIV /\
      colouring_ok f ret_handler live lt /\
      match h with
      | None => True
      | Some (v, (prog, (l1, l2))) =>
          INJ f (domain (insert v tt all_names)) UNIV /\ colouring_ok f prog live lt
      end
  | MustTerminate p => colouring_ok f p live lt
  | Loop names body exit_names =>
      INJ f (domain names) UNIV /\ INJ f (domain exit_names) UNIV /\
      colouring_ok f body names ((names, exit_names) :: lt)
  | prog =>
      let lset := get_live prog live lt in
      let iset := union (get_writes prog) live in
      INJ f (domain lset) UNIV /\ INJ f (domain iset) UNIV
  end.

End Colouring.

(** ** State relations *)

Section Rel.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** Equivalence on everything except the permutation and the locals. *)
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "word_state_eq_rel_def" *)
Definition word_state_eq_rel (s t : state) : Prop :=
  fp_regs t = fp_regs s /\
  store t = store s /\
  locals_size t = locals_size s /\
  stack t = stack s /\
  stack_limit t = stack_limit s /\
  stack_max t = stack_max s /\
  state_stack_size t = state_stack_size s /\
  memory t = memory s /\
  mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\
  gc_fun t = gc_fun s /\
  handler t = handler s /\
  clock t = clock s /\
  code t = code s /\
  ffi t = ffi s /\
  be t = be s /\
  termdep t = termdep s /\
  compile t = compile s /\
  compile_oracle t = compile_oracle s /\
  code_buffer t = code_buffer s /\
  data_buffer t = data_buffer s.

(** [t] differs from [s] in its locals and permutation only
    (Galette-only). *)
Lemma word_state_eq_rel_iff (s t : state) :
  word_state_eq_rel s t <-> t = set_permute (permute t) (set_locals (locals t) s).
Proof.
  split.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16
            & H17 & H18 & H19 & H20 & H21).
    destruct t, s; cbn in *; subst; reflexivity.
  - intros ->; destruct s; cbn; repeat split.
Qed.

Lemma word_state_eq_rel_refl (s : state) : word_state_eq_rel s s.
Proof. repeat split. Qed.

Lemma word_state_eq_rel_sym (s t : state) : word_state_eq_rel s t -> word_state_eq_rel t s.
Proof. unfold word_state_eq_rel; intros; destr_conj; repeat split; congruence. Qed.

Lemma word_state_eq_rel_trans (s t u : state) :
  word_state_eq_rel s t -> word_state_eq_rel t u -> word_state_eq_rel s u.
Proof. unfold word_state_eq_rel; intros; destr_conj; repeat split; congruence. Qed.

Lemma word_state_eq_rel_locals (s t : state) l l' :
  word_state_eq_rel s t -> word_state_eq_rel (set_locals l s) (set_locals l' t).
Proof. unfold word_state_eq_rel; cbn; intros; destr_conj; repeat split; congruence. Qed.

Lemma word_state_eq_rel_permute (s t : state) p p' :
  word_state_eq_rel s t -> word_state_eq_rel (set_permute p s) (set_permute p' t).
Proof. unfold word_state_eq_rel; cbn; intros; destr_conj; repeat split; congruence. Qed.

(** [tlocs] is a supermap of [slocs] under [f] for everything in [ls]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_def" *)
Definition strong_locals_rel {A} (f : N -> N) (ls : N -> Prop) (slocs tlocs : num_map A) : Prop :=
  forall n v, n IN ls /\ lookup n slocs = SOME v -> lookup (f n) tlocs = SOME v.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_subset_domain" *)
Theorem strong_locals_rel_subset_domain : forall {A} f s (l1 l2 : num_map A),
  strong_locals_rel f s l1 l2 /\ s SUBSET domain l1 ->
  forall v, v IN s -> f v IN domain l2.
Proof.
  intros A f s l1 l2 [H Hs] v Hv. pose proof (Hs v Hv) as Hd. apply IN_domain_iff in Hd as [x Hx].
  apply IN_domain_iff; exists x; apply H; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_numset_list_insert" *)
Theorem domain_numset_list_insert : forall ls locs,
  domain (numset_list_insert ls locs) = domain locs UNION set ls.
Proof.
  induction ls as [|x ls IH]; intros locs; apply set_ext; intros y; cbn [numset_list_insert].
  - unfold pred_set.UNION, pred_set.IN; cbn; tauto.
  - rewrite domain_insert. change (domain (numset_list_insert ls locs) y) with (y IN domain (numset_list_insert ls locs)).
    rewrite IH. unfold pred_set.UNION, pred_set.IN; cbn. fold (pred_set.IN y (set ls)). unfold pred_set.IN. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_get_var" *)
Theorem strong_locals_rel_get_var : forall f live (st cst : state) n x,
  strong_locals_rel f live (locals st) (locals cst) /\ n IN live /\ get_var n st = SOME x ->
  get_var (f n) cst = SOME x.
Proof. intros f live st cst n x (H & Hn & Hg); apply H; split; assumption. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_get_var_imm" *)
Theorem strong_locals_rel_get_var_imm : forall f live (st cst : state) (n : reg_imm a) x,
  strong_locals_rel f live (locals st) (locals cst) /\
  match n with Reg n => n IN live | _ => True end /\
  get_var_imm n st = SOME x ->
  get_var_imm (apply_colour_imm f n) cst = SOME x.
Proof.
  intros f live st cst [n|w] x (H & Hn & Hg); cbn in *; [|exact Hg].
  apply (strong_locals_rel_get_var f live st cst); auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_get_vars" *)
Theorem strong_locals_rel_get_vars : forall ls y f live (st cst : state),
  strong_locals_rel f live (locals st) (locals cst) /\
  (forall x, MEM x ls -> x IN live) /\
  get_vars ls st = SOME y ->
  get_vars (MAP f ls) cst = SOME y.
Proof.
  induction ls as [|x ls IH]; intros y f live st cst (H & Hm & Hg); cbn in *; [exact Hg|].
  destruct (get_var x st) as [v|] eqn:Ex; [|discriminate].
  destruct (get_vars ls st) as [vs|] eqn:Exs; [|discriminate]. injection Hg as <-.
  rewrite (strong_locals_rel_get_var f live st cst x v) by
    (repeat split; auto; apply Hm; unfold is_true; cbn; rewrite bd_true'; reflexivity).
  rewrite (IH vs f live st cst); [reflexivity|]. repeat split; auto.
  intros z Hz; apply Hm; unfold is_true in *; cbn; rewrite Hz, orb_true_r; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_UNION" *)
Theorem strong_locals_rel_UNION : forall {B} f A0 B0 (t l : num_map B),
  strong_locals_rel f (A0 UNION B0) t l <-> strong_locals_rel f A0 t l /\ strong_locals_rel f B0 t l.
Proof.
  intros B f A0 B0 t l; unfold strong_locals_rel, pred_set.UNION, pred_set.IN; split.
  - intros H; split; intros n v [Hn Hl]; apply H; auto.
  - intros [H1 H2] n v [[Hn|Hn] Hl]; [apply H1|apply H2]; auto.
Qed.

End Rel.

Section Lemmas.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_big_union_subset" *)
Theorem domain_big_union_subset : forall (ls : list (exp a)) a0,
  MEM a0 ls -> domain (get_live_exp a0) SUBSET domain (big_union (MAP get_live_exp ls)).
Proof.
  induction ls as [|e ls IH]; intros a0 Hm; [discriminate Hm|].
  unfold big_union in *; cbn [MAP List.map FOLDR]. rewrite domain_union.
  cbn [MEM] in Hm; unfold is_true in Hm; apply orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm; subst. intros x Hx; left; exact Hx.
  - intros x Hx; right; apply (IH a0 Hm), Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "apply_nummap_key_domain" *)
Theorem apply_nummap_key_domain : forall {A} f (names : num_map A),
  domain (apply_nummap_key f names) = IMAGE f (domain names).
Proof.
  intros A f names; unfold apply_nummap_key. rewrite domain_fromAList.
  apply set_ext; intros x; unfold pred_set.IMAGE, pred_set.IN. rewrite MEM_iff', List.map_map, in_map_iff.
  split.
  - intros [[k v] [<- Hin]]. exists k; split; [reflexivity|].
    apply IN_domain_iff; exists v. apply ALOOKUP_toAList_In. exact Hin.
  - intros [k [-> Hk]]. apply IN_domain_iff in Hk as [v Hv]. exists (k, v); split; [reflexivity|].
    apply ALOOKUP_toAList_In; exact Hv.
Qed.

End Lemmas.

(** ** Cutting environments *)

Section Cut.

Lemma lookup_apply_nummap_key_some {A} f (names : num_map A) n v :
  lookup n names = Some v -> exists v', lookup (f n) (apply_nummap_key f names) = Some v'.
Proof.
  intros H. apply IN_domain_iff. rewrite apply_nummap_key_domain.
  exists n; split; [reflexivity|apply IN_domain_iff; eauto].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_names_lemma" *)
Theorem cut_names_lemma : forall {A} (names : num_set) (sloc tloc x : num_map A) f,
  INJ f (domain names) UNIV /\
  cut_names names sloc = SOME x /\
  strong_locals_rel f (domain names) sloc tloc ->
  exists y,
    cut_names (apply_nummap_key f names) tloc = SOME y /\
    domain y = IMAGE f (domain x) /\
    strong_locals_rel f (domain names) x y /\
    INJ f (domain x) UNIV /\
    domain x = domain names.
Proof.
  intros A names sloc tloc x f (Hi & Hc & Hs). unfold cut_names in *.
  destruct (classical_dec (domain names SUBSET domain sloc)) as [Hsub|]; [|discriminate].
  injection Hc as <-.
  assert (Hdx : domain (inter sloc names) = domain names).
  { rewrite domain_inter; apply set_ext; intros n; split; [tauto|intros Hn; split; [apply Hsub, Hn|exact Hn]]. }
  assert (Hsub' : domain (apply_nummap_key f names) SUBSET domain tloc).
  { rewrite apply_nummap_key_domain. intros m [n [-> Hn]].
    apply (strong_locals_rel_subset_domain f (domain names) sloc tloc); [split; assumption|exact Hn]. }
  destruct (classical_dec _) as [_|Hn]; [|contradiction].
  eexists; split; [reflexivity|]. rewrite Hdx. split; [|split; [|split; [exact Hi|reflexivity]]].
  - rewrite domain_inter, apply_nummap_key_domain. apply set_ext; intros m; split; [tauto|].
    intros Hm; split; [apply Hsub'; rewrite apply_nummap_key_domain; exact Hm|exact Hm].
  - intros n v [Hn Hl]. rewrite lookup_inter in Hl |- *.
    destruct (lookup n sloc) as [v'|] eqn:El; [|discriminate].
    destruct (lookup n names) as [u|] eqn:En; [|discriminate]. injection Hl as <-.
    rewrite (Hs n v' (conj Hn El)).
    destruct (lookup_apply_nummap_key_some f names n u En) as [w ->]. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_envs_lemma" *)
Theorem cut_envs_lemma : forall {A} f (n1 n2 : num_set) (sloc tloc x1 x2 : num_map A),
  INJ f (domain n1) UNIV /\
  INJ f (domain n2) UNIV /\
  cut_envs (n1, n2) sloc = SOME (x1, x2) /\
  strong_locals_rel f (domain n1) sloc tloc /\
  strong_locals_rel f (domain n2) sloc tloc ->
  exists y1 y2,
    cut_envs (apply_nummaps_key f (n1, n2)) tloc = SOME (y1, y2) /\
    domain y1 = IMAGE f (domain n1) /\
    domain y2 = IMAGE f (domain n2) /\
    strong_locals_rel f (domain n1) x1 y1 /\
    strong_locals_rel f (domain n2) x2 y2 /\
    INJ f (domain x1) UNIV /\
    INJ f (domain x2) UNIV /\
    domain x1 = domain n1 /\
    domain x2 = domain n2.
Proof.
  intros A f n1 n2 sloc tloc x1 x2 (Hi1 & Hi2 & Hc & Hs1 & Hs2). unfold cut_envs in Hc; cbn [FST SND fst snd] in Hc.
  destruct (cut_names n1 sloc) as [e1|] eqn:E1; [|discriminate].
  destruct (cut_names n2 sloc) as [e2|] eqn:E2; [|discriminate]. injection Hc as <- <-.
  destruct (cut_names_lemma n1 sloc tloc e1 f (conj Hi1 (conj E1 Hs1))) as (y1 & F1 & D1 & S1 & I1 & X1).
  destruct (cut_names_lemma n2 sloc tloc e2 f (conj Hi2 (conj E2 Hs2))) as (y2 & F2 & D2 & S2 & I2 & X2).
  exists y1, y2. unfold cut_envs, apply_nummaps_key; cbn [FST SND fst snd].
  fold (apply_nummap_key f n1). fold (apply_nummap_key f n2). rewrite F1, F2.
  rewrite X1 in D1, I1. rewrite X2 in D2, I2. rewrite X1, X2.
  exact (conj eq_refl (conj D1 (conj D2 (conj S1 (conj S2 (conj I1 (conj I2 (conj eq_refl eq_refl)))))))).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_env_lemma" *)
Theorem cut_env_lemma : forall {A} f (names : cutsets) (sloc tloc x : num_map A),
  INJ f (domain (FST names) UNION domain (SND names)) UNIV /\
  cut_env names sloc = SOME x /\
  strong_locals_rel f (domain (FST names) UNION domain (SND names)) sloc tloc ->
  exists y,
    cut_env (apply_nummaps_key f names) tloc = SOME y /\
    domain y = IMAGE f (domain x) /\
    strong_locals_rel f (domain (FST names) UNION domain (SND names)) x y /\
    INJ f (domain x) UNIV /\
    domain x = domain (FST names) UNION domain (SND names).
Proof.
  intros A f [n1 n2] sloc tloc x (Hi & Hc & Hs); cbn [FST SND fst snd] in *.
  unfold cut_env in Hc. destruct (cut_envs (n1, n2) sloc) as [[x1 x2]|] eqn:Ec; [|discriminate].
  injection Hc as <-.
  apply INJ_UNION in Hi as Hi'. destruct Hi' as [Hi1 Hi2].
  apply strong_locals_rel_UNION in Hs as Hs'. destruct Hs' as [Hs1 Hs2].
  destruct (cut_envs_lemma f n1 n2 sloc tloc x1 x2 (conj Hi1 (conj Hi2 (conj Ec (conj Hs1 Hs2)))))
    as (y1 & y2 & F & D1 & D2 & S1 & S2 & I1 & I2 & X1 & X2).
  exists (union y2 y1). unfold cut_env. rewrite F.
  assert (Dx : domain (union x2 x1) = domain n1 UNION domain n2).
  { rewrite domain_union, X1, X2. apply set_ext; intros n; unfold pred_set.UNION, pred_set.IN; tauto. }
  rewrite Dx. split; [reflexivity|]. split; [|split; [|split; [exact Hi|reflexivity]]].
  - rewrite domain_union, D1, D2. apply set_ext; intros m; unfold pred_set.IMAGE, pred_set.UNION, pred_set.IN; split.
    + intros [[n [-> Hn]]|[n [-> Hn]]]; exists n; auto.
    + intros [n [-> [Hn|Hn]]]; [right|left]; exists n; auto.
  - intros n v [Hn Hl]. rewrite lookup_union in Hl |- *.
    destruct (lookup n x2) as [v2|] eqn:L2.
    + injection Hl as <-. rewrite (S2 n v2); [reflexivity|split; [|exact L2]].
      rewrite <- X2; apply IN_domain_iff; eauto.
    + assert (Hn1 : n IN domain n1).
      { rewrite <- X1; apply IN_domain_iff; eauto. }
      assert (Hn2 : ~ n IN domain n2).
      { rewrite <- X2; intros H; apply IN_domain_iff in H as [w Hw]; congruence. }
      destruct (lookup (f n) y2) as [w|] eqn:Ly2.
      * exfalso. assert (Hf : f n IN domain y2) by (apply IN_domain_iff; eauto).
        rewrite D2 in Hf. destruct Hf as [m [Em Hm]].
        apply Hn2. replace n with m; [exact Hm|].
        destruct Hi as [_ Hinj]. apply Hinj; [split; [right; exact Hm|left; exact Hn1]|symmetry; exact Em].
      * apply (S1 n v); split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "nummaps_to_nummap" *)
Theorem nummaps_to_nummap : forall {A B} f (a0 : num_map A * num_map B),
  FST (apply_nummaps_key f a0) = apply_nummap_key f (FST a0) /\
  SND (apply_nummaps_key f a0) = apply_nummap_key f (SND a0).
Proof. intros; split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "INJ_union" *)
Theorem INJ_union : forall {A B} (f : A -> B) A0 B0 C,
  INJ f (A0 UNION B0) C -> INJ f A0 C /\ INJ f B0 C.
Proof.
  intros A B f A0 B0 C [H1 H2]; split; split.
  - intros x Hx; apply H1; left; exact Hx.
  - intros x y [Hx Hy]; apply H2; split; left; assumption.
  - intros x Hx; apply H1; right; exact Hx.
  - intros x y [Hx Hy]; apply H2; split; right; assumption.
Qed.

End Cut.

(** ** Rearranging lists *)

Section Rearrange.

Lemma list_rearrange_cases' {A} `{Inhabited A} (f : N -> N) (ls : list A) :
  (BIJ f (count (LENGTH ls)) (count (LENGTH ls)) /\
   list_rearrange f ls = GENLIST (fun i => EL (f i) ls) (LENGTH ls)) \/
  (~ BIJ f (count (LENGTH ls)) (count (LENGTH ls)) /\ list_rearrange f ls = ls).
Proof.
  unfold list_rearrange; destruct (classical_dec _) as [Hb|Hb]; [left|right]; auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "LENGTH_list_rerrange" *)
Theorem LENGTH_list_rerrange : forall {A} `{Inhabited A} mover (xs : list A),
  LENGTH (list_rearrange mover xs) = LENGTH xs.
Proof.
  intros A IA mover xs. destruct (list_rearrange_cases' mover xs) as [[_ ->]|[_ ->]]; [|reflexivity].
  rewrite LENGTH_length, GENLIST_length, LENGTH_length; lia.
Qed.

(** HOL's [list_rearrange_perm], with Rocq's [Permutation] for HOL's
    [PERM]: for any two lists that are permutations of each other there is
    a rearranger mapping one to the other. *)
Theorem list_rearrange_perm : forall {A} `{Inhabited A} (xs ys : list A),
  Permutation xs ys -> exists perm, list_rearrange perm xs = ys.
Proof.
  intros A IA xs ys HP.
  apply Permutation_nth_error in HP as [Hlen [g [Hg Hn]]].
  set (n := length xs).
  assert (Hb : forall i, (i < n)%nat -> (g i < n)%nat).
  { intros i Hi. destruct (nth_error ys i) as [y|] eqn:E.
    - rewrite Hn in E. apply nth_error_Some. congruence.
    - apply nth_error_None in E. lia. }
  assert (Hbi : FinFun.bInjective n g) by (intros i j _ _ E; apply Hg, E).
  assert (Hbs : FinFun.bSurjective n g) by (apply FinFun.bInjective_bSurjective; assumption).
  exists (fun i => N.of_nat (g (N.to_nat i))).
  destruct (list_rearrange_cases' (fun i => N.of_nat (g (N.to_nat i))) xs) as [[_ ->]|[Hn' _]].
  - apply nth_ext with (d := ARB) (d' := ARB).
    + rewrite GENLIST_length, LENGTH_length; lia.
    + intros i Hi. rewrite GENLIST_length, LENGTH_length, Nat2N.id in Hi.
      rewrite GENLIST_nth by (rewrite LENGTH_length; lia). rewrite Nat2N.id.
      specialize (Hb i) as Hbi'. unfold n in Hbi'.
      rewrite EL_nth by (rewrite LENGTH_length; lia).
      rewrite Nat2N.id.
      assert (E1 : nth_error ys i = Some (nth i ys ARB)) by (apply nth_error_nth'; lia).
      assert (E2 : nth_error xs (g i) = Some (nth (g i) xs ARB)) by (apply nth_error_nth'; specialize (Hb i); lia).
      rewrite Hn in E1. rewrite E1 in E2. injection E2 as E2. symmetry; exact E2.
  - exfalso; apply Hn'. unfold BIJ, INJ, SURJ, count, pred_set.IN; rewrite LENGTH_length.
    split; split.
    + intros i Hi. specialize (Hb (N.to_nat i)). lia.
    + intros i j [Hi Hj] E. apply Nat2N.inj in E. apply Hbi in E; lia.
    + intros i Hi. specialize (Hb (N.to_nat i)). lia.
    + intros j Hj. destruct (Hbs (N.to_nat j)) as [i [Hi Ei]]; [lia|].
      exists (N.of_nat i). rewrite Nat2N.id, Ei. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "GENLIST_MAP" *)
Theorem GENLIST_MAP : forall {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) (l : list A) m k,
  (forall i, i < LENGTH l -> m i < LENGTH l) /\ k <= LENGTH l ->
  GENLIST (fun i => EL (m i) (MAP f l)) k = MAP f (GENLIST (fun i => EL (m i) l) k).
Proof.
  intros A B IA IB f l m k [Hm Hk].
  apply nth_ext with (d := ARB) (d' := ARB).
  - rewrite length_map, !GENLIST_length; reflexivity.
  - intros i Hi. rewrite GENLIST_length in Hi.
    rewrite GENLIST_nth by lia.
    rewrite (nth_indep (MAP f (GENLIST (fun i0 => EL (m i0) l) k)) ARB (f ARB))
      by (rewrite length_map, GENLIST_length; lia).
    rewrite map_nth, GENLIST_nth by lia.
    assert (Hmi : m (N.of_nat i) < LENGTH l) by (apply Hm; lia).
    rewrite !EL_nth by (rewrite ?LENGTH_MAP'; exact Hmi).
    rewrite LENGTH_length in Hmi. rewrite nth_indep with (d' := f ARB) by (rewrite length_map; lia).
    apply map_nth.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_MAP" *)
Theorem list_rearrange_MAP : forall {A B} `{Inhabited A} `{Inhabited B} (l : list A) (f : A -> B) m,
  list_rearrange m (MAP f l) = MAP f (list_rearrange m l).
Proof.
  intros A B IA IB l f m. unfold list_rearrange. rewrite LENGTH_MAP'.
  destruct (classical_dec _) as [[[Hm _] _]|]; [|reflexivity].
  apply GENLIST_MAP. split; [|lia]. intros i Hi; apply Hm, Hi.
Qed.

End Rearrange.

(** ** Pushing environments *)

Section Push.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma In_sort_toAList (x : num_map (word_loc a)) k v :
  In (k, v) (sort key_val_compare (toAList x)) <-> lookup k x = Some v.
Proof.
  split; intros H.
  - apply ALOOKUP_toAList_In. eapply Permutation_in; [symmetry; apply sort_Permutation|exact H].
  - eapply Permutation_in; [apply sort_Permutation|]. apply ALOOKUP_toAList_In, H.
Qed.

Lemma NoDup_FST_sort_toAList (x : num_map (word_loc a)) :
  NoDup (MAP fst (sort key_val_compare (toAList x))).
Proof.
  pose proof (ALL_DISTINCT_MAP_FST_toAList x) as Hd; rewrite ALL_DISTINCT_iff' in Hd.
  eapply Permutation_NoDup; [apply Permutation_map, sort_Permutation|exact Hd].
Qed.

Lemma ALL_DISTINCT_sort_toAList (x : num_map (word_loc a)) :
  ALL_DISTINCT (sort key_val_compare (toAList x)).
Proof. apply ALL_DISTINCT_iff', (NoDup_map_inv fst), NoDup_FST_sort_toAList. Qed.

(** The keys of the rearranged, sorted [toAList x] are [domain x]. *)
Lemma In_list_rearrange_sort (x : num_map (word_loc a)) p k v :
  In (k, v) (list_rearrange p (sort key_val_compare (toAList x))) <-> lookup k x = Some v.
Proof.
  rewrite <- In_sort_toAList. split; apply Permutation_in;
    [symmetry|]; apply PERM_list_rearrange, ALL_DISTINCT_sort_toAList.
Qed.

Lemma NoDup_FST_list_rearrange_sort (x : num_map (word_loc a)) p :
  NoDup (MAP fst (list_rearrange p (sort key_val_compare (toAList x)))).
Proof.
  eapply Permutation_NoDup; [apply Permutation_map, PERM_list_rearrange, ALL_DISTINCT_sort_toAList|].
  apply NoDup_FST_sort_toAList.
Qed.

(** For any target final permutation, we can push locals that match
    exactly under [f] using some initial permutation. *)
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "env_to_list_perm" *)
Theorem env_to_list_perm : forall (y x : num_map (word_loc a)) f perm tperm,
  domain y = IMAGE f (domain x) /\
  INJ f (domain x) UNIV /\
  strong_locals_rel f (domain x) x y ->
  let '(l, permute) := env_to_list y perm in
  exists perm',
    let '(l', permute') := env_to_list x perm' in
    permute' = tperm /\ MAP (fun '(x, y) => (f x, y)) l' = l.
Proof.
  intros y x f perm tperm (Hd & Hi & Hs). unfold env_to_list. cbv zeta.
  set (xls := sort key_val_compare (toAList x)).
  set (yls := sort key_val_compare (toAList y)).
  set (g := fun '(x0, y0) => (f x0, y0) : N * word_loc a).
  assert (HP1 : Permutation (MAP g xls) yls).
  { apply NoDup_Permutation.
    - apply (NoDup_map_inv fst). replace (MAP fst (MAP g xls)) with (MAP f (MAP fst xls))
        by (rewrite !List.map_map; apply map_ext; intros [? ?]; reflexivity).
      apply NoDup_map_inj; [apply NoDup_FST_sort_toAList|].
      intros k1 k2 H1 H2 E. destruct Hi as [_ Hinj]. apply Hinj; [|exact E].
      apply in_map_iff in H1 as [[k1' v1] [<- H1]], H2 as [[k2' v2] [<- H2]].
      apply In_sort_toAList in H1, H2. cbn. split; apply IN_domain_iff; eauto.
    - apply (NoDup_map_inv fst), NoDup_FST_sort_toAList.
    - intros [k v]; split.
      + intros Hin. apply in_map_iff in Hin as [[k0 v0] [E Hin]]. cbn in E. injection E as <- <-.
        apply In_sort_toAList in Hin. apply In_sort_toAList. apply Hs. split; [|exact Hin].
        apply IN_domain_iff; eauto.
      + intros Hin. apply In_sort_toAList in Hin.
        assert (Hk : k IN domain y) by (apply IN_domain_iff; eauto).
        rewrite Hd in Hk. destruct Hk as [k0 [-> Hk0]]. apply IN_domain_iff in Hk0 as [v0 Hv0].
        pose proof (Hs k0 v0 (conj (proj2 (IN_domain_iff _ _) (ex_intro _ v0 Hv0)) Hv0)) as E.
        rewrite Hin in E. injection E as <-.
        apply in_map_iff. exists (k0, v); split; [reflexivity|]. apply In_sort_toAList, Hv0. }
  assert (HP2 : Permutation yls (list_rearrange (perm 0) yls)).
  { apply PERM_list_rearrange, ALL_DISTINCT_sort_toAList. }
  destruct (list_rearrange_perm (MAP g xls) (list_rearrange (perm 0) yls) (Permutation_trans HP1 HP2))
    as [p Hp].
  exists (fun n => if n =? 0 then p else tperm (n - 1)). cbn beta. rewrite N.eqb_refl. split.
  - apply functional_extensionality; intros n.
    destruct (n + 1 =? 0) eqn:E; [apply N.eqb_eq in E; lia|]. f_equal; lia.
  - rewrite <- list_rearrange_MAP. exact Hp.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "push_env_s_val_eq" *)
Theorem push_env_s_val_eq : forall (st cst : state) (x y x' y' : num_map (word_loc a)) f
    (b b' : option (N * (prog a * (N * N)))) tperm,
  handler st = handler cst /\
  stack st = stack cst /\
  locals_size st = locals_size cst /\
  domain y = IMAGE f (domain x) /\
  INJ f (domain x) UNIV /\
  domain y' = IMAGE f (domain x') /\
  INJ f (domain x') UNIV /\
  strong_locals_rel f (domain x) x y /\
  match b with
  | None => b' = None
  | Some (w, (h, (l1, l2))) =>
      match b' with None => False | Some (a0, (b0, (c0, d))) => c0 = l1 /\ d = l2 end
  end ->
  exists perm,
    (let '(l, permute) := env_to_list y (permute cst) in
     let '(l', permute') := env_to_list x perm in
     permute' = tperm /\
     MAP (fun '(x, y) => (f x, y)) l' = l /\
     (forall x y, MEM x (MAP FST l') /\ MEM y (MAP FST l') /\ f x = f y -> x = y)) /\
    s_val_eq (stack (push_env (x', x) b (set_permute perm st)))
             (stack (push_env (y', y) b' cst)).
Proof.
  intros st cst x y x' y' f b b' tperm (Hh & Hst & Hls & Hd & Hi & Hd' & Hi' & Hs & Hb).
  pose proof (env_to_list_perm y x f (permute cst) tperm (conj Hd (conj Hi Hs))) as H.
  destruct (env_to_list y (permute cst)) as [l pm] eqn:El.
  destruct H as [perm' H]. exists perm'.
  destruct (env_to_list x perm') as [l' pm'] eqn:El'. destruct H as [Hp Hm].
  split; [split; [exact Hp|split; [exact Hm|]]|].
  - intros k1 k2 (H1 & H2 & E). destruct Hi as [_ Hinj]. apply Hinj; [|exact E].
    unfold env_to_list in El'; injection El' as <- _.
    rewrite MEM_iff' in H1, H2.
    apply in_map_iff in H1 as [[k1' v1] [<- H1]], H2 as [[k2' v2] [<- H2]].
    apply In_list_rearrange_sort in H1, H2. cbn. split; apply IN_domain_iff; eauto.
  - assert (Hsnd : MAP SND l' = MAP SND l).
    { rewrite <- Hm, List.map_map. apply map_ext; intros [? ?]; reflexivity. }
    destruct b as [[w [h [l1 l2]]]|], b' as [[a0 [b0 [c0 d]]]|]; try contradiction; try discriminate;
      unfold push_env; cbn [FST SND fst snd];
      rewrite ?permute_set_permute, ?stack_set_permute, ?handler_set_permute, ?locals_size_set_permute; rewrite El, El'; cbn [stack set_permute set_stack_max set_stack set_handler s_val_eq];
      (split; [rewrite Hst; apply s_val_eq_refl|]); apply s_frame_val_eq_def2;
      repeat split; try assumption; try congruence.
    destruct Hb as [-> ->]. cbn. rewrite Hh. reflexivity.
Qed.

End Push.

Ltac cbn_ws :=
  cbn [locals locals_size fp_regs store stack stack_limit stack_max state_stack_size memory
       mdomain sh_mdomain permute compile compile_oracle code_buffer data_buffer gc_fun handler
       clock termdep code be ffi set_locals set_locals_size set_fp_regs set_store_field set_stack
       set_stack_limit set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain
       set_permute set_compile set_compile_oracle set_code_buffer set_data_buffer set_gc_fun
       set_handler set_clock set_termdep set_code set_be set_ffi set_var set_vars unset_var
       set_store set_fp_var dec_clock fst snd] in *.

(** ** Frames and keys *)

Section Frames.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "gc_frame" *)
Theorem gc_frame : forall (st st' : state),
  gc st = SOME st' ->
  fp_regs st' = fp_regs st /\
  mdomain st' = mdomain st /\
  sh_mdomain st' = sh_mdomain st /\
  gc_fun st' = gc_fun st /\
  handler st' = handler st /\
  clock st' = clock st /\
  code st' = code st /\
  locals st' = locals st /\
  locals_size st' = locals_size st /\
  state_stack_size st' = state_stack_size st /\
  stack_max st' = stack_max st /\
  stack_limit st' = stack_limit st /\
  be st' = be st /\
  ffi st' = ffi st /\
  compile st' = compile st /\
  compile_oracle st' = compile_oracle st /\
  code_buffer st' = code_buffer st /\
  data_buffer st' = data_buffer st /\
  permute st' = permute st /\
  termdep st' = termdep st.
Proof.
  intros st st' H; unfold gc in H; cbn zeta in H.
  destruct (gc_fun st _) as [[wl [m s0]]|]; [|discriminate].
  destruct (dec_stack wl (stack st)) as [stk|]; [|discriminate].
  injection H as <-. repeat split.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "s_key_eq_val_eq_pop_env" *)
Theorem s_key_eq_val_eq_pop_env : forall (s s' : state) n lsz ls opt keys vals,
  pop_env s = SOME s' /\
  s_key_eq (stack s) (StackFrame n lsz ls opt :: keys) /\
  s_val_eq (stack s) vals ->
  exists lsz' ls' rest,
    vals = StackFrame n lsz' ls' opt :: rest /\
    locals s' = union (fromAList (ZIP (MAP FST ls, MAP SND ls'))) (fromAList lsz) /\
    s_key_eq (stack s') keys /\
    s_val_eq (stack s') rest /\
    match opt with None => handler s' = handler s | Some (h, (l1, l2)) => handler s' = h end.
Proof.
  intros s s' n lsz ls opt keys vals (Hp & Hk & Hv). unfold pop_env in Hp.
  destruct (stack s) as [|[m e0 e h] xs] eqn:Es; [discriminate|].
  destruct vals as [|[m' e0' e' h'] rest]; cbn [s_key_eq s_val_eq] in Hk, Hv; [contradiction|].
  destruct Hk as [Hk Hf]. apply s_frame_key_eq_def2 in Hf as (Hfst & -> & -> & ->).
  destruct Hv as [Hv Hf']. apply s_frame_val_eq_def2 in Hf' as (Hsnd & <- & <-).
  exists e0', e', rest.
  assert (He : e = ZIP (MAP FST ls, MAP SND e')).
  { rewrite <- Hfst, <- Hsnd, ZIP_combine'. clear. induction e as [|[k v] e IH]; [reflexivity|].
    cbn; f_equal; exact IH. }
  destruct opt as [[hn [l1 l2]]|]; injection Hp as <-; cbn_ws;
    repeat split; try assumption; try reflexivity; rewrite He; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_key_remap_2" *)
Theorem ALOOKUP_key_remap_2 : forall (ls : list N) (vals : list (word_loc a)) (f : N -> N) n v,
  (forall x y, MEM x ls /\ MEM y ls /\ f x = f y -> x = y) /\
  LENGTH ls = LENGTH vals /\
  ALOOKUP (ZIP (ls, vals)) n = SOME v ->
  ALOOKUP (ZIP (MAP f ls, vals)) (f n) = SOME v.
Proof.
  induction ls as [|h ls IH]; intros [|w vals] f n v (Hi & Hl & Ha); cbn in Ha; try discriminate.
  cbn [MAP List.map]. rewrite !ZIP_combine' in *. cbn [combine ALOOKUP] in *.
  destruct (decide (h = n)) as [->|Hn].
  - injection Ha as <-. destruct (decide (f n = f n)); [reflexivity|congruence].
  - assert (Hm : In n ls).
    { apply ALOOKUP_In in Ha. apply in_combine_l in Ha. exact Ha. }
    destruct (decide (f h = f n)) as [E|E].
    + exfalso; apply Hn, Hi. repeat split; try assumption.
      * unfold is_true; cbn; rewrite bd_true'; reflexivity.
      * rewrite MEM_iff'; right; exact Hm.
    + rewrite <- ZIP_combine'. apply IH. repeat split.
      * intros x y (Hx & Hy & E'). apply Hi. repeat split; try assumption;
          unfold is_true in *; cbn; [rewrite Hx|rewrite Hy]; apply orb_true_r.
      * rewrite !LENGTH_length in *; cbn in Hl; lia.
      * rewrite ZIP_combine'; exact Ha.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ALOOKUP_key_remap_INJ" *)
Theorem ALOOKUP_key_remap_INJ : forall (f : N -> N) n (ls : list N) (vals : list (word_loc a)),
  INJ f (n INSERT set ls) UNIV /\ LENGTH ls = LENGTH vals ->
  ALOOKUP (ZIP (ls, vals)) n = ALOOKUP (ZIP (MAP f ls, vals)) (f n).
Proof.
  intros f n ls vals [[_ Hi] Hl].
  destruct (ALOOKUP (ZIP (ls, vals)) n) as [v|] eqn:E.
  - symmetry; apply ALOOKUP_key_remap_2; repeat split; [|exact Hl|exact E].
    intros x y (Hx & Hy & Exy). apply Hi; [|exact Exy].
    rewrite MEM_iff' in Hx, Hy. split; right; apply IN_set; assumption.
  - symmetry. apply ALOOKUP_NONE. intros Hm. apply ALOOKUP_NONE in E. apply E.
    rewrite MEM_iff' in *. rewrite ZIP_combine' in *.
    rewrite map_fst_combine in Hm |- * by (rewrite ?length_map; rewrite !LENGTH_length in Hl; lia).
    apply in_map_iff in Hm as [x [Ex Hx]].
    replace n with x; [exact Hx|]. apply Hi; [split; [right; apply IN_set; exact Hx|left; reflexivity]|exact Ex].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_subset" *)
Theorem strong_locals_rel_subset : forall {A} f s s' (stl cstl : num_map A),
  s SUBSET s' /\ strong_locals_rel f s' stl cstl -> strong_locals_rel f s stl cstl.
Proof. intros A f s s' stl cstl [Hs H] n v [Hn Hl]; apply H; split; [apply Hs, Hn|exact Hl]. Qed.

Lemma In_list_rearrange' {A} `{Inhabited A} (p : N -> N) (ls : list A) x :
  In x (list_rearrange p ls) <-> In x ls.
Proof.
  destruct (list_rearrange_cases' p ls) as [[Hb ->]|[_ ->]]; [|reflexivity].
  rewrite In_GENLIST, In_nth_EL.
  destruct Hb as [[Hm _] [_ Hs]]. unfold pred_set.IN, count in *.
  split.
  - intros [i [Hi ->]]; exists (p i); split; [apply Hm, Hi|reflexivity].
  - intros [j [Hj ->]]; destruct (Hs j Hj) as [i [Hi Hfi]]; exists i; split; [exact Hi|].
    rewrite Hfi; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "env_to_list_keys" *)
Theorem env_to_list_keys : forall (x : num_map (word_loc a)) perm,
  let '(l, permute) := env_to_list x perm in set (MAP FST l) = domain x.
Proof.
  intros x perm; unfold env_to_list; cbv zeta. apply set_ext; intros k.
  change (set (MAP FST (list_rearrange (perm 0) (sort key_val_compare (toAList x)))) k)
    with (k IN set (MAP FST (list_rearrange (perm 0) (sort key_val_compare (toAList x))))).
  change (domain x k) with (k IN domain x).
  rewrite IN_set, IN_domain_iff, in_map_iff. split.
  - intros [[k' v] [<- H]]. apply In_list_rearrange_sort in H. eauto.
  - intros [v Hv]. exists (k, v). split; [reflexivity|]. apply In_list_rearrange_sort, Hv.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_keys" *)
Theorem list_rearrange_keys : forall {A B} `{Inhabited (A * B)} perm (ls : list (A * B)) e,
  list_rearrange perm ls = e -> set (MAP FST e) = set (MAP FST ls).
Proof.
  intros A B IAB perm ls e <-. apply set_ext; intros k.
  change (k IN set (MAP FST (list_rearrange perm ls)) <-> k IN set (MAP FST ls)).
  rewrite !IN_set, !in_map_iff. split; intros [y [Hy H]]; exists y; split; try assumption;
    [apply (In_list_rearrange' perm)|apply (In_list_rearrange' perm)]; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "list_rearrange_keys_2" *)
Theorem list_rearrange_keys_2 : forall {A B} `{Inhabited (A * B)} perm (ls : list (A * B)),
  set (MAP FST (list_rearrange perm ls)) = set (MAP FST ls).
Proof. intros A B IAB perm ls; eapply list_rearrange_keys; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "MAP_FST_list_rearrange_keys_SORT" *)
Theorem MAP_FST_list_rearrange_keys_SORT : forall perm (x : num_map (word_loc a)),
  set (MAP FST (list_rearrange perm (sort key_val_compare (toAList x)))) = domain x.
Proof.
  intros perm x. pose proof (env_to_list_keys x (fun _ => perm)) as H. exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "MAP_FST_keys_SORT" *)
Theorem MAP_FST_keys_SORT : forall {A} (f : N * A -> N * A -> bool) (x : num_map A),
  set (MAP FST (sort f (toAList x))) = domain x.
Proof.
  intros A f x. apply set_ext; intros k.
  change (k IN set (MAP FST (sort f (toAList x))) <-> k IN domain x).
  rewrite IN_set, IN_domain_iff, in_map_iff. split.
  - intros [[k' v] [<- H]]. exists v. apply ALOOKUP_toAList_In.
    eapply Permutation_in; [symmetry; apply sort_Permutation|exact H].
  - intros [v Hv]. exists (k, v); split; [reflexivity|].
    eapply Permutation_in; [apply sort_Permutation|apply ALOOKUP_toAList_In, Hv].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "pop_env_frame" *)
Theorem pop_env_frame : forall (r' y' y'' : state) st',
  s_val_eq (stack r') st' /\
  s_key_eq (stack y') (stack y'') /\
  pop_env (set_stack st' r') = SOME y'' /\
  pop_env r' = SOME y' ->
  word_state_eq_rel y' y''.
Proof.
  intros r' y' y'' st' (Hv & Hk & H1 & H2). unfold pop_env in *.
  rewrite stack_set_stack in H1.
  destruct (stack r') as [|[m e0 e h] xs] eqn:Es; [discriminate|].
  destruct st' as [|[m' e0' e' h'] xs']; cbn [s_val_eq] in Hv; [contradiction|].
  destruct Hv as [Hv Hf]. apply s_frame_val_eq_def2 in Hf as (_ & <- & <-).
  destruct h as [[hn x]|]; injection H1 as <-; injection H2 as <-; cbn_ws;
    cbn in Hk; unfold word_state_eq_rel; cbn; repeat split.
  - symmetry; apply s_val_and_key_eq; split; [exact Hv|exact Hk].
  - symmetry; apply s_val_and_key_eq; split; [exact Hv|exact Hk].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "key_map_implies" *)
Theorem key_map_implies : forall {B} (f : N -> N) (l' l : list (N * B)),
  MAP (fun '(x, y) => (f x, y)) l' = l -> MAP f (MAP FST l') = MAP FST l.
Proof.
  intros B f l' l <-. rewrite !List.map_map. apply map_ext; intros [? ?]; reflexivity.
Qed.

End Frames.

(** ** Expressions, inserting and setting variables *)

Section Exps.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma set_permute_permute (s : state) : set_permute (permute s) s = s.
Proof. destruct s; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "apply_colour_exp_lemma" *)
Theorem apply_colour_exp_lemma : forall (st : state) (w : exp a) (cst : state) f res,
  word_exp st w = SOME res /\
  word_state_eq_rel st cst /\
  strong_locals_rel f (domain (get_live_exp w)) (locals st) (locals cst) ->
  word_exp cst (apply_colour_exp f w) = SOME res.
Proof.
  intros st w; induction w as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    intros cst f res (H & Heq & Hs); cbn [word_exp apply_colour_exp get_live_exp] in *;
    pose proof Heq as Heq'; unfold word_state_eq_rel in Heq; destr_conj.
  - exact H.
  - unfold get_var in *. apply Hs. split; [|exact H]. rewrite domain_insert; left; reflexivity.
  - unfold get_store in *. congruence.
  - destruct (word_exp st e) as [[w|]|] eqn:E; try discriminate.
    rewrite (IH cst f (Word w) (conj eq_refl (conj Heq' Hs))).
    unfold mem_load in *. rewrite H7, H8. exact H.
  - destruct (the_words (MAP (word_exp st) es)) as [ws|] eqn:Ews; [|discriminate].
    assert (Hmap : MAP (word_exp cst) (MAP (apply_colour_exp f) es) = MAP (word_exp st) es).
    { rewrite List.map_map. apply map_ext_in. intros e He.
      pose proof (the_words_EVERY_IS_SOME _ _ Ews) as Hev. unfold is_true in Hev.
      rewrite EVERY_Forall, Forall_map, Forall_forall in Hev. specialize (Hev e He).
      destruct (word_exp st e) as [r|] eqn:Ee; [|discriminate].
      rewrite Forall_forall in IH. apply (IH e He cst f r). split; [exact Ee|split; [exact Heq'|]].
      apply (strong_locals_rel_subset f _ (domain (big_union (MAP get_live_exp es)))). split; [|exact Hs].
      apply domain_big_union_subset. apply MEM_iff', He. }
    rewrite Hmap, Ews. exact H.
  - rewrite domain_union in Hs.
    assert (Hs1 : strong_locals_rel f (domain (get_live_exp e1)) (locals st) (locals cst))
      by (eapply strong_locals_rel_subset; split; [|exact Hs]; intros x Hx; left; exact Hx).
    assert (Hs2 : strong_locals_rel f (domain (get_live_exp e2)) (locals st) (locals cst))
      by (eapply strong_locals_rel_subset; split; [|exact Hs]; intros x Hx; right; exact Hx).
    destruct (word_exp st e1) as [[w1|]|] eqn:E1; try discriminate.
    destruct (word_exp st e2) as [[w2|]|] eqn:E2; try discriminate.
    rewrite (IH1 cst f (Word w1) (conj eq_refl (conj Heq' Hs1))).
    rewrite (IH2 cst f (Word w2) (conj eq_refl (conj Heq' Hs2))). exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_insert" *)
Theorem strong_locals_rel_insert : forall {A} f n l (st cst : num_map A) v,
  INJ f (n INSERT l) UNIV /\
  strong_locals_rel f (l DELETE n) st cst ->
  strong_locals_rel f l (insert n v st) (insert (f n) v cst).
Proof.
  intros A f n l st cst v [Hi Hs] m w [Hm Hl]. rewrite lookup_insert in Hl |- *.
  destruct (decide (m = n)) as [->|Hne].
  - rewrite decide_True' by reflexivity. exact Hl.
  - rewrite decide_False'.
    + apply Hs. split; [|exact Hl]. split; [exact Hm|]. intros [E|[]]; contradiction.
    + apply (INJ_neq f (n INSERT l)); [exact Hi|right; exact Hm|left; reflexivity|exact Hne].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "LASTN_LENGTH2" *)
Theorem LASTN_LENGTH2 : forall {A} (x : A) xs, LASTN (LENGTH xs + 1) (x :: xs) = x :: xs.
Proof.
  intros A x xs. apply LASTN_LENGTH_cond. rewrite !LENGTH_length; cbn [length]; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "toAList_not_empty" *)
Theorem toAList_not_empty : forall {A} (t : spt A), domain t <> {} -> toAList t <> [].
Proof.
  intros A t Hd E. apply Hd. apply set_ext; intros k; split; [|intros []].
  intros Hk. change (k IN domain t) in Hk. apply IN_domain_iff in Hk as [v Hv].
  apply ALOOKUP_toAList_In in Hv. rewrite E in Hv. destruct Hv.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "PAIR_CASE_PAIR_MAP" *)
Theorem PAIR_CASE_PAIR_MAP : forall {A B C D E} (f : A -> C) (g : B -> D) (e : A * B) (h : C -> D -> E),
  (let '(x, y) := (f ## g) e in h x y) = (let '(x, y) := e in h (f x) (g y)).
Proof. intros; destruct e; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "permute_swap_lemma4" *)
Theorem permute_swap_lemma4 : forall (prog : prog a) (st : state) (P : option (result a) * state -> Prop),
  (forall st', evaluate (prog, st) = (SOME Error, st') -> P (SOME Error, st')) /\
  (exists perm, P ((I ## (fun s => set_permute perm s)) (evaluate (prog, st)))) ->
  exists perm, P (evaluate (prog, set_permute perm st)).
Proof.
  intros prog st P [H1 [perm H2]].
  pose proof (permute_swap_lemma prog st perm) as Hs.
  destruct (evaluate (prog, st)) as [res rst] eqn:E.
  destruct (decide (res = SOME Error)) as [->|Hr].
  - exists (permute st). rewrite set_permute_permute, E. apply H1; reflexivity.
  - destruct (Hs Hr) as [perm' Hp]. exists perm'. rewrite Hp. exact H2.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "MEM_ZIP_weak" *)
Theorem MEM_ZIP_weak : forall {A B} `{EqDecision A} `{EqDecision B} (l1 : list A) (l2 : list B) x1 x2,
  LENGTH l1 = LENGTH l2 /\ MEM (x1, x2) (ZIP (l1, l2)) -> MEM x1 l1 /\ MEM x2 l2.
Proof.
  intros A B EA EB l1 l2 x1 x2 [_ H]. rewrite !MEM_iff' in *. rewrite ZIP_combine' in H.
  split; [eapply in_combine_l|eapply in_combine_r]; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_set_vars_dom" *)
Theorem strong_locals_rel_set_vars_dom : forall f X d ns ls (s t : state),
  LENGTH ns = LENGTH ls /\
  INJ f X UNIV /\
  domain (locals s) SUBSET X /\
  set ns SUBSET X /\
  strong_locals_rel f d (locals s) (locals t) ->
  strong_locals_rel f d (locals (set_vars ns ls s)) (locals (set_vars (MAP f ns) ls t)).
Proof.
  intros f X d ns ls s t (Hl & Hi & Hd & Hn & Hs) n v [Hnd Hlk].
  unfold set_vars in *; rewrite !locals_set_locals in *.
  rewrite lookup_alist_insert in Hlk |- * by (rewrite ?LENGTH_MAP'; exact Hl).
  destruct (ALOOKUP (ZIP (ns, ls)) n) as [w|] eqn:Ea.
  - injection Hlk as <-. rewrite (ALOOKUP_key_remap_2 ns ls f n w); [reflexivity|].
    repeat split; [|exact Hl|exact Ea].
    intros x y (Hx & Hy & E). destruct Hi as [_ Hi]. apply Hi; [|exact E].
    rewrite MEM_iff' in Hx, Hy. split; apply Hn, IN_set; assumption.
  - assert (Hf : ALOOKUP (ZIP (MAP f ns, ls)) (f n) = None).
    { apply ALOOKUP_NONE. apply ALOOKUP_NONE in Ea. intros Hm; apply Ea.
      rewrite MEM_iff', ZIP_combine' in *. rewrite map_fst_combine in Hm |- *
        by (rewrite ?length_map; rewrite !LENGTH_length in Hl; lia).
      apply in_map_iff in Hm as [m [Em Hm]]. replace n with m; [exact Hm|].
      destruct Hi as [_ Hi]. apply Hi; [|exact Em]. split; [apply Hn, IN_set, Hm|].
      apply Hd, IN_domain_iff; eauto. }
    rewrite Hf. apply Hs; split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "s_key_eq_push_env_imp_MAP_FST" *)
Theorem s_key_eq_push_env_imp_MAP_FST : forall (x' x'' : num_map (word_loc a)) o0 (s : state) n' bb l opt ls ll res,
  s_key_eq (stack (push_env (x', x'') o0 s)) (StackFrame n' bb l opt :: ls) /\
  env_to_list x'' (permute s) = (ll, res) ->
  MAP FST ll = MAP FST l /\ set (MAP FST bb) = domain x'.
Proof.
  intros x' x'' o0 s n' bb l opt ls ll res [Hk He].
  assert (Hst : exists h, stack (push_env (x', x'') o0 s) = StackFrame (locals_size s) (toAList x') ll h :: stack s).
  { destruct o0 as [[? [? [? ?]]]|]; unfold push_env; cbn [FST SND fst snd]; rewrite He; eexists; reflexivity. }
  destruct Hst as [h Hst]. rewrite Hst in Hk. cbn [s_key_eq] in Hk. destruct Hk as [_ Hf].
  apply s_frame_key_eq_def2 in Hf as (Hm & _ & <- & _). split; [exact Hm|].
  apply set_ext; intros k. change (k IN set (MAP FST (toAList x')) <-> k IN domain x').
  rewrite IN_set, IN_domain_iff, in_map_iff. split.
  - intros [[k' v] [<- H]]; exists v; apply ALOOKUP_toAList_In, H.
  - intros [v Hv]; exists (k, v); split; [reflexivity|apply ALOOKUP_toAList_In, Hv].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_set_var_dom" *)
Theorem strong_locals_rel_set_var_dom : forall f X d n l (s t : state),
  INJ f X UNIV /\
  domain (locals s) SUBSET X /\
  n IN X /\
  strong_locals_rel f d (locals s) (locals t) ->
  strong_locals_rel f d (locals (set_var n l s)) (locals (set_var (f n) l t)).
Proof.
  intros f X d n l s t (Hi & Hd & Hn & Hs) m v [Hm Hl]. unfold set_var in *.
  rewrite !locals_set_locals, lookup_insert in *.
  destruct (decide (m = n)) as [->|Hne].
  - rewrite decide_True' by reflexivity. exact Hl.
  - rewrite decide_False'.
    + apply Hs; split; assumption.
    + apply (INJ_neq f X); [exact Hi| |exact Hn|exact Hne]. apply Hd, IN_domain_iff; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_extend_aux" *)
Theorem strong_locals_rel_extend_aux : forall {A} f s t0 (src tgt : num_map A),
  domain src SUBSET s /\ strong_locals_rel f s src tgt -> strong_locals_rel f t0 src tgt.
Proof.
  intros A f s t0 src tgt [Hd Hs] n v [_ Hl]. apply Hs; split; [|exact Hl].
  apply Hd, IN_domain_iff; eauto.
Qed.

End Exps.

(** ** Instructions (Galette-only infrastructure for [evaluate_apply_colour]) *)

(** Set reasoning on domains of sptrees. *)
Ltac set_simp :=
  unfold pred_set.SUBSET, pred_set.DELETE, pred_set.DIFF, pred_set.IMAGE, pred_set.UNION,
    pred_set.INTER, pred_set.INSERT, pred_set.EMPTY, pred_set.IN in *;
  repeat rewrite ?domain_insert, ?domain_delete, ?domain_union, ?domain_inter,
    ?domain_numset_list_insert in *;
  unfold pred_set.SUBSET, pred_set.DELETE, pred_set.DIFF, pred_set.IMAGE, pred_set.UNION,
    pred_set.INTER, pred_set.INSERT, pred_set.EMPTY, pred_set.IN in *;
  cbn beta in *; cbn [domain LIST_TO_SET] in *.

Ltac in_solve := set_simp; first [tauto | intuition congruence].

Ltac set_solve :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; in_solve.

(** Case-split innermost [match]es in [H]. *)
Ltac split_in H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [match _ with _ => _ end] => fail
      | _ => let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end
  end.

Ltac inj_less H :=
  eapply INJ_less; split; [exact H|set_solve].

Ltac slr Hi Hs :=
  repeat (apply strong_locals_rel_insert; split; [inj_less Hi|]);
  eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve.

Section Inst.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Lemma inst_apply_colour (i : asm.inst a) (st cst s1 : state) f live :
  INJ f (domain (union (get_writes_inst i) live)) UNIV ->
  word_state_eq_rel st cst ->
  strong_locals_rel f (domain (get_live_inst i live)) (locals st) (locals cst) ->
  inst i st = SOME s1 ->
  exists cs1, inst (apply_colour_inst f i) cst = SOME cs1 /\ word_state_eq_rel s1 cs1 /\
    strong_locals_rel f (domain live) (locals s1) (locals cs1).
Proof.
  intros Hi Heq Hs H.
  assert (Hg : forall r v, r IN domain (get_live_inst i live) -> get_var r st = Some v ->
                 get_var (f r) cst = Some v)
    by (intros r v Hr Hv; apply Hs; split; assumption).
  pose proof Heq as Heq'.
  destruct Heq as (Hfp & Hstore & Hls & Hstack & Hsl & Hsm & Hss & Hmem & Hmd & Hsmd & Hgc & Hh
                   & Hclk & Hcode & Hffi & Hbe & Htd & Hcomp & Hco & Hcb & Hdb).
  destruct_inst i;
    cbv beta iota zeta delta [inst wordSem.assign apply_colour_inst apply_colour_imm get_live_inst
         get_writes_inst get_vars] in *;
    cbn [word_exp the_words MAP List.map] in *;
    unfold mem_load, mem_store, get_fp_var, set_fp_var in *;
    split_in H; try discriminate H; try (injection H as <-); subst;
    repeat match goal with
           | E : get_var ?r st = Some ?v |- context [get_var (f ?r) cst] =>
               rewrite (Hg r v ltac:(in_solve) E)
           end;
    rewrite ?Hmem, ?Hmd, ?Hbe, ?Hfp in *;
    repeat match goal with
           | E : ?x = SOME _ |- context [?x] => lazymatch x with SOME _ => fail | _ => rewrite E end
           | E : ?x = true |- context [?x] => rewrite E
           | E : ?x = false |- context [?x] => rewrite E
           | E : ?x = (_, _) |- context [?x] => rewrite E
           | E : ?x = left _ |- context [?x] => rewrite E
           | E : ?x = right _ |- context [?x] => rewrite E
           end;
    try (eexists; split; [reflexivity|]; split;
      [ unfold word_state_eq_rel; cbn [set_var set_locals set_memory set_fp_regs locals fp_regs store locals_size stack stack_limit stack_max state_stack_size memory mdomain sh_mdomain gc_fun handler clock code ffi be termdep compile compile_oracle code_buffer data_buffer]; repeat split; congruence
      | cbn [set_var set_locals set_memory set_fp_regs locals]; slr Hi Hs ]).
Qed.

End Inst.

(** ** [evaluate_apply_colour] *)

Ltac wser := unfold word_state_eq_rel in *; cbn_ws; destr_conj; repeat split; congruence.

Ltac err_case Hev Hr := injection Hev as <- _; exfalso; apply Hr; reflexivity.

Ltac rw_eqs :=
  repeat match goal with
         | E : ?x = SOME _ |- context [?x] => lazymatch x with SOME _ => fail | _ => rewrite E end
         | E : ?x = true |- context [?x] => rewrite E
         | E : ?x = false |- context [?x] => rewrite E
         | E : ?x = (_, _) |- context [?x] => rewrite E
         | E : ?x = left _ |- context [?x] => rewrite E
         | E : ?x = right _ |- context [?x] => rewrite E
         | E : ?x = FFI_final _ |- context [?x] => rewrite E
         | E : ?x = FFI_return _ _ |- context [?x] => rewrite E
         end.

Section Main.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).
Implicit Types (st cst : state).

(** The post-condition of [evaluate_apply_colour] (Galette-only name). *)
Definition ac_post (f : N -> N) (live : num_set) (lt : list (num_set * num_set))
    (res : option (result a)) (rst rcst : state) : Prop :=
  match res with
  | NONE => strong_locals_rel f (domain live) (locals rst) (locals rcst)
  | SOME (Break n) =>
      match oEL n lt with
      | Some (_, exit_names) => strong_locals_rel f (domain exit_names) (locals rst) (locals rcst)
      | None => True
      end
  | SOME (Continue n) =>
      match oEL n lt with
      | Some (names, _) => strong_locals_rel f (domain names) (locals rst) (locals rcst)
      | None => True
      end
  | SOME _ => locals rst = locals rcst
  end.

(** The conclusion of [evaluate_apply_colour_Loop_helper] (Galette-only name). *)
Definition eac_concl (f : N -> N) (live : num_set) (lt : list (num_set * num_set))
    (p : prog a) (st cst : state) : Prop :=
  exists perm',
    let '(res, rst) := evaluate (p, set_permute perm' st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (apply_colour f p, cst) in
    res = res' /\ word_state_eq_rel rst rcst /\ ac_post f live lt res rst rcst.

Lemma eac_by p st cst f live lt :
  word_state_eq_rel st cst ->
  (forall res rst, word_state_eq_rel (set_permute (permute cst) st) cst ->
     evaluate (p, set_permute (permute cst) st) = (res, rst) -> res <> SOME Error ->
     let '(res', rcst) := evaluate (apply_colour f p, cst) in
     res = res' /\ word_state_eq_rel rst rcst /\ ac_post f live lt res rst rcst) ->
  eac_concl f live lt p st cst.
Proof.
  intros Heq H. exists (permute cst).
  destruct (evaluate (p, set_permute (permute cst) st)) as [res rst] eqn:E.
  destruct (decide (res = SOME Error)) as [->|Hr]; [left; reflexivity|right].
  apply H; [|reflexivity|exact Hr].
  apply word_state_eq_rel_iff in Heq. rewrite Heq at 2. apply word_state_eq_rel_iff.
  rewrite permute_set_permute, locals_set_permute, locals_set_locals. reflexivity.
Qed.

Lemma strong_locals_rel_alist_insert (f : N -> N) ns (vs : list (word_loc a)) L l1 l2 :
  LENGTH ns = LENGTH vs ->
  INJ f (set ns UNION L) UNIV ->
  strong_locals_rel f (L DIFF set ns) l1 l2 ->
  strong_locals_rel f L (alist_insert ns vs l1) (alist_insert (MAP f ns) vs l2).
Proof.
  intros Hl Hi Hs n v [Hn Hlk].
  rewrite lookup_alist_insert in Hlk |- * by (rewrite ?LENGTH_MAP'; exact Hl).
  destruct (ALOOKUP (ZIP (ns, vs)) n) as [w|] eqn:Ea.
  - injection Hlk as <-. rewrite (ALOOKUP_key_remap_2 ns vs f n w); [reflexivity|].
    repeat split; [|exact Hl|exact Ea].
    intros x y (Hx & Hy & E). destruct Hi as [_ Hi]. apply Hi; [|exact E].
    rewrite MEM_iff' in Hx, Hy. split; left; apply IN_set; assumption.
  - assert (Hnn : ~ In n ns).
    { apply ALOOKUP_NONE in Ea. intros Hm; apply Ea. rewrite MEM_iff', ZIP_combine'.
      rewrite map_fst_combine by (rewrite !LENGTH_length in Hl; lia). exact Hm. }
    assert (Hf : ALOOKUP (ZIP (MAP f ns, vs)) (f n) = None).
    { apply ALOOKUP_NONE. intros Hm. rewrite MEM_iff', ZIP_combine' in Hm.
      rewrite map_fst_combine in Hm by (rewrite length_map; rewrite !LENGTH_length in Hl; lia).
      apply in_map_iff in Hm as [m [Em Hm]]. apply Hnn. replace n with m; [exact Hm|].
      destruct Hi as [_ Hi]. apply Hi; [|exact Em]. split; [left; apply IN_set, Hm|right; exact Hn]. }
    rewrite Hf. apply Hs. split; [|exact Hlk]. split; [exact Hn|]. rewrite IN_set; exact Hnn.
Qed.

Definition eac_hyp (f : N -> N) (live : num_set) (lt : list (num_set * num_set))
    (p : prog a) (st cst : state) : Prop :=
  colouring_ok f p live lt /\ word_state_eq_rel st cst /\
  strong_locals_rel f (domain (get_live p live lt)) (locals st) (locals cst).

Ltac eac_start :=
  let res := fresh "res" in let rst := fresh "rst" in let Heq0 := fresh "Heq0" in
  let Hev := fresh "Hev" in let Hr := fresh "Hr" in let st0 := fresh "st0" in
  intros (Hc & Heq & Hs); apply eac_by; [exact Heq|];
  intros res rst Heq0 Hev Hr;
  lazymatch type of Heq0 with
  | word_state_eq_rel (set_permute ?p ?s) _ =>
      set (st0 := set_permute p s) in *; change (locals s) with (locals st0) in Hs
  end;
  rewrite evaluate_eqn in Hev; cbn [evaluate_body] in Hev;
  rewrite evaluate_eqn; cbn [evaluate_body apply_colour];
  cbn [colouring_ok get_live get_writes] in Hc, Hs; cbv zeta in Hc;
  try (let Hi1 := fresh "Hi1" in let Hi2 := fresh "Hi2" in destruct Hc as [Hi1 Hi2]).

Lemma eac_Skip st cst f live lt :
  eac_hyp f live lt (@Skip a) st cst -> eac_concl f live lt (@Skip a) st cst.
Proof.
  eac_start. injection Hev as <- <-. cbn [ac_post] in *.
  split; [reflexivity|split; [exact Heq0|exact Hs]].
Qed.

Lemma eac_Inst i st cst f live lt :
  eac_hyp f live lt (Inst i) st cst -> eac_concl f live lt (Inst i) st cst.
Proof.
  eac_start. destruct (inst i st0) as [s1|] eqn:Ei; [|err_case Hev Hr]. injection Hev as <- <-.
  destruct (inst_apply_colour i st0 cst s1 f live Hi2 Heq0 Hs Ei) as (cs1 & -> & Hw & Hl).
  cbn [ac_post]. auto.
Qed.

Lemma eac_Assign v e st cst f live lt :
  eac_hyp f live lt (Assign v e) st cst -> eac_concl f live lt (Assign v e) st cst.
Proof.
  eac_start. destruct (word_exp st0 e) as [w|] eqn:Ee; [|err_case Hev Hr]. injection Hev as <- <-.
  rewrite (apply_colour_exp_lemma st0 e cst f w); cycle 1.
  { split; [exact Ee|split; [exact Heq0|]]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  cbn [ac_post]. split; [reflexivity|split; [unfold set_var; apply word_state_eq_rel_locals, Heq0|]].
  unfold set_var; rewrite !locals_set_locals. slr Hi2 Hs.
Qed.

Lemma eac_Get v n st cst f live lt :
  eac_hyp f live lt (Get v n) st cst -> eac_concl f live lt (Get v n) st cst.
Proof.
  eac_start. destruct (get_store n st0) as [x|] eqn:Eg; [|err_case Hev Hr]. injection Hev as <- <-.
  replace (get_store n cst) with (get_store n st0) by (unfold get_store; destruct Heq0 as (_ & H & _); congruence).
  rewrite Eg. cbn [ac_post]. split; [reflexivity|split; [unfold set_var; apply word_state_eq_rel_locals, Heq0|]].
  unfold set_var; rewrite !locals_set_locals. slr Hi2 Hs.
Qed.

Lemma eac_Set v e st cst f live lt :
  eac_hyp f live lt (Set_ v e) st cst -> eac_concl f live lt (Set_ v e) st cst.
Proof.
  eac_start. destruct (_ || _); [err_case Hev Hr|].
  destruct (word_exp st0 e) as [w|] eqn:Ee; [|err_case Hev Hr]. injection Hev as <- <-.
  rewrite (apply_colour_exp_lemma st0 e cst f w); cycle 1.
  { split; [exact Ee|split; [exact Heq0|]]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  cbn [ac_post]. split; [reflexivity|split; [unfold set_store; wser|]].
  unfold set_store; cbn_ws. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
Qed.

Lemma eac_Store e v st cst f live lt :
  eac_hyp f live lt (Store e v) st cst -> eac_concl f live lt (Store e v) st cst.
Proof.
  eac_start. destruct (word_exp st0 e) as [[w|]|] eqn:Ee; try err_case Hev Hr.
  destruct (get_var v st0) as [x|] eqn:Ev; [|err_case Hev Hr].
  destruct (mem_store w x st0) as [s1|] eqn:Em; [|err_case Hev Hr]. injection Hev as <- <-.
  rewrite (apply_colour_exp_lemma st0 e cst f (Word w)); cycle 1.
  { split; [exact Ee|split; [exact Heq0|]]. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  rewrite (strong_locals_rel_get_var f _ st0 cst v x) by (split; [exact Hs|split; [in_solve|exact Ev]]).
  unfold mem_store in *. pose proof Heq0 as Heq1. destruct Heq1 as (_ & _ & _ & _ & _ & _ & _ & Hm & Hd & _).
  rewrite Hm, Hd. destruct (classical_dec _); [|discriminate]. injection Em as <-.
  cbn [ac_post]. split; [reflexivity|split; [wser|]].
  cbn_ws. eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve.
Qed.

Lemma MAP_FST_ZIP' {A B} (l1 : list A) (l2 : list B) :
  LENGTH l1 = LENGTH l2 -> MAP FST (ZIP (l1, l2)) = l1.
Proof. intros H; rewrite ZIP_combine'; apply map_fst_combine; rewrite !LENGTH_length in H; lia. Qed.

Lemma MAP_SND_ZIP' {A B} (l1 : list A) (l2 : list B) :
  LENGTH l1 = LENGTH l2 -> MAP SND (ZIP (l1, l2)) = l2.
Proof. intros H; rewrite ZIP_combine'; apply map_snd_combine; rewrite !LENGTH_length in H; lia. Qed.

Lemma eac_Move pri ls st cst f live lt :
  eac_hyp f live lt (Move pri ls) st cst -> eac_concl f live lt (Move pri ls) st cst.
Proof.
  eac_start.
  rewrite MAP_FST_ZIP', MAP_SND_ZIP' by (rewrite !LENGTH_MAP'; reflexivity).
  destruct (ALL_DISTINCT (MAP FST ls)) eqn:Ed; [|err_case Hev Hr].
  destruct (get_vars (MAP SND ls) st0) as [vs|] eqn:Eg; [|err_case Hev Hr]. injection Hev as <- <-.
  assert (Hd2 : ALL_DISTINCT (MAP (fun x => f (FST x)) ls) = true).
  { replace (MAP (fun x => f (FST x)) ls) with (MAP f (MAP FST ls)) by (rewrite List.map_map; reflexivity).
    apply ALL_DISTINCT_iff'. apply ALL_DISTINCT_iff' in Ed. apply NoDup_map_inj; [exact Ed|].
    intros x y Hx Hy E. destruct Hi2 as [_ Hinj]. apply Hinj; [|exact E].
    rewrite domain_union, domain_numset_list_insert. split; left; right; apply IN_set; assumption. }
  rewrite Hd2.
  replace (MAP (fun x => f (SND x)) ls) with (MAP f (MAP SND ls)) by (rewrite List.map_map; reflexivity).
  rewrite (strong_locals_rel_get_vars (MAP SND ls) vs f (domain (numset_list_insert (MAP SND ls) (FOLDR delete live (MAP FST ls)))) st0 cst); cycle 1.
  { split; [exact Hs|split; [|exact Eg]]. intros x Hx. rewrite domain_numset_list_insert.
    right; apply IN_set, MEM_iff', Hx. }
  cbn [ac_post]. split; [reflexivity|split; [unfold set_vars; apply word_state_eq_rel_locals, Heq0|]].
  replace (MAP (fun x => f (FST x)) ls) with (MAP f (MAP FST ls)) by (rewrite List.map_map; reflexivity).
  unfold set_vars; rewrite !locals_set_locals.
  apply strong_locals_rel_alist_insert.
  - apply get_vars_length_lemma in Eg. rewrite Eg, !LENGTH_MAP'; reflexivity.
  - eapply INJ_less; split; [exact Hi2|]. rewrite domain_union, domain_numset_list_insert.
    intros x [Hx|Hx]; [left; right; exact Hx|right; exact Hx].
  - eapply strong_locals_rel_subset; split; [|exact Hs].
    rewrite domain_numset_list_insert, domain_FOLDR_delete. intros x [Hx Hn]. left. split; [exact Hx|].
    rewrite IN_set in Hn. rewrite MEM_iff'. exact Hn.
Qed.

Lemma wser_set_locals_eq (s t : state) :
  word_state_eq_rel s t -> permute s = permute t -> t = set_locals (locals t) s.
Proof.
  intros H Hp. apply word_state_eq_rel_iff in H. rewrite H at 1. rewrite <- Hp.
  destruct s; reflexivity.
Qed.

Lemma strong_locals_rel_delete {A} f n l (st cst : num_map A) :
  INJ f (n INSERT l) UNIV /\ strong_locals_rel f (l DELETE n) st cst ->
  strong_locals_rel f l (delete n st) (delete (f n) cst).
Proof.
  intros [Hi Hs] m w [Hm Hl]. rewrite lookup_delete in Hl |- *.
  destruct (decide (m = n)) as [->|Hne]; [discriminate|].
  rewrite decide_False'.
  - apply Hs. split; [|exact Hl]. split; [exact Hm|]. intros [E|[]]; contradiction.
  - apply (INJ_neq f (n INSERT l)); [exact Hi|right; exact Hm|left; reflexivity|exact Hne].
Qed.

Ltac slr2 Hi Hs :=
  repeat (first [apply strong_locals_rel_insert|apply strong_locals_rel_delete]; split; [inj_less Hi|]);
  eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve.

(** Normal form: the coloured side runs on [set_locals L st0]. *)
Ltac eac_start2 :=
  eac_start;
  match goal with
  | st0 := _ |- _ =>
    match goal with
    | H0 : word_state_eq_rel st0 ?cst |- _ =>
      let Hcst := fresh "Hcst" in let L := fresh "L" in let HL := fresh "HL" in
      assert (Hcst : cst = set_locals (locals cst) st0)
        by (apply wser_set_locals_eq; [exact H0|reflexivity]);
      clearbody st0;
      remember (locals cst) as L eqn:HL; clear HL; subst cst
    end
  end;
  autorewrite with lrl in *.

Lemma wser_sl (s : state) l : word_state_eq_rel s (set_locals l s).
Proof. apply word_state_eq_rel_locals with (l := locals s), word_state_eq_rel_refl. Qed.

Lemma wser_sl' (s : state) l l' : word_state_eq_rel (set_locals l' s) (set_locals l s).
Proof. apply word_state_eq_rel_locals, word_state_eq_rel_refl. Qed.

Ltac close_wser := first [apply wser_sl | apply wser_sl' | apply word_state_eq_rel_refl | wser].

Lemma eac_StoreConsts t1 t2 ad off ws st cst f live lt :
  eac_hyp f live lt (StoreConsts t1 t2 ad off ws) st cst ->
  eac_concl f live lt (StoreConsts t1 t2 ad off ws) st cst.
Proof.
  eac_start2. unfold get_var in *; rewrite !locals_set_locals.
  destruct (lookup ad (locals st0)) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (lookup off (locals st0)) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  rewrite (Hs ad (Word w1)) by (split; [in_solve|exact E1]).
  rewrite (Hs off (Word w2)) by (split; [in_solve|exact E2]).
  destruct (negb _); [err_case Hev Hr|]. injection Hev as <- <-.
  cbn [ac_post]. split; [reflexivity|split; [wser|]].
  unfold set_var, unset_var; cbn_ws. slr2 Hi2 Hs.
Qed.

Lemma eac_Raise n st cst f live lt :
  eac_hyp f live lt (Raise n) st cst -> eac_concl f live lt (Raise n) st cst.
Proof.
  eac_start2. unfold get_var in *; rewrite !locals_set_locals.
  destruct (lookup n (locals st0)) as [w|] eqn:E1; [|err_case Hev Hr].
  rewrite (Hs n w) by (split; [in_solve|exact E1]).
  destruct (jump_exc st0) as [[s1 [l1 l2]]|]; [|err_case Hev Hr]. injection Hev as <- <-.
  cbn [ac_post]. auto using word_state_eq_rel_refl.
Qed.

Lemma eac_Return n ns st cst f live lt :
  eac_hyp f live lt (Return n ns) st cst -> eac_concl f live lt (Return n ns) st cst.
Proof.
  eac_start2.
  destruct (get_var n st0) as [[w|l1 l2]|] eqn:E1; try err_case Hev Hr.
  destruct (get_vars ns st0) as [ys|] eqn:E2; [|err_case Hev Hr]. injection Hev as <- <-.
  rewrite (strong_locals_rel_get_var f (domain (insert n tt (numset_list_insert ns live))) st0 (set_locals L st0) n (Loc l1 l2))
    by (split; [exact Hs|split; [in_solve|exact E1]]).
  rewrite (strong_locals_rel_get_vars ns ys f (domain (insert n tt (numset_list_insert ns live))) st0 (set_locals L st0)); cycle 1.
  { split; [exact Hs|split; [|exact E2]]. intros x Hx. rewrite domain_insert, domain_numset_list_insert.
    right; right; apply IN_set, MEM_iff', Hx. }
  cbn [ac_post]. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
Qed.

Lemma eac_Break n st cst f live lt :
  eac_hyp f live lt (wordLang.Break n) st cst -> eac_concl f live lt (wordLang.Break n) st cst.
Proof.
  eac_start2. injection Hev as <- <-. cbn [ac_post].
  split; [reflexivity|split; [apply wser_sl|]].
  destruct (oEL n lt) as [[nm ex]|]; [|exact Logic.I]. rewrite locals_set_locals. exact Hs.
Qed.

Lemma eac_Continue n st cst f live lt :
  eac_hyp f live lt (wordLang.Continue n) st cst -> eac_concl f live lt (wordLang.Continue n) st cst.
Proof.
  eac_start2. injection Hev as <- <-. cbn [ac_post].
  split; [reflexivity|split; [apply wser_sl|]].
  destruct (oEL n lt) as [[nm ex]|]; [|exact Logic.I]. rewrite locals_set_locals. exact Hs.
Qed.

Lemma eac_Tick st cst f live lt :
  eac_hyp f live lt (@Tick a) st cst -> eac_concl f live lt (@Tick a) st cst.
Proof.
  eac_start2. destruct (clock st0 =? 0); injection Hev as <- <-; cbn [ac_post].
  - split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
  - split; [reflexivity|split; [apply wser_sl|]]. rewrite locals_set_locals. exact Hs.
Qed.

Lemma eac_LocValue r l1 st cst f live lt :
  eac_hyp f live lt (LocValue r l1) st cst -> eac_concl f live lt (LocValue r l1) st cst.
Proof.
  eac_start2. destruct (classical_dec _); [|err_case Hev Hr]. injection Hev as <- <-.
  cbn [ac_post]. split; [reflexivity|split; [wser|]].
  unfold set_var; cbn_ws. slr2 Hi2 Hs.
Qed.

Lemma eac_OpCurrHeap b dst src st cst f live lt :
  eac_hyp f live lt (OpCurrHeap b dst src) st cst -> eac_concl f live lt (OpCurrHeap b dst src) st cst.
Proof.
  eac_start2. cbn [word_exp the_words MAP List.map] in *. unfold get_var in *; rewrite !locals_set_locals.
  destruct (lookup src (locals st0)) as [[w|]|] eqn:E1; try err_case Hev Hr.
  rewrite (Hs src (Word w)) by (split; [in_solve|exact E1]).
  destruct (get_store CurrHeap st0) as [[w'|]|] eqn:E2; try err_case Hev Hr.
  destruct (OPTION_MAP Word _) as [x|] eqn:E3; [|err_case Hev Hr]. injection Hev as <- <-.
  rewrite get_store_set_locals, E2, E3.
  cbn [ac_post]. split; [reflexivity|split; [wser|]].
  unfold set_var; cbn_ws. slr2 Hi2 Hs.
Qed.

Lemma eac_CodeBufferWrite r1 r2 st cst f live lt :
  eac_hyp f live lt (CodeBufferWrite r1 r2) st cst -> eac_concl f live lt (CodeBufferWrite r1 r2) st cst.
Proof.
  eac_start2. unfold get_var in *; rewrite !locals_set_locals.
  assert (Hd : forall x, x IN domain live \/ x = r1 \/ x = r2 -> x IN domain (list_insert [r1; r2] live)).
  { intros x Hx. apply domain_list_insert. unfold is_true; cbn [MEM]. destruct Hx as [Hx|[ -> | -> ]].
    - right; exact Hx.
    - left. rewrite bd_true' by reflexivity. reflexivity.
    - left. rewrite (bd_true' (r2 = r2)) by reflexivity. apply orb_true_r. }
  destruct (lookup r1 (locals st0)) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (lookup r2 (locals st0)) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  rewrite (Hs r1 (Word w1)) by (split; [apply Hd; auto|exact E1]).
  rewrite (Hs r2 (Word w2)) by (split; [apply Hd; auto|exact E2]).
  destruct (buffer_write _ _ _); [|err_case Hev Hr]. injection Hev as <- <-.
  cbn [ac_post]. split; [reflexivity|split; [wser|]].
  cbn_ws. eapply strong_locals_rel_subset; split; [|exact Hs]. intros x Hx; apply Hd; auto.
Qed.

Lemma eac_DataBufferWrite r1 r2 st cst f live lt :
  eac_hyp f live lt (DataBufferWrite r1 r2) st cst -> eac_concl f live lt (DataBufferWrite r1 r2) st cst.
Proof.
  eac_start2. unfold get_var in *; rewrite !locals_set_locals.
  assert (Hd : forall x, x IN domain live \/ x = r1 \/ x = r2 -> x IN domain (list_insert [r1; r2] live)).
  { intros x Hx. apply domain_list_insert. unfold is_true; cbn [MEM]. destruct Hx as [Hx|[ -> | -> ]].
    - right; exact Hx.
    - left. rewrite bd_true' by reflexivity. reflexivity.
    - left. rewrite (bd_true' (r2 = r2)) by reflexivity. apply orb_true_r. }
  destruct (lookup r1 (locals st0)) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (lookup r2 (locals st0)) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  rewrite (Hs r1 (Word w1)) by (split; [apply Hd; auto|exact E1]).
  rewrite (Hs r2 (Word w2)) by (split; [apply Hd; auto|exact E2]).
  destruct (buffer_write _ _ _); [|err_case Hev Hr]. injection Hev as <- <-.
  cbn [ac_post]. split; [reflexivity|split; [wser|]].
  cbn_ws. eapply strong_locals_rel_subset; split; [|exact Hs]. intros x Hx; apply Hd; auto.
Qed.

Definition eac_IH (p : prog a) : Prop :=
  forall st cst f live lt, eac_hyp f live lt p st cst -> eac_concl f live lt p st cst.

Lemma evaluate_Seq_eq' (p1 p2 : prog a) st :
  evaluate (Seq p1 p2, st) =
  let '(res, s1) := evaluate (p1, st) in
  if bool_decide (res = NONE) then evaluate (p2, s1) else (res, s1).
Proof. rewrite (evaluate_eqn (Seq p1 p2) st); cbn [evaluate_body]. rewrite fix_clock_evaluate. reflexivity. Qed.

Lemma eac_MustTerminate p st cst f live lt :
  eac_IH p -> eac_hyp f live lt (MustTerminate p) st cst -> eac_concl f live lt (MustTerminate p) st cst.
Proof.
  intros IH (Hc & Heq & Hs). cbn [colouring_ok get_live] in Hc, Hs.
  set (st' := set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) st)).
  set (cst' := set_termdep (termdep st - 1) (set_clock (MustTerminate_limit a) cst)).
  destruct (IH st' cst' f live lt) as [perm Hp].
  { split; [exact Hc|split; [subst st' cst'; wser|exact Hs]]. }
  exists perm. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite termdep_set_permute.
  destruct (termdep st =? 0) eqn:Et; [left; reflexivity|].
  rewrite set_clock_set_permute, set_termdep_set_permute. fold st'.
  destruct (evaluate (p, set_permute perm st')) as [res rst] eqn:E.
  destruct Hp as [->|Hp]; [destruct (⌜_⌝); left; reflexivity|].
  destruct (⌜res = SOME TimeOut⌝) eqn:Eto; [left; reflexivity|right].
  rewrite evaluate_eqn; cbn [evaluate_body apply_colour].
  assert (Htd : termdep cst = termdep st) by (destruct Heq; destr_conj; congruence).
  assert (Hck : clock cst = clock st) by (destruct Heq; destr_conj; congruence).
  rewrite Htd, Et. fold cst'.
  destruct (evaluate (apply_colour f p, cst')) as [res' rcst] eqn:E'.
  destruct Hp as (<- & Hw & Hpost). rewrite Eto. split; [reflexivity|split].
  - unfold word_state_eq_rel in *; cbn_ws; destr_conj; repeat split; congruence.
  - destruct res as [[]|]; cbn [ac_post] in *; cbn_ws; exact Hpost.
Qed.

Lemma eac_Seq p1 p2 st cst f live lt :
  eac_IH p1 -> eac_IH p2 -> eac_hyp f live lt (Seq p1 p2) st cst -> eac_concl f live lt (Seq p1 p2) st cst.
Proof.
  intros IH1 IH2 (Hc & Heq & Hs). cbn [colouring_ok get_live] in Hc, Hs. cbv zeta in Hc.
  destruct Hc as (Hi & Hc2 & Hc1).
  destruct (IH1 st cst f (get_live p2 live lt) lt (conj Hc1 (conj Heq Hs))) as [perm1 Hp1].
  destruct (evaluate (p1, set_permute perm1 st)) as [r1 s1] eqn:E1.
  destruct Hp1 as [->|Hp1].
  { exists perm1. rewrite evaluate_Seq_eq', E1. rewrite bd_false' by discriminate. left; reflexivity. }
  destruct (evaluate (apply_colour f p1, cst)) as [r1' cs1] eqn:E1'.
  destruct Hp1 as (<- & Hw1 & Hpost1).
  destruct r1 as [r1|].
  - exists perm1. rewrite evaluate_Seq_eq', E1. rewrite bd_false' by discriminate. cbn beta iota zeta. right.
    cbn [apply_colour]. rewrite evaluate_Seq_eq', E1', bd_false' by discriminate. cbn beta iota zeta.
    split; [reflexivity|split; [exact Hw1|]]. destruct r1; exact Hpost1.
  - cbn [ac_post] in Hpost1.
    destruct (IH2 s1 cs1 f live lt (conj Hc2 (conj Hw1 Hpost1))) as [perm2 Hp2].
    pose proof (permute_swap_lemma p1 (set_permute perm1 st) perm2) as H3.
    rewrite E1 in H3. assert (Hne : (NONE : option (result a)) <> SOME Error) by discriminate.
    destruct (H3 Hne) as [perm3 E3]. rewrite set_permute_set_permute in E3.
    exists perm3. rewrite evaluate_Seq_eq'. rewrite E3. rewrite bd_true' by reflexivity.
    cbn [apply_colour]. rewrite evaluate_Seq_eq', E1', bd_true' by reflexivity. exact Hp2.
Qed.

Lemma eac_If cmp r ri p1 p2 st cst f live lt :
  eac_IH p1 -> eac_IH p2 -> eac_hyp f live lt (If cmp r ri p1 p2) st cst ->
  eac_concl f live lt (If cmp r ri p1 p2) st cst.
Proof.
  intros IH1 IH2 (Hc & Heq & Hs). cbn [colouring_ok get_live] in Hc, Hs. cbv zeta in Hc.
  destruct Hc as (Hi & Hc1 & Hc2).
  assert (Hs1 : strong_locals_rel f (domain (get_live p1 live lt)) (locals st) (locals cst))
    by (eapply strong_locals_rel_subset; split; [|exact Hs]; destruct ri; set_solve).
  assert (Hs2 : strong_locals_rel f (domain (get_live p2 live lt)) (locals st) (locals cst))
    by (eapply strong_locals_rel_subset; split; [|exact Hs]; destruct ri; set_solve).
  destruct (IH1 st cst f live lt (conj Hc1 (conj Heq Hs1))) as [perm1 Hp1].
  destruct (IH2 st cst f live lt (conj Hc2 (conj Heq Hs2))) as [perm2 Hp2].
  destruct (get_var r st) as [x|] eqn:Ex; [|exists perm1; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite get_var_set_permute, Ex; cbn beta iota zeta; left; reflexivity].
  destruct (get_var_imm ri st) as [y|] eqn:Ey; [|exists perm1; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey; cbn beta iota zeta; left; reflexivity].
  assert (Ex' : get_var (f r) cst = Some x) by (apply Hs; split; [destruct ri; in_solve|exact Ex]).
  assert (Ey' : get_var_imm (apply_colour_imm f ri) cst = Some y).
  { destruct ri as [r2|w]; cbn [apply_colour_imm get_var_imm] in *; [|exact Ey].
    apply Hs; split; [in_solve|exact Ey]. }
  destruct (word_cmp cmp x y) as [[]|] eqn:Ec.
  - exists perm1. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey, Ec.
    destruct (evaluate (p1, set_permute perm1 st)) as [res rst]. destruct Hp1 as [Hp1|Hp1]; [left; exact Hp1|right].
    rewrite evaluate_eqn; cbn [evaluate_body apply_colour]. rewrite Ex', Ey', Ec. exact Hp1.
  - exists perm2. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey, Ec.
    destruct (evaluate (p2, set_permute perm2 st)) as [res rst]. destruct Hp2 as [Hp2|Hp2]; [left; exact Hp2|right].
    rewrite evaluate_eqn; cbn [evaluate_body apply_colour]. rewrite Ex', Ey', Ec. exact Hp2.
  - exists perm1. rewrite evaluate_eqn; cbn [evaluate_body].
    rewrite get_var_set_permute, get_var_imm_set_permute, Ex, Ey, Ec. cbn beta iota zeta. left; reflexivity.
Qed.

Lemma eac_ShareInst op v e st cst f live lt :
  eac_hyp f live lt (ShareInst op v e) st cst -> eac_concl f live lt (ShareInst op v e) st cst.
Proof.
  eac_start2.
  destruct (word_exp st0 e) as [[ad|]|] eqn:Ee; try err_case Hev Hr.
  rewrite (apply_colour_exp_lemma st0 e (set_locals L st0) f (Word ad)); cycle 1.
  { split; [exact Ee|split; [exact Heq0|]]. eapply strong_locals_rel_subset; split; [|exact Hs].
    destruct (is_store_op op); set_solve. }
  destruct op; cbn [share_inst get_writes] in *;
    match type of Hs with context [is_store_op ?o] =>
      let E := fresh "Eso" in
      assert (E : is_store_op o = ltac:(let b := eval vm_compute in (is_store_op o) in exact b))
        by reflexivity; rewrite E in Hs, Hi1 end;
    unfold sh_mem_set_var, sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32,
      sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32 in *;
    autorewrite with lrl in *; unfold get_var in *; rewrite ?locals_set_locals in *;
    split_in Hev; try err_case Hev Hr; injection Hev as <- <-;
    repeat match goal with
           | E : lookup ?r (locals st0) = Some ?v |- context [lookup (f ?r) L] =>
               rewrite (Hs r v ltac:(split; [in_solve|exact E]))
           end;
    rw_eqs; cbn [ac_post];
    (split; [reflexivity|split; [wser|]]);
    first [reflexivity
          | cbn_ws; eapply strong_locals_rel_subset; split; [|exact Hs]; set_solve
          | cbn_ws; slr2 Hi2 Hs].
Qed.

Lemma eac_FFI fi p1 l1 p2 l2 names st cst f live lt :
  eac_hyp f live lt (FFI fi p1 l1 p2 l2 names) st cst ->
  eac_concl f live lt (FFI fi p1 l1 p2 l2 names) st cst.
Proof.
  eac_start2. unfold get_var in *; rewrite ?locals_set_locals in *.
  destruct (lookup l1 (locals st0)) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (lookup p1 (locals st0)) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (lookup l2 (locals st0)) as [[w3|]|] eqn:E3; try err_case Hev Hr.
  destruct (lookup p2 (locals st0)) as [[w4|]|] eqn:E4; try err_case Hev Hr.
  repeat match goal with
         | E : lookup ?r (locals st0) = Some ?v |- context [lookup (f ?r) L] =>
             rewrite (Hs r v ltac:(split; [in_solve|exact E]))
         end.
  destruct (cut_env names (locals st0)) as [env|] eqn:Ec; [|err_case Hev Hr].
  destruct (cut_env_lemma f names (locals st0) L env) as (y & Ey & Dy & Sy & Iy & Dx).
  { split; [|split; [exact Ec|]].
    - eapply INJ_less; split; [exact Hi1|]. set_solve.
    - eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  rewrite Ey. split_in Hev; try err_case Hev Hr; injection Hev as <- <-; rw_eqs; cbn [ac_post].
  all: split; [reflexivity|split; [wser|]];
    first [reflexivity | (cbn_ws; eapply strong_locals_rel_extend_aux; split; [|exact Sy];
                          rewrite Dx; intros x Hx; exact Hx)].
Qed.

Lemma eac_Install r1 r2 r3 r4 names st cst f live lt :
  eac_hyp f live lt (Install r1 r2 r3 r4 names) st cst ->
  eac_concl f live lt (Install r1 r2 r3 r4 names) st cst.
Proof.
  eac_start2.
  assert (Hd : forall x, x IN domain (union (FST names) (SND names)) \/ x = r1 \/ x = r2 \/ x = r3 \/ x = r4 ->
                 x IN domain (list_insert [r1; r2; r3; r4] (union (FST names) (SND names)))).
  { intros x Hx. apply domain_list_insert. rewrite MEM_iff'. cbn [In].
    destruct Hx as [Hx|Hx]; [right; exact Hx|left; intuition congruence]. }
  destruct (cut_env names (locals st0)) as [env|] eqn:Ec; [|err_case Hev Hr].
  destruct (cut_env_lemma f names (locals st0) L env) as (y & Ey & Dy & Sy & Iy & Dx).
  { split; [|split; [exact Ec|]].
    - eapply INJ_less; split; [exact Hi1|]. intros x Hx; apply Hd; left; rewrite domain_union; exact Hx.
    - eapply strong_locals_rel_subset; split; [|exact Hs]. intros x Hx; apply Hd; left; rewrite domain_union; exact Hx. }
  rewrite Ey. unfold get_var in *; rewrite ?locals_set_locals in *.
  destruct (lookup r1 (locals st0)) as [[w1|]|] eqn:E1; try err_case Hev Hr.
  destruct (lookup r2 (locals st0)) as [[w2|]|] eqn:E2; try err_case Hev Hr.
  destruct (lookup r3 (locals st0)) as [[w3|]|] eqn:E3; try err_case Hev Hr.
  destruct (lookup r4 (locals st0)) as [[w4|]|] eqn:E4; try err_case Hev Hr.
  rewrite (Hs r1 (Word w1)) by (split; [apply Hd; auto|exact E1]).
  rewrite (Hs r2 (Word w2)) by (split; [apply Hd; auto|exact E2]).
  rewrite (Hs r3 (Word w3)) by (split; [apply Hd; auto|exact E3]).
  rewrite (Hs r4 (Word w4)) by (split; [apply Hd; auto|exact E4]).
  split_in Hev; try err_case Hev Hr; injection Hev as <- <-; rw_eqs; cbn [ac_post].
  split; [reflexivity|split; [wser|]]. cbn_ws.
  apply strong_locals_rel_insert. split; [inj_less Hi2|].
  eapply strong_locals_rel_extend_aux. split; [|exact Sy]. rewrite Dx. intros x Hx; exact Hx.
Qed.

Lemma apply_nummaps_key_LN {B} f (names : num_map B) :
  apply_nummaps_key f (names, (LN : num_set)) = (apply_nummap_key f names, LN).
Proof. reflexivity. Qed.

Lemma evaluate_Loop_eq names (body : prog a) exit_names s :
  evaluate (Loop names body exit_names, s) =
  match cut_state (names, LN) s return option (result a) * state with
  | NONE => (SOME Error, s)
  | SOME s =>
      let '(res, s1) := evaluate (body, s) in
      if cont_loop res then
        (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
         else evaluate (Loop names body exit_names, dec_clock s1))
      else if bool_decide (res = SOME (Break 0)) then
        match cut_state (exit_names, LN) s1 with
        | NONE => (SOME Error, s1)
        | SOME s2 => (NONE, s2)
        end
      else (exit_loop res, s1)
  end.
Proof.
  rewrite evaluate_eqn at 1; cbn [evaluate_body]. destruct (cut_state _ s); [|reflexivity].
  rewrite fix_clock_evaluate. reflexivity.
Qed.

Lemma eac_Loop names body exit_names f live lt :
  eac_IH body -> forall st cst,
  eac_hyp f live lt (Loop names body exit_names) st cst ->
  eac_concl f live lt (Loop names body exit_names) st cst.
Proof.
  intros IH st. remember (N.to_nat (clock st)) as k eqn:Hk. revert st Hk.
  induction k as [k IHk] using (well_founded_induction lt_wf). intros st Hk cst (Hc & Heq & Hs).
  pose proof Hc as Hc0. cbn [colouring_ok get_live] in Hc, Hs. destruct Hc as (Hin & Hex & Hcb).
  destruct (cut_env (names, LN) (locals st)) as [env|] eqn:Ec.
  2:{ exists (permute st). rewrite evaluate_Loop_eq. unfold cut_state. rewrite locals_set_permute, Ec.
      left; reflexivity. }
  destruct (cut_env_lemma f (names, LN) (locals st) (locals cst) env) as (y & Ey & Dy & Sy & Iy & Dx).
  { cbn [FST SND fst snd]. split; [|split; [exact Ec|]].
    - eapply INJ_less; split; [exact Hin|]. set_solve.
    - eapply strong_locals_rel_subset; split; [|exact Hs]. set_solve. }
  rewrite apply_nummaps_key_LN in Ey.
  set (s := set_locals env st). set (cs := set_locals y cst).
  destruct (IH s cs f names ((names, exit_names) :: lt)) as [perm1 Hp1].
  { split; [exact Hcb|split; [subst s cs; apply word_state_eq_rel_locals, Heq|]].
    change (locals s) with env; change (locals cs) with y.
    eapply strong_locals_rel_extend_aux.

    split; [|exact Sy]. rewrite Dx. intros x Hx; exact Hx. }
  assert (Hcs : cut_state (apply_nummap_key f names, LN) cst = SOME cs) by (unfold cut_state; rewrite Ey; reflexivity).
  assert (Hst : forall p, cut_state (names, LN) (set_permute p st) = SOME (set_permute p s))
    by (intros p; unfold cut_state; rewrite locals_set_permute, Ec; reflexivity).
  destruct (evaluate (body, set_permute perm1 s)) as [r1 t1] eqn:E1.
  destruct Hp1 as [->|Hp1].
  { exists perm1. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. left; reflexivity. }
  destruct (evaluate (apply_colour f body, cs)) as [r1' t1'] eqn:E1'.
  destruct Hp1 as (<- & Hw1 & Hpost1).
  assert (Hck : clock t1' = clock t1) by (destruct Hw1; destr_conj; assumption).
  assert (Hclk : (clock t1 <= clock st)%N).
  { apply evaluate_clock in E1 as [E1 _]. rewrite clock_set_permute in E1. exact E1. }
  assert (Hcolour : evaluate (apply_colour f (Loop names body exit_names), cst) =
    let '(res, s1) := (r1, t1') in
    if cont_loop res then
      (if clock s1 =? 0 then (SOME TimeOut, flush_state true s1)
       else evaluate (apply_colour f (Loop names body exit_names), dec_clock s1))
    else if bool_decide (res = SOME (Break 0)) then
      match cut_state (apply_nummap_key f exit_names, LN) s1 with
      | NONE => (SOME Error, s1)
      | SOME s2 => (NONE, s2)
      end
    else (exit_loop res, s1)).
  { cbn [apply_colour]. rewrite evaluate_Loop_eq, Hcs, E1'. reflexivity. }
  (* the recursive case *)
  assert (Hrec : cont_loop r1 = true -> clock t1 <> 0 ->
            ac_post f names ((names, exit_names) :: lt) r1 t1 t1' ->
            eac_concl f live lt (Loop names body exit_names) st cst).
  { intros Hcl Hc1 Hpost.
    assert (Hpn : strong_locals_rel f (domain names) (locals t1) (locals t1')).
    { destruct r1 as [[]|]; cbn [cont_loop] in Hcl; try discriminate; cbn [ac_post] in Hpost; [|exact Hpost].
      apply N.eqb_eq in Hcl; subst. exact Hpost. }
    destruct (IHk (N.to_nat (clock (dec_clock t1))) ltac:(unfold dec_clock; cbn_ws; lia) (dec_clock t1) eq_refl
                (dec_clock t1')) as [perm2 Hp2].
    { split; [exact Hc0|split; [unfold dec_clock; wser|exact Hpn]]. }
    pose proof (permute_swap_lemma body (set_permute perm1 s) perm2) as H3. rewrite E1 in H3.
    assert (Hne : r1 <> SOME Error) by (destruct r1 as [[]|]; cbn in Hcl; congruence).
    destruct (H3 Hne) as [perm3 E3]. rewrite set_permute_set_permute in E3.
    exists perm3. rewrite Hcolour. rewrite evaluate_Loop_eq, Hst, E3, Hcl, clock_set_permute.
    destruct (clock t1 =? 0) eqn:Ez; [apply N.eqb_eq in Ez; contradiction|].
    rewrite Hck, Ez, dec_clock_set_permute. exact Hp2. }
  assert (Hzero : cont_loop r1 = true -> clock t1 = 0 ->
            eac_concl f live lt (Loop names body exit_names) st cst).
  { intros Hcl Hc1. exists perm1. rewrite Hcolour, evaluate_Loop_eq, Hst, E1, Hcl, Hck, Hc1, N.eqb_refl. cbn beta iota.
    right. split; [reflexivity|split; [unfold flush_state; wser|]].
    destruct r1 as [[]|]; cbn [ac_post]; try reflexivity; discriminate. }
  assert (Hloop : cont_loop r1 = true -> ac_post f names ((names, exit_names) :: lt) r1 t1 t1' ->
            eac_concl f live lt (Loop names body exit_names) st cst).
  { intros Hcl Hp. destruct (clock t1 =? 0) eqn:Ez; [apply N.eqb_eq in Ez; apply Hzero; assumption|].
    apply Hrec; [exact Hcl| |exact Hp]. apply N.eqb_neq; exact Ez. }
  destruct r1 as [[x ys|x y'|n|n| | |ou|]|].
  - (* Result *) exists perm1. rewrite Hcolour. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. try rewrite bd_false' by discriminate.
    cbn [exit_loop]. auto.
  - (* Exception *) exists perm1. rewrite Hcolour. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop exit_loop].
    rewrite bd_false' by discriminate. right. cbn beta iota. try rewrite bd_false' by discriminate.
    cbn [exit_loop]. auto.
  - (* Break *)
    destruct (n =? 0) eqn:En.
    + apply N.eqb_eq in En; subst n. exists perm1. rewrite Hcolour. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop].
      rewrite bd_true' by reflexivity. cbn beta iota. try rewrite bd_true' by reflexivity.
      cbn [ac_post oEL N.eqb] in Hpost1.
      destruct (cut_state (exit_names, LN) t1) as [t2|] eqn:Ec2; [|left; reflexivity]. right.
      unfold cut_state in Ec2 |- *. destruct (cut_env (exit_names, LN) (locals t1)) as [env2|] eqn:Ee2; [|discriminate].
      injection Ec2 as <-.
      destruct (cut_env_lemma f (exit_names, LN) (locals t1) (locals t1') env2) as (y2 & Ey2 & _ & Sy2 & _ & Dx2).
      { cbn [FST SND fst snd]. split; [|split; [exact Ee2|]].
        - eapply INJ_less; split; [exact Hex|]. set_solve.
        - eapply strong_locals_rel_subset; split; [|exact Hpost1]. set_solve. }
      rewrite apply_nummaps_key_LN in Ey2. rewrite Ey2. cbn [ac_post].
      split; [reflexivity|split; [apply word_state_eq_rel_locals, Hw1|]]. rewrite !locals_set_locals.
      eapply strong_locals_rel_extend_aux. split; [|exact Sy2]. rewrite Dx2. intros z Hz; exact Hz.
    + exists perm1. rewrite Hcolour. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop].
      rewrite bd_false' by (intros E; injection E as ->; discriminate). cbn beta iota.
      try rewrite bd_false' by (intros E; injection E as ->; discriminate). right. cbn [exit_loop].
      split; [reflexivity|split; [exact Hw1|]]. cbn [ac_post oEL] in *. rewrite En in Hpost1. exact Hpost1.
  - (* Continue *)
    destruct (n =? 0) eqn:En.
    + apply Hloop; [cbn [cont_loop]; exact En|exact Hpost1].
    + exists perm1. rewrite Hcolour. rewrite evaluate_Loop_eq, Hst, E1. cbn [cont_loop]. rewrite En.
      rewrite bd_false' by discriminate. cbn beta iota. try rewrite bd_false' by discriminate. right. cbn [exit_loop].
      split; [reflexivity|split; [exact Hw1|]]. cbn [ac_post oEL] in *. rewrite En in Hpost1. exact Hpost1.
  - first [apply Hloop; [reflexivity|exact Hpost1]
         | exists perm1; rewrite Hcolour, evaluate_Loop_eq, Hst, E1; cbn [cont_loop];
           rewrite ?bd_false' by discriminate; cbn beta iota; try rewrite bd_false' by discriminate;
           first [left; reflexivity|right; cbn [exit_loop]; auto]].
  - first [apply Hloop; [reflexivity|exact Hpost1]
         | exists perm1; rewrite Hcolour, evaluate_Loop_eq, Hst, E1; cbn [cont_loop];
           rewrite ?bd_false' by discriminate; cbn beta iota; try rewrite bd_false' by discriminate;
           first [left; reflexivity|right; cbn [exit_loop]; auto]].
  - first [apply Hloop; [reflexivity|exact Hpost1]
         | exists perm1; rewrite Hcolour, evaluate_Loop_eq, Hst, E1; cbn [cont_loop];
           rewrite ?bd_false' by discriminate; cbn beta iota; try rewrite bd_false' by discriminate;
           first [left; reflexivity|right; cbn [exit_loop]; auto]].
  - first [apply Hloop; [reflexivity|exact Hpost1]
         | exists perm1; rewrite Hcolour, evaluate_Loop_eq, Hst, E1; cbn [cont_loop];
           rewrite ?bd_false' by discriminate; cbn beta iota; try rewrite bd_false' by discriminate;
           first [left; reflexivity|right; cbn [exit_loop]; auto]].
  - first [apply Hloop; [reflexivity|exact Hpost1]
         | exists perm1; rewrite Hcolour, evaluate_Loop_eq, Hst, E1; cbn [cont_loop];
           rewrite ?bd_false' by discriminate; cbn beta iota; try rewrite bd_false' by discriminate;
           first [left; reflexivity|right; cbn [exit_loop]; auto]].
Qed.

Lemma pop_env_set_locals' l (s : state) : pop_env (set_locals l s) = pop_env s.
Proof. unfold pop_env; cbn_ws. destruct (stack s) as [|[? ? ? [[? ?]|]] ?]; reflexivity. Qed.

Lemma pop_env_set_stack_some (r : state) (st' : list (stack_frame a)) (y' : state) :
  s_val_eq (stack r) st' -> pop_env r = SOME y' -> exists y'', pop_env (set_stack st' r) = SOME y''.
Proof.
  intros Hv Hp. unfold pop_env in *. rewrite stack_set_stack.
  destruct (stack r) as [|[m e0 e h] xs]; [discriminate|].
  destruct st' as [|[m' e0' e' h'] xs']; cbn [s_val_eq] in Hv; [contradiction|].
  destruct Hv as [_ Hf]. apply s_frame_val_eq_def2 in Hf as (_ & <- & <-).
  destruct h as [[? ?]|]; eexists; reflexivity.
Qed.

(** Two states equal except in their locals, permutation and stack. *)
Lemma state_eq_except (x y : state) :
  fp_regs y = fp_regs x -> store y = store x -> locals_size y = locals_size x ->
  stack_limit y = stack_limit x -> stack_max y = stack_max x ->
  state_stack_size y = state_stack_size x -> memory y = memory x -> mdomain y = mdomain x ->
  sh_mdomain y = sh_mdomain x -> gc_fun y = gc_fun x -> handler y = handler x ->
  clock y = clock x -> code y = code x -> ffi y = ffi x -> be y = be x -> termdep y = termdep x ->
  compile y = compile x -> compile_oracle y = compile_oracle x -> code_buffer y = code_buffer x ->
  data_buffer y = data_buffer x ->
  y = set_permute (permute y) (set_locals (locals y) (set_stack (stack y) x)).
Proof. intros; destruct x, y; cbn in *; subst; reflexivity. Qed.

Lemma union_fromAList_rel f (lx ly : list (N * word_loc a)) (x0 y1 : num_map (word_loc a)) S :
  MAP SND lx = MAP SND ly -> MAP FST ly = MAP f (MAP FST lx) ->
  strong_locals_rel f (domain x0) x0 y1 -> INJ f (domain x0 UNION set (MAP FST lx)) UNIV ->
  strong_locals_rel f S (union (fromAList lx) (fromAList (toAList x0)))
                        (union (fromAList ly) (fromAList (toAList y1))).
Proof.
  intros Hsnd Hfst Hs Hi n v [_ Hl]. rewrite lookup_union, !lookup_fromAList, !ALOOKUP_toAList in *.
  assert (Hlx : lx = ZIP (MAP FST lx, MAP SND lx)).
  { rewrite ZIP_combine'. clear. induction lx as [|[k w] lx IH]; [reflexivity|]. cbn; f_equal; exact IH. }
  assert (Hly : ly = ZIP (MAP f (MAP FST lx), MAP SND lx)).
  { rewrite <- Hfst, Hsnd, ZIP_combine'. clear. induction ly as [|[k w] ly IH]; [reflexivity|]. cbn; f_equal; exact IH. }
  assert (Hn : forall (P : Prop), (n IN domain x0 -> P) -> (In n (MAP FST lx) -> P) -> P).
  { intros P H1 H2. destruct (ALOOKUP lx n) as [w|] eqn:E.
    - apply H2. apply ALOOKUP_In, (in_map fst) in E. exact E.
    - apply H1, IN_domain_iff. exists v; exact Hl. }
  assert (Hk : ALOOKUP lx n = ALOOKUP ly (f n)).
  { apply Hn; intros Hn'; rewrite Hly; rewrite Hlx at 1; apply ALOOKUP_key_remap_INJ; (split;
      [eapply INJ_less; split; [exact Hi|]; intros z [->|Hz]; [|right; exact Hz];
       first [left; exact Hn'|right; apply IN_set; exact Hn']
      |rewrite !LENGTH_MAP'; reflexivity]). }
  rewrite <- Hk. destruct (ALOOKUP lx n) as [w|]; [exact Hl|]. apply Hs. split; [|exact Hl].
  apply IN_domain_iff; eauto.
Qed.

Lemma eac_Alloc n names st cst f live lt :
  eac_hyp f live lt (Alloc n names) st cst -> eac_concl f live lt (Alloc n names) st cst.
Proof.
  intros (Hc & Heq & Hs). cbn [colouring_ok get_live get_writes] in Hc, Hs. cbv zeta in Hc.
  destruct Hc as [Hi1 Hi2]. destruct names as [n1 n2]. cbn [FST SND fst snd] in *.
  destruct (get_var n st) as [[w|]|] eqn:Eg;
    try (exists (permute st); rewrite evaluate_eqn; cbn [evaluate_body]; rewrite get_var_set_permute, Eg;
         left; reflexivity).
  destruct (cut_envs (n1, n2) (locals st)) as [[x0 x1]|] eqn:Ec;
    [|exists (permute st); rewrite evaluate_eqn; cbn [evaluate_body]; rewrite get_var_set_permute, Eg;
      unfold alloc; rewrite locals_set_permute, Ec; left; reflexivity].
  destruct (cut_envs_lemma f n1 n2 (locals st) (locals cst) x0 x1) as
    (y1 & y2 & Ecy & D1 & D2 & S1 & S2 & I1 & I2 & X1 & X2).
  { split; [inj_less Hi1|split; [inj_less Hi1|split; [exact Ec|split]]];
      eapply strong_locals_rel_subset; (split; [|exact Hs]); set_solve. }
  set (sst := set_store AllocSize (Word w) st). set (scst := set_store AllocSize (Word w) cst).
  destruct (push_env_s_val_eq sst scst x1 y2 x0 y1 f None None (permute cst)) as [perm [Hpe Hsv]].
  { unfold word_state_eq_rel in Heq; destr_conj; subst sst scst; cbn_ws.
    repeat (split; [first [congruence|rewrite X2; exact D2|rewrite X2; exact I2|rewrite X1; exact D1|rewrite X1; exact I1]|]).
    split; [rewrite X2; exact S2|reflexivity]. }
  exists perm. rewrite evaluate_eqn; cbn [evaluate_body]. rewrite get_var_set_permute, Eg.
  assert (Eg' : get_var (f n) cst = SOME (Word w)) by (apply Hs; split; [in_solve|exact Eg]).
  unfold alloc. rewrite locals_set_permute, Ec, set_store_set_permute. fold sst.
  set (st' := push_env (x0, x1) NONE (set_permute perm sst)) in *.
  destruct (gc st') as [x|] eqn:Egc; [|left; reflexivity].
  destruct (pop_env x) as [xx|] eqn:Epx; [|left; reflexivity].
  set (cst' := push_env (y1, y2) NONE scst) in *.
  change (permute scst) with (permute cst) in *.
  destruct (env_to_list y2 (permute cst)) as [l pc] eqn:El.
  destruct (env_to_list x1 perm) as [l' pc'] eqn:El'.
  destruct Hpe as (Hpc & Hml & Hinj).
  pose proof Heq as Heq'. unfold word_state_eq_rel in Heq'.
  assert (Hst' : st' = set_permute pc' (set_stack_max (OPTION_MAP2 MAX (stack_max st)
            (stack_size (StackFrame (locals_size st) (toAList x0) l' NONE :: stack st)))
            (set_stack (StackFrame (locals_size st) (toAList x0) l' NONE :: stack st) (set_permute perm sst)))).
  { subst st'. unfold push_env. cbn [FST SND fst snd]. rewrite permute_set_permute, El'. reflexivity. }
  assert (Hcst' : cst' = set_permute pc (set_stack_max (OPTION_MAP2 MAX (stack_max cst)
            (stack_size (StackFrame (locals_size cst) (toAList y1) l NONE :: stack cst)))
            (set_stack (StackFrame (locals_size cst) (toAList y1) l NONE :: stack cst) scst))).
  { subst cst'. unfold push_env. cbn [FST SND fst snd]. subst scst. cbn_ws. rewrite El. reflexivity. }
  assert (Hss : stack_size (StackFrame (locals_size st) (toAList x0) l' NONE :: stack st) =
                stack_size (StackFrame (locals_size cst) (toAList y1) l NONE :: stack cst)).
  { apply s_val_eq_stack_size. rewrite Hst', Hcst' in Hsv. cbn_ws. exact Hsv. }
  destruct (gc_s_val_eq_gen st' cst' x) as (y & Egy & Hv2 & Hk2 & Hm2 & Hstore2 & Hsz2 & Hsm2 & Hsl2).
  { rewrite Hst', Hcst'. subst sst scst. cbn_ws. destr_conj.
    repeat (split; [congruence|]). split; [rewrite Hst', Hcst' in Hsv; cbn_ws; exact Hsv|].
    split; [congruence|]. split; [rewrite Hss; congruence|]. split; [congruence|].
    rewrite <- Hst'. exact Egc. }
  pose proof (gc_frame _ _ Egc) as Fx. pose proof (gc_frame _ _ Egy) as Fy.
  pose proof (gc_s_key_eq _ _ Egc) as Kx.
  assert (Hyx : y = set_permute (permute y) (set_locals (locals y) (set_stack (stack y) x))).
  { rewrite Hst', Hcst' in *. subst sst scst. cbn_ws. destr_conj.
    apply state_eq_except; congruence. }
  destruct (pop_env_set_stack_some x (stack y) xx Hv2 Epx) as [yy0 Epy0].
  assert (Epy : pop_env y = SOME (set_permute (permute y) yy0)).
  { rewrite Hyx, pop_env_set_permute, pop_env_set_locals', Epy0. reflexivity. }
  (* the stacks *)
  rewrite Hst' in Kx. rewrite Hcst' in Hk2. cbn_ws.
  unfold pop_env in Epx, Epy0. rewrite stack_set_stack in Epy0.
  destruct (stack x) as [|[mx ex0 lx hx] rx] eqn:Esx; [discriminate|].
  destruct (stack y) as [|[my ey0 ly hy] ry] eqn:Esy; [contradiction|].
  cbn [s_key_eq s_val_eq] in Kx, Hk2, Hv2. destruct Kx as [Kx Kfx], Hk2 as [Hk2 Kfy], Hv2 as [Hv2 Vf].
  apply s_frame_key_eq_def2 in Kfx as (Kx1 & <- & <- & <-).
  apply s_frame_key_eq_def2 in Kfy as (Ky1 & <- & <- & <-).
  apply s_frame_val_eq_def2 in Vf as (Vf1 & _ & _).
  injection Epx as Exx. injection Epy0 as Eyy.
  assert (Hrr : ry = rx).
  { symmetry; apply s_val_and_key_eq; split; [exact Hv2|].
    apply (s_key_eq_trans _ (stack st)); split; [apply s_key_eq_sym; exact Kx|].
    replace (stack st) with (stack cst) by (destr_conj; congruence). exact Hk2. }
  subst ry.
  assert (Hw : word_state_eq_rel xx (set_permute (permute y) yy0)).
  { subst xx yy0. unfold word_state_eq_rel; cbn_ws. destr_conj. repeat split; congruence. }
  assert (Hl : strong_locals_rel f (domain live) (locals xx) (locals (set_permute (permute y) yy0))).
  { subst xx yy0. cbn_ws. apply union_fromAList_rel.
    - exact Vf1.
    - rewrite <- Ky1, <- Kx1. symmetry; apply key_map_implies; exact Hml.
    - rewrite X1; exact S1.
    - pose proof (env_to_list_keys x1 perm) as Hk. rewrite El' in Hk. rewrite <- Kx1, Hk, X1, X2.
      eapply INJ_less; split; [exact Hi1|]. set_solve. }
  pose proof Hw as Hw'. destruct Hw' as (_ & Hstore & _).
  assert (Hcol : evaluate (apply_colour f (Alloc n (n1, n2)), cst) =
                 match get_store AllocSize (set_permute (permute y) yy0) with
                 | NONE => (SOME Error, set_permute (permute y) yy0)
                 | SOME w0 =>
                     match has_space w0 (set_permute (permute y) yy0) with
                     | NONE => (SOME Error, set_permute (permute y) yy0)
                     | SOME true => (NONE, set_permute (permute y) yy0)
                     | SOME false => (SOME NotEnoughSpace, flush_state true (set_permute (permute y) yy0))
                     end
                 end).
  { rewrite evaluate_eqn; cbn [evaluate_body apply_colour]. rewrite Eg'. unfold alloc.
    rewrite Ecy. fold scst. fold cst'. rewrite Egy, Epy. reflexivity. }
  rewrite Hcol. unfold get_store, has_space, get_store in *. rewrite Hstore.
  destruct (FLOOKUP (store xx) AllocSize) as [ws|]; [|left; reflexivity].
  destruct ws as [ws|]; [|left; reflexivity].
  destruct (FLOOKUP (store xx) NextFree) as [[nf|]|]; try (left; reflexivity).
  destruct (FLOOKUP (store xx) TriggerGC) as [[tg|]|]; try (left; reflexivity).
  destruct (_ <=? _); right; cbn [ac_post].
  - auto.
  - split; [reflexivity|split; [unfold flush_state; wser|reflexivity]].
Qed.

Lemma bad_dest_args_MAP (f : N -> N) dest args :
  bad_dest_args dest (MAP f args) = bad_dest_args dest args.
Proof. unfold bad_dest_args; destruct args; reflexivity. Qed.

Lemma eac_Call_None dest args h st cst f live lt :
  eac_hyp f live lt (Call None dest args h) st cst -> eac_concl f live lt (Call None dest args h) st cst.
Proof.
  eac_start2.
  destruct (get_vars args st0) as [xs|] eqn:Eg; [|err_case Hev Hr].
  rewrite (strong_locals_rel_get_vars args xs f (domain (numset_list_insert args LN)) st0 (set_locals L st0))
    by (split; [exact Hs|split; [intros x Hx; rewrite domain_numset_list_insert; right; apply IN_set, MEM_iff', Hx|exact Eg]]).
  rewrite bad_dest_args_MAP. destruct (bad_dest_args dest args); [err_case Hev Hr|].
  cbn [add_ret_loc] in *. autorewrite with lrl.
  destruct (find_code dest xs (code st0) (state_stack_size st0)) as [[args1 [prog ss]]|] eqn:Ef;
    [|err_case Hev Hr].
  destruct h as [[hv [hp [hl1 hl2]]]|].
  - rewrite bd_false' in Hev by discriminate. err_case Hev Hr.
  - rewrite bd_true' in Hev |- * by reflexivity.
    destruct (clock st0 =? 0).
    + injection Hev as <- <-. cbn [ac_post]. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    + rewrite ?dec_clock_set_locals, ?call_env_set_locals.
      destruct (evaluate (prog, call_env args1 ss (dec_clock st0))) as [r1 s1].
      destruct (bad_fun_return r1) eqn:Eb; [err_case Hev Hr|]. injection Hev as <- <-.
      split; [reflexivity|split; [apply word_state_eq_rel_refl|]].
      destruct r1 as [[]|]; cbn [ac_post bad_fun_return] in *; try reflexivity; discriminate.
Qed.

(** The continuation of a returning [Call] after the callee's body. *)
Definition call_cont (n : list N) (rh : prog a) (l1 l2 : N)
    (h : option (N * (prog a * (N * N)))) (envs : num_map (word_loc a) * num_map (word_loc a))
    (r : option (result a) * state) : option (result a) * state :=
  match r with
  | (SOME (Result x ys), s2) =>
      if negb (bool_decide (x = Loc l1 l2)) || negb (LENGTH ys =? LENGTH n) then (SOME Error, s2)
      else
        match pop_env s2 with
        | NONE => (SOME Error, s2)
        | SOME s1 =>
            if ⌜domain (locals s1) = domain (FST envs) UNION domain (SND envs)⌝
            then evaluate (rh, set_vars n ys s1)
            else (SOME Error, s1)
        end
  | (SOME (Exception x y), s2) =>
      match h with
      | NONE => (SOME (Exception x y), s2)
      | SOME (n', (h', (l1', l2'))) =>
          if negb (bool_decide (x = Loc l1' l2')) then (SOME Error, s2)
          else if ⌜domain (locals s2) = domain (FST envs) UNION domain (SND envs)⌝
          then evaluate (h', set_var n' y s2)
          else (SOME Error, s2)
      end
  | (NONE, s) => (SOME Error, s)
  | (SOME (Break _), s) => (SOME Error, s)
  | (SOME (Continue _), s) => (SOME Error, s)
  | res => res
  end.

Lemma evaluate_Call_Some_eq n names rh l1 l2 dest args h (s : state) xs args1 prog ss envs :
  get_vars args s = SOME xs -> bad_dest_args dest args = false ->
  find_code dest (Loc l1 l2 :: xs) (code s) (state_stack_size s) = SOME (args1, (prog, ss)) ->
  (⌜domain (FST names) = {}⌝ || negb (ALL_DISTINCT n)) = false ->
  cut_envs names (locals s) = SOME envs -> (clock s =? 0) = false ->
  evaluate (Call (Some (n, (names, (rh, (l1, l2))))) dest args h, s) =
  call_cont n rh l1 l2 h envs (evaluate (prog, call_env args1 ss (push_env envs h (dec_clock s)))).
Proof.
  intros E1 E2 E3 E4 E5 E6. rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc].
  rewrite E1, E2, E3, E4, E5, E6. rewrite fix_clock_evaluate.
  destruct (evaluate (prog, _)) as [[[]|] s2]; reflexivity.
Qed.

Lemma stack_max_call_env_push_env args1 ss envs envs' (h h' : option (N * (prog a * (N * N)))) (s t : state) :
  stack_max s = stack_max t -> stack s = stack t -> locals_size s = locals_size t ->
  (h = None <-> h' = None) ->
  stack_max (call_env args1 ss (push_env envs h s)) = stack_max (call_env args1 ss (push_env envs' h' t)).
Proof.
  intros H1 H2 H3 H4. destruct h as [[? [? [? ?]]]|], h' as [[? [? [? ?]]]|];
    try (exfalso; destruct H4 as [H4 H5]; first [specialize (H5 eq_refl)|specialize (H4 eq_refl)]; discriminate);
    unfold call_env, push_env; destruct (env_to_list _ _), (env_to_list _ _); cbn_ws;
    rewrite H1, H2, H3; reflexivity.
Qed.

Definition colour_h (f : N -> N) (h : option (N * (prog a * (N * N)))) : option (N * (prog a * (N * N))) :=
  match h with
  | None => None
  | Some (v, (prog, (l1, l2))) => Some (f v, (apply_colour f prog, (l1, l2)))
  end.

Lemma eac_err p st cst f live lt perm :
  FST (evaluate (p, set_permute perm st)) = SOME Error -> eac_concl f live lt p st cst.
Proof.
  intros H. exists perm. destruct (evaluate (p, set_permute perm st)) as [r t]. cbn in H. left; exact H.
Qed.

Lemma dom_union_frame (ly l : list (N * word_loc a)) (y1 y2 : num_map (word_loc a)) p pc :
  MAP FST l = MAP FST ly -> env_to_list y2 p = (l, pc) ->
  domain (union (fromAList ly) (fromAList (toAList y1))) = domain y1 UNION domain y2.
Proof.
  intros Hm El. pose proof (env_to_list_keys y2 p) as Hk. rewrite El in Hk.
  rewrite domain_union, domain_fromAList_toAList, domain_fromAList, <- Hk, Hm.
  apply set_ext; intros x. unfold pred_set.UNION. cbn beta.
  change (set (MAP FST ly) x) with (x IN set (MAP FST ly)).
  rewrite IN_set, MEM_iff'. unfold pred_set.IN. tauto.
Qed.

Lemma pair_list_eq {A B} (l1 l2 : list (A * B)) :
  MAP FST l1 = MAP FST l2 -> MAP SND l1 = MAP SND l2 -> l1 = l2.
Proof.
  revert l2; induction l1 as [|[x y] l1 IH]; intros [|[x' y'] l2] H1 H2; cbn in *; try discriminate; [reflexivity|].
  injection H1 as -> H1. injection H2 as -> H2. f_equal. apply IH; assumption.
Qed.

Lemma eac_Call_Some n names rh l1 l2 dest args h st cst f live lt :
  eac_IH rh -> (match h with Some (_, (p, _)) => eac_IH p | None => True end) ->
  eac_hyp f live lt (Call (Some (n, (names, (rh, (l1, l2))))) dest args h) st cst ->
  eac_concl f live lt (Call (Some (n, (names, (rh, (l1, l2))))) dest args h) st cst.
Proof.
  intros IHr IHh (Hc & Heq & Hs). cbn [colouring_ok get_live] in Hc, Hs. cbv zeta in Hc.
  destruct Hc as (Hi1 & Hi2 & Hcr & Hch).
  destruct names as [n1 n2]; cbn [FST SND fst snd] in *.
  pose proof Heq as Heq'. destruct Heq' as (Hfp & Hstore & Hls & Hstack & Hsl & Hsm & Hss & Hmem & Hmd & Hsmd
    & Hgc & Hh & Hclk & Hcode & Hffi & Hbe & Htd & Hcomp & Hco & Hcb & Hdb).
  (* the prefix of the evaluation *)
  destruct (get_vars args st) as [xs|] eqn:Eg.
  2:{ apply (eac_err _ _ _ _ _ _ (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body].
      rewrite Eg. reflexivity. }
  destruct (bad_dest_args dest args) eqn:Ebd.
  { apply (eac_err _ _ _ _ _ _ (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body].
    rewrite Eg, Ebd. reflexivity. }
  destruct (find_code dest (Loc l1 l2 :: xs) (code st) (state_stack_size st)) as [[args1 [prog ss]]|] eqn:Ef.
  2:{ apply (eac_err _ _ _ _ _ _ (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body add_ret_loc].
      rewrite Eg, Ebd, Ef. reflexivity. }
  destruct (⌜domain n1 = {}⌝ || negb (ALL_DISTINCT n)) eqn:Ecd.
  { apply (eac_err _ _ _ _ _ _ (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body add_ret_loc].
    rewrite Eg, Ebd, Ef. cbn [FST fst]. rewrite Ecd. reflexivity. }
  destruct (cut_envs (n1, n2) (locals st)) as [[x0 x1]|] eqn:Ec.
  2:{ apply (eac_err _ _ _ _ _ _ (permute st)). rewrite set_permute_permute, evaluate_eqn; cbn [evaluate_body add_ret_loc].
      rewrite Eg, Ebd, Ef. cbn [FST fst]. rewrite Ecd, Ec. reflexivity. }
  (* the coloured prefix *)
  assert (Eg' : get_vars (MAP f args) cst = SOME xs).
  { apply (strong_locals_rel_get_vars args xs f (domain (union (union n1 n2) (numset_list_insert args LN))) st cst).
    split; [exact Hs|split; [|exact Eg]]. intros x Hx. rewrite domain_union, domain_numset_list_insert.
    right; right; apply IN_set, MEM_iff', Hx. }
  assert (Ebd' : bad_dest_args dest (MAP f args) = false) by (rewrite bad_dest_args_MAP; exact Ebd).
  assert (Ef' : find_code dest (Loc l1 l2 :: xs) (code cst) (state_stack_size cst) = SOME (args1, (prog, ss)))
    by (rewrite Hcode, Hss; exact Ef).
  assert (Ecd' : (⌜domain (FST (apply_nummaps_key f (n1, n2))) = {}⌝ || negb (ALL_DISTINCT (MAP f n))) = false).
  { apply orb_false_iff in Ecd as [Ecd1 Ecd2]. apply orb_false_iff. split.
    - apply bd_false'. cbn [apply_nummaps_key FST fst]. fold (apply_nummap_key f n1).
      rewrite apply_nummap_key_domain. intros E. rewrite bd_true' in Ecd1; [discriminate|].
      apply set_ext; intros x; split; [|intros []]. intros Hx.
      assert (Hfx : f x IN IMAGE f (domain n1)) by (exists x; split; [reflexivity|exact Hx]).
      rewrite E in Hfx. destruct Hfx.
    - apply Bool.negb_false_iff in Ecd2. apply Bool.negb_false_iff.
      apply ALL_DISTINCT_iff' in Ecd2. apply ALL_DISTINCT_iff'. apply NoDup_map_inj; [exact Ecd2|].
      intros x y Hx Hy E. destruct Hi2 as [_ Hinj]. apply Hinj; [|exact E].
      rewrite domain_numset_list_insert. split; right; apply IN_set; assumption. }
  destruct (cut_envs_lemma f n1 n2 (locals st) (locals cst) x0 x1) as
    (y1 & y2 & Ecy & D1 & D2 & S1 & S2 & I1 & I2 & X1 & X2).
  { split; [inj_less Hi1|split; [inj_less Hi1|split; [exact Ec|split]]];
      eapply strong_locals_rel_subset; (split; [|exact Hs]); set_solve. }
  assert (Hcolour : (clock cst =? 0) = false ->
    evaluate (apply_colour f (Call (Some (n, ((n1, n2), (rh, (l1, l2))))) dest args h), cst) =
    call_cont (MAP f n) (apply_colour f rh) l1 l2 (colour_h f h) (y1, y2)
      (evaluate (prog, call_env args1 ss (push_env (y1, y2) (colour_h f h) (dec_clock cst))))).
  { intros Hz. exact (evaluate_Call_Some_eq (MAP f n) (apply_nummaps_key f (n1, n2)) (apply_colour f rh) l1 l2 dest (MAP f args) (colour_h f h) cst xs args1 prog ss (y1, y2) Eg' Ebd' Ef' Ecd' Ecy Hz). }
  destruct (clock st =? 0) eqn:Eck.
  { exists (permute st). rewrite set_permute_permute.
    rewrite evaluate_eqn; cbn [evaluate_body add_ret_loc]. rewrite Eg, Ebd, Ef. cbn [FST fst].
    rewrite Ecd, Ec, Eck. cbn beta iota. right.
    rewrite evaluate_eqn; cbn [evaluate_body apply_colour add_ret_loc]. rewrite Eg', Ebd', Ef'.
    rewrite Ecd', Ecy, Hclk, Eck. cbn beta iota. cbn [ac_post]. fold (colour_h f h).
    split; [reflexivity|split; [|reflexivity]].
    unfold flush_state; cbn_ws. unfold word_state_eq_rel; cbn_ws.
    rewrite (stack_max_call_env_push_env args1 ss (y1, y2) (x0, x1) (colour_h f h) h cst st) by
      (first [assumption | destruct h as [[? [? [? ?]]]|]; cbn; split; intros; congruence]).
    repeat split; congruence. }
  set (s' := dec_clock st). set (cs' := dec_clock cst).
  destruct (push_env_s_val_eq s' cs' x1 y2 x0 y1 f h (colour_h f h) (fun k => permute cst (k + 1)))
    as [P0 [Hpe Hsv]].
  { subst s' cs'. unfold dec_clock; cbn_ws.
    split; [congruence|split; [congruence|split; [congruence|]]].
    rewrite X2, X1. split; [exact D2|split; [rewrite <- X2; exact I2|split; [exact D1|split; [rewrite <- X1; exact I1|split; [exact S2|]]]]].
    destruct h as [[? [? [? ?]]]|]; cbn; auto. }
  set (st2 := call_env args1 ss (push_env (x0, x1) h (set_permute P0 s'))).
  set (cst2 := call_env args1 ss (push_env (y1, y2) (colour_h f h) cs')).
  change (permute cs') with (permute cst) in Hpe.
  destruct (env_to_list y2 (permute cst)) as [l pc] eqn:El.
  destruct (env_to_list x1 P0) as [l' pc'] eqn:El'.
  destruct Hpe as (Hpc & Hml & Hinj).
  assert (Hpc2 : pc = fun k => permute cst (k + 1)) by (unfold env_to_list in El; injection El as _ <-; reflexivity).
  assert (Hst2 : stack st2 = StackFrame (locals_size st) (toAList x0) l'
            (match h with None => None | Some (_, (_, (a1, a2))) => Some (handler st, (a1, a2)) end) :: stack st).
  { subst st2 s'. unfold call_env, push_env. destruct h as [[? [? [? ?]]]|]; cbn [FST SND fst snd];
      rewrite permute_set_permute, El'; reflexivity. }
  assert (Hcst2 : stack cst2 = StackFrame (locals_size st) (toAList y1) l
            (match h with None => None | Some (_, (_, (a1, a2))) => Some (handler st, (a1, a2)) end) :: stack st).
  { subst cst2 cs'. unfold call_env, push_env. destruct h as [[? [? [? ?]]]|]; cbn [FST SND fst snd colour_h];
      unfold dec_clock; cbn_ws; rewrite El; cbn_ws; rewrite Hls, Hstack, ?Hh; reflexivity. }
  assert (Hsv2 : s_val_eq (stack st2) (stack cst2)).
  { subst st2 cst2. unfold call_env. cbn_ws. exact Hsv. }
  assert (Hcs2 : cst2 = set_stack (stack cst2) st2).
  { pose proof (s_val_eq_stack_size _ _ Hsv2) as Hsz. rewrite Hst2, Hcst2 in Hsz.
    apply state_component_equality. repeat split.
    all: try (rewrite stack_set_stack; reflexivity).
    all: subst st2 cst2 s' cs'; unfold call_env, push_env, dec_clock;
      destruct h as [[? [? [? ?]]]|]; cbn [FST SND fst snd colour_h]; cbn_ws; rewrite ?El, ?El'; cbn_ws.
    all: first [congruence | rewrite Hsm, Hstack, ?Hls; rewrite Hsz; reflexivity
               | rewrite Hsm, Hstack, ?Hls; rewrite <- Hsz; reflexivity]. }
  assert (EQ1 : forall q, evaluate (Call (Some (n, ((n1, n2), (rh, (l1, l2))))) dest args h,
                                    set_permute (perm_cons (P0 0) q) st) =
                          call_cont n rh l1 l2 h (x0, x1) (evaluate (prog, set_permute q st2))).
  { intros q. rewrite (evaluate_Call_Some_eq n (n1, n2) rh l1 l2 dest args h _ xs args1 prog ss (x0, x1));
      rewrite ?get_vars_set_permute, ?code_set_permute, ?state_stack_size_set_permute,
              ?locals_set_permute, ?clock_set_permute; try assumption.
    f_equal. f_equal. rewrite dec_clock_set_permute. fold s'.
    replace (set_permute (perm_cons (P0 0) q) s') with
      (set_permute (perm_cons (permute (set_permute P0 s') 0) q) (set_permute P0 s'))
      by (rewrite permute_set_permute, set_permute_set_permute; reflexivity).
    rewrite push_env_perm_cons, call_env_set_permute. reflexivity. }
  assert (Hgoal : exists q, let '(res, rst) := call_cont n rh l1 l2 h (x0, x1) (evaluate (prog, set_permute q st2)) in
     res = SOME Error \/
     (let '(res', rcst) := call_cont (MAP f n) (apply_colour f rh) l1 l2 (colour_h f h) (y1, y2) (evaluate (prog, cst2)) in
      res = res' /\ word_state_eq_rel rst rcst /\ ac_post f live lt res rst rcst)).
  { apply (permute_swap_lemma4 prog st2 (fun r => let '(res, rst) := call_cont n rh l1 l2 h (x0, x1) r in
     res = SOME Error \/
     (let '(res', rcst) := call_cont (MAP f n) (apply_colour f rh) l1 l2 (colour_h f h) (y1, y2) (evaluate (prog, cst2)) in
      res = res' /\ word_state_eq_rel rst rcst /\ ac_post f live lt res rst rcst))).
    split; [intros st' _; cbn [call_cont]; left; reflexivity|].
    pose proof (evaluate_stack_swap prog st2) as SW.
    destruct (evaluate (prog, st2)) as [r1 s1] eqn:E1.
    unfold PAIR_MAP, I; cbn [FST SND fst snd].
    destruct r1 as [[x ys|x y'|k|k| | |ou|]|].
    - (* Result *)
      destruct SW as (SK & SH & SWf).
      destruct (SWf (stack cst2) Hsv2) as (st_ & Ecs & SV & SK2).
      rewrite <- Hcs2 in Ecs. rewrite Ecs. cbn [call_cont]. rewrite LENGTH_MAP'.
      destruct (negb ⌜x = Loc l1 l2⌝ || negb (LENGTH ys =? LENGTH n)) eqn:Echk;
        [exists P0; left; reflexivity|].
      rewrite Hst2 in SK. destruct (stack s1) as [|[m ex0 lx hx] rx] eqn:Es1; cbn [s_key_eq] in SK; [contradiction|].
      destruct SK as [SKr SKf]. apply s_frame_key_eq_def2 in SKf as (Kfst & <- & <- & <-).
      destruct st_ as [|[m' ey0 ly hy] ry]; cbn [s_val_eq] in SV; [contradiction|].
      destruct SV as [SVr SVf]. apply s_frame_val_eq_def2 in SVf as (Vsnd & <- & <-).
      rewrite Hcst2 in SK2. cbn [s_key_eq] in SK2. destruct SK2 as [SK2r SK2f].
      apply s_frame_key_eq_def2 in SK2f as (Kfst2 & _ & <- & _).
      set (hnd := match h with None => None | Some (_, (_, (a1, a2))) => Some (handler st, (a1, a2)) end) in *.
      assert (Ep1 : pop_env s1 = SOME (set_locals_size (locals_size st) (set_stack rx
                      (set_locals (union (fromAList lx) (fromAList (toAList x0))) (match hnd with None => s1 | Some (hn, _) => set_handler hn s1 end))))).
      { unfold pop_env. rewrite Es1. destruct hnd as [[hn [? ?]]|]; reflexivity. }
      assert (Ep2 : pop_env (set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: ry) s1) =
                    SOME (set_locals_size (locals_size st) (set_stack ry
                      (set_locals (union (fromAList ly) (fromAList (toAList y1)))
                        (match hnd with None => set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: ry) s1
                         | Some (hn, _) => set_handler hn (set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: ry) s1) end))))).
      { unfold pop_env. rewrite stack_set_stack. destruct hnd as [[hn [? ?]]|]; reflexivity. }
      assert (Hrr : ry = rx).
      { symmetry; apply s_val_and_key_eq; split; [exact SVr|].
        apply (s_key_eq_trans _ (stack st)); split; [apply s_key_eq_sym; exact SKr|exact SK2r]. }
      subst ry.
      assert (Hdc : ⌜domain (union (fromAList ly) (fromAList (toAList y1))) =
                     domain (FST (y1, y2)) UNION domain (SND (y1, y2))⌝ = true).
      { apply bd_true'. cbn [FST SND fst snd]. eapply dom_union_frame; [|exact El]. exact Kfst2. }
      apply orb_false_iff in Echk as [_ Elen]. apply Bool.negb_false_iff, N.eqb_eq in Elen.
      destruct (⌜domain (union (fromAList lx) (fromAList (toAList x0))) =
                domain (FST (x0, x1)) UNION domain (SND (x0, x1))⌝) eqn:Edc.
      2:{ exists P0. rewrite pop_env_set_permute, Ep1. cbn [OPTION_MAP option_map].
          rewrite locals_set_permute. cbn_ws. rewrite Edc. left; reflexivity. }
      apply bool_decide_spec in Edc. cbn [FST SND fst snd] in Edc.
      set (s1p := set_locals_size (locals_size st) (set_stack rx
                      (set_locals (union (fromAList lx) (fromAList (toAList x0))) (match hnd with None => s1 | Some (hn, _) => set_handler hn s1 end)))) in *.
      set (cs1p := set_locals_size (locals_size st) (set_stack rx
                      (set_locals (union (fromAList ly) (fromAList (toAList y1)))
                        (match hnd with None => set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: rx) s1
                         | Some (hn, _) => set_handler hn (set_stack (StackFrame (locals_size st) (toAList y1) ly hnd :: rx) s1) end)))) in *.
      assert (Hlr : strong_locals_rel f (domain (get_live rh live lt)) (locals s1p) (locals cs1p)).
      { subst s1p cs1p. cbn_ws. apply union_fromAList_rel.
        - exact Vsnd.
        - rewrite <- Kfst2, <- Kfst. symmetry; apply key_map_implies; exact Hml.
        - rewrite X1; exact S1.
        - pose proof (env_to_list_keys x1 P0) as Hk. rewrite El' in Hk. rewrite <- Kfst, Hk, X1, X2.
          eapply INJ_less; split; [exact Hi1|]. set_solve. }
      destruct (IHr (set_vars n ys s1p) (set_vars (MAP f n) ys cs1p) f live lt) as [prh Hrh].
      { split; [exact Hcr|split].
        - unfold set_vars. apply word_state_eq_rel_locals. subst s1p cs1p.
          destruct hnd as [[? [? ?]]|]; unfold word_state_eq_rel; cbn_ws; repeat split; reflexivity.
        - apply (strong_locals_rel_set_vars_dom f (domain (numset_list_insert n (union n2 n1)))).
          split; [symmetry; exact Elen|split; [exact Hi2|split; [|split; [|exact Hlr]]]].
          + subst s1p; cbn_ws. rewrite Edc, X1, X2. set_solve.
          + rewrite domain_numset_list_insert. intros z Hz; right; exact Hz. }
      exists prh. rewrite pop_env_set_permute, Ep1, Ep2. cbn [OPTION_MAP option_map].
      fold s1p. fold cs1p. rewrite locals_set_permute.
      replace (locals s1p) with (union (fromAList lx) (fromAList (toAList x0))) by reflexivity.
      replace (locals cs1p) with (union (fromAList ly) (fromAList (toAList y1))) by reflexivity.
      rewrite Hdc, bd_true' by (cbn [FST SND fst snd]; exact Edc).
      rewrite set_vars_set_permute. exact Hrh.
    - (* Exception *)
      destruct SW as (Hhl & e0 & e & nn & ls & m & lss & HL & Hm & (Hfe & Hloc) & SKs & Hhd & SWf).
      destruct h as [[n' [hp [l1' l2']]]|].
      + (* with a handler *)
        cbn [colour_h] in *. destruct Hch as [Hih Hch].
        assert (Hh2 : handler st2 = LENGTH (stack st)).
        { subst st2 s'. unfold call_env, push_env. cbn [FST SND fst snd].
          rewrite permute_set_permute, El'. cbn_ws. reflexivity. }
        rewrite Hh2, Hst2, LASTN_LENGTH2 in HL. injection HL as Hm0 He0 He Hnn Hls0.
        subst m e0 e nn ls.
        destruct (SWf (stack cst2) (toAList y1) l (stack st)) as (st_ & locs & Ecs & (lss' & Hfe' & Hlocs & Hsnd') & SVs & SKs2).
        { split; [|exact Hsv2]. rewrite Hh2, Hcst2, LASTN_LENGTH2. reflexivity. }
        rewrite <- Hcs2 in Ecs. rewrite Ecs. unfold call_env.
        set (cs1 := set_locals locs (set_handler (let '(a0, _) := (handler st, (l1', l2')) in a0) (set_stack st_ s1))).
        destruct (negb ⌜x = Loc l1' l2'⌝) eqn:Ex.
        { exists P0. unfold call_cont; cbn beta iota. rewrite Ex. left; reflexivity. }
        assert (Hdc : ⌜domain (locals cs1) = domain (FST (y1, y2)) UNION domain (SND (y1, y2))⌝ = true).
        { apply bd_true'. subst cs1. cbn_ws. rewrite Hlocs. cbn [FST SND fst snd].
          eapply dom_union_frame; [|exact El]. exact Hfe'. }
        destruct (⌜domain (locals s1) = domain (FST (x0, x1)) UNION domain (SND (x0, x1))⌝) eqn:Edc.
        2:{ exists P0. unfold call_cont; cbn beta iota. rewrite Ex, locals_set_permute, Edc. left; reflexivity. }
        apply bool_decide_spec in Edc. cbn [FST SND fst snd] in Edc.
        assert (Hss1 : st_ = stack s1).
        { symmetry; apply s_val_and_key_eq; split; [exact SVs|].
          apply (s_key_eq_trans _ (stack st)); split; [exact SKs|exact SKs2]. }
        assert (Hlr : strong_locals_rel f (domain (get_live hp live lt)) (locals s1) (locals cs1)).
        { subst cs1. cbn_ws. rewrite Hloc, Hlocs. apply union_fromAList_rel.
          - exact Hsnd'.
          - rewrite <- Hfe', <- Hfe. symmetry; apply key_map_implies; exact Hml.
          - rewrite X1; exact S1.
          - pose proof (env_to_list_keys x1 P0) as Hk. rewrite El' in Hk. rewrite <- Hfe, Hk, X1, X2.
            eapply INJ_less; split; [exact Hi1|]. set_solve. }
        destruct (IHh (set_var n' y' s1) (set_var (f n') y' cs1) f live lt) as [php Hhp].
        { split; [exact Hch|split].
          - unfold set_var. apply word_state_eq_rel_locals. subst cs1. rewrite Hss1.
            unfold word_state_eq_rel; cbn_ws. rewrite Hhd. repeat split.
          - apply (strong_locals_rel_set_var_dom f (domain (insert n' tt (union n2 n1)))).
            split; [exact Hih|split; [|split; [|exact Hlr]]].
            + rewrite Edc, X1, X2. set_solve.
            + in_solve. }
        exists php. unfold call_cont; cbn beta iota. rewrite Ex, locals_set_permute.
        rewrite bd_true' by (cbn [FST SND fst snd]; exact Edc). fold cs1. rewrite Hdc.
        rewrite set_var_set_permute. exact Hhp.
      + (* no handler *)
        cbn [colour_h] in *.
        assert (Hh2 : handler st2 = handler st).
        { subst st2 s'. unfold call_env, push_env. cbn [FST SND fst snd].
          rewrite permute_set_permute, El'. cbn_ws. reflexivity. }
        rewrite Hh2, Hst2 in Hhl. rewrite Hh2 in HL, SWf. rewrite Hst2 in HL.
        assert (Hlt : handler st + 1 <= LENGTH (stack st)).
        { destruct (N.eq_dec (handler st) (LENGTH (stack st))) as [E|E].
          - exfalso. rewrite E, LASTN_LENGTH2 in HL. discriminate HL.
          - rewrite !LENGTH_length in *. cbn [length] in Hhl. lia. }
        rewrite LASTN_cons_le in HL by exact Hlt.
        destruct (SWf (stack cst2) e0 e ls) as (st_ & locs & Ecs & (lss' & Hfe' & Hlocs & Hsnd') & SVs & SKs2).
        { split; [|exact Hsv2]. rewrite Hcst2, LASTN_cons_le by exact Hlt. exact HL. }
        rewrite <- Hcs2 in Ecs. rewrite Ecs. exists (permute s1). rewrite set_permute_permute.
        unfold call_cont; cbn beta iota. right.
        assert (Hlss : lss' = lss) by (apply pair_list_eq; [rewrite <- Hfe, <- Hfe'; reflexivity|symmetry; exact Hsnd']).
        subst lss'.
        assert (Hss1 : st_ = stack s1).
        { symmetry; apply s_val_and_key_eq; split; [exact SVs|].
          apply (s_key_eq_trans _ ls); split; [exact SKs|exact SKs2]. }
        split; [reflexivity|split].
        * rewrite Hss1. unfold word_state_eq_rel; cbn_ws. rewrite Hhd. repeat split.
        * cbn [ac_post]. cbn_ws. rewrite Hloc, Hlocs. reflexivity.
    - exists P0; left; reflexivity.
    - exists P0; left; reflexivity.
    - (* TimeOut *)
      destruct SW as (Hs1 & Hl1 & SWf). pose proof (SWf (stack cst2) Hsv2) as E2.
      rewrite <- Hcs2 in E2. rewrite E2. exists (permute s1). rewrite set_permute_permute.
      unfold call_cont; cbn beta iota. right. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    - (* NotEnoughSpace *)
      destruct SW as (Hs1 & Hl1 & SWf). pose proof (SWf (stack cst2) Hsv2) as E2.
      rewrite <- Hcs2 in E2. rewrite E2. exists (permute s1). rewrite set_permute_permute.
      unfold call_cont; cbn beta iota. right. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    - (* FinalFFI *)
      destruct SW as (Hs1 & Hl1 & SWf). pose proof (SWf (stack cst2) Hsv2) as E2.
      rewrite <- Hcs2 in E2. rewrite E2. exists (permute s1). rewrite set_permute_permute.
      unfold call_cont; cbn beta iota. right. split; [reflexivity|split; [apply word_state_eq_rel_refl|reflexivity]].
    - exists P0; left; reflexivity.
    - exists P0; left; reflexivity. }
  destruct Hgoal as [q Hq]. exists (perm_cons (P0 0) q). rewrite EQ1.
  rewrite (Hcolour ltac:(rewrite Hclk; exact Eck)). exact Hq.
Qed.

Lemma eac_all : forall p : prog a, eac_IH p.
Proof.
  intros p; induction p as [ |pri moves|i|v ex|gv gn|sn sexp|ex var|q IHq|ret dest args h IHret IHh
                     |q1 q2 IH1 IH2|cmp r ri q1 q2 IH1 IH2|names q exit_names IHq|an anames
                     |t1 t2 ad off ws|rv|rv rvs|k|k| |b dst src|lr ll|r1 r2 r3 r4 inames
                     |r1 r2|r1 r2|fi r1 r2 r3 r4 fnames|op v ex]
    using prog_nested_ind; intros st cst f live lt H.
  - apply eac_Skip; exact H.
  - apply eac_Move; exact H.
  - apply eac_Inst; exact H.
  - apply eac_Assign; exact H.
  - apply eac_Get; exact H.
  - apply eac_Set; exact H.
  - apply eac_Store; exact H.
  - apply eac_MustTerminate; assumption.
  - destruct ret as [[n [names [rh [l1 l2]]]]|].
    + apply eac_Call_Some; assumption.
    + apply eac_Call_None; exact H.
  - apply eac_Seq; assumption.
  - apply eac_If; assumption.
  - apply eac_Loop; assumption.
  - apply eac_Alloc; exact H.
  - apply eac_StoreConsts; exact H.
  - apply eac_Raise; exact H.
  - apply eac_Return; exact H.
  - apply eac_Break; exact H.
  - apply eac_Continue; exact H.
  - apply eac_Tick; exact H.
  - apply eac_OpCurrHeap; exact H.
  - apply eac_LocValue; exact H.
  - apply eac_Install; exact H.
  - apply eac_CodeBufferWrite; exact H.
  - apply eac_DataBufferWrite; exact H.
  - apply eac_FFI; exact H.
  - apply eac_ShareInst; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour_Loop_helper" *)
Theorem evaluate_apply_colour_Loop_helper : forall (st cst : state) f names body exit_names live lt,
  colouring_ok f (Loop names body exit_names) live lt /\
  word_state_eq_rel st cst /\
  strong_locals_rel f (domain (get_live (Loop names body exit_names) live lt)) (locals st) (locals cst) /\
  (forall (st cst : state) f live lt,
     colouring_ok f body live lt /\
     word_state_eq_rel st cst /\
     strong_locals_rel f (domain (get_live body live lt)) (locals st) (locals cst) ->
     exists perm',
       let '(res, rst) := evaluate (body, set_permute perm' st) in
       res = SOME Error \/
       let '(res', rcst) := evaluate (apply_colour f body, cst) in
       res = res' /\ word_state_eq_rel rst rcst /\
       match res with
       | NONE => strong_locals_rel f (domain live) (locals rst) (locals rcst)
       | SOME (Break n) =>
           match oEL n lt with
           | Some (_, exit_names) => strong_locals_rel f (domain exit_names) (locals rst) (locals rcst)
           | None => True
           end
       | SOME (Continue n) =>
           match oEL n lt with
           | Some (names, _) => strong_locals_rel f (domain names) (locals rst) (locals rcst)
           | None => True
           end
       | SOME _ => locals rst = locals rcst
       end) ->
  exists perm',
    let '(res, rst) := evaluate (Loop names body exit_names, set_permute perm' st) in
    res = SOME Error \/
    let '(res', rcst) := evaluate (apply_colour f (Loop names body exit_names), cst) in
    res = res' /\ word_state_eq_rel rst rcst /\
    match res with
    | NONE => strong_locals_rel f (domain live) (locals rst) (locals rcst)
    | SOME (Break n) =>
        match oEL n lt with
        | Some (_, exit_names) => strong_locals_rel f (domain exit_names) (locals rst) (locals rcst)
        | None => True
        end
    | SOME (Continue n) =>
        match oEL n lt with
        | Some (names, _) => strong_locals_rel f (domain names) (locals rst) (locals rcst)
        | None => True
        end
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros st cst f names body exit_names live lt (Hc & Heq & Hs & IH).
  exact (eac_Loop names body exit_names f live lt IH st cst (conj Hc (conj Heq Hs))).
Qed.

(** The liveness theorem. *)
(*! HOL "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour" *)
Theorem evaluate_apply_colour : forall (prog : prog a) (st cst : state) f live lt,
  colouring_ok f prog live lt /\
  word_state_eq_rel st cst /\
  strong_locals_rel f (domain (get_live prog live lt)) (locals st) (locals cst) ->
  exists perm',
    let '(res, rst) := evaluate (prog, set_permute perm' st) in
    if bool_decide (res = SOME Error) then True else
    let '(res', rcst) := evaluate (apply_colour f prog, cst) in
    res = res' /\
    word_state_eq_rel rst rcst /\
    match res with
    | NONE => strong_locals_rel f (domain live) (locals rst) (locals rcst)
    | SOME (Break n) =>
        match oEL n lt with
        | Some (_, exit_names) => strong_locals_rel f (domain exit_names) (locals rst) (locals rcst)
        | None => True
        end
    | SOME (Continue n) =>
        match oEL n lt with
        | Some (names, _) => strong_locals_rel f (domain names) (locals rst) (locals rcst)
        | None => True
        end
    | SOME _ => locals rst = locals rcst
    end.
Proof.
  intros prog st cst f live lt H.
  destruct (eac_all prog st cst f live lt H) as [perm Hp]. exists perm.
  destruct (evaluate (prog, set_permute perm st)) as [res rst].
  destruct (bool_decide (res = SOME Error)) eqn:E; [exact Logic.I|].
  destruct Hp as [Hp|Hp]; [subst; rewrite bd_true' in E by reflexivity; discriminate|exact Hp].
Qed.

End Main.
