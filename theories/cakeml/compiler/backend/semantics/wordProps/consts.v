(** * CakeML [wordProps]: constant-field lemmas

    Port of the first part of [cakeml/compiler/backend/semantics/wordPropsScript.sml]
    (up to the "CONST LEMMAS END" marker): preliminary list lemmas, the
    lemmas stating which state fields each semantic primitive leaves
    unchanged ([*_const]) and commutes with ([*_with_const]), and the
    [get]/[set] lemmas.

    Carrier notes:
    - HOL [s with f := v] is [set_f v s] (wordSem's helpers; the field
      [store] is updated by [set_store_field], the field [stack_size] is read
      by [state_stack_size]).  HOL's free variables are quantified; bound
      variables that clash with Rocq names ([c], [store], [ffi], [a]) are
      renamed ([c0], [store0], [ffi0], [ad]).
    - HOL's [sorting$PERM] is not ported: statements about it use Rocq's
      [Permutation] and are untagged ([PERM_list_rearrange],
      [PERM_ALL_DISTINCT_MAP]).
    - Not ported: [case_eq_thms] (a list of HOL's generated case-equality
      theorems, a proof-automation artifact) and the [local] theorems
      [evaluate_clock_const], [evaluate_clock_with_const] (stated by HOL as
      selected goals of [evaluate_ind]); Galette proves the corresponding
      facts inside the proofs of [wordProps.clock].

    The section "Galette-only infrastructure" (state congruences and
    case-splitting tactics shared by the [wordProps] files) has no HOL
    original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.basis.pure Require Import mlstring mllist.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem wordConvs backendProps.
From Stdlib Require Import Permutation.
Open Scope N_scope.

(** ** Galette-only infrastructure *)

Lemma state_eta {a c ffi_t} (s : state a c ffi_t) :
  s = mk_state (locals s) (locals_size s) (fp_regs s) (store s) (stack s) (stack_limit s)
        (stack_max s) (state_stack_size s) (memory s) (mdomain s) (sh_mdomain s) (permute s)
        (compile s) (compile_oracle s) (code_buffer s) (data_buffer s) (gc_fun s) (handler s)
        (clock s) (termdep s) (code s) (be s) (ffi s).
Proof. destruct s; reflexivity. Qed.

(** Unfold the field updates and projections of wordSem's states. *)
Ltac unfold_sets :=
  cbn [set_locals set_locals_size set_fp_regs set_store_field set_stack
    set_stack_limit set_stack_max set_stack_size set_memory set_mdomain set_sh_mdomain
    set_permute set_compile set_compile_oracle set_code_buffer set_data_buffer
    set_gc_fun set_handler set_clock set_termdep set_code set_be set_ffi
    locals locals_size fp_regs store stack stack_limit stack_max state_stack_size memory
    mdomain sh_mdomain permute compile compile_oracle code_buffer data_buffer gc_fun handler
    clock termdep code be ffi] in *.

(** Equality of two states built by updates: destruct all states and
    compare the fields. *)
Ltac state_eq :=
  repeat match goal with s : state _ _ _ |- _ => destruct s end;
  unfold dec_clock, set_var, set_vars, unset_var, set_store, set_fp_var, call_env,
    flush_state in *;
  unfold_sets; cbn in *; try reflexivity; try (f_equal; lia).

(** Case split the first [match]/[if] of the goal (reducing afterwards). *)
Ltac split_goal :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
  end.

(** Case split all [match]es of the goal. *)
Ltac split_goal_all := repeat split_goal.

(** Destruct all states and unfold, then split the goal's [match]es: used
    for the [*_with_const] lemmas, whose two sides scrutinise the same
    terms. *)
Ltac with_const_tac :=
  intros; repeat split;
  repeat match goal with s : state _ _ _ |- _ => destruct s end;
  unfold_sets; cbn; split_goal_all; cbn; reflexivity.

Section Consts.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** ** Preliminary list lemmas *)

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "domain_fromAList_toAList" *)
Theorem domain_fromAList_toAList : forall (l : num_map (word_loc a)),
  domain (fromAList (toAList l)) = domain l.
Proof. intros l; rewrite domain_fromAList; apply set_MAP_FST_toAList_domain. Qed.

End Consts.

(** GENLIST membership and element lemmas (Galette infrastructure). *)
Lemma GENLIST_length {A} (f : N -> A) n : length (GENLIST f n) = N.to_nat n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, length_app, IH; cbn; lia.
Qed.

Lemma GENLIST_nth {A} (f : N -> A) n i d :
  (i < N.to_nat n)%nat -> nth i (GENLIST f n) d = f (N.of_nat i).
Proof.
  induction n as [|n IH] using N.peano_ind; intros Hi; [cbn in Hi; lia|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app.
  destruct (Nat.lt_ge_cases i (N.to_nat n)) as [Hlt|Hge].
  - rewrite app_nth1 by (rewrite GENLIST_length; exact Hlt); apply IH, Hlt.
  - rewrite app_nth2 by (rewrite GENLIST_length; exact Hge).
    rewrite GENLIST_length. assert (i = N.to_nat n) by lia. subst i.
    rewrite Nat.sub_diag; cbn; f_equal; lia.
Qed.

Lemma In_GENLIST {A} (f : N -> A) n x :
  In x (GENLIST f n) <-> exists i, i < n /\ x = f i.
Proof.
  induction n as [|n IH] using N.peano_ind.
  - cbn; split; [tauto|intros [i [Hi _]]; lia].
  - rewrite (proj2 (GENLIST_thm f n)), SNOC_app, in_app_iff, IH; cbn.
    split.
    + intros [[i [Hi ->]]|[<-|[]]]; [exists i; split; [lia|reflexivity]|exists n; split; [lia|reflexivity]].
    + intros [i [Hi ->]]. destruct (N.eq_dec i n) as [->|Hn]; [right; left; reflexivity|].
      left; exists i; split; [lia|reflexivity].
Qed.

Lemma In_nth_EL {A} `{Inhabited A} (x : A) l :
  In x l <-> exists i, i < LENGTH l /\ x = EL i l.
Proof.
  rewrite LENGTH_length; split.
  - intros Hx; apply In_nth with (d := ARB) in Hx as [n [Hn <-]].
    exists (N.of_nat n); split; [lia|]. rewrite EL_nth by (rewrite LENGTH_length; lia).
    f_equal; lia.
  - intros [i [Hi ->]]; rewrite EL_nth by (rewrite LENGTH_length; lia). apply nth_In; lia.
Qed.

Section ListRearrange.
Context {A : Type} `{Inhabited A}.

Local Lemma list_rearrange_cases (f : N -> N) (ls : list A) :
  (BIJ f (count (LENGTH ls)) (count (LENGTH ls)) /\
   list_rearrange f ls = GENLIST (fun i => EL (f i) ls) (LENGTH ls)) \/
  list_rearrange f ls = ls.
Proof.
  unfold list_rearrange; destruct (classical_dec _) as [Hb|Hb]; [left; split; auto|right; auto].
Qed.

Local Lemma In_list_rearrange (f : N -> N) (ls : list A) x :
  In x (list_rearrange f ls) <-> In x ls.
Proof.
  destruct (list_rearrange_cases f ls) as [[Hb ->]| ->]; [|reflexivity].
  rewrite In_GENLIST, In_nth_EL.
  destruct Hb as [[Hm _] [_ Hs]]. unfold pred_set.IN, count in *.
  split.
  - intros [i [Hi ->]]; exists (f i); split; [apply Hm, Hi|reflexivity].
  - intros [j [Hj ->]]; destruct (Hs j Hj) as [i [Hi Hfi]]; exists i; split; [exact Hi|].
    rewrite Hfi; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "mem_list_rearrange" *)
Theorem mem_list_rearrange : forall `{EqDecision A} (ls : list A) x f,
  MEM x (list_rearrange f ls) <-> MEM x ls.
Proof. intros ? ls x f; unfold is_true; rewrite !MEM_In; apply In_list_rearrange. Qed.

Lemma list_rearrange_length (f : N -> N) (ls : list A) :
  length (list_rearrange f ls) = length ls.
Proof.
  destruct (list_rearrange_cases f ls) as [[_ ->]| ->]; [|reflexivity].
  rewrite GENLIST_length, LENGTH_length; lia.
Qed.

(** HOL's [PERM_list_rearrange], with Rocq's [Permutation] for HOL's
    [PERM]. *)
Theorem PERM_list_rearrange : forall `{EqDecision A} (f : N -> N) (xs : list A),
  ALL_DISTINCT xs -> Permutation xs (list_rearrange f xs).
Proof.
  intros ? f xs Hd; unfold is_true in Hd; rewrite ALL_DISTINCT_NoDup in Hd.
  apply NoDup_Permutation_bis; [exact Hd| rewrite list_rearrange_length; lia|].
  intros x Hx; apply In_list_rearrange, Hx.
Qed.

End ListRearrange.

(** HOL's [PERM_ALL_DISTINCT_MAP], with Rocq's [Permutation] for HOL's
    [PERM]. *)
Theorem PERM_ALL_DISTINCT_MAP : forall {A B} `{EqDecision A} `{EqDecision B} (f : A -> B) xs ys,
  Permutation xs ys ->
  ALL_DISTINCT (MAP f xs) ->
  ALL_DISTINCT (MAP f ys) /\ (forall x, MEM x ys <-> MEM x xs).
Proof.
  intros A B EA EB f xs ys HP Hd; unfold is_true in *; rewrite ALL_DISTINCT_NoDup in *; split.
  - eapply Permutation_NoDup; [apply Permutation_map, HP|exact Hd].
  - intros x; rewrite !MEM_In; split; apply Permutation_in; [symmetry|]; exact HP.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME" *)
Theorem ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME :
  forall {K V} `{EqDecision K} `{EqDecision V} (xs : list (K * V)) x y,
  ALL_DISTINCT (MAP FST xs) /\ MEM (x, y) xs -> ALOOKUP xs x = SOME y.
Proof.
  intros K V EK EV xs x y [Hd Hm]; unfold is_true in *; rewrite ALL_DISTINCT_NoDup in Hd;
    rewrite MEM_In in Hm.
  induction xs as [|[k v] xs IH]; [destruct Hm|].
  cbn in Hd |- *; inversion Hd as [|? ? Hk Hd']; subst.
  destruct Hm as [Heq|Hm].
  - injection Heq as -> ->; destruct (decide (x = x)); [reflexivity|congruence].
  - destruct (decide (k = x)) as [->|Hn]; [|apply IH; auto].
    exfalso; apply Hk; apply in_map_iff; exists (x, y); auto.
Qed.

Section Consts2.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** HOL's [state_const]: record updates are injective in the new value. *)
(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "state_const" *)
Theorem state_const : forall (s : state) l l' p p' clk clk' xs xs',
  (set_locals l s = set_locals l' s <-> l = l') /\
  (set_permute p s = set_permute p' s <-> p = p') /\
  (set_clock clk s = set_clock clk' s <-> clk = clk') /\
  (set_stack xs s = set_stack xs' s <-> xs = xs').
Proof.
  intros; repeat split; intros H; subst; try reflexivity;
    [apply (f_equal locals) in H|apply (f_equal permute) in H|apply (f_equal clock) in H
    |apply (f_equal stack) in H]; exact H.
Qed.

End Consts2.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "PAIR_MAP_EQ_PAIR" *)
Theorem PAIR_MAP_EQ_PAIR : forall {A B C D} (f : A -> C) (g : B -> D) p a0 b,
  (f ## g) p = (a0, b) <-> exists x y, p = (x, y) /\ f x = a0 /\ g y = b.
Proof.
  intros A B C D f g [x y] a0 b; unfold PAIR_MAP; cbn; split.
  - intros H; injection H as <- <-; exists x, y; auto.
  - intros [x' [y' [H [<- <-]]]]; injection H as -> ->; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "OPTION_CASE_OPTION_MAP" *)
Theorem OPTION_CASE_OPTION_MAP : forall {A B C} (f : A -> B) (a0 : option A) (e : C) (g : B -> C),
  match OPTION_MAP f a0 with NONE => e | SOME x => g x end =
  match a0 with NONE => e | SOME x => g (f x) end.
Proof. intros; destruct a0; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "OPTION_CASE_MAP" *)
Theorem OPTION_CASE_MAP : forall {A B} (f : A -> B) (x : option A),
  match x with NONE => NONE | SOME x => SOME (f x) end = OPTION_MAP f x.
Proof. intros; destruct x; reflexivity. Qed.

(** ** Constant fields *)

Section ConstLemmas.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_var_with_const" *)
Theorem get_var_with_const : forall x (y : state) ls fp store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  get_var x (set_locals_size ls y) = get_var x y /\
  get_var x (set_fp_regs fp y) = get_var x y /\
  get_var x (set_store_field store0 y) = get_var x y /\
  get_var x (set_stack xs y) = get_var x y /\
  get_var x (set_stack_limit sl y) = get_var x y /\
  get_var x (set_stack_max sm y) = get_var x y /\
  get_var x (set_stack_size ssize y) = get_var x y /\
  get_var x (set_memory m y) = get_var x y /\
  get_var x (set_mdomain md y) = get_var x y /\
  get_var x (set_sh_mdomain smd y) = get_var x y /\
  get_var x (set_permute p y) = get_var x y /\
  get_var x (set_compile c0 y) = get_var x y /\
  get_var x (set_compile_oracle co y) = get_var x y /\
  get_var x (set_code_buffer cb y) = get_var x y /\
  get_var x (set_data_buffer db y) = get_var x y /\
  get_var x (set_gc_fun g y) = get_var x y /\
  get_var x (set_handler hd y) = get_var x y /\
  get_var x (set_clock clk y) = get_var x y /\
  get_var x (set_termdep tdep y) = get_var x y /\
  get_var x (set_code cd y) = get_var x y /\
  get_var x (set_be b y) = get_var x y /\
  get_var x (set_ffi ffi0 y) = get_var x y.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_vars_with_const" *)
Theorem get_vars_with_const : forall x (y : state) ls fp store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  get_vars x (set_locals_size ls y) = get_vars x y /\
  get_vars x (set_fp_regs fp y) = get_vars x y /\
  get_vars x (set_store_field store0 y) = get_vars x y /\
  get_vars x (set_stack xs y) = get_vars x y /\
  get_vars x (set_stack_limit sl y) = get_vars x y /\
  get_vars x (set_stack_max sm y) = get_vars x y /\
  get_vars x (set_stack_size ssize y) = get_vars x y /\
  get_vars x (set_memory m y) = get_vars x y /\
  get_vars x (set_mdomain md y) = get_vars x y /\
  get_vars x (set_sh_mdomain smd y) = get_vars x y /\
  get_vars x (set_permute p y) = get_vars x y /\
  get_vars x (set_compile c0 y) = get_vars x y /\
  get_vars x (set_compile_oracle co y) = get_vars x y /\
  get_vars x (set_code_buffer cb y) = get_vars x y /\
  get_vars x (set_data_buffer db y) = get_vars x y /\
  get_vars x (set_gc_fun g y) = get_vars x y /\
  get_vars x (set_handler hd y) = get_vars x y /\
  get_vars x (set_clock clk y) = get_vars x y /\
  get_vars x (set_termdep tdep y) = get_vars x y /\
  get_vars x (set_code cd y) = get_vars x y /\
  get_vars x (set_be b y) = get_vars x y /\
  get_vars x (set_ffi ffi0 y) = get_vars x y.
Proof. intros; repeat split; induction x as [|v x IH]; cbn [get_vars]; try rewrite IH; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_var_const" *)
Theorem set_var_const : forall x y (z : state),
  locals_size (set_var x y z) = locals_size z /\
  fp_regs (set_var x y z) = fp_regs z /\
  store (set_var x y z) = store z /\
  stack (set_var x y z) = stack z /\
  stack_limit (set_var x y z) = stack_limit z /\
  stack_max (set_var x y z) = stack_max z /\
  state_stack_size (set_var x y z) = state_stack_size z /\
  memory (set_var x y z) = memory z /\
  mdomain (set_var x y z) = mdomain z /\
  sh_mdomain (set_var x y z) = sh_mdomain z /\
  permute (set_var x y z) = permute z /\
  compile (set_var x y z) = compile z /\
  compile_oracle (set_var x y z) = compile_oracle z /\
  code_buffer (set_var x y z) = code_buffer z /\
  data_buffer (set_var x y z) = data_buffer z /\
  gc_fun (set_var x y z) = gc_fun z /\
  handler (set_var x y z) = handler z /\
  clock (set_var x y z) = clock z /\
  termdep (set_var x y z) = termdep z /\
  code (set_var x y z) = code z /\
  be (set_var x y z) = be z /\
  ffi (set_var x y z) = ffi z.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_var_with_const" *)
Theorem set_var_with_const : forall x y (z : state) ls fp store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  set_var x y (set_locals_size ls z) = set_locals_size ls (set_var x y z) /\
  set_var x y (set_fp_regs fp z) = set_fp_regs fp (set_var x y z) /\
  set_var x y (set_store_field store0 z) = set_store_field store0 (set_var x y z) /\
  set_var x y (set_stack xs z) = set_stack xs (set_var x y z) /\
  set_var x y (set_stack_limit sl z) = set_stack_limit sl (set_var x y z) /\
  set_var x y (set_stack_max sm z) = set_stack_max sm (set_var x y z) /\
  set_var x y (set_stack_size ssize z) = set_stack_size ssize (set_var x y z) /\
  set_var x y (set_memory m z) = set_memory m (set_var x y z) /\
  set_var x y (set_mdomain md z) = set_mdomain md (set_var x y z) /\
  set_var x y (set_sh_mdomain smd z) = set_sh_mdomain smd (set_var x y z) /\
  set_var x y (set_permute p z) = set_permute p (set_var x y z) /\
  set_var x y (set_compile c0 z) = set_compile c0 (set_var x y z) /\
  set_var x y (set_compile_oracle co z) = set_compile_oracle co (set_var x y z) /\
  set_var x y (set_code_buffer cb z) = set_code_buffer cb (set_var x y z) /\
  set_var x y (set_data_buffer db z) = set_data_buffer db (set_var x y z) /\
  set_var x y (set_gc_fun g z) = set_gc_fun g (set_var x y z) /\
  set_var x y (set_handler hd z) = set_handler hd (set_var x y z) /\
  set_var x y (set_clock clk z) = set_clock clk (set_var x y z) /\
  set_var x y (set_termdep tdep z) = set_termdep tdep (set_var x y z) /\
  set_var x y (set_code cd z) = set_code cd (set_var x y z) /\
  set_var x y (set_be b z) = set_be b (set_var x y z) /\
  set_var x y (set_ffi ffi0 z) = set_ffi ffi0 (set_var x y z).
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "unset_var_const" *)
Theorem unset_var_const : forall x (z : state),
  locals_size (unset_var x z) = locals_size z /\
  fp_regs (unset_var x z) = fp_regs z /\
  store (unset_var x z) = store z /\
  stack (unset_var x z) = stack z /\
  stack_limit (unset_var x z) = stack_limit z /\
  stack_max (unset_var x z) = stack_max z /\
  state_stack_size (unset_var x z) = state_stack_size z /\
  memory (unset_var x z) = memory z /\
  mdomain (unset_var x z) = mdomain z /\
  sh_mdomain (unset_var x z) = sh_mdomain z /\
  permute (unset_var x z) = permute z /\
  compile (unset_var x z) = compile z /\
  compile_oracle (unset_var x z) = compile_oracle z /\
  code_buffer (unset_var x z) = code_buffer z /\
  data_buffer (unset_var x z) = data_buffer z /\
  gc_fun (unset_var x z) = gc_fun z /\
  handler (unset_var x z) = handler z /\
  clock (unset_var x z) = clock z /\
  termdep (unset_var x z) = termdep z /\
  code (unset_var x z) = code z /\
  be (unset_var x z) = be z /\
  ffi (unset_var x z) = ffi z.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "unset_var_with_const" *)
Theorem unset_var_with_const : forall x (z : state) ls fp store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  unset_var x (set_locals_size ls z) = set_locals_size ls (unset_var x z) /\
  unset_var x (set_fp_regs fp z) = set_fp_regs fp (unset_var x z) /\
  unset_var x (set_store_field store0 z) = set_store_field store0 (unset_var x z) /\
  unset_var x (set_stack xs z) = set_stack xs (unset_var x z) /\
  unset_var x (set_stack_limit sl z) = set_stack_limit sl (unset_var x z) /\
  unset_var x (set_stack_max sm z) = set_stack_max sm (unset_var x z) /\
  unset_var x (set_stack_size ssize z) = set_stack_size ssize (unset_var x z) /\
  unset_var x (set_memory m z) = set_memory m (unset_var x z) /\
  unset_var x (set_mdomain md z) = set_mdomain md (unset_var x z) /\
  unset_var x (set_sh_mdomain smd z) = set_sh_mdomain smd (unset_var x z) /\
  unset_var x (set_permute p z) = set_permute p (unset_var x z) /\
  unset_var x (set_compile c0 z) = set_compile c0 (unset_var x z) /\
  unset_var x (set_compile_oracle co z) = set_compile_oracle co (unset_var x z) /\
  unset_var x (set_code_buffer cb z) = set_code_buffer cb (unset_var x z) /\
  unset_var x (set_data_buffer db z) = set_data_buffer db (unset_var x z) /\
  unset_var x (set_gc_fun g z) = set_gc_fun g (unset_var x z) /\
  unset_var x (set_handler hd z) = set_handler hd (unset_var x z) /\
  unset_var x (set_clock clk z) = set_clock clk (unset_var x z) /\
  unset_var x (set_termdep tdep z) = set_termdep tdep (unset_var x z) /\
  unset_var x (set_code cd z) = set_code cd (unset_var x z) /\
  unset_var x (set_be b z) = set_be b (unset_var x z) /\
  unset_var x (set_ffi ffi0 z) = set_ffi ffi0 (unset_var x z).
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_vars_const" *)
Theorem set_vars_const : forall x y (z : state),
  locals_size (set_vars x y z) = locals_size z /\
  fp_regs (set_vars x y z) = fp_regs z /\
  store (set_vars x y z) = store z /\
  stack (set_vars x y z) = stack z /\
  stack_limit (set_vars x y z) = stack_limit z /\
  stack_max (set_vars x y z) = stack_max z /\
  state_stack_size (set_vars x y z) = state_stack_size z /\
  memory (set_vars x y z) = memory z /\
  mdomain (set_vars x y z) = mdomain z /\
  sh_mdomain (set_vars x y z) = sh_mdomain z /\
  permute (set_vars x y z) = permute z /\
  compile (set_vars x y z) = compile z /\
  compile_oracle (set_vars x y z) = compile_oracle z /\
  code_buffer (set_vars x y z) = code_buffer z /\
  data_buffer (set_vars x y z) = data_buffer z /\
  gc_fun (set_vars x y z) = gc_fun z /\
  handler (set_vars x y z) = handler z /\
  clock (set_vars x y z) = clock z /\
  termdep (set_vars x y z) = termdep z /\
  code (set_vars x y z) = code z /\
  be (set_vars x y z) = be z /\
  ffi (set_vars x y z) = ffi z.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_vars_with_const" *)
Theorem set_vars_with_const : forall x y (z : state) ls fp store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  set_vars x y (set_locals_size ls z) = set_locals_size ls (set_vars x y z) /\
  set_vars x y (set_fp_regs fp z) = set_fp_regs fp (set_vars x y z) /\
  set_vars x y (set_store_field store0 z) = set_store_field store0 (set_vars x y z) /\
  set_vars x y (set_stack xs z) = set_stack xs (set_vars x y z) /\
  set_vars x y (set_stack_limit sl z) = set_stack_limit sl (set_vars x y z) /\
  set_vars x y (set_stack_max sm z) = set_stack_max sm (set_vars x y z) /\
  set_vars x y (set_stack_size ssize z) = set_stack_size ssize (set_vars x y z) /\
  set_vars x y (set_memory m z) = set_memory m (set_vars x y z) /\
  set_vars x y (set_mdomain md z) = set_mdomain md (set_vars x y z) /\
  set_vars x y (set_sh_mdomain smd z) = set_sh_mdomain smd (set_vars x y z) /\
  set_vars x y (set_permute p z) = set_permute p (set_vars x y z) /\
  set_vars x y (set_compile c0 z) = set_compile c0 (set_vars x y z) /\
  set_vars x y (set_compile_oracle co z) = set_compile_oracle co (set_vars x y z) /\
  set_vars x y (set_code_buffer cb z) = set_code_buffer cb (set_vars x y z) /\
  set_vars x y (set_data_buffer db z) = set_data_buffer db (set_vars x y z) /\
  set_vars x y (set_gc_fun g z) = set_gc_fun g (set_vars x y z) /\
  set_vars x y (set_handler hd z) = set_handler hd (set_vars x y z) /\
  set_vars x y (set_clock clk z) = set_clock clk (set_vars x y z) /\
  set_vars x y (set_termdep tdep z) = set_termdep tdep (set_vars x y z) /\
  set_vars x y (set_code cd z) = set_code cd (set_vars x y z) /\
  set_vars x y (set_be b z) = set_be b (set_vars x y z) /\
  set_vars x y (set_ffi ffi0 z) = set_ffi ffi0 (set_vars x y z).
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_store_with_const" *)
Theorem get_store_with_const : forall x (y : state) l ls fp xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  get_store x (set_locals l y) = get_store x y /\
  get_store x (set_locals_size ls y) = get_store x y /\
  get_store x (set_fp_regs fp y) = get_store x y /\
  get_store x (set_stack xs y) = get_store x y /\
  get_store x (set_stack_limit sl y) = get_store x y /\
  get_store x (set_stack_max sm y) = get_store x y /\
  get_store x (set_stack_size ssize y) = get_store x y /\
  get_store x (set_memory m y) = get_store x y /\
  get_store x (set_mdomain md y) = get_store x y /\
  get_store x (set_sh_mdomain smd y) = get_store x y /\
  get_store x (set_permute p y) = get_store x y /\
  get_store x (set_compile c0 y) = get_store x y /\
  get_store x (set_compile_oracle co y) = get_store x y /\
  get_store x (set_code_buffer cb y) = get_store x y /\
  get_store x (set_data_buffer db y) = get_store x y /\
  get_store x (set_gc_fun g y) = get_store x y /\
  get_store x (set_handler hd y) = get_store x y /\
  get_store x (set_clock clk y) = get_store x y /\
  get_store x (set_termdep tdep y) = get_store x y /\
  get_store x (set_code cd y) = get_store x y /\
  get_store x (set_be b y) = get_store x y /\
  get_store x (set_ffi ffi0 y) = get_store x y.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_store_const" *)
Theorem set_store_const : forall x y (z : state),
  locals (set_store x y z) = locals z /\
  locals_size (set_store x y z) = locals_size z /\
  fp_regs (set_store x y z) = fp_regs z /\
  stack (set_store x y z) = stack z /\
  stack_limit (set_store x y z) = stack_limit z /\
  stack_max (set_store x y z) = stack_max z /\
  state_stack_size (set_store x y z) = state_stack_size z /\
  memory (set_store x y z) = memory z /\
  mdomain (set_store x y z) = mdomain z /\
  sh_mdomain (set_store x y z) = sh_mdomain z /\
  permute (set_store x y z) = permute z /\
  compile (set_store x y z) = compile z /\
  compile_oracle (set_store x y z) = compile_oracle z /\
  code_buffer (set_store x y z) = code_buffer z /\
  data_buffer (set_store x y z) = data_buffer z /\
  gc_fun (set_store x y z) = gc_fun z /\
  handler (set_store x y z) = handler z /\
  clock (set_store x y z) = clock z /\
  termdep (set_store x y z) = termdep z /\
  code (set_store x y z) = code z /\
  be (set_store x y z) = be z /\
  ffi (set_store x y z) = ffi z.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_store_with_const" *)
Theorem set_store_with_const : forall x y (z : state) l ls fp xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  set_store x y (set_locals l z) = set_locals l (set_store x y z) /\
  set_store x y (set_locals_size ls z) = set_locals_size ls (set_store x y z) /\
  set_store x y (set_fp_regs fp z) = set_fp_regs fp (set_store x y z) /\
  set_store x y (set_stack xs z) = set_stack xs (set_store x y z) /\
  set_store x y (set_stack_limit sl z) = set_stack_limit sl (set_store x y z) /\
  set_store x y (set_stack_max sm z) = set_stack_max sm (set_store x y z) /\
  set_store x y (set_stack_size ssize z) = set_stack_size ssize (set_store x y z) /\
  set_store x y (set_memory m z) = set_memory m (set_store x y z) /\
  set_store x y (set_mdomain md z) = set_mdomain md (set_store x y z) /\
  set_store x y (set_sh_mdomain smd z) = set_sh_mdomain smd (set_store x y z) /\
  set_store x y (set_permute p z) = set_permute p (set_store x y z) /\
  set_store x y (set_compile c0 z) = set_compile c0 (set_store x y z) /\
  set_store x y (set_compile_oracle co z) = set_compile_oracle co (set_store x y z) /\
  set_store x y (set_code_buffer cb z) = set_code_buffer cb (set_store x y z) /\
  set_store x y (set_data_buffer db z) = set_data_buffer db (set_store x y z) /\
  set_store x y (set_gc_fun g z) = set_gc_fun g (set_store x y z) /\
  set_store x y (set_handler hd z) = set_handler hd (set_store x y z) /\
  set_store x y (set_clock clk z) = set_clock clk (set_store x y z) /\
  set_store x y (set_termdep tdep z) = set_termdep tdep (set_store x y z) /\
  set_store x y (set_code cd z) = set_code cd (set_store x y z) /\
  set_store x y (set_be b z) = set_be b (set_store x y z) /\
  set_store x y (set_ffi ffi0 z) = set_ffi ffi0 (set_store x y z).
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_fp_var_with_const" *)
Theorem get_fp_var_with_const : forall x (y : state) l ls store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  get_fp_var x (set_locals l y) = get_fp_var x y /\
  get_fp_var x (set_locals_size ls y) = get_fp_var x y /\
  get_fp_var x (set_store_field store0 y) = get_fp_var x y /\
  get_fp_var x (set_stack xs y) = get_fp_var x y /\
  get_fp_var x (set_stack_limit sl y) = get_fp_var x y /\
  get_fp_var x (set_stack_max sm y) = get_fp_var x y /\
  get_fp_var x (set_stack_size ssize y) = get_fp_var x y /\
  get_fp_var x (set_memory m y) = get_fp_var x y /\
  get_fp_var x (set_mdomain md y) = get_fp_var x y /\
  get_fp_var x (set_sh_mdomain smd y) = get_fp_var x y /\
  get_fp_var x (set_permute p y) = get_fp_var x y /\
  get_fp_var x (set_compile c0 y) = get_fp_var x y /\
  get_fp_var x (set_compile_oracle co y) = get_fp_var x y /\
  get_fp_var x (set_code_buffer cb y) = get_fp_var x y /\
  get_fp_var x (set_data_buffer db y) = get_fp_var x y /\
  get_fp_var x (set_gc_fun g y) = get_fp_var x y /\
  get_fp_var x (set_handler hd y) = get_fp_var x y /\
  get_fp_var x (set_clock clk y) = get_fp_var x y /\
  get_fp_var x (set_termdep tdep y) = get_fp_var x y /\
  get_fp_var x (set_code cd y) = get_fp_var x y /\
  get_fp_var x (set_be b y) = get_fp_var x y /\
  get_fp_var x (set_ffi ffi0 y) = get_fp_var x y.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_fp_var_const" *)
Theorem set_fp_var_const : forall x y (z : state),
  locals (set_fp_var x y z) = locals z /\
  locals_size (set_fp_var x y z) = locals_size z /\
  store (set_fp_var x y z) = store z /\
  stack (set_fp_var x y z) = stack z /\
  stack_limit (set_fp_var x y z) = stack_limit z /\
  stack_max (set_fp_var x y z) = stack_max z /\
  state_stack_size (set_fp_var x y z) = state_stack_size z /\
  memory (set_fp_var x y z) = memory z /\
  mdomain (set_fp_var x y z) = mdomain z /\
  sh_mdomain (set_fp_var x y z) = sh_mdomain z /\
  permute (set_fp_var x y z) = permute z /\
  compile (set_fp_var x y z) = compile z /\
  compile_oracle (set_fp_var x y z) = compile_oracle z /\
  code_buffer (set_fp_var x y z) = code_buffer z /\
  data_buffer (set_fp_var x y z) = data_buffer z /\
  gc_fun (set_fp_var x y z) = gc_fun z /\
  handler (set_fp_var x y z) = handler z /\
  clock (set_fp_var x y z) = clock z /\
  termdep (set_fp_var x y z) = termdep z /\
  code (set_fp_var x y z) = code z /\
  be (set_fp_var x y z) = be z /\
  ffi (set_fp_var x y z) = ffi z.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_fp_var_with_const" *)
Theorem set_fp_var_with_const : forall x y (z : state) l ls store0 xs sl sm ssize m md smd p c0 co cb db g hd clk tdep cd b ffi0,
  set_fp_var x y (set_locals l z) = set_locals l (set_fp_var x y z) /\
  set_fp_var x y (set_locals_size ls z) = set_locals_size ls (set_fp_var x y z) /\
  set_fp_var x y (set_store_field store0 z) = set_store_field store0 (set_fp_var x y z) /\
  set_fp_var x y (set_stack xs z) = set_stack xs (set_fp_var x y z) /\
  set_fp_var x y (set_stack_limit sl z) = set_stack_limit sl (set_fp_var x y z) /\
  set_fp_var x y (set_stack_max sm z) = set_stack_max sm (set_fp_var x y z) /\
  set_fp_var x y (set_stack_size ssize z) = set_stack_size ssize (set_fp_var x y z) /\
  set_fp_var x y (set_memory m z) = set_memory m (set_fp_var x y z) /\
  set_fp_var x y (set_mdomain md z) = set_mdomain md (set_fp_var x y z) /\
  set_fp_var x y (set_sh_mdomain smd z) = set_sh_mdomain smd (set_fp_var x y z) /\
  set_fp_var x y (set_permute p z) = set_permute p (set_fp_var x y z) /\
  set_fp_var x y (set_compile c0 z) = set_compile c0 (set_fp_var x y z) /\
  set_fp_var x y (set_compile_oracle co z) = set_compile_oracle co (set_fp_var x y z) /\
  set_fp_var x y (set_code_buffer cb z) = set_code_buffer cb (set_fp_var x y z) /\
  set_fp_var x y (set_data_buffer db z) = set_data_buffer db (set_fp_var x y z) /\
  set_fp_var x y (set_gc_fun g z) = set_gc_fun g (set_fp_var x y z) /\
  set_fp_var x y (set_handler hd z) = set_handler hd (set_fp_var x y z) /\
  set_fp_var x y (set_clock clk z) = set_clock clk (set_fp_var x y z) /\
  set_fp_var x y (set_termdep tdep z) = set_termdep tdep (set_fp_var x y z) /\
  set_fp_var x y (set_code cd z) = set_code cd (set_fp_var x y z) /\
  set_fp_var x y (set_be b z) = set_be b (set_fp_var x y z) /\
  set_fp_var x y (set_ffi ffi0 z) = set_ffi ffi0 (set_fp_var x y z).
Proof. intros; repeat split; reflexivity. Qed.

End ConstLemmas.
Section ConstLemmas2.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

Local Ltac push_tac :=
  intros; repeat split;
  repeat match goal with y : option (N * (prog a * (N * N))) |- _ =>
           destruct y as [[? [? [? ?]]]|] end;
  unfold push_env; repeat match goal with |- context [env_to_list ?e ?p] =>
    destruct (env_to_list e p) eqn:? end; reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_const" *)
Theorem push_env_const : forall x y (z : state),
  clock (push_env x y z) = clock z /\
  memory (push_env x y z) = memory z /\
  store (push_env x y z) = store z /\
  handler (push_env x NONE z) = handler z /\
  ffi (push_env x y z) = ffi z /\
  termdep (push_env x y z) = termdep z /\
  data_buffer (push_env x y z) = data_buffer z /\
  code_buffer (push_env x y z) = code_buffer z /\
  compile (push_env x y z) = compile z /\
  compile_oracle (push_env x y z) = compile_oracle z /\
  mdomain (push_env x y z) = mdomain z /\
  sh_mdomain (push_env x y z) = sh_mdomain z /\
  gc_fun (push_env x y z) = gc_fun z /\
  be (push_env x y z) = be z /\
  fp_regs (push_env x y z) = fp_regs z /\
  code (push_env x y z) = code z /\
  stack_limit (push_env x y z) = stack_limit z /\
  state_stack_size (push_env x y z) = state_stack_size z.
Proof. push_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_with_const" *)
Theorem push_env_with_const : forall x y (z : state) k c0 co code0 termdep0 l,
  push_env x y (set_clock k z) = set_clock k (push_env x y z) /\
  push_env x y (set_compile c0 z) = set_compile c0 (push_env x y z) /\
  push_env x y (set_compile_oracle co z) = set_compile_oracle co (push_env x y z) /\
  push_env x y (set_code code0 z) = set_code code0 (push_env x y z) /\
  push_env x y (set_termdep termdep0 z) = set_termdep termdep0 (push_env x y z) /\
  push_env x y (set_locals l z) = set_locals l (push_env x y z).
Proof. intros x [[? [? [? ?]]]|]; with_const_tac. Qed.

Local Ltac pop_tac :=
  intros; repeat match goal with H : pop_env _ = _ |- _ => revert H end;
  unfold pop_env; cbn;
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta
         end;
  intros; repeat match goal with H : SOME _ = SOME _ |- _ => injection H as <- end;
  try discriminate; repeat split; reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "pop_env_const" *)
Theorem pop_env_const : forall (x y : state),
  pop_env x = SOME y ->
  clock y = clock x /\
  ffi y = ffi x /\
  be y = be x /\
  compile y = compile x /\
  compile_oracle y = compile_oracle x /\
  memory y = memory x /\
  mdomain y = mdomain x /\
  sh_mdomain y = sh_mdomain x /\
  store y = store x /\
  fp_regs y = fp_regs x /\
  gc_fun y = gc_fun x /\
  termdep y = termdep x /\
  permute y = permute x /\
  data_buffer y = data_buffer x /\
  code_buffer y = code_buffer x /\
  code y = code x /\
  stack_limit y = stack_limit x /\
  stack_max y = stack_max x /\
  state_stack_size y = state_stack_size x.
Proof. pop_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "pop_env_with_const" *)
Theorem pop_env_with_const : forall (z : state) k c0 co code0 termdep0 perm l ls,
  pop_env (set_clock k z) = OPTION_MAP (fun s => set_clock k s) (pop_env z) /\
  pop_env (set_compile c0 z) = OPTION_MAP (fun s => set_compile c0 s) (pop_env z) /\
  pop_env (set_compile_oracle co z) = OPTION_MAP (fun s => set_compile_oracle co s) (pop_env z) /\
  pop_env (set_code code0 z) = OPTION_MAP (fun s => set_code code0 s) (pop_env z) /\
  pop_env (set_termdep termdep0 z) = OPTION_MAP (fun s => set_termdep termdep0 s) (pop_env z) /\
  pop_env (set_permute perm z) = OPTION_MAP (fun s => set_permute perm s) (pop_env z) /\
  pop_env (set_locals l z) = pop_env z /\
  pop_env (set_locals_size ls z) = pop_env z.
Proof. unfold pop_env; with_const_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "pop_env_code_gc_fun_clock" *)
Theorem pop_env_code_gc_fun_clock : forall (r x : state),
  pop_env r = SOME x ->
  code r = code x /\
  code_buffer r = code_buffer x /\
  data_buffer r = data_buffer x /\
  gc_fun r = gc_fun x /\
  clock r = clock x /\
  be r = be x /\
  mdomain r = mdomain x /\
  sh_mdomain r = sh_mdomain x /\
  compile r = compile x /\
  compile_oracle r = compile_oracle x /\
  stack_limit r = stack_limit x /\
  stack_max r = stack_max x /\
  state_stack_size r = state_stack_size x.
Proof. pop_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "call_env_const" *)
Theorem call_env_const : forall x ss (y : state),
  store (call_env x ss y) = store y /\
  termdep (call_env x ss y) = termdep y /\
  clock (call_env x ss y) = clock y /\
  handler (call_env x ss y) = handler y /\
  stack (call_env x ss y) = stack y /\
  compile_oracle (call_env x ss y) = compile_oracle y /\
  compile (call_env x ss y) = compile y /\
  be (call_env x ss y) = be y /\
  memory (call_env x ss y) = memory y /\
  mdomain (call_env x ss y) = mdomain y /\
  sh_mdomain (call_env x ss y) = sh_mdomain y /\
  gc_fun (call_env x ss y) = gc_fun y /\
  ffi (call_env x ss y) = ffi y /\
  code (call_env x ss y) = code y /\
  code_buffer (call_env x ss y) = code_buffer y /\
  data_buffer (call_env x ss y) = data_buffer y /\
  stack_limit (call_env x ss y) = stack_limit y /\
  state_stack_size (call_env x ss y) = state_stack_size y.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "call_env_with_const" *)
Theorem call_env_with_const : forall x ss (y : state) l k termdep0 c0 co code0 k' perm,
  call_env x ss (set_locals l y) = call_env x ss y /\
  call_env x ss (set_clock k y) = set_clock k (call_env x ss y) /\
  call_env x ss (set_termdep termdep0 y) = set_termdep termdep0 (call_env x ss y) /\
  call_env x ss (set_compile c0 y) = set_compile c0 (call_env x ss y) /\
  call_env x ss (set_compile_oracle co y) = set_compile_oracle co (call_env x ss y) /\
  call_env x ss (set_code code0 y) = set_code code0 (call_env x ss y) /\
  call_env x ss (set_handler k' y) = set_handler k' (call_env x ss y) /\
  call_env x ss (set_permute perm y) = set_permute perm (call_env x ss y).
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "flush_state_const" *)
Theorem flush_state_const : forall b (y : state),
  clock (flush_state b y) = clock y /\
  compile_oracle (flush_state b y) = compile_oracle y /\
  compile (flush_state b y) = compile y /\
  be (flush_state b y) = be y /\
  gc_fun (flush_state b y) = gc_fun y /\
  ffi (flush_state b y) = ffi y /\
  code (flush_state b y) = code y /\
  code_buffer (flush_state b y) = code_buffer y /\
  data_buffer (flush_state b y) = data_buffer y /\
  stack_limit (flush_state b y) = stack_limit y /\
  state_stack_size (flush_state b y) = state_stack_size y /\
  stack (flush_state false y) = stack y.
Proof. intros [] y; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "flush_state_with_const" *)
Theorem flush_state_with_const : forall b (y : state) l ls xs p sm k,
  flush_state b (set_locals l y) = flush_state b y /\
  flush_state b (set_locals_size ls y) = flush_state b y /\
  flush_state true (set_stack xs y) = flush_state true y /\
  flush_state b (set_permute p y) = set_permute p (flush_state b y) /\
  flush_state b (set_stack_max sm y) = set_stack_max sm (flush_state b y) /\
  flush_state b (set_clock k y) = set_clock k (flush_state b y).
Proof. intros [] y; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "has_space_with_const" *)
Theorem has_space_with_const : forall x (y : state) k c0 co code0 termdep0 l ls xs,
  has_space x (set_clock k y) = has_space x y /\
  has_space x (set_compile c0 y) = has_space x y /\
  has_space x (set_compile_oracle co y) = has_space x y /\
  has_space x (set_code code0 y) = has_space x y /\
  has_space x (set_termdep termdep0 y) = has_space x y /\
  has_space x (set_locals l y) = has_space x y /\
  has_space x (set_locals_size ls y) = has_space x y /\
  has_space x (set_stack xs y) = has_space x y.
Proof. intros; repeat split; reflexivity. Qed.

Local Ltac gc_tac :=
  intros; repeat match goal with H : gc _ = _ |- _ => revert H end;
  unfold gc; cbn;
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta
         end;
  intros; repeat match goal with H : SOME _ = SOME _ |- _ => injection H as <- end;
  try discriminate; repeat split; reflexivity.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_const" *)
Theorem gc_const : forall (x y : state),
  gc x = SOME y ->
  clock y = clock x /\
  ffi y = ffi x /\
  code y = code x /\
  be y = be x /\
  code_buffer y = code_buffer x /\
  data_buffer y = data_buffer x /\
  compile y = compile x /\
  handler y = handler x /\
  compile_oracle y = compile_oracle x /\
  locals_size y = locals_size x /\
  stack_limit y = stack_limit x /\
  stack_max y = stack_max x /\
  state_stack_size y = state_stack_size x.
Proof. gc_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "gc_with_const" *)
Theorem gc_with_const : forall (x : state) k c0 co code0 perm t l ls,
  gc (set_clock k x) = OPTION_MAP (fun s => set_clock k s) (gc x) /\
  gc (set_compile c0 x) = OPTION_MAP (fun s => set_compile c0 s) (gc x) /\
  gc (set_compile_oracle co x) = OPTION_MAP (fun s => set_compile_oracle co s) (gc x) /\
  gc (set_code code0 x) = OPTION_MAP (fun s => set_code code0 s) (gc x) /\
  gc (set_permute perm x) = OPTION_MAP (fun s => set_permute perm s) (gc x) /\
  gc (set_termdep t x) = OPTION_MAP (fun s => set_termdep t s) (gc x) /\
  gc (set_locals l x) = OPTION_MAP (fun s => set_locals l s) (gc x) /\
  gc (set_locals_size ls x) = OPTION_MAP (fun s => set_locals_size ls s) (gc x).
Proof. unfold gc; with_const_tac. Qed.

End ConstLemmas2.

(** ** Galette-only helpers for the implication lemmas *)

(** Turn a leaf equation of a case split into substitutions. *)
Ltac leaf H :=
  lazymatch type of H with
  | SOME _ = SOME _ => injection H as <-
  | (_, _) = (_, _) => injection H as <- <-
  | NONE = SOME _ => discriminate H
  | SOME _ = NONE => discriminate H
  | _ => idtac
  end.

Ltac destr_conj :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Section ConstLemmas3.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** [word_exp] reads only the locals, the store, the memory and its
    domain. *)
Lemma word_exp_state_cong (s t : state) e :
  locals s = locals t -> store s = store t -> memory s = memory t -> mdomain s = mdomain t ->
  word_exp s e = word_exp t e.
Proof.
  intros H1 H2 H3 H4.
  induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [word_exp]; unfold get_var, get_store, mem_load; rewrite ?H1, ?H2, ?H3, ?H4; try reflexivity.
  - rewrite IH; reflexivity.
  - replace (MAP (word_exp s) es) with (MAP (word_exp t) es); [reflexivity|].
    induction IH as [|x l Hx Hl IHl]; cbn; [reflexivity|]. rewrite Hx, IHl; reflexivity.
  - rewrite IH1, IH2; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "mem_store_const" *)
Theorem mem_store_const : forall x y (z a0 : state),
  mem_store x y z = SOME a0 ->
  locals a0 = locals z /\
  clock a0 = clock z /\
  be a0 = be z /\
  gc_fun a0 = gc_fun z /\
  mdomain a0 = mdomain z /\
  sh_mdomain a0 = sh_mdomain z /\
  ffi a0 = ffi z /\
  handler a0 = handler z /\
  code a0 = code z /\
  code_buffer a0 = code_buffer z /\
  data_buffer a0 = data_buffer z /\
  compile a0 = compile z /\
  compile_oracle a0 = compile_oracle z /\
  stack a0 = stack z /\
  locals_size a0 = locals_size z /\
  stack_limit a0 = stack_limit z /\
  stack_max a0 = stack_max z /\
  state_stack_size a0 = state_stack_size z.
Proof.
  intros x y z a0 H; unfold mem_store in H; split_H H; leaf H; repeat split; reflexivity.
Qed.

(** Facts about the primitives in the context, then reduce field
    projections of updates and close by congruence. *)
Ltac const_facts :=
  repeat match goal with
         | E : gc _ = SOME _ |- _ => apply gc_const in E
         | E : pop_env _ = SOME _ |- _ => apply pop_env_const in E
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E
         end;
  repeat match goal with
         | H : context [push_env ?x ?y ?z] |- _ =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         end;
  destr_conj;
  unfold flush_state, set_store, set_var, set_vars, unset_var, set_fp_var, dec_clock,
    call_env in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  unfold_sets.

Local Ltac alloc_tac :=
  intros ? ? ? ? ? H; unfold alloc in H; split_H H; leaf H; const_facts; repeat split; congruence.


(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "alloc_const" *)
Theorem alloc_const : forall c0 names (s : state) r s',
  alloc c0 names s = (r, s') ->
  clock s' = clock s /\
  ffi s' = ffi s /\
  code s' = code s /\
  be s' = be s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  compile s' = compile s /\
  compile_oracle s' = compile_oracle s /\
  stack_limit s' = stack_limit s /\
  state_stack_size s' = state_stack_size s.
Proof. alloc_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "alloc_code_gc_fun_const" *)
Theorem alloc_code_gc_fun_const : forall x names (s : state) res t,
  alloc x names s = (res, t) ->
  code t = code s /\
  code_buffer t = code_buffer s /\
  data_buffer t = data_buffer s /\
  gc_fun t = gc_fun s /\
  mdomain t = mdomain s /\
  sh_mdomain t = sh_mdomain s /\
  be t = be s /\
  compile t = compile s /\
  compile_oracle t = compile_oracle s /\
  stack_limit t = stack_limit s /\
  state_stack_size t = state_stack_size s.
Proof.
  intros ? ? ? ? ? H; unfold alloc in H; split_H H; leaf H;
    repeat match goal with
           | E : gc _ = SOME _ |- _ =>
               let E' := fresh in pose proof E as E'; unfold gc in E'; split_H E'; leaf E';
               apply gc_const in E
           end;
    const_facts; repeat split; congruence.
Qed.

End ConstLemmas3.

Section ConstLemmas4.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inst_const" *)
Theorem inst_const : forall i (s s' : state),
  inst i s = SOME s' ->
  clock s' = clock s /\
  ffi s' = ffi s.
Proof.
  intros i s s' H;
    destruct i as [|r w|ar|m r [ad w]|f]; [|cbn [inst] in H|destruct ar|destruct m|destruct f];
    cbn [inst] in H; unfold assign in H; split_H H; leaf H; repeat match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E end;
    destr_conj; unfold flush_state, set_var, set_vars, set_fp_var in *;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; unfold_sets; split; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "share_inst_const" *)
Theorem share_inst_const : forall op v c0 (s : state) res s',
  share_inst op v c0 s = (res, s') ->
  be s' = be s /\
  gc_fun s' = gc_fun s /\
  mdomain s' = mdomain s /\
  sh_mdomain s' = sh_mdomain s /\
  code s' = code s /\
  code_buffer s' = code_buffer s /\
  data_buffer s' = data_buffer s /\
  compile s' = compile s /\
  compile_oracle s' = compile_oracle s /\
  permute s' = permute s /\
  clock s' = clock s /\
  handler s' = handler s /\
  stack_limit s' = stack_limit s /\
  stack_max s' = stack_max s.
Proof.
  intros op v c0 s res s' H; destruct op; cbn [share_inst] in H;
    unfold sh_mem_set_var, sh_mem_load, sh_mem_load_byte, sh_mem_load16, sh_mem_load32,
      sh_mem_store, sh_mem_store_byte, sh_mem_store16, sh_mem_store32 in H;
    split_H H; leaf H; repeat match goal with E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E end;
    destr_conj; unfold flush_state, set_var, set_vars, set_fp_var in *;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; unfold_sets; repeat split; reflexivity.
Qed.

End ConstLemmas4.
