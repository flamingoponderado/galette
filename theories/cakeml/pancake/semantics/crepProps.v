(** * CakeML Pancake [crepProps]: properties of crepLang and crepSem

    Port of [cakeml/pancake/semantics/crepPropsScript.sml].

    Carrier notes: HOL's [s with locals := l] is [set_locals l s] (crepSem's
    setters); HOL's [MEM] is the boolean [MEM]; [≼] is [isPREFIX]; list
    lengths and indices are [N].  [MEM (LoadGlob ad) (exps e)] needs
    decidable equality on [crepLang$exp], given here by the Galette-only
    instance [cexp_eq_dec].

    Proof method: HOL's [recInduct evaluate_ind] is well-founded induction
    on [eval_lt] ([crepSem]); a case of [evaluate] is unfolded with
    [evaluate_eqn] and [fix_clock_evaluate] (lemma [evaluate_unfold]), and
    its [match]es are split by the guarded tactics below.  The Galette-only
    helpers in the first sections (nested induction on [exp], [eval]
    congruence, state-update lemmas, small list/finite-map facts, tactics)
    have no HOL original. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.pancake Require panLang.
From Galette.cakeml.pancake Require Import pan_common crepLang.
From Galette.cakeml.pancake.semantics Require panSem.
From Galette.cakeml.pancake.semantics Require panProps.
From Galette.cakeml.pancake.semantics Require Import pan_commonProps crepSem.
Import panSem(word_lab(..), isWord, theWord, mem_load_32, mem_load_byte, mem_store,
              mem_store_32, mem_store_byte, write_bytearray).
Open Scope N_scope.
Local Open Scope fmap_scope.

(** ** Galette-only infrastructure *)

Section ExpInd.
Context {a : N}.

(** Induction on expressions with induction hypotheses for the nested
    lists. *)
Fixpoint cexp_nested_ind (P : exp a -> Prop)
    (Hc : forall w, P (Const w)) (Hv : forall v0, P (Var v0))
    (Hl : forall e, P e -> P (Load e))
    (Hl32 : forall e, P e -> P (Load32 e))
    (Hlb : forall e, P e -> P (LoadByte e))
    (Hlg : forall g, P (LoadGlob g))
    (Hop : forall op es, Forall P es -> P (Op op es))
    (Hcop : forall op es, Forall P es -> P (Crepop op es))
    (Hcmp : forall c e1 e2, P e1 -> P e2 -> P (Cmp c e1 e2))
    (Hsh : forall s e1 e2, P e1 -> P e2 -> P (Shift s e1 e2))
    (Hb : P BaseAddr) (Ht : P TopAddr) (e : exp a) : P e :=
  let rec := cexp_nested_ind P Hc Hv Hl Hl32 Hlb Hlg Hop Hcop Hcmp Hsh Hb Ht in
  let fix go (l : list (exp a)) : Forall P l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec x) (go xs) end in
  match e with
  | Const w => Hc w
  | Var v0 => Hv v0
  | Load e => Hl e (rec e)
  | Load32 e => Hl32 e (rec e)
  | LoadByte e => Hlb e (rec e)
  | LoadGlob g => Hlg g
  | Op op es => Hop op es (go es)
  | Crepop op es => Hcop op es (go es)
  | Cmp c e1 e2 => Hcmp c e1 e2 (rec e1) (rec e2)
  | Shift s e1 e2 => Hsh s e1 e2 (rec e1) (rec e2)
  | BaseAddr => Hb
  | TopAddr => Ht
  end.

Fixpoint cexp_eq_dec_f (x y : exp a) {struct x} : Decision (x = y).
Proof.
  unfold Decision.
  refine (match x, y with
    | Const w1, Const w2 => match decide (w1 = w2) with left _ => left _ | right _ => right _ end
    | Var v1, Var v2 => match decide (v1 = v2) with left _ => left _ | right _ => right _ end
    | Load e1, Load e2 => match cexp_eq_dec_f e1 e2 with left _ => left _ | right _ => right _ end
    | Load32 e1, Load32 e2 => match cexp_eq_dec_f e1 e2 with left _ => left _ | right _ => right _ end
    | LoadByte e1, LoadByte e2 => match cexp_eq_dec_f e1 e2 with left _ => left _ | right _ => right _ end
    | LoadGlob g1, LoadGlob g2 => match decide (g1 = g2) with left _ => left _ | right _ => right _ end
    | Op o1 l1, Op o2 l2 =>
        match decide (o1 = o2) with
        | left _ =>
            match (fix go (l1 l2 : list (exp a)) : {l1 = l2} + {l1 <> l2} :=
                     match l1, l2 with
                     | [], [] => left eq_refl
                     | u :: us, v :: vs =>
                         match cexp_eq_dec_f u v with
                         | left _ => match go us vs with left _ => left _ | right _ => right _ end
                         | right _ => right _
                         end
                     | _, _ => right _
                     end) l1 l2 with left _ => left _ | right _ => right _ end
        | right _ => right _
        end
    | Crepop o1 l1, Crepop o2 l2 =>
        match decide (o1 = o2) with
        | left _ =>
            match (fix go (l1 l2 : list (exp a)) : {l1 = l2} + {l1 <> l2} :=
                     match l1, l2 with
                     | [], [] => left eq_refl
                     | u :: us, v :: vs =>
                         match cexp_eq_dec_f u v with
                         | left _ => match go us vs with left _ => left _ | right _ => right _ end
                         | right _ => right _
                         end
                     | _, _ => right _
                     end) l1 l2 with left _ => left _ | right _ => right _ end
        | right _ => right _
        end
    | Cmp c1 a1 b1, Cmp c2 a2 b2 =>
        match decide (c1 = c2), cexp_eq_dec_f a1 a2, cexp_eq_dec_f b1 b2 with
        | left _, left _, left _ => left _ | _, _, _ => right _ end
    | Shift c1 a1 b1, Shift c2 a2 b2 =>
        match decide (c1 = c2), cexp_eq_dec_f a1 a2, cexp_eq_dec_f b1 b2 with
        | left _, left _, left _ => left _ | _, _, _ => right _ end
    | BaseAddr, BaseAddr => left eq_refl
    | TopAddr, TopAddr => left eq_refl
    | _, _ => right _
    end); try congruence;
  repeat match goal with H : _ <> _ |- _ => let H' := fresh in intros H'; injection H'; intros; subst; tauto end.
Defined.

#[global] Instance cexp_eq_dec : EqDecision (exp a) := cexp_eq_dec_f.

End ExpInd.

Lemma OPT_MMAP_ext_In' {A B} (f g : A -> option B) l :
  (forall x, In x l -> f x = g x) -> OPT_MMAP f l = OPT_MMAP g l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption).
  reflexivity.
Qed.

Lemma MEM_bool_In {A} `{EqDecision A} (x : A) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

Lemma isPREFIX_app {A} `{EqDecision A} (l1 l2 : list A) :
  is_true (isPREFIX l1 l2) <-> exists l, l2 = l1 ++ l.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros l2; cbn.
  - split; [intros _; exists l2; reflexivity|intros _; destruct l2; reflexivity].
  - destruct l2 as [|y l2]; [split; [discriminate|intros [l Hl]; discriminate]|].
    unfold is_true; rewrite Bool.andb_true_iff, bool_decide_spec.
    split.
    + intros [-> Hp]. apply IH in Hp as [l ->]. exists l; reflexivity.
    + intros [l Hl]. injection Hl as -> ->. split; [reflexivity|]. apply IH; exists l; reflexivity.
Qed.

Lemma isPREFIX_refl {A} `{EqDecision A} (l : list A) : is_true (isPREFIX l l).
Proof. apply isPREFIX_app; exists []; rewrite app_nil_r; reflexivity. Qed.

Lemma isPREFIX_trans {A} `{EqDecision A} (l1 l2 l3 : list A) :
  is_true (isPREFIX l1 l2) -> is_true (isPREFIX l2 l3) -> is_true (isPREFIX l1 l3).
Proof.
  rewrite !isPREFIX_app; intros [x ->] [y ->]; exists (x ++ y); rewrite app_assoc; reflexivity.
Qed.

Lemma isPREFIX_app_r {A} `{EqDecision A} (l1 l2 : list A) : is_true (isPREFIX l1 (l1 ++ l2)).
Proof. apply isPREFIX_app; exists l2; reflexivity. Qed.

Section StateHelpers.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** [eval] reads only the locals, globals, memory, memaddrs, [be],
    [base_addr] and [top_addr] of the state. *)
Lemma eval_state_cong s t :
  locals s = locals t -> globals s = globals t ->
  memory s = memory t -> memaddrs s = memaddrs t -> be s = be t ->
  base_addr s = base_addr t -> top_addr s = top_addr t ->
  eval s = eval t.
Proof.
  intros H1 H2 H4 H5 H6 H7 H8; apply functional_extensionality; intros e.
  induction e using cexp_nested_ind; cbn [eval]; unfold mem_load;
    rewrite ?H1, ?H2, ?H4, ?H5, ?H6, ?H7, ?H8;
    repeat match goal with IH : eval s ?e = eval t ?e |- _ => rewrite IH; clear IH end;
    try match goal with IH : Forall _ ?l |- context [OPT_MMAP ?f ?l] =>
      erewrite (OPT_MMAP_ext_In' f _ l); [|intros x Hx; exact (proj1 (Forall_forall _ _) IH x Hx)]
    end;
    reflexivity.
Qed.

Lemma eval_set_clock k s : eval (set_clock k s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_set_ffi f s : eval (set_ffi f s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_set_code c s : eval (set_code c s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.
Lemma eval_dec_clock s : eval (dec_clock s) = eval s.
Proof. apply eval_state_cong; reflexivity. Qed.

Lemma set_clock_id s : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.
Lemma set_clock_set_clock k1 k2 s : set_clock k1 (set_clock k2 s) = set_clock k1 s.
Proof. destruct s; reflexivity. Qed.
Lemma set_locals_id s : set_locals (locals s) s = s.
Proof. destruct s; reflexivity. Qed.

(** [evaluate] unfolded one step, with HOL's [fix_clock] rewritten away. *)
Lemma evaluate_unfold (p : prog a) s :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s')) p s.
Proof. apply evaluate_eqn. Qed.

End StateHelpers.

Ltac eval_simp := rewrite ?eval_set_clock, ?eval_set_ffi, ?eval_set_code, ?eval_dec_clock in *.

(** Projections of state updates. *)
Ltac state_cbn :=
  cbn [locals globals code memory memaddrs sh_memaddrs clock be ffi base_addr top_addr
       set_locals set_memory set_clock set_ffi set_code set_globals dec_clock empty_locals
       set_var] in *.

(** Turn [(x =? y) = b] hypotheses into arithmetic facts. *)
Ltac eqb_facts :=
  repeat match goal with
         | H : (_ =? _)%N = false |- _ => apply N.eqb_neq in H
         | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
         end.

(** Split, in hypothesis [H], the first [match]/[if] on a scrutinee;
    pairs produced by [evaluate] are destructed with [eqn]. *)
Ltac split_in H :=
  match type of H with
  | context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
  end.

(** ** HOL's [crepProps] *)

Section Props.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "cexp_heads_simp_def" *)
Definition cexp_heads_simp {A} `{EqDecision A} `{Inhabited A} (es : list (list A))
    : option (list A) :=
  if MEM [] es then NONE else SOME (MAP HD es).

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "lookup_locals_eq_map_vars" *)
Theorem lookup_locals_eq_map_vars : forall ns (t : state a ffi_t),
  OPT_MMAP (FLOOKUP (locals t)) ns =
  OPT_MMAP (eval t) (MAP Var ns).
Proof.
  induction ns as [|n ns IH]; intros t; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_shape_eq_shape" *)
Theorem length_load_shape_eq_shape : forall n (a0 : word a) (e : exp a),
  LENGTH (load_shape a0 n e) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; intros a0 e.
  - reflexivity.
  - rewrite (proj2 (load_shape_def a0 e n)).
    destruct (decide _); rewrite LENGTH_cons, IH; lia.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "eval_load_shape_el_rel" *)
Theorem eval_load_shape_el_rel : forall m n (a0 : word a) (t : state a ffi_t) e,
  (n < m)%N ->
  eval t (EL n (load_shape a0 m e)) =
  eval t (Load (Op Add [e; Const (a0 + bytes_in_word * n2w n)])).
Proof.
  induction m as [|m IH] using N.peano_ind; intros n a0 t e Hn; [lia|].
  rewrite (proj2 (load_shape_def a0 e m)).
  destruct (N.eq_dec n 0) as [->|Hn0].
  - destruct (decide (a0 = n2w 0)) as [->|Ha0]; rewrite EL_cons_0;
      [|replace (a0 + bytes_in_word * n2w 0) with a0 by word_ring; reflexivity].
    cbn [eval OPT_MMAP].
    destruct (eval t e) as [[w]|]; [|reflexivity].
    cbn. f_equal. unfold wordLang.word_op; cbn [FOLDR].
    replace (w + (n2w 0 + bytes_in_word * n2w 0 + n2w 0)) with w by word_ring.
    reflexivity.
  - destruct (decide _); rewrite EL_cons_pos, IH by lia;
      match goal with |- eval _ (Load (Op _ [_; Const ?x])) = eval _ (Load (Op _ [_; Const ?y])) =>
        replace x with y; [reflexivity|]
      end;
      word_Z; apply zcong_eq; rewrite N2Z.inj_sub by lia; ring.
Qed.

End Props.

(** ** [eval] and local variables *)

Section EvalLocals.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma In_FLAT_MAP {A B} (f : A -> list B) l x y :
  In x l -> In y (f x) -> In y (FLAT (MAP f l)).
Proof. intros H1 H2; apply in_concat; exists (f x); split; [apply in_map|]; assumption. Qed.

(** [eval] reads the locals only at the variables of the expression
    (Galette-only). *)
Lemma eval_locals_cong s l1 l2 (e : exp a) :
  (forall n, In n (var_cexp e) -> FLOOKUP l1 n = FLOOKUP l2 n) ->
  eval (set_locals l1 s) e = eval (set_locals l2 s) e.
Proof.
  induction e as [w|v0|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using cexp_nested_ind; intros H; cbn [eval var_cexp] in *; unfold mem_load;
    cbn [locals globals memory memaddrs be base_addr top_addr set_locals]; try reflexivity.
  - apply H; left; reflexivity.
  - rewrite IH by exact H; reflexivity.
  - rewrite IH by exact H; reflexivity.
  - rewrite IH by exact H; reflexivity.
  - erewrite OPT_MMAP_ext_In'; [reflexivity|]. intros x Hx.
    apply (proj1 (Forall_forall _ _) IH x Hx). intros n Hn; apply H; eapply In_FLAT_MAP; eassumption.
  - erewrite OPT_MMAP_ext_In'; [reflexivity|]. intros x Hx.
    apply (proj1 (Forall_forall _ _) IH x Hx). intros n Hn; apply H; eapply In_FLAT_MAP; eassumption.
  - rewrite IH1, IH2 by (intros; apply H; apply in_or_app; auto); reflexivity.
  - rewrite IH1, IH2 by (intros; apply H; apply in_or_app; auto); reflexivity.
Qed.

Lemma eval_set_locals_upd_notin s (e : exp a) n w lcl :
  ~ is_true (MEM n (var_cexp e)) ->
  eval (set_locals (lcl |+ (n, w)) s) e = eval (set_locals lcl s) e.
Proof.
  intros Hn; apply eval_locals_cong; intros m Hm; rewrite FLOOKUP_UPDATE.
  destruct (decide (n = m)) as [->|]; [|reflexivity].
  exfalso; apply Hn, MEM_In, Hm.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "update_locals_not_vars_eval_eq" *)
Theorem update_locals_not_vars_eval_eq : forall s (e : exp a) v n w,
  ~ MEM n (var_cexp e) /\
  eval s e = SOME v ->
  eval (set_locals (locals s |+ (n, w)) s) e = SOME v.
Proof.
  intros s e v n w [Hn He]. rewrite eval_set_locals_upd_notin by exact Hn.
  rewrite set_locals_id; exact He.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "update_locals_not_vars_eval_eq'" 194 *)
Theorem update_locals_not_vars_eval_eq' : forall s (e : exp a) (v : word_lab a) n w,
  ~ MEM n (var_cexp e) ->
  eval (set_locals (locals s |+ (n, w)) s) e = eval s e.
Proof.
  intros s e v n w Hn. rewrite eval_set_locals_upd_notin by exact Hn.
  rewrite set_locals_id; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "update_locals_not_vars_eval_eq''" *)
Theorem update_locals_not_vars_eval_eq'' : forall s (e : exp a) (v : word_lab a) n w lcl,
  ~ MEM n (var_cexp e) ->
  eval (set_locals (lcl |+ (n, w)) s) e = eval (set_locals lcl s) e.
Proof. intros s e v n w lcl Hn; apply eval_set_locals_upd_notin, Hn. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "var_exp_load_shape" *)
Theorem var_exp_load_shape : forall i (a0 : word a) (e : exp a) n,
  MEM n (load_shape a0 i e) ->
  var_cexp n = var_cexp e.
Proof.
  induction i as [|i IH] using N.peano_ind; intros a0 e n Hm; [discriminate|].
  rewrite (proj2 (load_shape_def a0 e i)) in Hm.
  apply MEM_In in Hm.
  destruct (decide _); destruct Hm as [<-|Hm];
    try (eapply IH; apply MEM_In; exact Hm).
  - reflexivity.
  - cbn; rewrite !app_nil_r; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "map_var_cexp_eq_var" *)
Theorem map_var_cexp_eq_var : forall vs,
  FLAT (MAP var_cexp (MAP (@Var a) vs)) = vs.
Proof. induction vs as [|v vs IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

End EvalLocals.

(** ** [res_var] *)

Section ResVar.
Context {a : N}.
Implicit Types lc l : fmap varname (word_lab a).

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "res_var_commutes" *)
Theorem res_var_commutes : forall n h lc lc',
  n <> h ->
  res_var (res_var lc (h, FLOOKUP lc' h))
  (n, FLOOKUP lc' n) =
  res_var (res_var lc (n, FLOOKUP lc' n))
  (h, FLOOKUP lc' h).
Proof.
  intros n h lc lc' Hne; apply fmap_ext; intros k.
  destruct (FLOOKUP lc' h), (FLOOKUP lc' n); cbn [res_var]; fm_auto.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_diff_eq" *)
Theorem flookup_res_var_diff_eq : forall n m l (v : option (word_lab a)),
  n <> m ->
  FLOOKUP (res_var l (m, v)) n = FLOOKUP l n.
Proof. intros n m l [v|] Hne; cbn [res_var]; fm_auto. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_thm" *)
Theorem flookup_res_var_thm : forall l m (v : option (word_lab a)) n,
  FLOOKUP (res_var l (m, v)) n =
  if decide (n = m) then
    v
  else
    FLOOKUP l n.
Proof. intros l m [v|] n; cbn [res_var]; fm_auto. Qed.

End ResVar.

(** ** State projections *)

Section Simp.
Context {a : N} {ffi_t : Type}.
Implicit Types s : state a ffi_t.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "dec_clock_simp" *)
Theorem dec_clock_simp : forall s,
  locals (dec_clock s) = locals s /\
  globals (dec_clock s) = globals s /\
  code (dec_clock s) = code s /\
  memory (dec_clock s) = memory s /\
  memaddrs (dec_clock s) = memaddrs s /\
  sh_memaddrs (dec_clock s) = sh_memaddrs s /\
  be (dec_clock s) = be s /\
  ffi (dec_clock s) = ffi s /\
  base_addr (dec_clock s) = base_addr s /\
  top_addr (dec_clock s) = top_addr s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "empty_locals_simp" *)
Theorem empty_locals_simp : forall s,
  globals (empty_locals s) = globals s /\
  code (empty_locals s) = code s /\
  memory (empty_locals s) = memory s /\
  memaddrs (empty_locals s) = memaddrs s /\
  sh_memaddrs (empty_locals s) = sh_memaddrs s /\
  clock (empty_locals s) = clock s /\
  be (empty_locals s) = be s /\
  ffi (empty_locals s) = ffi s /\
  base_addr (empty_locals s) = base_addr s /\
  top_addr (empty_locals s) = top_addr s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "FLOOKUP_set_globals" *)
Theorem FLOOKUP_set_globals : forall gv (w : word_lab a) s n,
  FLOOKUP (locals (set_globals gv w s)) n = FLOOKUP (locals s) n.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "sh_mem_load_FLOOKUP_locals" *)
Theorem sh_mem_load_FLOOKUP_locals : forall v (addr : word a) nb s res t n k,
  sh_mem_load v addr nb s = (res, t) /\ n <> v /\
  (res = NONE \/ res = SOME (Continue k) \/ res = SOME (Break k)) ->
  FLOOKUP (locals t) n = FLOOKUP (locals s) n.
Proof.
  intros v addr nb s res t n k [H [Hne Hres]]; unfold sh_mem_load in H.
  repeat split_in H; injection H as <- <-;
    try (destruct Hres as [?|[?|?]]; discriminate); try reflexivity.
  all: state_cbn; fm_auto.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "sh_mem_store_FLOOKUP_locals" *)
Theorem sh_mem_store_FLOOKUP_locals : forall v (addr : word a) nb s res t n,
  sh_mem_store v addr nb s = (res, t) ->
  FLOOKUP (locals t) n = FLOOKUP (locals s) n.
Proof.
  intros v addr nb s res t n H; unfold sh_mem_store in H.
  repeat split_in H; injection H as <- <-; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "set_mem_op_FLOOKUP_locals" *)
Theorem set_mem_op_FLOOKUP_locals : forall op r (ad : word a) s res t n k,
  sh_mem_op op r ad s = (res, t) /\ r <> n /\
  (res = NONE \/ res = SOME (Continue k) \/ res = SOME (Break k)) ->
  FLOOKUP (locals t) n = FLOOKUP (locals s) n.
Proof.
  intros op r ad s res t n k [H [Hne Hres]].
  destruct op; cbn [sh_mem_op] in H;
    first [ eapply sh_mem_store_FLOOKUP_locals; exact H
          | eapply sh_mem_load_FLOOKUP_locals; split; [exact H|split; [congruence|exact Hres]] ].
Qed.

End Simp.

(** ** Induction on [evaluate] (Galette-only tactics) *)

(** Record [clock] facts for [evaluate] results in the context. *)
Ltac clocks :=
  repeat match goal with
  | E : evaluate (?p, ?s) = (?r, ?t) |- _ =>
      lazymatch goal with
      | _ : (clock t <= clock s)%N |- _ => fail
      | _ => pose proof (evaluate_clock p s r t E)
      end
  end.

Ltac lt_tac := unfold eval_lt; cbn [fst snd psize]; clocks; state_cbn; eqb_facts; lia.

(** Unfold one step of [evaluate] in hypothesis [H]. *)
Ltac unfold_eval_in H :=
  rewrite evaluate_unfold in H; cbn [evaluate_body] in H; rewrite ?fcl_evaluate in H;
  cbn beta in H.

(** Membership side conditions. *)
Ltac mem_tac :=
  unfold is_true in *; rewrite ?MEM_In in *; cbn [In] in *;
  rewrite ?in_app_iff, ?filter_In, ?bool_decide_spec in *;
  first [tauto | intuition congruence].

(** Close [FLOOKUP (locals _) n] goals with an induction hypothesis [IH]
    of the shape of [unassigned_free_vars_evaluate_same]. *)
Ltac ih_flookup IH n k :=
  match goal with
  | E : evaluate (?p', ?s') = (?r, ?s0) |- context [FLOOKUP (locals ?s0) n] =>
      let kk := lazymatch r with SOME (Break ?j) => j | SOME (Continue ?j) => j | _ => k end in
      let Hx := fresh "Hx" in
      assert (Hx : FLOOKUP (locals s0) n = FLOOKUP (locals s') n)
        by (apply (IH (p', s') ltac:(lt_tac) r s0 n kk E);
            [ first [ assumption | left; reflexivity | right; left; reflexivity
                    | right; right; reflexivity ]
            | cbn [fst]; mem_tac ]);
      rewrite Hx; clear Hx
  end.

Section Unassigned.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "unassigned_free_vars_evaluate_same" *)
Theorem unassigned_free_vars_evaluate_same : forall (p : prog a) (s : state a ffi_t) res t n k,
  evaluate (p, s) = (res, t) /\
  (res = NONE \/ res = SOME (Continue k) \/ res = SOME (Break k)) /\
  ~ MEM n (assigned_free_vars p) ->
  FLOOKUP (locals t) n = FLOOKUP (locals s) n.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res t n k,
            evaluate x = (res, t) ->
            (res = NONE \/ res = SOME (Continue k) \/ res = SOME (Break k)) ->
            ~ is_true (MEM n (assigned_free_vars (fst x))) ->
            FLOOKUP (locals t) n = FLOOKUP (locals (snd x)) n)
    by (intros p s res t n k (H1 & H2 & H3); exact (G (p, s) res t n k H1 H2 H3)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t n k H Hres Hn; cbn [fst snd] in *.
  destruct p; unfold_eval_in H; cbn [assigned_free_vars] in Hn; repeat split_in H.
  all: try (injection H as <- <-; first [destruct Hres as [?|[?|?]]; discriminate | idtac]).
  all: try reflexivity.
  all: repeat match type of Hn with
         | context [match ?x with _ => _ end] => destruct x; cbn [APPEND] in Hn
         end.
  (* Dec *)
  1: { state_cbn. destruct (decide (n = n0)) as [->|Hne].
       - destruct (FLOOKUP (locals s) n0); fm_auto.
       - transitivity (FLOOKUP (locals s0) n); [destruct (FLOOKUP (locals s) n0); fm_auto|].
         ih_flookup IH n k. clear IH. state_cbn; fm_auto. }
  all: try solve [ eapply set_mem_op_FLOOKUP_locals; split; [exact H|split; [|exact Hres]];
                   intros ->; apply Hn, MEM_In; left; reflexivity ].
  all: repeat ih_flookup IH n k.
  all: clear IH; state_cbn; try reflexivity.
  all: try solve [ assert (Hne : n0 <> n) by (intros ->; apply Hn, MEM_In; left; reflexivity);
                   rewrite FLOOKUP_UPDATE; destruct (decide (n0 = n)); congruence ].
  all: try solve [ rewrite FLOOKUP_FUPDATE_LIST_notin; [reflexivity|];
                   intros Hi; apply In_map_fst_ZIP in Hi; apply Hn; mem_tac ].
Qed.

End Unassigned.

(** ** Assigned variables *)

Section Assigned.
Context {a : N} {ffi_t : Type}.

(** Induction on programs with an induction hypothesis for the handler of
    [Call] (Galette-only). *)
Fixpoint cprog_nested_ind (P : prog a -> Prop)
    (Hsk : P Skip) (Hdec : forall v e p, P p -> P (Dec v e p))
    (Has : forall v e, P (Assign v e))
    (Hpr : forall l op r, P (Primitive l op r))
    (Hst : forall e1 e2, P (Store e1 e2)) (Hst32 : forall e1 e2, P (Store32 e1 e2))
    (Hstb : forall e1 e2, P (StoreByte e1 e2)) (Hstg : forall g e, P (StoreGlob g e))
    (Hseq : forall p q, P p -> P q -> P (Seq p q))
    (Hif : forall e p q, P p -> P q -> P (If e p q))
    (Hwh : forall e p, P p -> P (While e p))
    (Hbr : forall n, P (crepLang.Break n)) (Hco : forall n, P (crepLang.Continue n))
    (Hcall : forall o f es, (forall rts w p, o = SOME (rts, SOME (w, p)) -> P p) -> P (Call o f es))
    (Hext : forall f p1 l1 p2 l2, P (ExtCall f p1 l1 p2 l2))
    (Hra : forall w, P (Raise w)) (Hret : forall es, P (crepLang.Return es))
    (Hsh : forall op v e, P (ShMem op v e)) (Htk : P Tick) (p : prog a) : P p :=
  let rec := cprog_nested_ind P Hsk Hdec Has Hpr Hst Hst32 Hstb Hstg Hseq Hif Hwh Hbr Hco
               Hcall Hext Hra Hret Hsh Htk in
  match p with
  | Skip => Hsk
  | Dec v e p => Hdec v e p (rec p)
  | Assign v e => Has v e
  | Primitive l op r => Hpr l op r
  | Store e1 e2 => Hst e1 e2
  | Store32 e1 e2 => Hst32 e1 e2
  | StoreByte e1 e2 => Hstb e1 e2
  | StoreGlob g e => Hstg g e
  | Seq p q => Hseq p q (rec p) (rec q)
  | If e p q => Hif e p q (rec p) (rec q)
  | While e p => Hwh e p (rec p)
  | crepLang.Break n => Hbr n
  | crepLang.Continue n => Hco n
  | Call o f es =>
      Hcall o f es
        (match o as o' return (forall rts w p, o' = SOME (rts, SOME (w, p)) -> P p) with
         | SOME (rts0, SOME (w0, q)) => fun rts w p E =>
             eq_ind q P (rec q) p
               (f_equal (fun x => match x with SOME (_, SOME (_, r)) => r | _ => q end) E)
         | SOME (rts0, NONE) => fun rts w p E => ltac:(discriminate)
         | NONE => fun rts w p E => ltac:(discriminate)
         end)
  | ExtCall f p1 l1 p2 l2 => Hext f p1 l1 p2 l2
  | Raise w => Hra w
  | crepLang.Return es => Hret es
  | ShMem op v e => Hsh op v e
  | Tick => Htk
  end.

Lemma ZIP_cons {A B} (x : A) (y : B) xs ys : ZIP (x :: xs, y :: ys) = (x, y) :: ZIP (xs, ys).
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_IMP_assigned_vars" *)
Theorem assigned_free_vars_IMP_assigned_vars : forall (prog : prog a) x,
  MEM x (assigned_free_vars prog) -> MEM x (assigned_vars prog).
Proof.
  intros p; induction p using cprog_nested_ind; intros x Hx; cbn [assigned_free_vars assigned_vars] in *;
    unfold is_true in *; rewrite ?MEM_In in *; rewrite ?in_app_iff in *; try tauto.
  - apply filter_In in Hx; right; apply MEM_In, IHp, MEM_In; tauto.
  - rewrite <- !MEM_In in *; firstorder.
  - rewrite <- !MEM_In in *; firstorder.
  - rewrite <- !MEM_In in *; firstorder.
  - destruct o as [[rts [[w q]|]]|]; cbn in *; try tauto.
    rewrite in_app_iff in *. destruct Hx as [Hx|Hx]; [tauto|].
    right; apply MEM_In, (H rts w q eq_refl), MEM_In, Hx.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "unassigned_vars_evaluate_same" *)
Theorem unassigned_vars_evaluate_same : forall (p : prog a) (s : state a ffi_t) res t n k,
  evaluate (p, s) = (res, t) /\
  (res = NONE \/ res = SOME (Continue k) \/ res = SOME (Break k)) /\
  ~ MEM n (assigned_free_vars p) ->
  FLOOKUP (locals t) n = FLOOKUP (locals s) n.
Proof. exact unassigned_free_vars_evaluate_same. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_nested_decs_append" *)
Theorem assigned_vars_nested_decs_append : forall ns (es : list (exp a)) p,
  LENGTH ns = LENGTH es ->
  assigned_vars (nested_decs ns es p) = ns ++ assigned_vars p.
Proof.
  induction ns as [|n ns IH]; intros [|e es] p Hl; rewrite ?LENGTH_cons in Hl; cbn in Hl; try lia;
    cbn [nested_decs assigned_vars]; [reflexivity|].
  rewrite IH by lia; reflexivity.
Qed.

Lemma filter_filter_and {A} (f g : A -> bool) l :
  FILTER f (FILTER g l) = FILTER (fun x => g x && f x) l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  destruct (g x); cbn; [destruct (f x)|]; cbn; rewrite IH; reflexivity.
Qed.

Lemma filter_true_id {A} (f : A -> bool) l : (forall x, f x = true) -> FILTER f l = l.
Proof. intros H; induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_nested_decs_append" *)
Theorem assigned_free_vars_nested_decs_append : forall ns (es : list (exp a)) p,
  LENGTH ns = LENGTH es ->
  assigned_free_vars (nested_decs ns es p) = FILTER (fun x => negb (MEM x ns)) (assigned_free_vars p).
Proof.
  induction ns as [|n ns IH]; intros [|e es] p Hl; rewrite ?LENGTH_cons in Hl; cbn in Hl; try lia;
    cbn [nested_decs assigned_free_vars].
  - symmetry; apply filter_true_id; reflexivity.
  - rewrite IH by lia. rewrite filter_filter_and. apply filter_ext; intros x; cbn [MEM].
    destruct (MEM x ns); [rewrite Bool.orb_true_r; reflexivity|].
    rewrite Bool.orb_false_r, Bool.andb_true_l; unfold bool_decide.
    destruct (decide (n <> x)), (decide (x = n)); cbn;
      first [reflexivity | exfalso; congruence
            | exfalso; match goal with H : ~ (_ <> _) |- _ => apply H; congruence end].
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_vars_eq" *)
Theorem nested_seq_assigned_vars_eq : forall ns (vs : list (exp a)),
  LENGTH ns = LENGTH vs ->
  assigned_vars (nested_seq (MAP2 Assign ns vs)) = ns.
Proof.
  induction ns as [|n ns IH]; intros [|v vs] Hl; rewrite ?LENGTH_cons in Hl; cbn in Hl; try lia;
    cbn [MAP2 nested_seq assigned_vars]; [reflexivity|].
  rewrite IH by lia; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "nested_seq_assigned_free_vars_eq" *)
Theorem nested_seq_assigned_free_vars_eq : forall ns (vs : list (exp a)),
  LENGTH ns = LENGTH vs ->
  assigned_free_vars (nested_seq (MAP2 Assign ns vs)) = ns.
Proof.
  induction ns as [|n ns IH]; intros [|v vs] Hl; rewrite ?LENGTH_cons in Hl; cbn in Hl; try lia;
    cbn [MAP2 nested_seq assigned_free_vars]; [reflexivity|].
  rewrite IH by lia; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_seq_store_empty" *)
Theorem assigned_vars_seq_store_empty : forall (es : list (exp a)) ad a0,
  assigned_vars (nested_seq (stores ad es a0)) = [].
Proof. induction es as [|e es IH]; intros ad a0; cbn; [reflexivity|]. destruct (decide _); cbn; apply IH. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_seq_store_empty" *)
Theorem assigned_free_vars_seq_store_empty : forall (es : list (exp a)) ad a0,
  assigned_free_vars (nested_seq (stores ad es a0)) = [].
Proof. induction es as [|e es IH]; intros ad a0; cbn; [reflexivity|]. destruct (decide _); cbn; apply IH. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_vars_store_globals_empty" *)
Theorem assigned_vars_store_globals_empty : forall (es : list (exp a)) ad,
  assigned_vars (nested_seq (store_globals ad es)) = [].
Proof. induction es as [|e es IH]; intros ad; cbn; [reflexivity|]. apply IH. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "assigned_free_vars_store_globals_empty" *)
Theorem assigned_free_vars_store_globals_empty : forall (es : list (exp a)) ad,
  assigned_free_vars (nested_seq (store_globals ad es)) = [].
Proof. induction es as [|e es IH]; intros ad; cbn; [reflexivity|]. apply IH. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "length_load_globals_eq_read_size" *)
Theorem length_load_globals_eq_read_size : forall ads (a0 : word 5),
  LENGTH (@load_globals a a0 ads) = ads.
Proof.
  induction ads as [|n IH] using N.peano_ind; intros a0; [reflexivity|].
  rewrite (proj2 (load_globals_def a0 n)), LENGTH_cons, IH; lia.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "el_load_globals_elem" *)
Theorem el_load_globals_elem : forall ads (a0 : word 5) n,
  (n < ads)%N ->
  EL n (@load_globals a a0 ads) = LoadGlob (word_add a0 (n2w n)).
Proof.
  induction ads as [|m IH] using N.peano_ind; intros a0 n Hn; [lia|].
  rewrite (proj2 (load_globals_def a0 m)).
  destruct (N.eq_dec n 0) as [->|Hn0].
  - rewrite EL_cons_0; f_equal; word_ring.
  - rewrite EL_cons_pos, IH by lia. f_equal.
    word_Z; apply zcong_eq; rewrite N2Z.inj_sub by lia; ring.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_seq_stroes_locals_eq" *)
Theorem evaluate_seq_stroes_locals_eq : forall (es : list (exp a)) ad a0 (s : state a ffi_t) res t,
  evaluate (nested_seq (stores ad es a0), s) = (res, t) ->
  locals t = locals s.
Proof.
  induction es as [|e es IH]; intros ad a0 s res t H; cbn [stores nested_seq] in H.
  - rewrite (proj1 evaluate_def) in H; injection H as _ <-; reflexivity.
  - destruct (decide _); cbn [nested_seq] in H; unfold_eval_in H; repeat split_in H.
    all: lazymatch goal with
         | E : evaluate (Store _ _, _) = _ |- _ =>
             unfold_eval_in E; repeat split_in E; first [discriminate E | injection E; intros; subst]
         end.
    all: first [ apply IH in H; rewrite H; reflexivity | injection H; intros; subst; reflexivity ].
Qed.

End Assigned.

(** ** Globals, [res_var] folds and local lookups *)

Section Globals.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

(** HOL [s with globals := g] (Galette-only helper; crepSem's [set_globals]
    is HOL's different function [set_globals gv w s]). *)
Definition set_globals_field (g : fmap (word 5) (word_lab a)) (s : state a ffi_t) : state a ffi_t :=
  mk_state s.(locals) g s.(code) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be)
    s.(ffi) s.(base_addr) s.(top_addr).

Lemma eval_set_globals_field_noglob s g (e : exp a) :
  (forall ad, ~ In (LoadGlob ad) (exps e)) ->
  eval (set_globals_field g s) e = eval s e.
Proof.
  induction e as [w|v0|e IH|e IH|e IH|gd|op es IH|op es IH|c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using cexp_nested_ind; intros H; cbn [eval exps] in *; unfold mem_load;
    cbn [locals globals memory memaddrs be base_addr top_addr set_globals_field]; try reflexivity.
  - rewrite IH by exact H; reflexivity.
  - rewrite IH by exact H; reflexivity.
  - rewrite IH by exact H; reflexivity.
  - exfalso; apply (H gd); left; reflexivity.
  - erewrite OPT_MMAP_ext_In'; [reflexivity|]. intros x Hx.
    apply (proj1 (Forall_forall _ _) IH x Hx). intros ad Hi; apply (H ad); eapply In_FLAT_MAP; eassumption.
  - erewrite OPT_MMAP_ext_In'; [reflexivity|]. intros x Hx.
    apply (proj1 (Forall_forall _ _) IH x Hx). intros ad Hi; apply (H ad); eapply In_FLAT_MAP; eassumption.
  - rewrite IH1, IH2 by (intros ad Hi; apply (H ad); apply in_or_app; auto); reflexivity.
  - rewrite IH1, IH2 by (intros ad Hi; apply (H ad); apply in_or_app; auto); reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "eval_exps_not_load_global_eq" *)
Theorem eval_exps_not_load_global_eq : forall s (e : exp a) v g,
  eval s e = SOME v /\
  (forall ad, ~ MEM (LoadGlob ad) (exps e)) ->
  eval (set_globals_field g s) e = SOME v.
Proof.
  intros s e v g [He H]. rewrite eval_set_globals_field_noglob; [exact He|].
  intros ad Hi; apply (H ad), MEM_In, Hi.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "load_glob_not_mem_load" *)
Theorem load_glob_not_mem_load : forall i (a0 : word a) (h : exp a) ad,
  ~ MEM (LoadGlob ad) (exps h) ->
  ~ MEM (LoadGlob ad) (FLAT (MAP exps (load_shape a0 i h))).
Proof.
  induction i as [|i IH] using N.peano_ind; intros a0 h ad Hn; [discriminate|].
  rewrite (proj2 (load_shape_def a0 h i)).
  specialize (IH (a0 + bytes_in_word)%w h ad Hn).
  unfold is_true in *; rewrite MEM_In in *.
  destruct (decide _); cbn [MAP FLAT exps]; rewrite !in_app_iff; cbn [FLAT MAP exps];
    rewrite ?app_nil_r; intros Hi; cbn [In] in *;
    repeat match goal with H : _ \/ _ |- _ => destruct H end; try discriminate; tauto.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "var_cexp_load_globals_empty" *)
Theorem var_cexp_load_globals_empty : forall ads (a0 : word 5),
  FLAT (MAP var_cexp (@load_globals a a0 ads)) = [].
Proof.
  induction ads as [|n IH] using N.peano_ind; intros a0; [reflexivity|].
  rewrite (proj2 (load_globals_def a0 n)); cbn [MAP FLAT var_cexp]; apply IH.
Qed.

Implicit Types fm lc : fmap varname (word_lab a).

Lemma FLOOKUP_res_var fm m (v : option (word_lab a)) n :
  FLOOKUP (res_var fm (m, v)) n = if decide (n = m) then v else FLOOKUP fm n.
Proof. destruct v; cbn [res_var]; fm_auto. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_distinct_eq" *)
Theorem flookup_res_var_distinct_eq : forall xs x fm,
  ~ MEM x (MAP FST xs) ->
  FLOOKUP (FOLDL res_var fm xs) x =
  FLOOKUP fm x.
Proof.
  induction xs as [|[y v] xs IH]; intros x fm Hn; [reflexivity|].
  cbn [FOLDL]. rewrite IH.
  - rewrite FLOOKUP_res_var. destruct (decide (x = y)) as [->|]; [|reflexivity].
    exfalso; apply Hn, MEM_In; left; reflexivity.
  - intros Hm; apply Hn, MEM_In; right; apply MEM_In, Hm.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_distinct_zip_eq" *)
Theorem flookup_res_var_distinct_zip_eq : forall xs (ys : list (option (word_lab a))) x fm,
  LENGTH xs = LENGTH ys /\
  ~ MEM x xs ->
  FLOOKUP (FOLDL res_var fm (ZIP (xs, ys))) x =
  FLOOKUP fm x.
Proof.
  intros xs ys x fm [_ Hn]. apply flookup_res_var_distinct_eq.
  intros Hm; apply Hn, MEM_In, (In_map_fst_ZIP xs ys), MEM_In, Hm.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_distinct" *)
Theorem flookup_res_var_distinct : forall ys xs (zs : list (option (word_lab a))) fm,
  distinct_lists xs ys /\
  LENGTH xs = LENGTH zs ->
  MAP (FLOOKUP (FOLDL res_var fm (ZIP (xs, zs)))) ys =
  MAP (FLOOKUP fm) ys.
Proof.
  intros ys xs zs fm [Hd Hl]. apply map_ext_in; intros y Hy.
  apply flookup_res_var_distinct_zip_eq; split; [exact Hl|].
  intros Hm. unfold distinct_lists, is_true in Hd. apply EVERY_Forall in Hd; rewrite Forall_forall in Hd.
  apply MEM_In in Hm. specialize (Hd y Hm). cbn in Hd.
  apply Bool.negb_true_iff in Hd. rewrite (proj2 (MEM_In y ys) Hy) in Hd. discriminate.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "flookup_res_var_zip_distinct" *)
Theorem flookup_res_var_zip_distinct : forall ys xs (as_ : list (word_lab a))
    (cs : list (option (word_lab a))) fm,
  distinct_lists xs ys /\
  LENGTH xs = LENGTH as_ /\
  LENGTH xs = LENGTH cs ->
  MAP (FLOOKUP (FOLDL res_var (fm |++ ZIP (xs, as_)) (ZIP (xs, cs)))) ys =
  MAP (FLOOKUP fm) ys.
Proof.
  intros ys xs as_ cs fm [Hd [H1 H2]].
  rewrite flookup_res_var_distinct by (split; assumption).
  apply map_ext_in; intros y Hy. apply FLOOKUP_FUPDATE_LIST_notin.
  intros Hi; apply In_map_fst_ZIP in Hi.
  unfold distinct_lists, is_true in Hd. apply EVERY_Forall in Hd; rewrite Forall_forall in Hd.
  specialize (Hd y Hi). cbn in Hd.
  apply Bool.negb_true_iff in Hd. rewrite (proj2 (MEM_In y ys) Hy) in Hd. discriminate.
Qed.

Lemma FOLDL_res_var_map_lookup (f : varname -> option (word_lab a)) xs m k :
  FLOOKUP (FOLDL res_var m (ZIP (xs, MAP f xs))) k =
  if in_dec (fun x y => decide (x = y)) k xs then f k else FLOOKUP m k.
Proof.
  revert m; induction xs as [|x xs IH]; intros m; [reflexivity|].
  cbn [MAP]. rewrite ZIP_cons. cbn [FOLDL]. rewrite IH, FLOOKUP_res_var.
  destruct (in_dec _ k xs), (in_dec _ k (x :: xs)); cbn in *; try tauto;
    destruct (decide (k = x)); subst; first [reflexivity | intuition congruence].
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "res_var_lookup_original_eq" *)
Theorem res_var_lookup_original_eq : forall xs (ys : list (word_lab a)) lc,
  ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ->
  FOLDL res_var (lc |++ ZIP (xs, ys)) (ZIP (xs, MAP (FLOOKUP lc) xs)) = lc.
Proof.
  intros xs ys lc _. apply fmap_ext; intros k.
  rewrite FOLDL_res_var_map_lookup. destruct (in_dec _ k xs) as [|Hn]; [reflexivity|].
  apply FLOOKUP_FUPDATE_LIST_notin. intros Hi; apply Hn, (In_map_fst_ZIP xs ys), Hi.
Qed.

Lemma OPT_MMAP_In_SOME {A B} (f : A -> option B) l ws x :
  OPT_MMAP f l = SOME ws -> In x l -> exists y, f x = SOME y.
Proof.
  revert ws; induction l as [|y l IH]; intros ws H Hi; [destruct Hi|].
  cbn in H. destruct (f y) eqn:Ey; [|discriminate].
  destruct (OPT_MMAP f l) eqn:El; [|discriminate].
  destruct Hi as [<-|Hi]; [eexists; exact Ey|exact (IH _ eq_refl Hi)].
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "eval_some_var_cexp_local_lookup" *)
Theorem eval_some_var_cexp_local_lookup : forall s (e : exp a) v n,
  eval s e = SOME v /\ MEM n (var_cexp e) ->
  exists w, FLOOKUP (locals s) n = SOME w.
Proof.
  intros s e; induction e as [w|v0|e IH|e IH|e IH|gd|op es IH|op es IH|c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using cexp_nested_ind; intros v n [He Hn]; cbn [eval var_cexp] in *;
    unfold is_true in Hn; rewrite MEM_In in Hn; cbn [In] in Hn; try tauto.
  - destruct Hn as [<-|[]]; eexists; exact He.
  - destruct (eval s e) as [[w]|] eqn:E; [|discriminate]. apply (IH (Word w)); split; [reflexivity|apply MEM_In, Hn].
  - destruct (eval s e) as [[w]|] eqn:E; [|discriminate]. apply (IH (Word w)); split; [reflexivity|apply MEM_In, Hn].
  - destruct (eval s e) as [[w]|] eqn:E; [|discriminate]. apply (IH (Word w)); split; [reflexivity|apply MEM_In, Hn].
  - destruct (OPT_MMAP (eval s) es) eqn:Eo; [|discriminate].
    apply in_concat in Hn as [l0 [Hl Hnl]]. apply in_map_iff in Hl as [x [<- Hx]].
    destruct (OPT_MMAP_In_SOME _ _ _ x Eo Hx) as [y Hy].
    eapply (proj1 (Forall_forall _ _) IH x Hx); split; [exact Hy|apply MEM_In, Hnl].
  - destruct (OPT_MMAP (eval s) es) eqn:Eo; [|discriminate].
    apply in_concat in Hn as [l0 [Hl Hnl]]. apply in_map_iff in Hl as [x [<- Hx]].
    destruct (OPT_MMAP_In_SOME _ _ _ x Eo Hx) as [y Hy].
    eapply (proj1 (Forall_forall _ _) IH x Hx); split; [exact Hy|apply MEM_In, Hnl].
  - destruct (eval s e1) as [[w1]|] eqn:E1, (eval s e2) as [[w2]|] eqn:E2; try discriminate.
    apply in_app_iff in Hn as [Hn|Hn]; [eapply IH1|eapply IH2]; (split; [reflexivity|apply MEM_In, Hn]).
  - destruct (eval s e1) as [[w1]|] eqn:E1, (eval s e2) as [[w2]|] eqn:E2; try discriminate.
    apply in_app_iff in Hn as [Hn|Hn]; [eapply IH1|eapply IH2]; (split; [reflexivity|apply MEM_In, Hn]).
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "opt_mmap_eval_some_var_cexp_local_lookup" *)
Theorem opt_mmap_eval_some_var_cexp_local_lookup : forall s (es : list (exp a)) vs n,
  OPT_MMAP (eval s) es = SOME vs /\ MEM n (FLAT (MAP var_cexp es)) ->
  exists w, FLOOKUP (locals s) n = SOME w.
Proof.
  intros s es vs n [Ho Hn]. unfold is_true in Hn; rewrite MEM_In in Hn.
  apply in_concat in Hn as [l0 [Hl Hnl]]. apply in_map_iff in Hl as [x [<- Hx]].
  destruct (OPT_MMAP_In_SOME _ _ _ x Ho Hx) as [y Hy].
  eapply eval_some_var_cexp_local_lookup; split; [exact Hy|apply MEM_In, Hnl].
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "eval_upd_clock_eq" *)
Theorem eval_upd_clock_eq : forall t (e : exp a) ck, eval (set_clock ck t) e = eval t e.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "opt_mmap_eval_upd_clock_eq" *)
Theorem opt_mmap_eval_upd_clock_eq : forall (es : list (exp a)) s ck,
  OPT_MMAP (eval (set_clock (ck + clock s) s)) es =
  OPT_MMAP (eval s) es.
Proof. intros; rewrite eval_set_clock; reflexivity. Qed.

End Globals.

(** ** Invariants of [evaluate]: code and I/O-event prefix *)

Lemma call_FFI_io_events_prefix {F} (st : ffi_state F) s conf bytes st' bytes' :
  call_FFI st s conf bytes = FFI_return st' bytes' ->
  is_true (isPREFIX (io_events st) (io_events st')).
Proof.
  unfold call_FFI; intros H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         end; try discriminate; injection H as <- _; cbn [io_events];
    first [apply isPREFIX_app_r | apply isPREFIX_refl].
Qed.

Section Invariants.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Definition code_io_inv s t : Prop :=
  code t = code s /\ is_true (isPREFIX (io_events (ffi s)) (io_events (ffi t))).

Lemma code_io_inv_refl s : code_io_inv s s.
Proof. split; [reflexivity|apply isPREFIX_refl]. Qed.

Lemma code_io_inv_trans s t u : code_io_inv s t -> code_io_inv t u -> code_io_inv s u.
Proof.
  intros [H1 H2] [H3 H4]; split; [congruence|eapply isPREFIX_trans; eassumption].
Qed.

Lemma sh_mem_op_code_io op r (ad : word a) s res t :
  sh_mem_op op r ad s = (res, t) -> code_io_inv s t.
Proof.
  intros H; destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
    repeat split_in H; injection H as _ <-; unfold code_io_inv; state_cbn;
    (split; [reflexivity|]); first [apply isPREFIX_refl | eapply call_FFI_io_events_prefix; eassumption].
Qed.

Ltac inv_close IH :=
  repeat match goal with
  | E : evaluate (?p', ?s') = (?r, ?s0) |- _ =>
      let Hc := fresh "Hc" in
      assert (Hc : code_io_inv s' s0) by (apply (IH (p', s') ltac:(lt_tac) r s0 E));
      clear E
  | E : sh_mem_op _ _ _ _ = (_, _) |- _ => apply sh_mem_op_code_io in E
  | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ => apply call_FFI_io_events_prefix in E
  end;
  unfold code_io_inv in *; state_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  split; [congruence|];
  eauto using isPREFIX_trans, isPREFIX_refl.

Lemma evaluate_code_io (p : prog a) s res t :
  evaluate (p, s) = (res, t) -> code_io_inv s t.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res t,
            evaluate x = (res, t) -> code_io_inv (snd x) t)
    by exact (G (p, s) res t).
  clear p s res t.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros res t H; cbn [snd].
  destruct p; unfold_eval_in H; repeat split_in H.
  all: first [ injection H as _ <- | idtac ].
  all: inv_close IH.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall (exps : prog a) s1 res s2,
  evaluate (exps, s1) = (res, s2)
  ->
  is_true (isPREFIX (io_events (ffi s1)) (io_events (ffi s2))).
Proof. intros p s1 res s2 H; apply (evaluate_code_io p s1 res s2 H). Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_code_invariant" *)
Theorem evaluate_code_invariant : forall (p : prog a) t res st,
  evaluate (p, t) = (res, st) ->
  code st = code t.
Proof. intros p t res st H; apply (evaluate_code_io p t res st H). Qed.

End Invariants.

(** ** Adding clock *)

Ltac st_eq :=
  cbv beta iota delta [set_clock dec_clock set_locals set_memory set_ffi set_code set_globals
       set_var empty_locals];
  cbn [clock locals globals code memory memaddrs sh_memaddrs be ffi base_addr top_addr];
  first [ reflexivity | f_equal; lia ].

Ltac add_clock_rw IH ck :=
  match goal with
  | E : evaluate (?p', ?Y) = (?r, ?s0) |- context [evaluate (?p', ?X)] =>
      let Hx := fresh "Hx" in
      assert (Hx : evaluate (p', set_clock (clock Y + ck) Y) = (r, set_clock (clock s0 + ck) s0))
        by (apply (IH (p', Y) ltac:(lt_tac) r s0 ck E); first [discriminate | assumption | congruence]);
      replace X with (set_clock (clock Y + ck) Y) by st_eq;
      rewrite Hx; clear Hx; cbn beta iota zeta
  end.

Ltac rw_eqs :=
  repeat match goal with
  | E : ?x = _ |- context [?x] =>
      tryif is_var x then fail else (rewrite E; cbn beta iota zeta)
  end.

Ltac clock_tests ck :=
  repeat match goal with
  | |- context [(?c + ck =? 0)%N] =>
      let E := fresh "Ec" in
      destruct (N.eqb_spec (c + ck) 0) as [E|E]; [exfalso; lia|]; cbn beta iota zeta
  end.

Section AddClock.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Lemma sh_mem_op_set_clock op v (addr : word a) k s :
  sh_mem_op op v addr (set_clock k s) =
  (fst (sh_mem_op op v addr s), set_clock k (snd (sh_mem_op op v addr s))).
Proof.
  destruct op; cbn [sh_mem_op]; unfold sh_mem_load, sh_mem_store; destruct s; cbn;
    repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x eqn:?; cbn beta iota zeta end; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_add_clock_eq" *)
Theorem evaluate_add_clock_eq : forall (p : prog a) t res st ck,
  evaluate (p, t) = (res, st) /\ res <> SOME TimeOut ->
  evaluate (p, set_clock (clock t + ck) t) = (res, set_clock (clock st + ck) st).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall res st ck,
            evaluate x = (res, st) -> res <> SOME TimeOut ->
            evaluate (fst x, set_clock (clock (snd x) + ck) (snd x)) =
              (res, set_clock (clock st + ck) st))
    by (intros p t res st ck [H1 H2]; exact (G (p, t) res st ck H1 H2)).
  intros x; induction x as [[p t] IH] using (well_founded_induction eval_lt_wf).
  intros res st ck H Hres; cbn [fst snd].
  destruct p; unfold_eval_in H; rewrite evaluate_unfold; cbn [evaluate_body]; rewrite ?fcl_evaluate;
    cbn beta; eval_simp; state_cbn; repeat split_in H; eqb_facts.
  all: first [ injection H as <- <-; first [ exfalso; apply Hres; reflexivity | idtac ] | idtac ].
  all: repeat (first [ progress rw_eqs | progress clock_tests ck | add_clock_rw IH ck ]).
  all: try reflexivity.
  all: try solve [ f_equal; st_eq ].
  all: pose proof (sh_mem_op_clock _ _ _ _ _ _ H) as Hc;
       rewrite sh_mem_op_set_clock, H; cbn [fst snd]; rewrite Hc; reflexivity.
Qed.

End AddClock.

Section AddClockIO.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.

Ltac add_clock_rw2 ck :=
  match goal with
  | E : evaluate (?p', ?Y) = (?r, ?s0) |- context [evaluate (?p', ?X)] =>
      lazymatch r with SOME TimeOut => fail | _ => idtac end;
      let Hx := fresh "Hx" in
      assert (Hx : evaluate (p', set_clock (clock Y + ck) Y) = (r, set_clock (clock s0 + ck) s0))
        by (apply evaluate_add_clock_eq; split; [exact E|first [discriminate | assumption | congruence]]);
      replace X with (set_clock (clock Y + ck) Y) by st_eq;
      rewrite Hx; clear Hx; cbn beta iota zeta
  end.

Ltac cont_mono :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             let E := fresh "C" in destruct x eqn:E; cbn beta iota zeta
         | |- context [evaluate ?y] =>
             let E := fresh "C" in destruct (evaluate y) eqn:E; cbn beta iota zeta
         end;
  repeat match goal with
         | E : evaluate (_, _) = (_, _) |- _ => apply evaluate_io_events_mono in E
         end;
  cbn [fst snd] in *; state_cbn; eauto 8 using isPREFIX_trans, isPREFIX_refl.

Ltac to_case IH ck :=
  clock_tests ck;
  match goal with
  | E : evaluate (?p', ?Y) = (SOME TimeOut, ?t1) |- context [evaluate (?p', ?X)] =>
      replace X with (set_clock (clock Y + ck) Y) by st_eq;
      let Hih := fresh "Hih" in
      pose proof (IH (p', Y) ltac:(lt_tac) ck) as Hih; cbn [fst snd] in Hih;
      rewrite E in Hih; cbn [snd] in Hih;
      intros _; revert Hih;
      let r1 := fresh "r" in let t1' := fresh "t" in let E1 := fresh "E" in
      destruct (evaluate (p', set_clock (clock Y + ck) Y)) as [r1 t1'] eqn:E1;
      cbn [snd]; intros Hih; cont_mono
  end.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_add_clock_io_events_mono" *)
Theorem evaluate_add_clock_io_events_mono : forall (exps : prog a) s extra,
  is_true (isPREFIX (io_events (ffi (snd (evaluate (exps, s)))))
    (io_events (ffi (snd (evaluate (exps, set_clock (clock s + extra) s)))))).
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall extra,
            is_true (isPREFIX (io_events (ffi (snd (evaluate x))))
              (io_events (ffi (snd (evaluate (fst x, set_clock (clock (snd x) + extra) (snd x))))))))
    by (intros p s extra; exact (G (p, s) extra)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros extra; cbn [fst snd].
  destruct (evaluate (p, s)) as [r t] eqn:H.
  destruct (decide (r = SOME TimeOut)) as [->|Hr].
  2: { rewrite (evaluate_add_clock_eq p s r t extra (conj H Hr)); cbn [snd ffi set_clock].
       apply isPREFIX_refl. }
  cbn [snd].
  pose proof (evaluate_io_events_mono p (set_clock (clock s + extra) s) _ _ (surjective_pairing _))
    as Hmono.
  cbn [ffi set_clock] in Hmono. revert Hmono.
  destruct p; unfold_eval_in H; rewrite evaluate_unfold; cbn [evaluate_body]; rewrite ?fcl_evaluate;
    cbn beta; eval_simp; state_cbn; repeat split_in H; eqb_facts.
  all: first [ discriminate H
             | injection H; repeat (match goal with |- _ = _ -> _ => intro end); subst
             | idtac ].
  all: repeat (first [ progress rw_eqs | add_clock_rw2 extra ]).
  all: first [ solve [ intros Hm; state_cbn; exact Hm ]
             | solve [ rewrite sh_mem_op_set_clock, H; cbn [fst snd]; intros _; state_cbn;
                       apply isPREFIX_refl ]
             | to_case IH extra ].
Qed.

End AddClockIO.

(** ** Store and load sequences *)

Lemma GENLIST_ext {A} (f g : N -> A) n :
  (forall i, (i < n)%N -> f i = g i) -> GENLIST f n = GENLIST g n.
Proof.
  revert f g. induction n as [|n IH] using N.peano_ind; intros f g H; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), (proj2 (GENLIST_thm g n)), (IH f g) by (intros; apply H; lia).
  rewrite H by lia; reflexivity.
Qed.

Section Stores.
Context {a : N} {ffi_t : Type}.
Implicit Types s t : state a ffi_t.
Local Open Scope word_scope.

Lemma FLOOKUP_ZIP_Forall2 (f : fmap varname (word_lab a)) es vs :
  is_true (ALL_DISTINCT es) -> LENGTH es = LENGTH vs ->
  Forall2 (fun e v => FLOOKUP (f |++ ZIP (es, vs)) e = SOME v) es vs.
Proof.
  revert f vs; induction es as [|e es IH]; intros f [|v vs] Hd Hl;
    rewrite ?LENGTH_cons in Hl; cbn in Hl; try lia; [constructor|].
  cbn in Hd; unfold is_true in Hd; apply Bool.andb_true_iff in Hd as [Hm Hd].
  rewrite ZIP_cons. change ((f |+ (e, v)) |++ ZIP (es, vs)) with (f |++ ((e, v) :: ZIP (es, vs))).
  constructor.
  - cbn [FUPDATE_LIST FOLDL]. change (FOLDL FUPDATE (f |+ (e, v)) (ZIP (es, vs))) with ((f |+ (e, v)) |++ ZIP (es, vs)).
    rewrite FLOOKUP_FUPDATE_LIST_notin; [fm_auto|].
    intros Hi; apply In_map_fst_ZIP, MEM_In in Hi. rewrite Hi in Hm; discriminate.
  - apply (IH (f |+ (e, v)) vs Hd); lia.
Qed.

Lemma evaluate_stores_gen : forall (es : list varname) vs ad (addr : word a) a0 s m res t,
  FLOOKUP (locals s) ad = SOME (Word addr) ->
  Forall2 (fun e v => FLOOKUP (locals s) e = SOME v) es vs ->
  panSem.mem_stores (addr + a0) vs (memaddrs s) (memory s) = SOME m ->
  evaluate (nested_seq (stores (Var ad) (MAP Var es) a0), s) = (res, t) ->
  res = NONE /\ t = set_memory m s.
Proof.
  induction es as [|e es IH]; intros vs ad addr a0 s m res t Had Hf Hm H; inversion Hf; subst.
  - cbn in Hm; injection Hm as <-. cbn [MAP stores nested_seq] in H; rewrite (proj1 evaluate_def) in H.
    injection H as <- <-; split; [reflexivity|destruct s; reflexivity].
  - rename y into v, l' into vs.
    cbn [panSem.mem_stores] in Hm. destruct (mem_store (addr + a0) v (memaddrs s) (memory s)) as [m'|] eqn:Ems;
      [|discriminate].
    cbn [MAP stores] in H.
    assert (Hst : evaluate (if decide (a0 = n2w 0) then Store (Var ad) (Var e)
                            else Store (Op Add [Var ad; Const a0]) (Var e), s) = (NONE, set_memory m' s)).
    { destruct (decide _) as [->|]; rewrite evaluate_unfold; cbn [evaluate_body eval OPT_MMAP OPTION_BIND]; rewrite Had;
        match goal with H2 : FLOOKUP (locals s) e = SOME v |- _ => rewrite H2 end.
      - replace (addr + n2w 0) with addr in Ems by word_ring. cbn. rewrite Ems; reflexivity.
      - cbn. unfold wordLang.word_op; cbn [FOLDR].
        replace (addr + (a0 + n2w 0)) with (addr + a0) by word_ring. rewrite Ems; reflexivity. }
    destruct (decide _); cbn [nested_seq] in H; rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))))) in H;
      rewrite Hst in H; cbn beta iota in H;
      (apply IH with (vs := vs) (addr := addr) (m := m) in H;
       [ destruct H as [-> ->]; split; [reflexivity | destruct s; reflexivity]
       | exact Had | assumption
       | state_cbn; replace (addr + (a0 + bytes_in_word)) with (addr + a0 + bytes_in_word)
           by word_ring; exact Hm ]).
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_seq_stores_mem_state_rel" *)
Theorem evaluate_seq_stores_mem_state_rel : forall es vs ad a0 s res t addr m,
  LENGTH es = LENGTH vs /\ ~ MEM ad es /\ ALL_DISTINCT es /\
  panSem.mem_stores (addr + a0) vs (memaddrs s) (memory s) = SOME m /\
  evaluate (nested_seq (stores (Var ad) (MAP Var es) a0),
            set_locals (locals s |++
              ((ad, Word addr) :: ZIP (es, vs))) s) = (res, t) ->
  res = NONE /\ memory t = m /\
  memaddrs t = memaddrs s /\
  sh_memaddrs t = sh_memaddrs s /\ be t = be s /\
  ffi t = ffi s /\ code t = code s /\ clock t = clock s /\
  base_addr t = base_addr s /\
  top_addr t = top_addr s.
Proof.
  intros es vs ad a0 s res t addr m (Hl & Hn & Hd & Hm & H).
  eapply evaluate_stores_gen in H as [-> ->].
  - repeat split.
  - state_cbn. change (locals s |++ ((ad, Word addr) :: ZIP (es, vs)))
      with ((locals s |+ (ad, Word addr)) |++ ZIP (es, vs)).
    rewrite FLOOKUP_FUPDATE_LIST_notin; [fm_auto|].
    intros Hi; apply In_map_fst_ZIP, MEM_In in Hi; exact (Hn Hi).
  - state_cbn. change (locals s |++ ((ad, Word addr) :: ZIP (es, vs)))
      with ((locals s |+ (ad, Word addr)) |++ ZIP (es, vs)).
    apply FLOOKUP_ZIP_Forall2; assumption.
  - exact Hm.
Qed.

Lemma Forall2_FLOOKUP_set_globals es vs g (w : word_lab a) s :
  Forall2 (fun e v => FLOOKUP (locals s) e = SOME v) es vs ->
  Forall2 (fun e v => FLOOKUP (locals (set_globals g w s)) e = SOME v) es vs.
Proof. exact (fun H => H). Qed.

Lemma evaluate_store_globals_gen : forall (vars : list varname) vs (a0 : word 5) s,
  Forall2 (fun e v => FLOOKUP (locals s) e = SOME v) vars vs ->
  evaluate (nested_seq (store_globals a0 (MAP Var vars)), s) =
  (NONE, set_globals_field (globals s |++ ZIP (GENLIST (fun x => a0 + n2w x) (LENGTH vs), vs)) s).
Proof.
  induction vars as [|h vars IH]; intros vs a0 s Hf; inversion Hf; subst.
  - cbn [MAP store_globals nested_seq LENGTH ZIP]. rewrite (proj1 evaluate_def). destruct s; reflexivity.
  - rename y into v, l' into vs.
    cbn [MAP store_globals nested_seq].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))))).
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))).
    cbn [eval]. match goal with H2 : FLOOKUP (locals s) h = SOME v |- _ => rewrite H2 end.
    cbn beta iota. rewrite (IH vs) by assumption.
    f_equal. unfold set_globals_field, set_globals; cbn [locals globals code memory memaddrs
      sh_memaddrs clock be ffi base_addr top_addr]. f_equal.
    rewrite LENGTH_cons, N.add_1_r, GENLIST_CONS_aux, ZIP_cons, (proj2 (FUPDATE_LIST_THM _)).
    replace (a0 + n2w 0) with a0 by word_ring.
    rewrite (GENLIST_ext _ (fun i => a0 + n2w (SUC i))); [reflexivity|].
    intros i _; word_Z; apply zcong_eq; rewrite N2Z.inj_succ; ring.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_seq_store_globals_res" *)
Theorem evaluate_seq_store_globals_res : forall vars vs t (a0 : word 5),
  ALL_DISTINCT vars /\ LENGTH vars = LENGTH vs /\ (w2n a0 + LENGTH vs <= 32)%N ->
  evaluate (nested_seq (store_globals a0 (MAP Var vars)),
            set_locals (locals t |++ ZIP (vars, vs)) t) =
  (NONE, set_globals_field (globals t |++ ZIP (GENLIST (fun x => a0 + n2w x) (LENGTH vs), vs))
           (set_locals (locals t |++ ZIP (vars, vs)) t)).
Proof.
  intros vars vs t a0 (Hd & Hl & _).
  rewrite (evaluate_store_globals_gen vars vs); [reflexivity|].
  apply FLOOKUP_ZIP_Forall2; assumption.
Qed.

Lemma evaluate_assign_load_globals_gen : forall ns t (a0 : word 5),
  (forall n, MEM n ns -> FLOOKUP (locals t) n <> NONE) /\
  (forall n, MEM n (GENLIST (fun x => a0 + n2w x) (LENGTH ns)) -> FLOOKUP (globals t) n <> NONE) ->
  evaluate (nested_seq (MAP2 Assign ns (load_globals a0 (LENGTH ns))), t) =
  (NONE, set_locals (locals t |++
           ZIP (ns, MAP (fun n => THE (FLOOKUP (globals t) n)) (GENLIST (fun x => a0 + n2w x) (LENGTH ns)))) t).
Proof.
  induction ns as [|h ns IH]; intros t a0 (Hloc & Hglob).
  - cbn [MAP2 nested_seq LENGTH]. rewrite (proj1 evaluate_def). destruct t; reflexivity.
  - rewrite LENGTH_cons, N.add_1_r, (proj2 (load_globals_def a0 (LENGTH ns))), GENLIST_CONS_aux.
    cbn [MAP2 nested_seq MAP].
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 evaluate_def)))))))))).
    rewrite (proj1 (proj2 (proj2 (proj2 evaluate_def)))).
    cbn [eval].
    assert (Hg : FLOOKUP (globals t) a0 <> NONE).
    { apply Hglob. rewrite LENGTH_cons, N.add_1_r, GENLIST_CONS_aux.
      replace (a0 + n2w 0) with a0 by word_ring. apply MEM_In; left; reflexivity. }
    assert (Hlh : FLOOKUP (locals t) h <> NONE) by (apply Hloc, MEM_In; left; reflexivity).
    destruct (FLOOKUP (globals t) a0) as [x|] eqn:Ex; [|congruence].
    destruct (FLOOKUP (locals t) h) as [y|] eqn:Ey; [|congruence].
    cbn beta iota.
    rewrite IH.
    + f_equal. unfold set_locals; cbn [locals globals code memory memaddrs sh_memaddrs clock be
        ffi base_addr top_addr]. f_equal.
      replace (a0 + n2w 0) with a0 by word_ring. rewrite Ex. cbn [THE MAP].
      rewrite ZIP_cons, (proj2 (FUPDATE_LIST_THM _)).
      rewrite (GENLIST_ext (fun x0 => a0 + n2w 1 + n2w x0) (fun i => a0 + n2w (SUC i))); [reflexivity|].
      intros i _; word_Z; apply zcong_eq; rewrite N2Z.inj_succ; ring.
    + split.
      * intros n Hn. state_cbn. rewrite FLOOKUP_UPDATE. destruct (decide _); [discriminate|].
        apply Hloc, MEM_In; right; apply MEM_In, Hn.
      * intros n Hn. state_cbn. apply Hglob. rewrite LENGTH_cons, N.add_1_r, GENLIST_CONS_aux.
        apply MEM_In; right. apply MEM_In in Hn. 
        erewrite GENLIST_ext; [exact Hn|]. intros i _. word_Z; apply zcong_eq; rewrite N2Z.inj_succ; ring.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_seq_assign_load_globals" *)
Theorem evaluate_seq_assign_load_globals : forall ns t (a0 : word 5),
  ALL_DISTINCT ns /\ (w2n a0 + LENGTH ns <= 32)%N /\
  (forall n, MEM n ns -> FLOOKUP (locals t) n <> NONE) /\
  (forall n, MEM n (GENLIST (fun x => a0 + n2w x) (LENGTH ns)) -> FLOOKUP (globals t) n <> NONE) ->
  evaluate (nested_seq (MAP2 Assign ns (load_globals a0 (LENGTH ns))), t) =
  (NONE, set_locals (locals t |++
           ZIP (ns, MAP (fun n => THE (FLOOKUP (globals t) n)) (GENLIST (fun x => a0 + n2w x) (LENGTH ns)))) t).
Proof. intros ns t a0 (_ & _ & H1 & H2); apply evaluate_assign_load_globals_gen; split; assumption. Qed.

End Stores.

(** ** Flattened memory loads *)

Lemma EL_app_N {A} `{Inhabited A} n (l1 l2 : list A) :
  (n < LENGTH (l1 ++ l2))%N ->
  EL n (l1 ++ l2) = if (n <? LENGTH l1)%N then EL n l1 else EL (n - LENGTH l1) l2.
Proof.
  intros Hn. rewrite !LENGTH_length, length_app in *.
  rewrite EL_nth by (rewrite LENGTH_length, length_app; lia).
  destruct (N.ltb_spec n (N.of_nat (length l1))).
  - rewrite EL_nth by (rewrite LENGTH_length; lia). apply app_nth1; lia.
  - rewrite EL_nth by (rewrite LENGTH_length; lia). rewrite app_nth2 by lia.
    f_equal; lia.
Qed.

Section MemLoadFlat.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

Lemma LENGTH_app {A} (l1 l2 : list A) : LENGTH (l1 ++ l2) = (LENGTH l1 + LENGTH l2)%N.
Proof. rewrite !LENGTH_length, length_app; lia. Qed.

Lemma mem_load_flat_gen : forall sh (adr : word a) dm m stcs v,
  panSem.mem_load sh adr dm m stcs = SOME v -> is_true (panProps.is_wf_shape_nil sh) ->
  LENGTH (panSem.flatten v) = panLang.size_of_sh_with_ctxt stcs sh /\
  forall (s : state a ffi_t) n, (n < LENGTH (panSem.flatten v))%N -> dm = memaddrs s -> m = memory s ->
    mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (panSem.flatten v)).
Proof.
  intros sh; induction sh as [|shs IH|nm] using panSem.shape_nested_ind;
    intros adr dm m stcs v Hl Hwf; rewrite (proj1 panSem.mem_load_def) in Hl.
  - destruct (classical_dec _) as [Hin|]; [|discriminate]. injection Hl as <-.
    split; [reflexivity|]. intros s n Hn -> ->. cbn in Hn. assert (n = 0%N) as -> by lia.
    unfold mem_load. replace (adr + bytes_in_word * n2w 0) with adr by word_ring.
    destruct (classical_dec _); [reflexivity|contradiction].
  - destruct (panSem.mem_loads shs adr dm m stcs) as [vs|] eqn:Hls; [|discriminate].
    injection Hl as <-. cbn [panSem.flatten panLang.size_of_sh_with_ctxt].
    cbn [panLang.is_wf_shape] in Hwf.
    revert adr vs Hls Hwf; induction IH as [|sh shs Hsh Hshs IHl]; intros adr vs Hls Hwf.
    + rewrite (proj1 (proj2 panSem.mem_load_def)) in Hls. injection Hls as <-.
      split; [reflexivity|]. intros s n Hn; cbn in Hn; lia.
    + cbn [EVERY] in Hwf; unfold is_true in Hwf; apply Bool.andb_true_iff in Hwf as [Hw1 Hw2].
      rewrite (proj1 (proj2 (proj2 panSem.mem_load_def))) in Hls.
      destruct (panSem.mem_load sh adr dm m stcs) as [v0|] eqn:E1; [|discriminate].
      destruct (panSem.mem_loads shs _ dm m stcs) as [vs0|] eqn:E2; [|discriminate].
      injection Hls as <-.
      destruct (Hsh adr dm m stcs v0 E1 Hw1) as [Hlen1 Hel1].
      destruct (IHl _ vs0 E2 Hw2) as [Hlen2 Hel2].
      cbn [MAP FLAT SUM]. rewrite LENGTH_app, Hlen1, Hlen2.
      split; [reflexivity|]. intros s n Hn Hdm Hm.
      assert (Hn' : (n < LENGTH (panSem.flatten v0 ++ FLAT (MAP panSem.flatten vs0)))%N)
        by (rewrite LENGTH_app, Hlen1, Hlen2; exact Hn).
      rewrite EL_app_N by exact Hn'.
      destruct (N.ltb_spec n (LENGTH (panSem.flatten v0))).
      * apply Hel1; assumption.
      * rewrite <- (Hel2 s ((n - LENGTH (panSem.flatten v0))%N)) by (try assumption; lia).
        f_equal. rewrite Hlen1. word_Z; apply zcong_eq.
        rewrite N2Z.inj_sub by lia. ring.
  - cbn in Hwf. discriminate.
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "mem_loads_flat_rel" *)
Theorem mem_loads_flat_rel :
  (forall sh adr dm (m : word a -> word_lab a) stcs v,
     panSem.mem_load sh adr dm m stcs = SOME v /\ panProps.is_wf_shape_nil sh ->
     forall (s : state a ffi_t) n,
       (n < LENGTH (panSem.flatten v))%N ->
       dm = memaddrs s ->
       m = memory s ->
       mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (panSem.flatten v))) /\
  (forall shs adr dm (m : word a -> word_lab a) stcs v,
     panSem.mem_loads shs adr dm m stcs = SOME v /\ EVERY (panProps.is_wf_shape_nil) shs ->
     forall (s : state a ffi_t) n,
       (n < LENGTH (FLAT (MAP panSem.flatten v)))%N ->
       dm = memaddrs s ->
       m = memory s ->
       mem_load (adr + bytes_in_word * n2w n) s = SOME (EL n (FLAT (MAP panSem.flatten v)))) /\
  (forall flds adr dm (m : word a -> word_lab a) stcs vs,
     panSem.mem_load_flds flds adr dm m stcs = SOME vs ->
     True).
Proof.
  split; [|split; [|tauto]].
  - intros sh adr dm m stcs v [Hl Hw]. exact (proj2 (mem_load_flat_gen sh adr dm m stcs v Hl Hw)).
  - intros shs adr dm m stcs v [Hl Hw].
    assert (Hc : panSem.mem_load (panLang.Comb shs) adr dm m stcs = SOME (panSem.RStruct v)).
    { rewrite (proj1 panSem.mem_load_def), Hl; reflexivity. }
    exact (proj2 (mem_load_flat_gen _ adr dm m stcs _ Hc Hw)).
Qed.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "mem_load_flat_rel" *)
Theorem mem_load_flat_rel : forall sh adr (s : state a ffi_t) v n stcs,
  panSem.mem_load sh adr (memaddrs s) (memory s) stcs = SOME v /\
  (n < LENGTH (panSem.flatten v))%N /\
  panProps.is_wf_shape_nil sh ->
  mem_load (adr + bytes_in_word * n2w (LENGTH (TAKE n (panSem.flatten v)))) s =
  SOME (EL n (panSem.flatten v)).
Proof.
  intros sh adr s v n stcs (Hl & Hn & Hw).
  replace (LENGTH (TAKE n (panSem.flatten v))) with n.
  - apply (proj1 mem_loads_flat_rel sh adr _ _ stcs v (conj Hl Hw) s n Hn eq_refl eq_refl).
  - rewrite TAKE_firstn, LENGTH_length, length_firstn. rewrite LENGTH_length in Hn. lia.
Qed.

End MemLoadFlat.

(** ** Expressions of programs *)

Section ExpsOf.
Context {a : N}.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "exps_of_def" *)
Fixpoint exps_of (p : prog a) : list (exp a) :=
  match p with
  | Dec _ e p => e :: exps_of p
  | Seq p q => exps_of p ++ exps_of q
  | If e p q => e :: exps_of p ++ exps_of q
  | While e p => e :: exps_of p
  | Call NONE e es => es
  | Call (SOME (_, NONE)) e es => es
  | Call (SOME (_, SOME (_, p'))) e es => es ++ exps_of p'
  | Store e1 e2 => [e1; e2]
  | Store32 e1 e2 => [e1; e2]
  | StoreByte e1 e2 => [e1; e2]
  | StoreGlob _ e => [e]
  | crepLang.Return es => es
  | Assign _ e => [e]
  | ShMem _ _ e => [e]
  | _ => []
  end.

(*! HOL "cakeml/pancake/semantics/crepPropsScript.sml" "every_exp_def" *)
Fixpoint every_exp (P : exp a -> bool) (e : exp a) : bool :=
  match e with
  | Const w => P (Const w)
  | Var v => P (Var v)
  | Load e => P (Load e) && every_exp P e
  | Load32 e => P (Load32 e) && every_exp P e
  | LoadByte e => P (LoadByte e) && every_exp P e
  | LoadGlob w => P (LoadGlob w)
  | Op bop es => P (Op bop es) && EVERY (every_exp P) es
  | Crepop op es => P (Crepop op es) && EVERY (every_exp P) es
  | Cmp c e1 e2 => P (Cmp c e1 e2) && every_exp P e1 && every_exp P e2
  | Shift sh e1 e2 => P (Shift sh e1 e2) && every_exp P e1 && every_exp P e2
  | BaseAddr => P BaseAddr
  | TopAddr => P TopAddr
  end.

End ExpsOf.
