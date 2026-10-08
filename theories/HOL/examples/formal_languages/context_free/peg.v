(** * HOL4 [peg]: parsing expression grammars

    Port of [HOL/examples/formal-languages/context-free/pegScript.sml]
    (after Koprowski and Binzstok, "TRX: A Formally Verified Parser
    Interpreter").

    Type parameters: HOL's [('a,'b,'c,'e) pegsym] is [pegsym A B C E] (token,
    nonterminal, semantic value and error types).  HOL's [peg] record and
    [pegresult] keep their field/constructor names and order.  HOL tuples
    nest to the right: the result of [peg_eval_list] is
    [(s1, (list, err))].

    The relation [peg0]/[peggt0]/[pegfail] has rules whose premises are
    disjunctions in HOL; here each disjunct is its own constructor (the
    defined relations are the same), which keeps the generated induction
    principle usable.  [peg_eval]/[wfpeg] have HOL's rules one-for-one.

    [subexprs], [Gexprs] are sets ([A -> Prop]).  [pegf], [choicel],
    [checkAhead] use [ARB] values as HOL does.

    Theorems about [IS_SUFFIX]/[IS_PREFIX] ([peg_eval_suffix],
    [peg_eval_suffix'], [peg_eval_list_suffix'], [IS_PREFIX_MEM]) are not
    ported ([rich_list] has no [IS_PREFIX] yet); their content is proved in
    the untagged [peg_eval_suffix_app]/[peg_eval_suffix_len].
    [peg_eval_strongind'] (a reformulated induction principle) is replaced
    by the Rocq schemes [peg_eval_mutind]; [lemma4_1a] is proved in the
    form of HOL's [lemma4_1a0] (untagged, as [lemma4_1a0]'s statement is
    [local] and [lemma4_1a] is its [SIMP_RULE] normal form). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.HOL.examples.formal_languages.context_free Require Import location grammar.
Open Scope N_scope.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "pegsym" *)
Inductive pegsym (A B C E : Type) : Type :=
| empty : C -> pegsym A B C E
| any : (A * locs -> C) -> pegsym A B C E
| tok : (A -> bool) -> (A * locs -> C) -> pegsym A B C E
| nt : inf B -> (C -> C) -> pegsym A B C E
| seq : pegsym A B C E -> pegsym A B C E -> (C -> C -> C) -> pegsym A B C E
| choice : pegsym A B C E -> pegsym A B C E -> (C + C -> C) -> pegsym A B C E
| rpt : pegsym A B C E -> (list C -> C) -> pegsym A B C E
| not : pegsym A B C E -> C -> pegsym A B C E
| error : E -> pegsym A B C E.
Arguments empty {A B C E} _.
Arguments any {A B C E} _.
Arguments tok {A B C E} _ _.
Arguments nt {A B C E} _ _.
Arguments seq {A B C E} _ _ _.
Arguments choice {A B C E} _ _ _.
Arguments rpt {A B C E} _ _.
Arguments not {A B C E} _ _.
Arguments error {A B C E} _.

#[global] Instance pegsym_inhabited {A B C E} : Inhabited (pegsym A B C E) :=
  nt (inr 0) (fun x => x).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg" *)
Record peg (A B C E : Type) : Type := {
  start : pegsym A B C E;
  anyEOF : E;
  tokFALSE : E;
  tokEOF : E;
  notFAIL : E;
  rules : fmap (inf B) (pegsym A B C E)
}.
Arguments start {A B C E} _.
Arguments anyEOF {A B C E} _.
Arguments tokFALSE {A B C E} _.
Arguments tokEOF {A B C E} _.
Arguments notFAIL {A B C E} _.
Arguments rules {A B C E} _.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "pegresult" *)
Inductive pegresult (A C E : Type) : Type :=
| Success : A -> C -> option (locs * E) -> pegresult A C E
| Failure : locs -> E -> pegresult A C E.
Arguments Success {A C E} _ _ _.
Arguments Failure {A C E} _ _.

Section Results.
Context {A C E : Type}.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "isSuccess_def" *)
Definition isSuccess (r : pegresult A C E) : bool :=
  match r with Success _ _ _ => true | Failure _ _ => false end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "isFailure_def" *)
Definition isFailure (r : pegresult A C E) : bool :=
  match r with Success _ _ _ => false | Failure _ _ => true end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "resultmap_def" *)
Definition resultmap {D} (f : C -> D) (r : pegresult A C E) : pegresult A D E :=
  match r with
  | Success a c eo => Success a (f c) eo
  | Failure fl fe => Failure fl fe
  end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "resultmap_EQ_Success" *)
Theorem resultmap_EQ_Success : forall {D} (f : C -> D) r a x eo,
  resultmap f r = Success a x eo <-> exists x0, r = Success a x0 eo /\ x = f x0.
Proof.
  intros D f [a0 c0 eo0|fl fe] a x eo; cbn; split.
  - intros h; injection h as <- <- <-; eauto.
  - intros [x0 [h ->]]; injection h as <- <- <-; reflexivity.
  - discriminate.
  - intros [x0 [h _]]; discriminate.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "resultmap_EQ_Failure" *)
Theorem resultmap_EQ_Failure : forall {D} (f : C -> D) r fl fe,
  (resultmap f r = Failure fl fe <-> r = Failure fl fe) /\
  (Failure fl fe = resultmap f r <-> r = Failure fl fe).
Proof. intros D f [] fl fe; cbn; repeat split; congruence. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "resultmap_I" *)
Theorem resultmap_I : forall (r : pegresult A C E), resultmap (fun x => x) r = r.
Proof. intros []; reflexivity. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "UNCURRY_Failure_EQ_Success" *)
Theorem UNCURRY_Failure_EQ_Success : forall (fle : locs * E) (s : A) (r : C) eo,
  UNCURRY Failure fle <> Success s r eo.
Proof. intros [] s r eo; discriminate. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "FORALL_result" *)
Theorem FORALL_result : forall P : pegresult A C E -> Prop,
  (forall r, P r) <-> (forall a c eo, P (Success a c eo)) /\ (forall fl fe, P (Failure fl fe)).
Proof. intros P; split; [intros h; split; intros; apply h|intros [h1 h2] []; auto]. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "EXISTS_result" *)
Theorem EXISTS_result : forall P : pegresult A C E -> Prop,
  (exists r, P r) <-> (exists a c eo, P (Success a c eo)) \/ (exists fl fe, P (Failure fl fe)).
Proof.
  intros P; split.
  - intros [[] h]; [left|right]; eauto.
  - intros [[a [c [eo h]]]|[fl [fe h]]]; eauto.
Qed.

End Results.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "MAXerr_def" *)
Definition MAXerr {E} (p1 p2 : locs * E) : locs * E :=
  let (fl1, fe1) := p1 in let (fl2, fe2) := p2 in
  if locsle fl1 fl2 then (fl2, fe2) else (fl1, fe1).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "optmax_def" *)
Definition optmax {X} (f : X -> X -> X) (o1 o2 : option X) : option X :=
  match o1, o2 with
  | NONE, NONE => NONE
  | NONE, SOME x => SOME x
  | SOME x, NONE => SOME x
  | SOME x, SOME y => SOME (f x y)
  end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "sloc_def" *)
Definition sloc {A} (l : list (A * locs)) : locs :=
  match l with [] => Locs EOFpt EOFpt | h :: t => SND h end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "sloc_thm" *)
Theorem sloc_thm : forall {A} (c : A) l t,
  sloc (@nil (A * locs)) = Locs EOFpt EOFpt /\ sloc ((c, l) :: t) = l.
Proof. split; reflexivity. Qed.

Section Eval.
Context {A B C E : Type}.

#[local] Abbreviation input := (list (A * locs)).
#[local] Abbreviation psym := (pegsym A B C E).
#[local] Abbreviation result := (pegresult input C E).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval" *)
Inductive peg_eval (G : peg A B C E) : input * psym -> result -> Prop :=
| peg_eval_empty : forall s c, peg_eval G (s, empty c) (Success s c NONE)
| peg_eval_nt : forall n s f res,
    n IN FDOM (rules G) -> peg_eval G (s, FAPPLY (rules G) n) res ->
    peg_eval G (s, nt n f) (resultmap f res)
| peg_eval_any_success : forall h t f, peg_eval G (h :: t, any f) (Success t (f h) NONE)
| peg_eval_any_failure : forall f, peg_eval G ([], any f) (Failure (Locs EOFpt EOFpt) (anyEOF G))
| peg_eval_tok_success : forall e t (P : A -> bool) f,
    P (FST e) -> peg_eval G (e :: t, tok P f) (Success t (f e) NONE)
| peg_eval_tok_failureF : forall h t (P : A -> bool) f,
    ~ P (FST h) -> peg_eval G (h :: t, tok P f) (Failure (SND h) (tokFALSE G))
| peg_eval_tok_failureEOF : forall (P : A -> bool) f,
    peg_eval G ([], tok P f) (Failure (Locs EOFpt EOFpt) (tokEOF G))
| peg_eval_not_success : forall e s c fr,
    peg_eval G (s, e) fr -> isFailure fr -> peg_eval G (s, not e c) (Success s c NONE)
| peg_eval_not_failure : forall e s r c,
    peg_eval G (s, e) r -> isSuccess r -> peg_eval G (s, not e c) (Failure (sloc s) (notFAIL G))
| peg_eval_seq_fail1 : forall e1 e2 s f fl fe,
    peg_eval G (s, e1) (Failure fl fe) -> peg_eval G (s, seq e1 e2 f) (Failure fl fe)
| peg_eval_seq_fail2 : forall e1 e2 f s0 eo s1 c1 fl fe,
    peg_eval G (s0, e1) (Success s1 c1 eo) -> peg_eval G (s1, e2) (Failure fl fe) ->
    peg_eval G (s0, seq e1 e2 f) (Failure fl fe)
| peg_eval_seq_success : forall e1 e2 s0 s1 s2 c1 c2 f eo1 eo2,
    peg_eval G (s0, e1) (Success s1 c1 eo1) -> peg_eval G (s1, e2) (Success s2 c2 eo2) ->
    peg_eval G (s0, seq e1 e2 f) (Success s2 (f c1 c2) eo2)
| peg_eval_choice_fail : forall e1 e2 s f fl1 fe1 fl2 fe2,
    peg_eval G (s, e1) (Failure fl1 fe1) -> peg_eval G (s, e2) (Failure fl2 fe2) ->
    peg_eval G (s, choice e1 e2 f) (UNCURRY Failure (MAXerr (fl1, fe1) (fl2, fe2)))
| peg_eval_choice_success1 : forall e1 e2 s0 f s r eo,
    peg_eval G (s0, e1) (Success s r eo) ->
    peg_eval G (s0, choice e1 e2 f) (Success s (f (inl r)) eo)
| peg_eval_choice_success2 : forall e1 e2 s0 s r eo f fl fe,
    peg_eval G (s0, e1) (Failure fl fe) -> peg_eval G (s0, e2) (Success s r eo) ->
    peg_eval G (s0, choice e1 e2 f) (Success s (f (inr r)) (optmax MAXerr (SOME (fl, fe)) eo))
| peg_eval_error : forall e s, peg_eval G (s, error e) (Failure (sloc s) e)
| peg_eval_rpt : forall e f s s1 list err,
    peg_eval_list G (s, e) (s1, (list, err)) ->
    peg_eval G (s, rpt e f) (Success s1 (f list) (SOME err))
with peg_eval_list (G : peg A B C E) : input * psym -> input * (list C * (locs * E)) -> Prop :=
| peg_eval_list_nil : forall e s fl fe,
    peg_eval G (s, e) (Failure fl fe) -> peg_eval_list G (s, e) (s, ([], (fl, fe)))
| peg_eval_list_cons : forall e eo0 eo s0 s1 s2 c cs,
    peg_eval G (s0, e) (Success s1 c eo0) -> peg_eval_list G (s1, e) (s2, (cs, eo)) ->
    peg_eval_list G (s0, e) (s2, (c :: cs, eo)).

Scheme peg_eval_ind2 := Minimality for peg_eval Sort Prop
  with peg_eval_list_ind2 := Minimality for peg_eval_list Sort Prop.
Combined Scheme peg_eval_mutind from peg_eval_ind2, peg_eval_list_ind2.

Lemma UNCURRY_Failure_isFailure (fle : locs * E) :
  @UNCURRY _ _ result Failure fle = Failure (fst fle) (snd fle).
Proof. destruct fle; reflexivity. Qed.

(** Determinism: the result of evaluation is unique. *)
Ltac use_det_ih :=
  repeat match goal with
  | IH : forall r', peg_eval ?G ?p r' -> r' = _, H : peg_eval ?G ?p _ |- _ =>
      let E := fresh "E" in
      pose proof (IH _ H) as E; clear H;
      try discriminate E; try (injection E; clear E; intros; subst)
  | IH : forall q', peg_eval_list ?G ?p q' -> q' = _, H : peg_eval_list ?G ?p _ |- _ =>
      let E := fresh "E" in
      pose proof (IH _ H) as E; clear H;
      try discriminate E; try (injection E; clear E; intros; subst)
  end.

Lemma peg_deterministic0 (G : peg A B C E) :
  (forall p r, peg_eval G p r -> forall r', peg_eval G p r' -> r' = r) /\
  (forall p q, peg_eval_list G p q -> forall q', peg_eval_list G p q' -> q' = q).
Proof.
  apply peg_eval_mutind; intros;
  lazymatch goal with
  | |- ?x = _ =>
      match goal with
      | H : peg_eval _ _ x |- _ => inversion H; subst; clear H
      | H : peg_eval_list _ _ x |- _ => inversion H; subst; clear H
      end
  end; use_det_ih; subst; try reflexivity;
  repeat match goal with
  | H : is_true (isFailure ?r), H' : is_true (isSuccess ?r) |- _ =>
      destruct r; discriminate
  | H : ~ is_true ?b, H' : is_true ?b |- _ => contradiction
  | H : Failure _ _ = UNCURRY Failure ?x |- _ => destruct x; discriminate
  | H : UNCURRY Failure ?x = Success _ _ _ |- _ => destruct x; discriminate
  | H : resultmap _ ?r = Success _ _ _ |- _ => destruct r; discriminate
  end; try (exfalso; congruence).
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_deterministic" *)
Theorem peg_deterministic : forall G : peg A B C E,
  (forall s0 e sr, peg_eval G (s0, e) sr -> forall sr', peg_eval G (s0, e) sr' <-> sr' = sr) /\
  (forall s0 e s rl err, peg_eval_list G (s0, e) (s, (rl, err)) ->
     forall srl', peg_eval_list G (s0, e) srl' <-> srl' = (s, (rl, err))).
Proof.
  intros G; destruct (peg_deterministic0 G) as [h1 h2]; split.
  - intros s0 e sr H sr'; split; [apply h1, H|intros ->; exact H].
  - intros s0 e s rl err H srl'; split; [apply h2, H|intros ->; exact H].
Qed.

(** ** Suffix property (HOL's Theorem 3.1) *)

Lemma peg_eval_suffix_app (G : peg A B C E) :
  (forall p r, peg_eval G p r ->
     forall s c eo, r = Success s c eo -> exists pre, fst p = pre ++ s) /\
  (forall p q, peg_eval_list G p q -> exists pre, fst p = pre ++ fst q).
Proof.
  apply peg_eval_mutind; cbn; intros; try discriminate;
  repeat match goal with
  | H : Success _ _ _ = Success _ _ _ |- _ => injection H; clear H; intros; subst
  | H : resultmap _ ?r = Success _ _ _ |- _ =>
      apply resultmap_EQ_Success in H; destruct H as [? [? ?]]; subst
  | H : UNCURRY Failure ?x = Success _ _ _ |- _ => destruct x; discriminate
  end.
  all: try (exists []; reflexivity).
  all: try (exists [h]; reflexivity).
  all: try (exists [e]; reflexivity).
  all: try solve [eauto].
  - (* seq_success *)
    destruct (H0 _ _ _ eq_refl) as [p1 ->]; destruct (H2 _ _ _ eq_refl) as [p2 ->].
    exists (p1 ++ p2); rewrite app_assoc; reflexivity.
  - (* list_cons *)
    destruct (H0 _ _ _ eq_refl) as [p1 ->]; destruct H2 as [p2 ->].
    exists (p1 ++ p2); rewrite app_assoc; reflexivity.
Qed.


Lemma peg_eval_suffix_len (G : peg A B C E) s0 e s c eo :
  peg_eval G (s0, e) (Success s c eo) -> s0 = s \/ (length s < length s0)%nat.
Proof.
  intros h; destruct (proj1 (peg_eval_suffix_app G) _ _ h _ _ _ eq_refl) as [pre Hpre].
  cbn in Hpre; subst; destruct pre; [left; reflexivity|right; cbn; rewrite length_app; lia].
Qed.

Lemma peg_eval_list_suffix_len (G : peg A B C E) s0 e s rl err :
  peg_eval_list G (s0, e) (s, (rl, err)) -> s0 = s \/ (length s < length s0)%nat.
Proof.
  intros h; destruct (proj2 (peg_eval_suffix_app G) _ _ h) as [pre Hpre].
  cbn in Hpre; subst; destruct pre; [left; reflexivity|right; cbn; rewrite length_app; lia].
Qed.

(** ** Nullability *)

(** HOL's rules with disjunctive premises are split into one constructor
    per disjunct. *)
(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0" *)
Inductive peg0 (G : peg A B C E) : psym -> Prop :=
| peg0_empty : forall c, peg0 G (empty c)
| peg0_rpt : forall e f, pegfail G e -> peg0 G (rpt e f)
| peg0_nt : forall n f, n IN FDOM (rules G) -> peg0 G (FAPPLY (rules G) n) -> peg0 G (nt n f)
| peg0_seq : forall e1 e2 f, peg0 G e1 -> peg0 G e2 -> peg0 G (seq e1 e2 f)
| peg0_choice1 : forall e1 e2 f, peg0 G e1 -> peg0 G (choice e1 e2 f)
| peg0_choice2 : forall e1 e2 f, pegfail G e1 -> peg0 G e2 -> peg0 G (choice e1 e2 f)
| peg0_not : forall e c, pegfail G e -> peg0 G (not e c)
with peggt0 (G : peg A B C E) : psym -> Prop :=
| peggt0_any : forall f, peggt0 G (any f)
| peggt0_tok : forall t f, peggt0 G (tok t f)
| peggt0_rpt : forall e f, peggt0 G e -> peggt0 G (rpt e f)
| peggt0_nt : forall n f, n IN FDOM (rules G) -> peggt0 G (FAPPLY (rules G) n) -> peggt0 G (nt n f)
| peggt0_seq1 : forall e1 e2 f, peggt0 G e1 -> peg0 G e2 -> peggt0 G (seq e1 e2 f)
| peggt0_seq2 : forall e1 e2 f, peggt0 G e1 -> peggt0 G e2 -> peggt0 G (seq e1 e2 f)
| peggt0_seq3 : forall e1 e2 f, peg0 G e1 -> peggt0 G e2 -> peggt0 G (seq e1 e2 f)
| peggt0_choice1 : forall e1 e2 f, peggt0 G e1 -> peggt0 G (choice e1 e2 f)
| peggt0_choice2 : forall e1 e2 f, pegfail G e1 -> peggt0 G e2 -> peggt0 G (choice e1 e2 f)
with pegfail (G : peg A B C E) : psym -> Prop :=
| pegfail_any : forall f, pegfail G (any f)
| pegfail_tok : forall t f, pegfail G (tok t f)
| pegfail_nt : forall n f, n IN FDOM (rules G) -> pegfail G (FAPPLY (rules G) n) -> pegfail G (nt n f)
| pegfail_seq1 : forall e1 e2 f, pegfail G e1 -> pegfail G (seq e1 e2 f)
| pegfail_seq2 : forall e1 e2 f, peg0 G e1 -> pegfail G e2 -> pegfail G (seq e1 e2 f)
| pegfail_seq3 : forall e1 e2 f, peggt0 G e1 -> pegfail G e2 -> pegfail G (seq e1 e2 f)
| pegfail_choice : forall e1 e2 f, pegfail G e1 -> pegfail G e2 -> pegfail G (choice e1 e2 f)
| pegfail_not1 : forall e c, peg0 G e -> pegfail G (not e c)
| pegfail_not2 : forall e c, peggt0 G e -> pegfail G (not e c)
| pegfail_error : forall e, pegfail G (error e).

Scheme peg0_ind2 := Minimality for peg0 Sort Prop
  with peggt0_ind2 := Minimality for peggt0 Sort Prop
  with pegfail_ind2 := Minimality for pegfail Sort Prop.
Combined Scheme peg0_mutind from peg0_ind2, peggt0_ind2, pegfail_ind2.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0_error" *)
Theorem peg0_error : forall G (e : E), ~ peg0 G (error e).
Proof. intros G e h; inversion h. Qed.

Scheme peg_eval_ind3 := Induction for peg_eval Sort Prop
  with peg_eval_list_ind3 := Induction for peg_eval_list Sort Prop.
Combined Scheme peg_eval_mutind3 from peg_eval_ind3, peg_eval_list_ind3.

Create HintDb pegc.
#[local] Hint Constructors peg0 peggt0 pegfail : pegc.

(** HOL's [lemma4_1a0]. *)
Lemma lemma4_1a0 (G : peg A B C E) :
  (forall p r, peg_eval G p r ->
     (forall c eo, r = Success (fst p) c eo -> peg0 G (snd p)) /\
     (isFailure r -> pegfail G (snd p)) /\
     (forall s c eo, r = Success s c eo -> (length s < length (fst p))%nat -> peggt0 G (snd p))) /\
  (forall p q, peg_eval_list G p q ->
     (fst p = fst q -> pegfail G (snd p)) /\
     ((length (fst q) < length (fst p))%nat -> peggt0 G (snd p))).
Proof.
  apply (peg_eval_mutind3 G
    (fun p r _ =>
     (forall c eo, r = Success (fst p) c eo -> peg0 G (snd p)) /\
     (isFailure r -> pegfail G (snd p)) /\
     (forall s c eo, r = Success s c eo -> (length s < length (fst p))%nat -> peggt0 G (snd p)))
    (fun p q _ =>
     (fst p = fst q -> pegfail G (snd p)) /\
     ((length (fst q) < length (fst p))%nat -> peggt0 G (snd p))));
    cbn; intros;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : is_true (isSuccess ?r) |- _ => destruct r; [clear H|discriminate H]
    end;
    repeat split; intros; try discriminate;
    try match goal with
    | H : is_true (isFailure (resultmap _ ?r)) |- _ => destruct r; [cbn in H; discriminate H|]
    end;
    repeat match goal with
    | H : Success _ _ _ = Success _ _ _ |- _ => injection H; clear H; intros; subst
    | H : resultmap _ ?r = Success _ _ _ |- _ =>
        apply resultmap_EQ_Success in H; destruct H as [? [? ?]]; subst
    | H : UNCURRY Failure ?x = Success _ _ _ |- _ => destruct x; discriminate
    end;
    repeat match goal with
    | H : peg_eval G (?x, _) (Success ?z _ _) |- _ =>
        let h := fresh "hs" in
        destruct (peg_eval_suffix_len G _ _ _ _ _ H) as [h|h]; clear H; [try subst x; try subst z|]
    | H : peg_eval_list G (?x, _) (?z, _) |- _ =>
        let h := fresh "hs" in
        destruct (peg_eval_list_suffix_len G _ _ _ _ _ H) as [h|h]; clear H; [try subst x; try subst z|]
    end;
    repeat match goal with
    | H : ?t = _ :: ?t |- _ => apply (f_equal (@length _)) in H; cbn in H; lia
    end;
    try lia;
    try (match goal with H : @eq (list _) _ _ |- _ => rewrite H in *; lia end);
    eauto 4 with pegc.
Qed.

(** ** Well-formedness *)

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "wfpeg" *)
Inductive wfpeg (G : peg A B C E) : psym -> Prop :=
| wfpeg_nt : forall n f, n IN FDOM (rules G) -> wfpeg G (FAPPLY (rules G) n) -> wfpeg G (nt n f)
| wfpeg_empty : forall c, wfpeg G (empty c)
| wfpeg_any : forall f, wfpeg G (any f)
| wfpeg_tok : forall t f, wfpeg G (tok t f)
| wfpeg_error : forall e, wfpeg G (error e)
| wfpeg_not : forall e c, wfpeg G e -> wfpeg G (not e c)
| wfpeg_seq : forall e1 e2 f, wfpeg G e1 -> (peg0 G e1 -> wfpeg G e2) -> wfpeg G (seq e1 e2 f)
| wfpeg_choice : forall e1 e2 f, wfpeg G e1 -> wfpeg G e2 -> wfpeg G (choice e1 e2 f)
| wfpeg_rpt : forall e f, wfpeg G e -> ~ peg0 G e -> wfpeg G (rpt e f).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "subexprs_def" *)
Fixpoint subexprs (e : psym) : psym -> Prop :=
  match e with
  | any f1 => any f1 INSERT EMPTY
  | empty c => empty c INSERT EMPTY
  | tok t f2 => tok t f2 INSERT EMPTY
  | error e => error e INSERT EMPTY
  | nt s f => nt s f INSERT EMPTY
  | not e c => not e c INSERT subexprs e
  | seq e1 e2 f3 => seq e1 e2 f3 INSERT subexprs e1 UNION subexprs e2
  | choice e1 e2 f4 => choice e1 e2 f4 INSERT subexprs e1 UNION subexprs e2
  | rpt e f5 => rpt e f5 INSERT subexprs e
  end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "subexprs_included" *)
Theorem subexprs_included : forall e : psym, e IN subexprs e.
Proof. intros []; cbn; unfold_sets; auto. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "Gexprs_def" *)
Definition Gexprs (G : peg A B C E) : psym -> Prop :=
  BIGUNION (IMAGE subexprs (start G INSERT FRANGE (rules G))).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "start_IN_Gexprs" *)
Theorem start_IN_Gexprs : forall G, start G IN Gexprs G.
Proof.
  intros G; unfold Gexprs; unfold_sets.
  exists (subexprs (start G)); split; [exists (start G); auto|apply subexprs_included].
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "wfG_def" *)
Definition wfG (G : peg A B C E) : Prop := forall e, e IN Gexprs G -> wfpeg G e.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "IN_subexprs_TRANS" *)
Theorem IN_subexprs_TRANS : forall a b c : psym,
  a IN subexprs b /\ b IN subexprs c -> a IN subexprs c.
Proof.
  intros a b c; induction c; cbn; unfold_sets; intros [h1 h2];
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; cbn in h1; unfold_sets;
    try tauto; try (right; eauto; fail); try (right; left; eauto; fail);
    try (right; right; eauto; fail).
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "Gexprs_subexprs" *)
Theorem Gexprs_subexprs : forall G e, e IN Gexprs G -> subexprs e SUBSET Gexprs G.
Proof.
  intros G e; unfold Gexprs; unfold_sets; intros [s [[x [-> hx]] he]] y hy.
  exists (subexprs x); split; [eauto|].
  apply (IN_subexprs_TRANS y e x); split; assumption.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "IN_Gexprs_E" *)
Theorem IN_Gexprs_E : forall G,
  (forall e c, not e c IN Gexprs G -> e IN Gexprs G) /\
  (forall e1 e2 f, seq e1 e2 f IN Gexprs G -> e1 IN Gexprs G /\ e2 IN Gexprs G) /\
  (forall e1 e2 f2, choice e1 e2 f2 IN Gexprs G -> e1 IN Gexprs G /\ e2 IN Gexprs G) /\
  (forall e f3, rpt e f3 IN Gexprs G -> e IN Gexprs G).
Proof.
  intros G; repeat split; intros;
    match goal with H : _ IN Gexprs G |- _ => apply Gexprs_subexprs in H; apply H end;
    cbn; unfold_sets;
    first [right; apply subexprs_included
          | right; left; apply subexprs_included
          | right; right; apply subexprs_included].
Qed.

Lemma reducing_peg_eval_makes_list (G : peg A B C E) e n :
  (forall s : input, (length s < n)%nat -> exists r, peg_eval G (s, e) r) -> ~ peg0 G e ->
  forall s0 : input, (length s0 < n)%nat -> exists s' rl err, peg_eval_list G (s0, e) (s', (rl, err)).
Proof.
  intros hs hn s0; induction s0 as [s0 IH] using (well_founded_induction
    (well_founded_ltof _ (@length (A * locs)))); intros hlen.
  destruct (hs s0 hlen) as [[s1 c eo|fl fe] h].
  - destruct (peg_eval_suffix_len G _ _ _ _ _ h) as [<-|hlt].
    + exfalso; apply hn; apply (proj1 (proj1 (lemma4_1a0 G) _ _ h) c eo); reflexivity.
    + destruct (IH s1 hlt) as [s' [rl [err h']]]; [lia|].
      exists s', (c :: rl), err; eapply peg_eval_list_cons; eauto.
  - exists s0, [], (fl, fe); constructor; exact h.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_total" *)
Theorem peg_eval_total : forall G : peg A B C E,
  wfG G -> forall s e, e IN Gexprs G -> exists r, peg_eval G (s, e) r.
Proof.
  intros G hwf s; induction s as [s IHs] using (well_founded_induction
    (well_founded_ltof _ (@length (A * locs)))).
  intros e he; generalize (hwf e he); intros hwfe; revert he.
  induction hwfe as [n f hn hw IH| c | f | t f | err | e c hw IH
                    | e1 e2 f hw1 IH1 hw2 IH2 | e1 e2 f hw1 IH1 hw2 IH2 | e f hw IH hn];
    intros he; destruct (IN_Gexprs_E G) as (hnot & hseq & hch & hrpt).
  - destruct IH as [r hr].
    { unfold Gexprs; unfold_sets.
      exists (subexprs (FAPPLY (rules G) n)); split; [|apply subexprs_included].
      exists (FAPPLY (rules G) n); split; [reflexivity|right].
      apply IN_FRANGE; eauto. }
    eexists; eapply peg_eval_nt; eauto.
  - eexists; constructor.
  - destruct s; eexists; constructor.
  - destruct s as [|h t0]; [eexists; constructor|].
    destruct (t (FST h)) eqn:Et.
    + eexists; apply peg_eval_tok_success; rewrite Et; reflexivity.
    + eexists; apply peg_eval_tok_failureF; rewrite Et; discriminate.
  - eexists; constructor.
  - destruct (IH (hnot _ _ he)) as [[s1 c1 eo|fl fe] hr].
    + eexists; eapply peg_eval_not_failure; [exact hr|reflexivity].
    + eexists; eapply peg_eval_not_success; [exact hr|reflexivity].
  - destruct (hseq _ _ _ he) as [he1 he2].
    destruct (IH1 he1) as [[s1 c1 eo|fl fe] hr1].
    + destruct (peg_eval_suffix_len G _ _ _ _ _ hr1) as [<-|hlt].
      * assert (h0 : peg0 G e1) by (apply (proj1 (proj1 (lemma4_1a0 G) _ _ hr1) c1 eo); reflexivity).
        destruct (IH2 h0 he2) as [[s2 c2 eo2|fl fe] hr2].
        -- eexists; eapply peg_eval_seq_success; eauto.
        -- eexists; eapply peg_eval_seq_fail2; eauto.
      * destruct (IHs s1 hlt e2 he2) as [[s2 c2 eo2|fl fe] hr2].
        -- eexists; eapply peg_eval_seq_success; eauto.
        -- eexists; eapply peg_eval_seq_fail2; eauto.
    + eexists; eapply peg_eval_seq_fail1; eauto.
  - destruct (hch _ _ _ he) as [he1 he2].
    destruct (IH1 he1) as [[s1 c1 eo|fl fe] hr1].
    + eexists; eapply peg_eval_choice_success1; eauto.
    + destruct (IH2 he2) as [[s2 c2 eo2|fl2 fe2] hr2].
      * eexists; eapply peg_eval_choice_success2; eauto.
      * eexists; eapply peg_eval_choice_fail; eauto.
  - pose proof (hrpt _ _ he) as he'.
    destruct (IH he') as [[s1 c1 eo|fl fe] hr].
    + destruct (peg_eval_suffix_len G _ _ _ _ _ hr) as [<-|hlt].
      * exfalso; apply hn, (proj1 (proj1 (lemma4_1a0 G) _ _ hr) c1 eo); reflexivity.
      * destruct (reducing_peg_eval_makes_list G e (length s)
                   (fun s' hs' => IHs s' hs' e he') hn s1 hlt) as [s' [rl [err hl]]].
        eexists; eapply peg_eval_rpt, peg_eval_list_cons; eauto.
    + eexists; eapply peg_eval_rpt, peg_eval_list_nil; eauto.
Qed.

(** ** Derived forms *)

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "pegf_def" *)
Definition pegf `{Inhabited C} (sym : psym) (f : C -> C) : pegsym A B C E :=
  seq sym (empty ARB) (fun l1 l2 => f l1).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "ignoreL_def" *)
Definition ignoreL (s1 s2 : psym) : psym := seq s1 s2 (fun a b => b).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "ignoreR_def" *)
Definition ignoreR (s1 s2 : psym) : psym := seq s1 s2 (fun a b => a).

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "choicel_def" *)
Fixpoint choicel `{Inhabited C} (l : list psym) : psym :=
  match l with
  | [] => not (empty ARB) ARB
  | h :: t => choice h (choicel t) (fun s => match s with inl x => x | inr y => y end)
  end.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "checkAhead_def" *)
Definition checkAhead `{Inhabited C} (P : A -> bool) (s : psym) : psym :=
  ignoreL (not (not (tok P ARB) ARB) ARB) s.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_seq_SOME" *)
Theorem peg_eval_seq_SOME : forall G i0 s1 s2 f i r eo,
  peg_eval G (i0, seq s1 s2 f) (Success i r eo) <->
  exists i1 r1 r2 eo1,
    peg_eval G (i0, s1) (Success i1 r1 eo1) /\ peg_eval G (i1, s2) (Success i r2 eo) /\ r = f r1 r2.
Proof.
  intros; split.
  - intros h; inversion h; subst; eauto 10.
  - intros (i1 & r1 & r2 & eo1 & h1 & h2 & ->); eapply peg_eval_seq_success; eauto.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_seq_NONE" *)
Theorem peg_eval_seq_NONE : forall G i0 s1 s2 f fl fe,
  peg_eval G (i0, seq s1 s2 f) (Failure fl fe) <->
  peg_eval G (i0, s1) (Failure fl fe) \/
  exists i r eo, peg_eval G (i0, s1) (Success i r eo) /\ peg_eval G (i, s2) (Failure fl fe).
Proof.
  intros; split.
  - intros h; inversion h; subst; eauto 10.
  - intros [h|(i & r & eo & h1 & h2)]; [eapply peg_eval_seq_fail1|eapply peg_eval_seq_fail2]; eauto.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_tok_SOME" *)
Theorem peg_eval_tok_SOME : forall G i0 P f i r eo,
  peg_eval G (i0, tok P f) (Success i r eo) <->
  exists h l, P h /\ i0 = (h, l) :: i /\ r = f (h, l) /\ eo = NONE.
Proof.
  intros; split.
  - intros hh; inversion hh; subst; destruct e as [h l]; eauto 10.
  - intros (h & l & hP & -> & -> & ->); apply peg_eval_tok_success; exact hP.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_empty" *)
Theorem peg_eval_empty_thm : forall G i r x,
  peg_eval G (i, empty r) x <-> x = Success i r NONE.
Proof. intros; split; [intros h; inversion h; reflexivity|intros ->; constructor]. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_NT_SOME" *)
Theorem peg_eval_NT_SOME : forall G i0 N f i r eo,
  peg_eval G (i0, nt N f) (Success i r eo) <->
  exists r0, r = f r0 /\ N IN FDOM (rules G) /\ peg_eval G (i0, FAPPLY (rules G) N) (Success i r0 eo).
Proof.
  intros; split.
  - intros h; inversion h; subst.
    match goal with H : resultmap _ _ = _ |- _ => apply resultmap_EQ_Success in H; destruct H as [x0 [-> ->]] end.
    eauto.
  - intros (r0 & -> & hn & h).
    change (Success i (f r0) eo) with (resultmap f (Success i r0 eo)); eapply peg_eval_nt; eauto.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_rpt" *)
Theorem peg_eval_rpt_thm : forall G i0 s f x,
  peg_eval G (i0, rpt s f) x <->
  exists i l err, peg_eval_list G (i0, s) (i, (l, err)) /\ x = Success i (f l) (SOME err).
Proof.
  intros; split.
  - intros h; inversion h; subst; eauto.
  - intros (i & l & err & h & ->); apply peg_eval_rpt; exact h.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg_eval_list" *)
Theorem peg_eval_list_thm : forall G i0 e i r err,
  peg_eval_list G (i0, e) (i, (r, err)) <->
  (exists fl fe, peg_eval G (i0, e) (Failure fl fe) /\ i = i0 /\ r = [] /\ err = (fl, fe)) \/
  (exists i1 rh rt eo0,
     peg_eval G (i0, e) (Success i1 rh eo0) /\ peg_eval_list G (i1, e) (i, (rt, err)) /\ r = rh :: rt).
Proof.
  intros; split.
  - intros h; inversion h; subst; [left|right]; eauto 10.
  - intros [(fl & fe & h & -> & -> & ->)|(i1 & rh & rt & eo0 & h1 & h2 & ->)].
    + apply peg_eval_list_nil; exact h.
    + eapply peg_eval_list_cons; eauto.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "pegfail_empty" *)
Theorem pegfail_empty : forall G (r : C), ~ pegfail G (empty r).
Proof. intros G r h; inversion h. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0_empty" *)
Theorem peg0_empty_thm : forall G (r : C), peg0 G (empty r).
Proof. intros; constructor. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0_not" *)
Theorem peg0_not_thm : forall G s (r : C), peg0 G (not s r) <-> pegfail G s.
Proof. intros; split; [intros h; inversion h; auto|apply peg0_not]. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0_choice" *)
Theorem peg0_choice_thm : forall G s1 s2 f,
  peg0 G (choice s1 s2 f) <-> peg0 G s1 \/ pegfail G s1 /\ peg0 G s2.
Proof.
  intros; split; [intros h; inversion h; auto|].
  intros [h|[h1 h2]]; [apply peg0_choice1|apply peg0_choice2]; auto.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0_seq" *)
Theorem peg0_seq_thm : forall G s1 s2 f, peg0 G (seq s1 s2 f) <-> peg0 G s1 /\ peg0 G s2.
Proof. intros; split; [intros h; inversion h; auto|intros []; apply peg0_seq; auto]. Qed.

(*! HOL "HOL/examples/formal-languages/context-free/pegScript.sml" "peg0_tok" *)
Theorem peg0_tok : forall G P f, ~ peg0 G (tok P f).
Proof. intros G P f h; inversion h. Qed.

End Eval.

(** ** Checking well-formedness (Galette)

    A sufficient, computable criterion for [wfG], used to prove concrete
    grammars well-formed by evaluation.  [np0 nn e] approximates
    [~ peg0 G e] assuming that the nonterminals in [nn] never succeed
    without consuming input; [nofail e] approximates [~ pegfail G e];
    [wfl] checks [wfpeg] of an expression given well-formed nonterminals,
    and [wf_order] establishes the nonterminals' well-formedness in a
    given (topological) order. *)

Section WfCheck.
Context {A B C E : Type} `{EqDecision B}.

#[local] Abbreviation psym := (pegsym A B C E).

Fixpoint nofail (e : psym) : bool :=
  match e with
  | empty _ => true
  | seq e1 e2 _ => nofail e1 && nofail e2
  | choice e1 e2 _ => nofail e1 || nofail e2
  | rpt _ _ => true
  | _ => false
  end.

Fixpoint np0 (nn : list (inf B)) (e : psym) : bool :=
  match e with
  | empty _ => false
  | any _ => true
  | tok _ _ => true
  | nt n _ => MEM n nn
  | seq e1 e2 _ => np0 nn e1 || np0 nn e2
  | choice e1 e2 _ => np0 nn e1 && np0 nn e2
  | rpt _ _ => false
  | not e _ => nofail e
  | error _ => true
  end.

Definition nn_ok (G : peg A B C E) (nn : list (inf B)) : bool :=
  forallb (fun n => match FLOOKUP (rules G) n with Some e => np0 nn e | None => true end) nn.

Lemma np0_sound (G : peg A B C E) nn :
  nn_ok G nn = true ->
  (forall e, peg0 G e -> np0 nn e = false) /\
  (forall e, peggt0 G e -> True) /\
  (forall e, pegfail G e -> nofail e = false).
Proof.
  intros hok; apply peg0_mutind; intros; cbn; auto;
    repeat match goal with H : _ = false |- _ => rewrite H end;
    rewrite ?andb_false_r, ?orb_false_r; auto.
  (* nt *)
  destruct (MEM n nn) eqn:hm; [|reflexivity].
  unfold nn_ok in hok; rewrite forallb_forall in hok.
  apply MEM_In in hm; specialize (hok n hm).
  unfold FDOM in *; unfold_sets; unfold FAPPLY, THE in *.
  destruct (FLOOKUP (rules G) n); [congruence|contradiction].
Qed.

(** [wfl ok e]: [e] is well-formed provided the nonterminals in [ok] are;
    only nonterminals in positions not preceded by a non-nullable
    expression are consulted. *)
Fixpoint wfl (nn ok : list (inf B)) (e : psym) : bool :=
  match e with
  | nt n _ => MEM n ok
  | empty _ | any _ | tok _ _ | error _ => true
  | not e _ => wfl nn ok e
  | seq e1 e2 _ => wfl nn ok e1 && (np0 nn e1 || wfl nn ok e2)
  | choice e1 e2 _ => wfl nn ok e1 && wfl nn ok e2
  | rpt e _ => wfl nn ok e && np0 nn e
  end.

Lemma wfl_sound (G : peg A B C E) nn ok e :
  nn_ok G nn = true ->
  (forall n f, In n ok -> wfpeg G (nt n f)) -> wfl nn ok e = true -> wfpeg G e.
Proof.
  intros hok hnt; destruct (np0_sound G nn hok) as [hnp _].
  induction e; intros h; cbn in h; repeat rewrite andb_true_iff in h;
    repeat rewrite orb_true_iff in h; try (constructor; fail).
  - apply hnt, MEM_In, h.
  - destruct h as [h1 [h2|h2]]; apply wfpeg_seq; auto.
    intros h0; rewrite (hnp _ h0) in h2; discriminate.
  - destruct h as [h1 h2]; apply wfpeg_choice; auto.
  - destruct h as [h1 h2]; apply wfpeg_rpt; auto.
    intros h0; rewrite (hnp _ h0) in h2; discriminate.
  - apply wfpeg_not; auto.
Qed.

(** [wf_order nn ok order]: each nonterminal of [order] has a rule that is
    well-formed given the nonterminals before it. *)
Fixpoint wf_order (G : peg A B C E) (nn ok order : list (inf B)) : bool :=
  match order with
  | [] => true
  | n :: t =>
      match FLOOKUP (rules G) n with
      | Some r => wfl nn ok r && wf_order G nn (n :: ok) t
      | None => false
      end
  end.

Lemma wf_order_sound (G : peg A B C E) nn ok order :
  nn_ok G nn = true -> (forall n f, In n ok -> wfpeg G (nt n f)) ->
  wf_order G nn ok order = true -> forall n f, In n (ok ++ order) -> wfpeg G (nt n f).
Proof.
  intros hok; revert ok; induction order as [|m t IH]; intros ok hnt h n f hin.
  - rewrite app_nil_r in hin; auto.
  - cbn in h; destruct (FLOOKUP (rules G) m) as [r|] eqn:hl; [|discriminate].
    rewrite andb_true_iff in h; destruct h as [h1 h2].
    assert (hm : forall f, wfpeg G (nt m f)).
    { intros f'; apply wfpeg_nt; [unfold FDOM; unfold_sets; congruence|].
      unfold FAPPLY, THE; rewrite hl; apply (wfl_sound G nn ok); auto. }
    apply (IH (m :: ok)); auto.
    + intros n' f' [<-|hn']; auto.
    + rewrite in_app_iff in hin |- *; cbn in hin |- *; tauto.
Qed.

Fixpoint subexprs_list (e : psym) : list psym :=
  match e with
  | not e' _ => e :: subexprs_list e'
  | seq e1 e2 _ => e :: subexprs_list e1 ++ subexprs_list e2
  | choice e1 e2 _ => e :: subexprs_list e1 ++ subexprs_list e2
  | rpt e' _ => e :: subexprs_list e'
  | _ => [e]
  end.

Lemma subexprs_list_spec x e : x IN subexprs e -> In x (subexprs_list e).
Proof.
  induction e; cbn; unfold_sets; rewrite ?in_app_iff; intuition.
Qed.

Theorem wfG_check (G : peg A B C E) nn order (rl : list psym) :
  nn_ok G nn = true ->
  wf_order G nn [] order = true ->
  (forall k v, FLOOKUP (rules G) k = Some v -> In v rl) ->
  forallb (fun e => forallb (wfl nn order) (subexprs_list e)) (start G :: rl) = true ->
  wfG G.
Proof.
  intros hok hord hrl hchk e he.
  pose proof (wf_order_sound G nn [] order hok (fun n f h => match h with end) hord) as hnt.
  unfold Gexprs in he; unfold_sets; destruct he as [s [[x [-> hx]] hex]].
  rewrite forallb_forall in hchk.
  assert (hin : In x (start G :: rl)).
  { destruct hx as [->|[k hk]]; [left; reflexivity|right; eapply hrl, hk]. }
  specialize (hchk x hin); rewrite forallb_forall in hchk.
  apply (wfl_sound G nn order); [exact hok| |].
  - intros n f h; apply hnt, h.
  - apply hchk, subexprs_list_spec, hex.
Qed.

End WfCheck.

