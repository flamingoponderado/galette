(** * CakeML [backendProps]: generic definitions and theorems for backend
    proofs (compiler-oracle combinators, [option_le]). *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.relation Require Import relation.
From Galette.cakeml.misc Require Import misc.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_cc_def" *)
Definition state_cc {S C P Q Co Da} (f : S -> P -> S * Q)
    (cc : C -> Q -> option (Co * (Da * C))) : S * C -> P -> option (Co * (Da * (S * C))) :=
  fun '(state, cfg) prog =>
    let '(state1, prog1) := f state prog in
    match cc cfg prog1 with
    | NONE => NONE
    | SOME (code, (data, cfg1)) => SOME (code, (data, (state1, cfg1)))
    end.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_cc_def" *)
Definition pure_cc {C P Q R} (f : P -> Q) (cc : C -> Q -> R) : C -> P -> R :=
  fun cfg prog => let prog1 := f prog in cc cfg prog1.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_co_def" *)
Definition state_co {S C P Q} (f : S -> P -> S * Q) (co : N -> (S * C) * P) : N -> C * Q :=
  fun n =>
    let '((state, cfg), progs) := co n in
    let '(state1, progs) := f state progs in
    (cfg, progs).

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "FST_state_co" *)
Theorem FST_state_co : forall {S C P Q} (f : S -> P -> S * Q) (co : N -> (S * C) * P) n,
  FST (state_co f co n) = SND (FST (co n)).
Proof.
  intros; unfold state_co; destruct (co n) as [[st cfg] progs]; cbn.
  destruct (f st progs); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "SND_state_co" *)
Theorem SND_state_co : forall {S C P Q} (f : S -> P -> S * Q) (co : N -> (S * C) * P) n,
  SND (state_co f co n) = SND (f (FST (FST (co n))) (SND (co n))).
Proof.
  intros; unfold state_co; destruct (co n) as [[st cfg] progs]; cbn.
  destruct (f st progs); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "the_eqn" *)
Theorem the_eqn : forall {A} (x : A) y, the x y = match y with NONE => x | SOME z => z end.
Proof. intros; destruct y; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "the_F_eq" *)
Theorem the_F_eq : forall opt, is_true (the false opt) <-> (exists x, opt = SOME x /\ is_true x).
Proof.
  intros [x|]; cbn; split; [eauto|intros [y [H Hy]]; inversion H; subst; exact Hy
                           |discriminate|intros [y [H _]]; discriminate].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_def" *)
Definition pure_co {A B C} (f : B -> C) : A * B -> A * C := I ## f.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "SND_pure_co" *)
Theorem SND_pure_co : forall {A B C} (co : B -> C) (x : A * B), SND (pure_co co x) = co (SND x).
Proof. intros ? ? ? co [a b]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "FST_pure_co" *)
Theorem FST_pure_co : forall {A B C} (co : B -> C) (x : A * B), FST (pure_co co x) = FST x.
Proof. intros ? ? ? co [a b]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_comb_pure_co" *)
Theorem pure_co_comb_pure_co : forall {X A B C D} (f : C -> D) (g : B -> C) (co : X -> A * B),
  pure_co f ∘ pure_co g ∘ co = pure_co (f ∘ g) ∘ co.
Proof.
  intros; apply functional_extensionality; intros x; unfold pure_co, PAIR_MAP, I.
  destruct (co x); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_I" *)
Theorem pure_co_I : forall {A B}, @pure_co A B B I = I.
Proof. intros; apply functional_extensionality; intros [a b]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_cc_I" *)
Theorem pure_cc_I : forall {C P R}, @pure_cc C P P R I = I.
Proof. intros; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_def" *)
Definition oracle_monotonic {A B} (f : A -> B -> Prop) (R : B -> B -> Prop) (S : B -> Prop)
    (orac : N -> A) : Prop :=
  (forall i j x y, i < j /\ x IN f (orac i) /\ y IN f (orac j) -> R x y) /\
  (forall i x y, x IN S /\ y IN f (orac i) -> R x y).

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_step" *)
Theorem oracle_monotonic_step : forall {A B} (f : A -> B -> Prop) R S orac,
  oracle_monotonic f R S orac ->
  forall i j x y, i < j /\ x IN f (orac i) /\ y IN f (orac j) -> R x y.
Proof. intros ? ? f R S orac [H _]; exact H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_init" *)
Theorem oracle_monotonic_init : forall {A B} (f : A -> B -> Prop) R S orac,
  oracle_monotonic f R S orac ->
  forall i x y, x IN S /\ y IN f (orac i) -> R x y.
Proof. intros ? ? f R S orac [_ H]; exact H. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_step2" *)
Theorem oracle_monotonic_step2 : forall {A B} (f : A -> B -> Prop) R St orac,
  oracle_monotonic f R St orac ->
  forall i j x y, x IN f (orac i) /\ y IN f (orac j) /\ i < j -> R x y.
Proof. intros ? ? f R St orac H i j x y [Hx [Hy Hij]]; eapply (proj1 H); eauto. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "oracle_monotonic_DISJOINT_init" *)
Theorem oracle_monotonic_DISJOINT_init : forall {A B} (f : A -> B -> Prop) R St co (i : N),
  oracle_monotonic f R St co /\ irreflexive R -> DISJOINT St (f (co i)).
Proof.
  intros ? ? f R St co i [[_ H] Hirr]. unfold irreflexive in Hirr.
  rewrite DISJOINT_iff. intros x [H1 H2]. exact (Hirr x (H i x x (conj H1 H2))).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "is_state_oracle_def" *)
Definition is_state_oracle {S C P Q} (compile_inc_f : S -> P -> S * Q)
    (co : N -> (S * C) * P) : Prop :=
  forall n, FST (FST (co (SUC n))) = FST (compile_inc_f (FST (FST (co n))) (SND (co n))).

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "syntax_to_full_oracle_def" *)
Definition syntax_to_full_oracle {P M} (mk : (N -> P) -> N -> M) (progs : N -> P) (i : N) : M * P :=
  (mk progs i, progs i).

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_progs_def" *)
Definition pure_co_progs {A B} (f : A -> B) (orac : N -> A) : N -> B := f ∘ orac.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_zero_def" *)
Definition restrict_zero (labels : N * N -> Prop) : N * N -> Prop :=
  fun l => l IN labels /\ SND l = 0.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "restrict_nonzero_def" *)
Definition restrict_nonzero (labels : N * N -> Prop) : N * N -> Prop :=
  fun l => l IN labels /\ SND l <> 0.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_def" *)
Definition option_le (x y : option N) : bool :=
  match x, y with
  | _, NONE => true
  | NONE, SOME _ => false
  | SOME n1, SOME n2 => n1 <=? n2
  end.

Ltac ole_tac :=
  unfold is_true, OPTION_MAP2, option_le in *; cbn in *;
  repeat rewrite N.leb_le in *; rewrite ?MAX_max in *;
  intuition (try discriminate; try lia).

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_refl" *)
Theorem option_le_refl : forall x, option_le x x.
Proof. intros [x|]; cbn; [apply N.leb_le; lia|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_SOME_0" *)
Theorem option_le_SOME_0 : forall x, option_le (SOME 0) x.
Proof. intros [x|]; cbn; [apply N.leb_le; lia|reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_trans" *)
Theorem option_le_trans : forall x y z, option_le x y /\ option_le y z -> option_le x z.
Proof. intros [?|] [?|] [?|]; ole_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_max" *)
Theorem option_le_max : forall n m x,
  option_le (OPTION_MAP2 MAX n m) x <-> option_le n x /\ option_le m x.
Proof. intros [?|] [?|] [?|]; ole_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_max_right" *)
Theorem option_le_max_right : forall x n m,
  option_le x (OPTION_MAP2 MAX n m) <-> option_le x n \/ option_le x m.
Proof. intros [?|] [?|] [?|]; ole_tac. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_add_comm" *)
Theorem option_add_comm : forall (n m : option N),
  OPTION_MAP2 N.add n m = OPTION_MAP2 N.add m n.
Proof. intros [n|] [m|]; unfold OPTION_MAP2; cbn; f_equal; lia. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_add_assoc" *)
Theorem option_add_assoc : forall (n m p : option N),
  OPTION_MAP2 N.add n (OPTION_MAP2 N.add m p) = OPTION_MAP2 N.add (OPTION_MAP2 N.add n m) p.
Proof. intros [n|] [m|] [p|]; unfold OPTION_MAP2; cbn; try reflexivity; f_equal; lia. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "option_le_add" *)
Theorem option_le_add : forall n m, option_le n (OPTION_MAP2 N.add n m).
Proof. intros [n|] [m|]; unfold OPTION_MAP2; cbn; try reflexivity; apply N.leb_le; lia. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "OPTION_MAP2_MAX_COMM" *)
Theorem OPTION_MAP2_MAX_COMM : forall x y, OPTION_MAP2 MAX x y = OPTION_MAP2 MAX y x.
Proof. intros [x|] [y|]; unfold OPTION_MAP2; cbn; rewrite ?MAX_max; f_equal; lia. Qed.

(*! HOL "cakeml/compiler/backend/semantics/backendPropsScript.sml" "OPTION_MAP2_MAX_ASSOC" *)
Theorem OPTION_MAP2_MAX_ASSOC : forall x y z,
  OPTION_MAP2 MAX x (OPTION_MAP2 MAX y z) = OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) z.
Proof. intros [x|] [y|] [z|]; unfold OPTION_MAP2; cbn; rewrite ?MAX_max; try reflexivity; f_equal; lia. Qed.
