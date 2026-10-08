(** * Pancake [crep_arith]: simplification of arithmetic in crepLang

    Port of [cakeml/pancake/crep_arithScript.sml].

    [dest_2exp] recurses on [word_lsr w 1] (HOL termination by [w2n w]); it
    is computed here by structural recursion on the binary digits of
    [w2n w] ([dest_2exp_pos]), and HOL's equation is the tagged
    [dest_2exp_def] theorem. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.pancake Require Import crepLang.
Open Scope N_scope.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/crep_arithScript.sml" "dest_const_def" *)
Definition dest_const (e : exp a) : option (word a) :=
  match e with Const w => Some w | _ => None end.

(** [dest_2exp n w] on the binary digits of [w2n w] (Galette). *)
Fixpoint dest_2exp_pos (n : N) (p : positive) : option N :=
  match p with
  | xH => Some n
  | xI _ => None
  | xO p' => dest_2exp_pos (n + 1) p'
  end.

Definition dest_2exp (n : N) (w : word a) : option N :=
  match w2n w with
  | N0 => None
  | Npos p => dest_2exp_pos n p
  end.

Lemma w2n_1 : w2n (n2w 1 : word a) = 1.
Proof. rewrite w2n_n2w; apply N.mod_small, ONE_LT_dimword. Qed.

(*! HOL "cakeml/pancake/crep_arithScript.sml" "dest_2exp_def" *)
Theorem dest_2exp_def : forall n (w : word a),
  dest_2exp n w =
  if decide (w = n2w 0) then None
  else if decide (w = n2w 1) then Some n
  else if decide (word_and w (n2w 1) <> n2w 0) then None
  else dest_2exp (n + 1) (word_lsr w 1).
Proof.
  intros n w; unfold dest_2exp.
  assert (E0 : w = n2w 0 <-> w2n w = 0).
  { split; [intros ->; rewrite w2n_n2w; apply N.Div0.mod_0_l|].
    intros H; apply word_eq_w2n; rewrite H, w2n_n2w; symmetry; apply N.Div0.mod_0_l. }
  assert (E1 : w = n2w 1 <-> w2n w = 1).
  { split; [intros ->; apply w2n_1|intros H; apply word_eq_w2n; rewrite H, w2n_1; reflexivity]. }
  assert (EA : word_and w (n2w 1) = n2w 0 <-> w2n w mod 2 = 0).
  { unfold word_and; rewrite w2n_1.
    change 1 with (N.ones 1) at 1; rewrite N.land_ones; change (2 ^ 1) with 2.
    split; [intros H; apply (f_equal w2n) in H; rewrite !w2n_n2w in H|intros H; rewrite H; reflexivity].
    rewrite N.Div0.mod_0_l, N.mod_small in H; [exact H|].
    apply N.lt_le_trans with 2; [apply N.mod_lt; lia|].
    pose proof (ONE_LT_dimword (a := a)); lia. }
  rewrite w2n_lsr; change (2 ** 1) with 2.
  destruct (w2n w) as [|p] eqn:Hw.
  - destruct (decide (w = n2w 0)); [reflexivity|tauto].
  - destruct (decide (w = n2w 0)) as [H0|H0]; [apply E0 in H0; congruence|].
    destruct (decide (w = n2w 1)) as [H1|H1].
    + apply E1 in H1; injection H1 as ->; reflexivity.
    + rewrite E1 in H1.
      destruct p as [p|p|]; [| |exfalso; apply H1; reflexivity].
      * destruct (decide (word_and w (n2w 1) <> n2w 0)) as [_|H]; [reflexivity|].
        exfalso; apply H; rewrite EA; lia.
      * destruct (decide (word_and w (n2w 1) <> n2w 0)) as [H|_].
        { exfalso; apply H; apply EA; lia. }
        replace (N.pos p~0 DIV 2) with (N.pos p); [reflexivity|].
        replace (N.pos p~0) with (N.pos p * 2) by lia; rewrite N.div_mul; lia.
Qed.

Lemma dest_2exp_pos_lemma : forall p i n,
  dest_2exp_pos i p = Some n -> i <= n /\ Npos p = 2 ** (n - i).
Proof.
  induction p as [p IH|p IH|]; cbn; intros i n H; [discriminate| |].
  - apply IH in H as [H1 H2]; split; [lia|].
    replace (n - i) with (N.succ (n - (i + 1))) by lia.
    rewrite N.pow_succ_r', <- H2; reflexivity.
  - injection H as <-; split; [lia|]; rewrite N.sub_diag; reflexivity.
Qed.

(*! HOL "cakeml/pancake/crep_arithScript.sml" "dest_2exp_thm" *)
Theorem dest_2exp_thm : forall (w : word a) n2,
  dest_2exp 0 w = Some n2 -> w = word_lsl (n2w 1) n2.
Proof.
  intros w n2; unfold dest_2exp; destruct (w2n w) as [|p] eqn:Hw; [discriminate|].
  intros H; apply dest_2exp_pos_lemma in H as [_ H]; rewrite N.sub_0_r in H.
  pose proof (w2n_lt w) as Hlt; rewrite Hw, H in Hlt; unfold dimword in Hlt.
  unfold word_lsl.
  assert (Hn : n2 < dimindex a) by (apply (N.pow_lt_mono_r_iff 2); lia).
  destruct (N.ltb_spec (dimindex a - 1) n2); [lia|].
  apply word_eq_w2n; rewrite w2n_1, w2n_n2w, Hw, H, N.mul_1_l, N.mod_small; [reflexivity|].
  unfold dimword; exact Hlt.
Qed.

(*! HOL "cakeml/pancake/crep_arithScript.sml" "mul_const_def" *)
Definition mul_const (exp : exp a) (c : word a) : crepLang.exp a :=
  if decide (c = n2w 0) then Const (n2w 0)
  else if decide (c = n2w 1) then exp
  else match dest_2exp 0 c with
       | None => Crepop Mul [exp; Const c]
       | Some i => Shift Lsl exp (Const (n2w i))
       end.

(*! HOL "cakeml/pancake/crep_arithScript.sml" "simp_exp_def" *)
Fixpoint simp_exp (e : exp a) : exp a :=
  match e with
  | Crepop op exps =>
      let exps := MAP simp_exp exps in
      match op, exps with
      | Mul, [exp1; exp2] =>
          match dest_const exp1, dest_const exp2 with
          | Some c, Some c2 => Const (word_mul c c2)
          | Some c, _ => mul_const exp2 c
          | _, Some c => mul_const exp1 c
          | _, _ => Crepop op exps
          end
      | _, _ => Crepop op exps
      end
  | Load32 exp => Load32 (simp_exp exp)
  | LoadByte exp => LoadByte (simp_exp exp)
  | Load exp => Load (simp_exp exp)
  | Op bop exps => Op bop (MAP simp_exp exps)
  | Cmp cmp exp1 exp2 => Cmp cmp (simp_exp exp1) (simp_exp exp2)
  | Shift s exp1 exp2 => Shift s (simp_exp exp1) (simp_exp exp2)
  | exp => exp
  end.

(*! HOL "cakeml/pancake/crep_arithScript.sml" "simp_prog_def" *)
Fixpoint simp_prog (p : prog a) : prog a :=
  match p with
  | Dec v exp p => Dec v (simp_exp exp) (simp_prog p)
  | Assign v exp => Assign v (simp_exp exp)
  | Store exp1 exp2 => Store (simp_exp exp1) (simp_exp exp2)
  | Store32 exp1 exp2 => Store32 (simp_exp exp1) (simp_exp exp2)
  | StoreByte exp1 exp2 => StoreByte (simp_exp exp1) (simp_exp exp2)
  | StoreGlob g exp => StoreGlob g (simp_exp exp)
  | Seq p1 p2 => Seq (simp_prog p1) (simp_prog p2)
  | If exp p1 p2 => If (simp_exp exp) (simp_prog p1) (simp_prog p2)
  | While exp p => While (simp_exp exp) (simp_prog p)
  | Call call_type e exps =>
      let call_type2 :=
        match call_type with
        | None => None
        | Some (rv, opt_handler) =>
            Some (rv, match opt_handler with
                      | None => None
                      | Some (ix, ep) => Some (ix, simp_prog ep)
                      end)
        end in
      Call call_type2 e (MAP simp_exp exps)
  | Return exp => Return (MAP simp_exp exp)
  | ShMem op vn exp => ShMem op vn (simp_exp exp)
  | p => p
  end.

End Defs.
