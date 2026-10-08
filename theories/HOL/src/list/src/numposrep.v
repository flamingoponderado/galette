(** * HOL4 [numposrep]: positional representations of numbers

    [n2l] and [n2lA] are defined in HOL by well-founded recursion on [n]
    (the recursive call is on [n DIV b] with [2 <= b <= n]); here they use
    [Fix] over [N.lt], and HOL's recursion equations are the tagged [_def]
    theorems.  Extracted, the recursion depth is the number of digits. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
Open Scope N_scope.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "l2n_def" *)
Fixpoint l2n (b : N) (l : list N) : N :=
  match l with [] => 0 | h :: t => h MOD b + b * l2n b t end.

Lemma n2l_dec_lt b n : (n <? b) || (b <? 2) = false -> n DIV b < n.
Proof.
  intros H; apply orb_false_iff in H as [H1 H2]; apply N.ltb_ge in H1, H2.
  apply N.div_lt; lia.
Qed.

(** [N.lt_wf_0] guarded by [Acc_intro_generator] so that [n2l]/[n2lA] also
    compute in the kernel ([vm_compute]); the recursion depth is the number
    of digits. *)
Definition N_lt_wf : well_founded N.lt := Acc_intro_generator 32 N.lt_wf_0.
#[global] Opaque N_lt_wf.

Definition n2l_F (b n : N) (rec : forall m, m < n -> list N) : list N :=
  match Sumbool.sumbool_of_bool ((n <? b) || (b <? 2)) with
  | left _ => [n MOD b]
  | right H => n MOD b :: rec (n DIV b) (n2l_dec_lt b n H)
  end.

(** HOL [n2l] (see [n2l_def]). *)
Definition n2l (b n : N) : list N := Fix N_lt_wf (fun _ => list N) (n2l_F b) n.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "n2l_def" *)
Theorem n2l_def : forall b n,
  n2l b n = if (n <? b) || (b <? 2) then [n MOD b] else n MOD b :: n2l b (n DIV b).
Proof.
  intros b n; unfold n2l at 1; rewrite Fix_eq.
  - unfold n2l_F; destruct (Sumbool.sumbool_of_bool _) as [E|E]; rewrite E; reflexivity.
  - intros x f g Hfg; unfold n2l_F; destruct (Sumbool.sumbool_of_bool _); [reflexivity|].
    rewrite Hfg; reflexivity.
Qed.

Definition n2lA_F {B} (f : N -> B) (b n : N) (rec : forall m, m < n -> list B -> list B)
  (A : list B) : list B :=
  match Sumbool.sumbool_of_bool ((n <? b) || (b <? 2)) with
  | left _ => f (n MOD b) :: A
  | right H => rec (n DIV b) (n2l_dec_lt b n H) (f (n MOD b) :: A)
  end.

(** HOL [n2lA] (see [n2lA_def]). *)
Definition n2lA {B} (A : list B) (f : N -> B) (b n : N) : list B :=
  Fix N_lt_wf (fun _ => list B -> list B) (n2lA_F f b) n A.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "n2lA_def" *)
Theorem n2lA_def : forall {B} (A : list B) f b n,
  n2lA A f b n =
  if (n <? b) || (b <? 2) then f (n MOD b) :: A else n2lA (f (n MOD b) :: A) f b (n DIV b).
Proof.
  intros B A f b n; unfold n2lA at 1; rewrite Fix_eq.
  - unfold n2lA_F; destruct (Sumbool.sumbool_of_bool _) as [E|E]; rewrite E; reflexivity.
  - intros x g h Hgh; apply functional_extensionality; intros A'.
    unfold n2lA_F; destruct (Sumbool.sumbool_of_bool _); [reflexivity|].
    rewrite Hgh; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_from_bin_list_def" *)
Definition num_from_bin_list : list N -> N := fun l => l2n 2 (REVERSE l).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_from_oct_list_def" *)
Definition num_from_oct_list : list N -> N := fun l => l2n 8 (REVERSE l).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_from_dec_list_def" *)
Definition num_from_dec_list : list N -> N := fun l => l2n 10 (REVERSE l).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_from_hex_list_def" *)
Definition num_from_hex_list : list N -> N := fun l => l2n 16 (REVERSE l).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_to_bin_list_def" *)
Definition num_to_bin_list : N -> list N := fun n => REVERSE (n2l 2 n).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_to_oct_list_def" *)
Definition num_to_oct_list : N -> list N := fun n => REVERSE (n2l 8 n).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_to_dec_list_def" *)
Definition num_to_dec_list : N -> list N := fun n => REVERSE (n2l 10 n).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "num_to_hex_list_def" *)
Definition num_to_hex_list : N -> list N := fun n => REVERSE (n2l 16 n).

(*! HOL "HOL/src/list/src/numposrepScript.sml" "n2lA_10" *)
Theorem n2lA_10 : forall {B} (A : list B) f n,
  n2lA A f 10 n = if n <? 10 then f n :: A else n2lA (f (n MOD 10) :: A) f 10 (n DIV 10).
Proof.
  intros B A f n; rewrite n2lA_def; cbn [N.ltb N.compare].
  destruct (N.ltb_spec n 10) as [H|H]; cbn; [rewrite N.mod_small by exact H|]; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "n2lA_n2l" *)
Theorem n2lA_n2l : forall {B} (f : N -> B) b A n, n2lA A f b n = MAP f (REVERSE (n2l b n)) ++ A.
Proof.
  intros B f b A n; revert A; induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  intros A; rewrite n2lA_def, n2l_def.
  destruct ((n <? b) || (b <? 2)) eqn:E; [reflexivity|].
  rewrite IH by (apply n2l_dec_lt, E).
  cbn [REVERSE List.rev]; rewrite map_app, <- app_assoc; reflexivity.
Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "n2l_n2lA" *)
Theorem n2l_n2lA : forall b n, n2l b n = REVERSE (n2lA [] (fun x => x) b n).
Proof. intros b n; rewrite n2lA_n2l, app_nil_r, map_id, rev_involutive; reflexivity. Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "l2n_n2l" *)
Theorem l2n_n2l : forall b n, 1 < b -> l2n b (n2l b n) = n.
Proof.
  intros b n Hb; induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  rewrite n2l_def; destruct ((n <? b) || (b <? 2)) eqn:E.
  - apply orb_true_iff in E as [E|E]; apply N.ltb_lt in E; [|lia].
    cbn [l2n]; rewrite !(N.mod_small n b E); lia.
  - cbn [l2n]; rewrite IH by (apply n2l_dec_lt, E).
    rewrite N.Div0.mod_mod.
    pose proof (N.div_mod n b) as D; lia.
Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "n2l_BOUND" *)
Theorem n2l_BOUND : forall b n, 0 < b -> EVERY (fun x => x <? b) (n2l b n).
Proof.
  intros b n Hb; induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  rewrite n2l_def; destruct ((n <? b) || (b <? 2)) eqn:E; cbn [EVERY];
    rewrite (proj2 (N.ltb_lt _ _) (N.mod_lt n b ltac:(lia))); cbn; [reflexivity|].
  apply IH, n2l_dec_lt, E.
Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "l2n_APPEND" *)
Theorem l2n_APPEND : forall b l1 l2, l2n b (l1 ++ l2) = l2n b l1 + b ** LENGTH l1 * l2n b l2.
Proof.
  intros b l1 l2; induction l1 as [|h t IH]; cbn [app l2n LENGTH].
  - rewrite N.pow_0_r; lia.
  - rewrite IH, N.pow_succ_r'; lia.
Qed.

(*! HOL "HOL/src/list/src/numposrepScript.sml" "l2n_lt" *)
Theorem l2n_lt : forall l b, 0 < b -> l2n b l < b ** LENGTH l.
Proof.
  intros l b Hb; induction l as [|h t IH]; cbn [l2n LENGTH]; [rewrite N.pow_0_r; lia|].
  rewrite N.pow_succ_r'.
  pose proof (N.mod_lt h b ltac:(lia)).
  assert (l2n b t + 1 <= b ** LENGTH t) by lia.
  nia.
Qed.
