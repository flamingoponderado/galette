(** * CakeML [wordProps]: more clock lemmas and constant fields

    Port of the part of [cakeml/compiler/backend/semantics/wordPropsScript.sml]
    between [evaluate_add_clock] and the stack swap lemma: removing the
    unused clock ([evaluate_dec_clock]), the fields that [evaluate] never
    changes ([evaluate_consts]), and small lemmas on [get_vars] and
    [stack_size].

    [evaluate_dec_clock] is derived from the Galette-only generalisation
    [evaluate_sub_clock] (subtract from the clock any amount not exceeding
    the final clock), proved by well-founded induction on [eval_lt] with
    [evaluate_eqn]; HOL's proof is by [recInduct evaluate_ind] using
    [evaluate_add_clock].  HOL [s with clock := k] is [set_clock k s]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import consts clock consts_with.
Open Scope N_scope.

(** ** Subtracting clock (Galette-only) *)

Lemma set_clock_id {a c ffi_t} (s : state a c ffi_t) : set_clock (clock s) s = s.
Proof. destruct s; reflexivity. Qed.

Ltac bool_facts :=
  repeat match goal with
         | H : (_ =? _)%N = true |- _ => apply N.eqb_eq in H
         | H : (_ =? _)%N = false |- _ => apply N.eqb_neq in H
         end.

Ltac sc_hyp IH H :=
  repeat first
    [ progress (rewrite ?fix_clock_evaluate in H)
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in let Hi := fresh "Hi" in
          pose proof (evaluate_clock p' s'' r' t E) as Hc;
          pose proof (IH (p', s'') ltac:(wd_eval_lt) r' t E) as Hi; clear E; cbn [fst snd] in Hi
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; ac_simpl H
      end ].

Ltac sc_side := wd_clk; bool_facts; unfold flush_state in *; unfold_sets; lia.

Ltac sc_goal d :=
  repeat first
    [ bd_contra
    | progress (rewrite ?fix_clock_evaluate)
    | progress (autorewrite with wdc; cbn [PAIR_MAP option_map cont_loop exit_loop bad_fun_return fst snd])
    | progress rw_cases
    | match goal with
      | E : alloc _ _ _ = _ |- context [alloc _ _ _] => rewrite E
      | E : share_inst _ _ _ _ = _ |- context [share_inst _ _ _ _] => rewrite E
      end
    | match goal with
      | |- context [(?x =? 0)%N] =>
          lazymatch x with context [d] => idtac end;
          destruct (N.eqb_spec x 0); cbn beta iota zeta;
          [try (exfalso; sc_side) | try (exfalso; sc_side)]
      end
    | match goal with
      | Hi : forall d', d' <= clock ?t -> evaluate (?p', set_clock (clock ?s'' - d') ?s'') = _
        |- context [evaluate (?p', ?X)] =>
          replace X with (set_clock (clock s'' - (clock s'' - clock X)) s'') by
            (autorewrite with wdc; f_equal; sc_side);
          rewrite Hi by sc_side; cbn beta iota zeta
      end ].


Section DecClock.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(** Galette-only: the clock can be lowered by any amount not exceeding the
    final clock without changing the result. *)
Lemma evaluate_sub_clock : forall (p : prog a) (s : state) r t,
  evaluate (p, s) = (r, t) -> forall d, d <= clock t ->
  evaluate (p, set_clock (clock s - d) s) = (r, set_clock (clock t - d) t).
Proof.
  enough (G : forall x : prog a * state, forall r t, evaluate x = (r, t) -> forall d, d <= clock t ->
    evaluate (fst x, set_clock (clock (snd x) - d) (snd x)) = (r, set_clock (clock t - d) t))
    by (intros p s r t H; exact (G (p, s) r t H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H d Hd; cbn [fst snd].
  rewrite evaluate_eqn in H |- *.
  destruct p; cbn [evaluate_body] in H |- *; ac_simpl H; sc_hyp IH H;
  try discriminate H; try (injection H as <- <-);
  sc_goal d.
  all: try (wd_clk; bool_facts; first [ reflexivity | apply pair_equal_spec; split; [reflexivity|]; f_equal; lia | f_equal; lia ]).
  all: try (wd_clk; bool_facts; unfold flush_state in *; unfold_sets; repeat f_equal; lia).
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "with_locals_same_clock" *)
Theorem with_locals_same_clock : forall (s : state) l,
  set_clock (clock s) (set_locals l s) = set_locals l s.
Proof. intros; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "cont_loop_not_timeout" *)
Theorem cont_loop_not_timeout : forall (res : option (result a)),
  cont_loop res -> res <> SOME TimeOut.
Proof. intros [[]|] H; unfold is_true in H; cbn in H; discriminate. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_add_clock_body" *)
Theorem evaluate_add_clock_body : forall (c0 : prog a) (s : state) res s',
  evaluate (c0, s) = (res, s') /\ cont_loop res ->
  forall extra,
    evaluate (c0, set_clock (clock s + extra) s) = (res, set_clock (clock s' + extra) s').
Proof.
  intros c0 s res s' [H Hc] extra. apply evaluate_add_clock; split; [exact H|].
  apply cont_loop_not_timeout, Hc.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_dec_clock" *)
Theorem evaluate_dec_clock : forall (prog : prog a) (st : state) res rst,
  evaluate (prog, st) = (res, rst) ->
  evaluate (prog, set_clock (clock st - clock rst) st) = (res, set_clock 0 rst).
Proof.
  intros prog st res rst H. rewrite (evaluate_sub_clock prog st res rst H (clock rst)) by lia.
  rewrite N.sub_diag; reflexivity.
Qed.

End DecClock.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "SND_alt_def" *)
Theorem SND_alt_def : forall {A B} (c0 : A * B), SND c0 = (fun '(a, b) => b) c0.
Proof. intros A B [x y]; reflexivity. Qed.

(** ** Constant fields *)

(** Facts about the primitives in the context (for [evaluate_consts]). *)
Local Ltac ec_facts :=
  repeat match goal with
         | E : alloc _ _ _ = (_, _) |- _ => apply alloc_code_gc_fun_const in E
         | E : inst _ _ = SOME _ |- _ => apply inst_code_gc_fun_const in E
         | E : mem_store _ _ _ = SOME _ |- _ => apply mem_store_const in E
         | E : jump_exc _ = SOME (_, _) |- _ => apply jump_exc_const in E
         | E : share_inst _ _ _ _ = (_, _) |- _ => apply share_inst_const in E
         | E : pop_env _ = SOME _ |- _ => apply pop_env_code_gc_fun_clock in E
         | E : cut_state _ _ = SOME _ |- _ =>
             let l := fresh "l" in apply cut_state_const in E; destruct E as [l ->]
         end;
  repeat match goal with
         | |- context [push_env ?x ?y ?z] =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         | H : context [push_env ?x ?y ?z] |- _ =>
             lazymatch goal with
             | _ : clock (push_env x y z) = _ |- _ => fail
             | _ => pose proof (push_env_const x y z); destr_conj
             end
         end;
  destr_conj.

Section Consts.
Context {a : N} {c ffi_t : Type}.
Local Abbreviation state := (state a c ffi_t).

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_consts" *)
Theorem evaluate_consts : forall (xs : prog a) (s1 : state) vs s2,
  evaluate (xs, s1) = (vs, s2) ->
  gc_fun s1 = gc_fun s2 /\
  mdomain s1 = mdomain s2 /\
  sh_mdomain s1 = sh_mdomain s2 /\
  be s1 = be s2 /\
  compile s1 = compile s2 /\
  stack_limit s1 = stack_limit s2.
Proof.
  enough (G : forall x : prog a * state, forall r s2, evaluate x = (r, s2) ->
    gc_fun (snd x) = gc_fun s2 /\ mdomain (snd x) = mdomain s2 /\ sh_mdomain (snd x) = sh_mdomain s2 /\
    be (snd x) = be s2 /\ compile (snd x) = compile s2 /\ stack_limit (snd x) = stack_limit s2)
    by (intros xs s1 vs s2 H; exact (G (xs, s1) vs s2 H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s2 H; cbn [snd].
  rewrite evaluate_eqn in H; destruct p; cbn [evaluate_body] in H; io_step IH H;
  repeat match goal with E : (_, _) = (_, _) |- _ => injection E as <- <- end;
  ec_facts;
  unfold flush_state, dec_clock, call_env, set_var, set_vars, unset_var, set_store in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn [fst snd] in *; destr_conj; unfold_sets; repeat split; congruence.
Qed.

(** ** [get_vars] and [stack_size] *)

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_vars_length_lemma" *)
Theorem get_vars_length_lemma : forall ls (s : state) y,
  get_vars ls s = SOME y -> LENGTH y = LENGTH ls.
Proof.
  induction ls as [|l ls IH]; intros s y H; cbn in H.
  - injection H as <-; reflexivity.
  - destruct (get_var l s); [|discriminate]. destruct (get_vars ls s) as [ys|] eqn:E; [|discriminate].
    injection H as <-. rewrite !LENGTH_length in *. cbn. specialize (IH s ys E).
    rewrite !LENGTH_length in IH. lia.
Qed.

End Consts.

Section StackSize.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_eq" *)
Theorem stack_size_eq : forall n l0 l (stack : list (stack_frame a)) n' l0' l' handler,
  stack_size (StackFrame n l0 l NONE :: stack) = OPTION_MAP2 N.add n (stack_size stack) /\
  stack_size (StackFrame n' l0' l' (SOME handler) :: stack) =
    OPTION_MAP2 N.add (OPTION_MAP (N.add 3) n') (stack_size stack) /\
  stack_size (@nil (stack_frame a)) = SOME 1.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_eq2" *)
Theorem stack_size_eq2 : forall (sfrm : stack_frame a) stack,
  stack_size (sfrm :: stack) = OPTION_MAP2 N.add (stack_size_frame sfrm) (stack_size stack) /\
  stack_size (@nil (stack_frame a)) = SOME 1.
Proof. intros; split; reflexivity. Qed.

End StackSize.
