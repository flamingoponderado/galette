(** * Pancake [crep_arithProof]: correctness of the [crep_arith] pass

    Port of [cakeml/pancake/proofs/crep_arithProofScript.sml].

    HOL's local overloads [mapc f s] ([s with code := FMAP_MAP2 f s.code])
    and [mapcs] ([mapc (\(s,n,p). (n, simp_prog p))]) are written out in the
    statements with crepSem's [set_code].  HOL's local lemmas
    ([OPT_MMAP_EQ_SOME_MONO], [simp_exp_correct1], [lookup_code],
    [sh_mem_op_code], [ind_thm]) are replaced by the untagged helpers below
    ([eval] does not read the code, so [simp_exp_eval] is stated for the
    unchanged state).  Proof method as in [crepProps]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.pancake Require Import crepLang crep_arith.
From Galette.cakeml.pancake.semantics Require panSem.
From Galette.cakeml.pancake.semantics Require Import crepSem crepProps.
Import panSem(word_lab(..)).
Open Scope N_scope.
Local Open Scope fmap_scope.

Section Exp.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_2exp_bound" *)
Theorem dest_2exp_bound : forall n (w : word a) m,
  dest_2exp n w = SOME m ->
  m <= n + w2n (word_log2 w).
Proof.
  intros n w m H; unfold dest_2exp in H.
  destruct (w2n w) as [|p] eqn:Hw; [discriminate|].
  apply dest_2exp_pos_lemma in H as [H1 H2].
  unfold word_log2, LOG2; rewrite w2n_n2w, Hw, H2, N.log2_pow2 by lia.
  pose proof (w2n_lt w) as Hlt. rewrite Hw, H2, dimword_pow in Hlt.
  apply N.pow_lt_mono_r_iff in Hlt; [|lia].
  rewrite N.mod_small; [lia|].
  pose proof (dimindex_lt_dimword (a := a)); lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_2exp_bound'" *)
Theorem dest_2exp_bound' : forall (n : N) (w : word a) m,
  dest_2exp 0 w = SOME m ->
  m < dimindex a.
Proof.
  intros _ w m H; unfold dest_2exp in H.
  destruct (w2n w) as [|p] eqn:Hw; [discriminate|].
  apply dest_2exp_pos_lemma in H as [_ H2]. rewrite N.sub_0_r in H2.
  pose proof (w2n_lt w) as Hlt. rewrite Hw, H2, dimword_pow in Hlt.
  apply N.pow_lt_mono_r_iff in Hlt; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_const_thm" *)
Theorem dest_const_thm : forall (exp : exp a) v,
  dest_const exp = SOME v -> exp = Const v.
Proof. intros [] v H; cbn in H; try discriminate; injection H as ->; reflexivity. Qed.

Local Open Scope word_scope.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "eval_mul_const" *)
Theorem eval_mul_const : forall (s : state a ffi_t) exp w c,
  eval s exp = SOME (Word w) ->
  eval s (mul_const exp c) = SOME (Word (w * c)).
Proof.
  intros s exp w c H; unfold mul_const.
  destruct (decide (c = n2w 0)) as [->|H0].
  { cbn. f_equal; f_equal; word_ring. }
  destruct (decide (c = n2w 1)) as [->|H1].
  { rewrite H. f_equal; f_equal; word_ring. }
  destruct (dest_2exp 0 c) as [i|] eqn:Hd.
  - pose proof (dest_2exp_bound' 0 c i Hd) as Hi.
    apply dest_2exp_thm in Hd. cbn [eval]. rewrite H.
    assert (Hwi : w2n (n2w i : word a) = i).
    { rewrite w2n_n2w, N.mod_small; [reflexivity|].
      pose proof (dimindex_lt_dimword (a := a)); lia. }
    rewrite Hwi. unfold wordLang.word_sh.
    destruct (andb (negb (i =? 0)%N) (dimindex a <=? i)%N) eqn:E.
    { apply Bool.andb_true_iff in E as [_ E]; apply N.leb_le in E; lia. }
    cbn. f_equal; f_equal. subst c. unfold word_lsl.
    destruct (N.ltb_spec (dimindex a - 1) i); [lia|].
    rewrite w2n_1, N.mul_1_l. rewrite <- (n2w_w2n w) at 2.
    word_Z; apply zcong_eq; rewrite N2Z.inj_mul; ring.
  - cbn [eval OPT_MMAP OPTION_BIND]. rewrite H. cbn. reflexivity.
Qed.

Lemma OPT_MMAP_MAP_mono {A B} (f : A -> option B) (g : A -> A) xs ys :
  OPT_MMAP f xs = SOME ys ->
  (forall x z, In x xs -> f x = SOME z -> f (g x) = SOME z) ->
  OPT_MMAP f (MAP g xs) = SOME ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys H Hg; [exact H|].
  cbn in H |- *. destruct (f x) as [z|] eqn:Ef; [|discriminate].
  rewrite (Hg x z (or_introl eq_refl) Ef). cbn.
  destruct (OPT_MMAP f xs) as [zs|] eqn:Ez; [|discriminate].
  rewrite (IH zs eq_refl) by (intros; apply Hg; [right|]; assumption). exact H.
Qed.

(** [simp_exp] preserves successful evaluation (Galette-only form of HOL's
    local [simp_exp_correct1]). *)
Lemma simp_exp_eval : forall (s : state a ffi_t) e v,
  eval s e = SOME v -> eval s (simp_exp e) = SOME v.
Proof.
  intros s e; induction e as [w|v0|e IH|e IH|e IH|g|op es IH|op es IH|c e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using cexp_nested_ind; intros v H; cbn [simp_exp]; try exact H.
  - cbn [eval] in H |- *. destruct (eval s e) as [[w]|] eqn:E; [|discriminate].
    rewrite (IH _ eq_refl); exact H.
  - cbn [eval] in H |- *. destruct (eval s e) as [[w]|] eqn:E; [|discriminate].
    rewrite (IH _ eq_refl); exact H.
  - cbn [eval] in H |- *. destruct (eval s e) as [[w]|] eqn:E; [|discriminate].
    rewrite (IH _ eq_refl); exact H.
  - cbn [eval] in H |- *. destruct (OPT_MMAP (eval s) es) as [ws|] eqn:E; [|discriminate].
    rewrite (OPT_MMAP_MAP_mono _ _ _ _ E); [exact H|].
    intros x z Hx Hz. exact (proj1 (Forall_forall _ _) IH x Hx z Hz).
  - assert (Hgen : eval s (Crepop op (MAP simp_exp es)) = SOME v).
    { cbn [eval] in H |- *. destruct (OPT_MMAP (eval s) es) as [ws|] eqn:E; [|discriminate].
      rewrite (OPT_MMAP_MAP_mono _ _ _ _ E); [exact H|].
      intros x z Hx Hz. exact (proj1 (Forall_forall _ _) IH x Hx z Hz). }
    destruct op. destruct es as [|x1 [|x2 [|x3 es]]]; cbn [MAP] in *; try exact Hgen.
    inversion IH as [|? ? IHx1 IH']; inversion IH' as [|? ? IHx2 _]; subst.
    cbn [eval OPT_MMAP OPTION_BIND] in H.
    destruct (eval s x1) as [[w1]|] eqn:E1; [|discriminate].
    destruct (eval s x2) as [[w2]|] eqn:E2; [|discriminate].
    cbn in H. injection H as <-.
    pose proof (IHx1 _ eq_refl) as S1; pose proof (IHx2 _ eq_refl) as S2.
    destruct (dest_const (simp_exp x1)) as [c|] eqn:D1;
      [apply dest_const_thm in D1; rewrite D1 in S1; cbn in S1; injection S1 as <-|];
      (destruct (dest_const (simp_exp x2)) as [c2|] eqn:D2;
        [apply dest_const_thm in D2; rewrite D2 in S2; cbn in S2; injection S2 as <-|]).
    + reflexivity.
    + rewrite (eval_mul_const s _ w2 c S2). f_equal; f_equal; apply WORD_MULT_COMM.
    + rewrite (eval_mul_const s _ w1 c2 S1). reflexivity.
    + cbn [eval OPT_MMAP OPTION_BIND]. rewrite S1, S2. reflexivity.
  - cbn [eval] in H |- *.
    destruct (eval s e1) as [[w1]|] eqn:E1; [|discriminate].
    destruct (eval s e2) as [[w2]|] eqn:E2; [|discriminate].
    rewrite (IH1 _ eq_refl), (IH2 _ eq_refl); exact H.
  - cbn [eval] in H |- *.
    destruct (eval s e1) as [[w1]|] eqn:E1; [|discriminate].
    destruct (eval s e2) as [[w2]|] eqn:E2; [|discriminate].
    rewrite (IH1 _ eq_refl), (IH2 _ eq_refl); exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_exp_correct" *)
Theorem simp_exp_correct : forall (s : state a ffi_t) exp v f,
  eval s exp = SOME v ->
  eval (set_code (FMAP_MAP2 f (code s)) s) (simp_exp exp) = SOME v.
Proof. intros s exp v f H; rewrite eval_set_code; apply simp_exp_eval, H. Qed.

Lemma opt_mmap_simp_exp_eval (s : state a ffi_t) es vs :
  OPT_MMAP (eval s) es = SOME vs ->
  OPT_MMAP (eval s) (MAP simp_exp es) = SOME vs.
Proof. intros H; apply (OPT_MMAP_MAP_mono _ _ _ _ H); intros; apply simp_exp_eval; assumption. Qed.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "opt_mmap_simp_exp_correct" *)
Theorem opt_mmap_simp_exp_correct : forall (s : state a ffi_t) es vs f,
  OPT_MMAP (eval s) es = SOME vs ->
  OPT_MMAP (eval (set_code (FMAP_MAP2 f (code s)) s)) (MAP simp_exp es) = SOME vs.
Proof. intros s es vs f H; rewrite eval_set_code; apply opt_mmap_simp_exp_eval, H. Qed.

End Exp.

Section Prog.
Context {a : N} {ffi_t : Type}.

Definition simp_code_fn (x : funname * (list varname * prog a)) : list varname * prog a :=
  let '(_, (n, p)) := x in (n, simp_prog p).

(** HOL's local overload [mapcs]. *)
Definition mapcs (s : state a ffi_t) : state a ffi_t :=
  set_code (FMAP_MAP2 simp_code_fn (code s)) s.

Lemma lookup_code_simp c fname (args : list (word_lab a)) (len : N) :
  lookup_code (FMAP_MAP2 simp_code_fn c) fname args len =
  OPTION_MAP (fun '(p, l) => (simp_prog p, l)) (lookup_code c fname args len).
Proof.
  unfold lookup_code; rewrite FLOOKUP_FMAP_MAP2.
  destruct (FLOOKUP c fname) as [[ns p]|]; cbn; [|reflexivity].
  destruct (_ && _); reflexivity.
Qed.

Lemma sh_mem_op_mapcs op v (addr : word a) (s : state a ffi_t) :
  sh_mem_op op v addr (mapcs s) =
  (fst (sh_mem_op op v addr s), mapcs (snd (sh_mem_op op v addr s))).
Proof.
  destruct op; cbn [sh_mem_op]; unfold sh_mem_load, sh_mem_store, mapcs; destruct s; cbn;
    repeat match goal with |- context [match ?x with _ => _ end] =>
      destruct x eqn:?; cbn beta iota zeta end; reflexivity.
Qed.

Ltac st_eq2 :=
  unfold mapcs;
  cbv beta iota delta [set_clock dec_clock set_locals set_memory set_ffi set_code set_globals
       set_var empty_locals];
  cbn [clock locals globals code memory memaddrs sh_memaddrs be ffi base_addr top_addr];
  first [ reflexivity | f_equal; lia ].

Ltac simp_rw IH :=
  match goal with
  | E : evaluate (?p', ?Y) = (?r, ?s0) |- context [evaluate (?q, ?X)] =>
      replace q with (simp_prog p') by reflexivity;
      let Hx := fresh "Hx" in
      assert (Hx : evaluate (simp_prog p', mapcs Y) = (r, mapcs s0))
        by (apply (IH (p', Y) ltac:(lt_tac) r s0 E); first [discriminate | assumption | congruence]);
      replace X with (mapcs Y) by st_eq2;
      rewrite Hx; clear Hx; cbn beta iota zeta
  end.

Ltac exp_rw :=
  repeat match goal with
  | E : eval ?s ?e = SOME ?v |- context [eval ?s (simp_exp ?e)] =>
      rewrite (simp_exp_eval s e v E)
  | E : OPT_MMAP (eval ?s) ?es = SOME ?v |- context [OPT_MMAP (eval ?s) (MAP simp_exp ?es)] =>
      rewrite (opt_mmap_simp_exp_eval s es v E)
  end; cbn beta iota zeta.

(*! HOL "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct" *)
Theorem simp_prog_correct : forall (p : prog a) (s : state a ffi_t) r s',
  evaluate (p, s) = (r, s') ->
  r <> SOME Error ->
  evaluate (simp_prog p,
            set_code (FMAP_MAP2 (fun '(s, (n, p)) => (n, simp_prog p)) (code s)) s) =
  (r, set_code (FMAP_MAP2 (fun '(s, (n, p)) => (n, simp_prog p)) (code s')) s').
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s',
            evaluate x = (r, s') -> r <> SOME Error ->
            evaluate (simp_prog (fst x), mapcs (snd x)) = (r, mapcs s'))
    by (intros p s r s' H1 H2; exact (G (p, s) r s' H1 H2)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r t H Hr; cbn [fst snd].
  destruct p; try match goal with |- context [simp_prog (Call ?o _ _)] =>
                     destruct o as [[? [[? ?]|]]|] end;
    unfold_eval_in H; cbn [simp_prog]; rewrite evaluate_unfold; cbn [evaluate_body];
    rewrite ?fcl_evaluate; cbn beta; unfold mapcs; rewrite ?eval_set_code;
    state_cbn; repeat split_in H; eqb_facts.
  all: first [ discriminate H | injection H as <- <-; first [ exfalso; apply Hr; reflexivity | idtac ]
             | idtac ].
  all: repeat (first [ progress exp_rw | progress rw_eqs | simp_rw IH
                      | rewrite lookup_code_simp; cbn beta iota zeta
                      | progress cbn [OPTION_MAP] ]).
  all: try reflexivity.
  all: try solve [ f_equal; st_eq2 ].
  all: change (set_code (FMAP_MAP2 simp_code_fn (code s)) s) with (mapcs s);
       rewrite sh_mem_op_mapcs, H; reflexivity.
Qed.

End Prog.
