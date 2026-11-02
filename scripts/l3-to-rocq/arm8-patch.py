import re, sys
p = sys.argv[1]
s = open(p).read()

def replace_def(name, new):
    global s
    tag = '(*! HOL "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "%s_def" *)\n' % name
    i = s.index(tag)
    j = s.index('\n\n', i)
    s = s[:i] + new.strip('\n') + s[j:]

# ByteList: structural recursion
s = s.replace('''(* RECURSIVE: needs hand translation *)
Definition ByteList ''', '''Fixpoint ByteList ''')

replace_def('Poly32Mod2_loop', r'''
(** [Poly32Mod2_loop] recurses on [i] down to [31]; it is defined by
    primitive recursion on the number of steps [i - 31], and HOL's equation
    is the theorem [Poly32Mod2_loop_def]. *)
Definition Poly32Mod2_loop_steps (k : N) : (N * ((list bool) * (list bool))) -> (list bool) :=
  num_rec (fun '((i, (data, poly)) : (N * ((list bool) * (list bool)))) => data)
    (fun _ rec '((i, (data, poly)) : (N * ((list bool) * (list bool)))) =>
       (if (i <? 32) then data else (rec ((i - 1), ((if (testbit i data) then ((field ((LENGTH data) - 1) i data) ++ (bxor (field (i - 1) 0 data) (PAD_RIGHT false i poly))) else data), poly))))) k.

Definition Poly32Mod2_loop (p : (N * ((list bool) * (list bool)))) : (list bool) :=
  Poly32Mod2_loop_steps (fst p - 31) p.

(*! HOL "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "Poly32Mod2_loop_def" *)
Theorem Poly32Mod2_loop_def : forall i data poly,
  Poly32Mod2_loop (i, (data, poly)) =
  (if (i <? 32) then data else (Poly32Mod2_loop ((i - 1), ((if (testbit i data) then ((field ((LENGTH data) - 1) i data) ++ (bxor (field (i - 1) 0 data) (PAD_RIGHT false i poly))) else data), poly)))).
Proof.
  intros i data poly; unfold Poly32Mod2_loop at 1; cbn [fst].
  destruct (N.ltb_spec i 32) as [Hi|Hi].
  - replace (i - 31) with 0 by lia. unfold Poly32Mod2_loop_steps; rewrite num_rec_0. reflexivity.
  - replace (i - 31) with (SUC (i - 1 - 31)) by lia.
    unfold Poly32Mod2_loop_steps at 1; rewrite num_rec_SUC. cbn beta iota.
    destruct (N.ltb_spec i 32); [lia|]. reflexivity.
Qed.
''')

replace_def('CountTrailing', r'''
(** [CountTrailing] recurses on [w >>> 1]; it stops after at most
    [dimindex(:'N)] steps, so it is defined with that many steps of fuel
    (by primitive recursion), and HOL's equation is the theorem
    [CountTrailing_def]. *)
Definition CountTrailing_fuel {Nw : N} (k : N) : (bool * (word Nw)) -> N :=
  num_rec (fun _ => 0)
    (fun _ rec '((b, w) : (bool * (word Nw))) =>
       (if ((bool_decide ((word_bit 0 w) = b)) || (if b then (bool_decide (w = (n2w 0 : (word Nw)))) else (bool_decide (w = (word_2comp (n2w 1 : (word Nw))))))) then 0 else (1 + (rec (b, (word_lsr w 1)))))) k.

Definition CountTrailing {Nw : N} (p : (bool * (word Nw))) : N :=
  CountTrailing_fuel (SUC (dimindex Nw)) p.

Lemma CountTrailing_w2n_lsr1 {Nw : N} (w : word Nw) : w2n (word_lsr w 1) = w2n w / 2.
Proof.
  unfold word_lsr, word_bits; rewrite w2n_n2w.
  unfold BITS, MOD_2EXP, DIV_2EXP.
  pose proof (w2n_lt w) as Hw; unfold dimword in Hw.
  pose proof (DIMINDEX_GT_0 Nw) as Hd.
  replace (MIN (dimindex Nw - 1) (dimindex Nw - 1)) with (dimindex Nw - 1) by (unfold MIN; destruct (_ <? _); lia).
  replace (SUC (dimindex Nw - 1) - 1) with (dimindex Nw - 1) by lia.
  change (2 ** 1) with 2.
  assert (Hq : w2n w / 2 < 2 ** (dimindex Nw - 1)).
  { apply N.Div0.div_lt_upper_bound.
    replace (2 * 2 ** (dimindex Nw - 1)) with (2 ** dimindex Nw); [exact Hw|].
    rewrite <- N.pow_succ_r'; f_equal; lia. }
  rewrite (N.mod_small (w2n w / 2) (2 ** (dimindex Nw - 1))) by exact Hq.
  apply N.mod_small. unfold dimword.
  apply N.lt_le_trans with (2 ** (dimindex Nw - 1)); [exact Hq|].
  apply N.pow_le_mono_r; lia.
Qed.

Lemma CountTrailing_fuel_enough {Nw : N} : forall k (b : bool) (w : word Nw),
  N.size (w2n w) < k ->
  CountTrailing_fuel (SUC k) (b, w) = CountTrailing_fuel k (b, w).
Proof.
  intros k; induction k as [|k IH] using N.peano_ind; intros b w Hk; [lia|].
  unfold CountTrailing_fuel at 1; rewrite num_rec_SUC; fold (@CountTrailing_fuel Nw (SUC k)).
  unfold CountTrailing_fuel at 2; rewrite num_rec_SUC; fold (@CountTrailing_fuel Nw k).
  destruct (_ || _) eqn:Hc; [reflexivity|].
  f_equal.
  destruct (N.eq_dec (w2n w) 0) as [Hz|Hnz].
  - exfalso.
    assert (Hw : w = n2w 0) by (apply word_eq_w2n; rewrite w2n_n2w, N.Div0.mod_0_l; exact Hz).
    subst w. apply Bool.orb_false_iff in Hc as [H1 H2].
    destruct b.
    + assert (bool_decide ((n2w 0 : word Nw) = n2w 0) = true) by (apply bool_decide_spec; reflexivity).
      congruence.
    + assert (bool_decide (word_bit 0 (n2w 0 : word Nw) = false) = true); [|congruence].
      apply bool_decide_spec. unfold word_bit, fcp_index.
      rewrite w2n_n2w, N.Div0.mod_0_l, Bool.andb_false_r. reflexivity.
  - apply IH. rewrite CountTrailing_w2n_lsr1, <- N.div2_div.
    destruct (w2n w) as [|pw]; [contradiction|].
    destruct pw; cbn [N.div2 N.size Pos.size Pos.div2] in *; lia.
Qed.

Lemma CountTrailing_fuel_mono {Nw : N} : forall j k (b : bool) (w : word Nw),
  N.size (w2n w) < k ->
  CountTrailing_fuel (k + j) (b, w) = CountTrailing_fuel k (b, w).
Proof.
  intros j; induction j as [|j IH] using N.peano_ind; intros k b w Hk; [now rewrite N.add_0_r|].
  rewrite N.add_succ_r, CountTrailing_fuel_enough by lia. apply IH, Hk.
Qed.

Lemma CountTrailing_size_le {Nw : N} (w : word Nw) : N.size (w2n w) <= dimindex Nw.
Proof.
  pose proof (w2n_lt w) as Hw; unfold dimword in Hw.
  destruct (N.eq_dec (w2n w) 0) as [->|Hnz]; [cbn; lia|].
  rewrite N.size_log2 by exact Hnz.
  apply N.log2_lt_pow2 in Hw; lia.
Qed.

(*! HOL "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml" "CountTrailing_def" *)
Theorem CountTrailing_def {Nw : N} : forall (b : bool) (w : word Nw),
  CountTrailing (b, w) =
  (if ((bool_decide ((word_bit 0 w) = b)) || (if b then (bool_decide (w = (n2w 0 : (word Nw)))) else (bool_decide (w = (word_2comp (n2w 1 : (word Nw))))))) then 0 else (1 + ((CountTrailing (Nw:=Nw)) (b, (word_lsr w 1))))).
Proof.
  intros b w; unfold CountTrailing at 1, CountTrailing_fuel; rewrite num_rec_SUC;
    fold (@CountTrailing_fuel Nw (dimindex Nw)).
  destruct (_ || _); [reflexivity|]. f_equal.
  unfold CountTrailing. symmetry.
  assert (H : N.size (w2n (word_lsr w 1)) < dimindex Nw).
  { rewrite CountTrailing_w2n_lsr1, <- N.div2_div.
    pose proof (CountTrailing_size_le w) as Hs'.
    destruct (w2n w) as [|pw]; [cbn; pose proof (DIMINDEX_GT_0 Nw); lia|].
    destruct pw; cbn [N.div2 N.size Pos.size Pos.div2] in *; lia. }
  apply CountTrailing_fuel_enough. exact H.
Qed.
''')


# boolify<n> (generated by HOL's bitstringLib on demand): right-nested tuples
ns = sorted(set(int(m) for m in re.findall(r'\bboolify(\d+)\b', s)))
helpers = "(** HOL's [boolify<n>] (generated by [bitstringLib.bitify_boolify]):\n    the bits of a word, most significant first. *)\n"
for n in ns:
    ty = " * (".join(["bool"]*n) + ")"*(n-1)
    body = ", (".join("word_bit %d w" % (n-1-i) for i in range(n)) + ")"*(n-1)
    helpers += "Definition boolify%d (w : word %d) : %s :=\n  (%s).\n" % (n, n, ty, body)
s = s.replace("(** ** Definitions *)\n", "(** ** Definitions *)\n\n" + helpers + "\n", 1)

open(p, 'w').write(s)
