(** * CakeML [arm8_targetProof]: [encoder_correct] for ARMv8

    Port of [cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml].

    HOL proves the theorem with the step evaluator ([arm8_stepLib]),
    bit-blasting ([blastLib]) and the tactics of [arm8_targetProofLib]
    (generated per case in ML).  Here the proof follows the structure of
    the RISC-V port ([riscv_targetProof]) with Galette-only lemmas:

    - a bit-blasting tactic [wblast] for concrete bit indices (copied from
      [riscv_targetProof] and extended with [word_ror] and
      [bit_field_insert]), and a tactic [decode_tac] that evaluates the L3
      [Decode] on an encoded word;
    - [Decode w = i] whenever [Encode i = ARM8 w], for the ARMv8
      instructions emitted by the encoder ([dec_MoveWide], ...; for the
      loads and stores up to the flags that [Run] ignores);
    - the effect of [Run] on these instructions as an abstract function
      [aexec] on registers, program counter, memory and the N, Z, C, V
      flags (which [arm8_proj] includes, so interference preserves them)
      ([run_MoveWide], ...), the byte-level meaning of [Mem]/[write'Mem]
      for aligned accesses, and the step theorem [step_thm] for
      [NextStateARM8];
    - a simulation lemma along a path of instructions ([enc_sim]) and one
      lemma per ASM instruction ([sim_skip], [sim_const], ..., [sim_mem],
      [sim_jc_reg], ...).

    HOL's [lsl], [lsr] and [asr2] are proved for each of the 64 shift
    amounts by evaluating [DecodeBitMasks]; [asr], [ror] and [mul_long] by
    bit-level reasoning.

    Not ported:
    - the [local] lemmas [lsl_lem1], [lsl_lem2], [lsl_lem4], [lsl_lem5],
      [lsr_lem1], [lsr_lem2], [asr_lem1] (steps of HOL's proofs of [lsl],
      [lsr], [asr2], which are proved differently here) and the first,
      [local] declaration of [arm8_encoding] (with [let l = arm8_enc i]);
      its [SIMP_RULE] form, the non-local [arm8_encoding], is ported;
    - the ML values [ev], [replicate1], [and_max], [lsl_lem3], [lsl_lem6],
      [ext12], [print_tac], [fs], [rfs] (conversions, rewrites computed in
      ML and tactic helpers, not theorems of the script);
    - the contents of [arm8_targetProofLib] (ML values proved with
      [Q.prove] or [BBLAST_PROVE], e.g. [word_log2_7],
      [DecodeBitMasks_SOME], [lem1]...[lem37], and the tactics), which are
      not declarations of the script. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words bitstring alignment.
From Galette.HOL.src.n_bit.words Require Import fcp_defs.
From Galette.HOL.src.n_bit.words Require lemmas.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.marker Require Import marker.
From Galette.HOL.src.monad.more_monads Require Import state_transformer.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.HOL.examples.l3_machine_code.arm8.model Require Import arm8.
From Galette.HOL.examples.l3_machine_code.arm8.step Require Import arm8_step.
From Galette.cakeml.compiler.encoders.arm8 Require Import arm8_target.
Open Scope N_scope.

(** ** Bit lemmas and a bit-blasting tactic (Galette-only) *)

Section Bits.

Lemma fcp_index_w2w {a b : N} (w : word a) i : i < dimindex b -> fcp_index (w2w w : word b) i = fcp_index w i.
Proof. intros Hi; unfold w2w; rewrite fcp_index_n2w by exact Hi; rewrite BIT_testbit, fcp_index_testbit; reflexivity. Qed.

Lemma word_bit_alt {a : N} (w : word a) i : word_bit i w = (i <? dimindex a) && fcp_index w i.
Proof.
  unfold word_bit. pose proof (@dimindex_pos a) as H.
  destruct (N.leb_spec i (dimindex a - 1)), (N.ltb_spec i (dimindex a)); try reflexivity; lia.
Qed.

Lemma word_bit_concat {a b c : N} (v : word a) (w : word b) i :
  dimindex (a + b) = dimindex a + dimindex b -> i < dimindex c -> i < dimindex a + dimindex b ->
  word_bit i (word_concat v w : word c) =
  if i <? dimindex b then word_bit i w else word_bit (i - dimindex b) v.
Proof.
  intros Hd Hc Hab. rewrite !word_bit_alt.
  unfold word_concat, word_join; cbv zeta.
  rewrite fcp_index_w2w by exact Hc. rewrite fcp_index_word_or by lia.
  rewrite fcp_index_word_lsl by lia. rewrite !fcp_index_w2w by lia.
  destruct (N.ltb_spec i (dimindex c)); [|lia]. cbn [andb].
  destruct (N.ltb_spec i (dimindex b)) as [Hb|Hb].
  - destruct (N.leb_spec (dimindex b) i); [lia|]. cbn [andb orb].
    destruct (N.ltb_spec i (dimindex b)); [reflexivity|lia].
  - destruct (N.leb_spec (dimindex b) i); [|lia]. cbn [andb].
    rewrite (fcp_index_high w i) by lia. rewrite Bool.orb_false_r.
    destruct (N.ltb_spec (i - dimindex b) (dimindex a)); [reflexivity|lia].
Qed.

(** Bit-level characterisations of the word operations. *)

Lemma wb_high {a : N} (w : word a) i : dimindex a <= i -> word_bit i w = false.
Proof. intros H; rewrite word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [lia|reflexivity]. Qed.

Lemma wb_fcp {a : N} (w : word a) i : i < dimindex a -> fcp_index w i = word_bit i w.
Proof. intros H; rewrite word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia]. Qed.

Lemma wb_and {a : N} (v w : word a) i : word_bit i (word_and v w) = word_bit i v && word_bit i w.
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_word_and by assumption; reflexivity.
Qed.

Lemma wb_or {a : N} (v w : word a) i : word_bit i (word_or v w) = word_bit i v || word_bit i w.
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_word_or by assumption; reflexivity.
Qed.

Lemma wb_xor {a : N} (v w : word a) i : word_bit i (word_xor v w) = xorb (word_bit i v) (word_bit i w).
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_word_xor by assumption; cbn [andb].
  destruct (fcp_index v i), (fcp_index w i); reflexivity.
Qed.

Lemma wb_not {a : N} (w : word a) i : word_bit i (word_1comp w) = (i <? dimindex a) && negb (word_bit i w).
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_word_1comp by assumption; reflexivity.
Qed.

Lemma wb_lsl {a : N} (w : word a) n i :
  word_bit i (word_lsl w n) = (i <? dimindex a) && (n <=? i) && word_bit (i - n) w.
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_word_lsl by assumption; cbn [andb].
  destruct (N.leb_spec n i); [|reflexivity]; cbn [andb].
  destruct (N.ltb_spec (i - n) (dimindex a)); [reflexivity|lia].
Qed.

Lemma wb_lsr {a : N} (w : word a) n i :
  word_bit i (word_lsr w n) = (i <? dimindex a) && word_bit (i + n) w.
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_word_lsr by assumption; reflexivity.
Qed.

Lemma wb_asr {a : N} (w : word a) n i :
  word_bit i (word_asr w n) =
  (i <? dimindex a) &&
  (if i + n <? dimindex a then word_bit (i + n) w else word_bit (dimindex a - 1) w).
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite word_asr_def, fcp_index_FCP by assumption; cbn [andb].
  pose proof (@dimindex_pos a).
  destruct (N.leb_spec (dimindex a) (i + n)), (N.ltb_spec (i + n) (dimindex a)); try lia.
  - rewrite fcp_defs.word_msb_def.
    destruct (N.ltb_spec (dimindex a - 1) (dimindex a)); [reflexivity|lia].
  - reflexivity.
Qed.

Lemma wb_w2w {a b : N} (w : word a) i :
  word_bit i (w2w w : word b) = (i <? dimindex b) && word_bit i w.
Proof.
  rewrite !word_bit_alt; destruct (N.ltb_spec i (dimindex b)); [|reflexivity].
  rewrite fcp_index_w2w by assumption; cbn [andb].
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|].
  apply fcp_index_high; lia.
Qed.

Lemma wb_extract {a b : N} (w : word a) h l i :
  word_bit i (word_extract h l w : word b) = (i <? dimindex b) && (i + l <=? h) && word_bit (i + l) w.
Proof.
  unfold word_extract. rewrite wb_w2w.
  destruct (N.ltb_spec i (dimindex b)); [|reflexivity]; cbn [andb].
  rewrite !word_bit_alt. destruct (N.ltb_spec i (dimindex a)) as [Ha|Ha]; cbn [andb].
  - rewrite fcp_index_word_bits by assumption. rewrite MIN_min.
    destruct (N.leb_spec (i + l) h), (N.ltb_spec (i + l) (dimindex a)), (N.leb_spec (i + l) (N.min h (dimindex a - 1))); cbn [andb]; try lia; try reflexivity.
  - destruct (N.leb_spec (i + l) h), (N.ltb_spec (i + l) (dimindex a)); try lia; reflexivity.
Qed.

Lemma wb_concat {a b c : N} (v : word a) (w : word b) i :
  dimindex (a + b) = dimindex a + dimindex b ->
  word_bit i (word_concat v w : word c) =
  (i <? dimindex c) && (if i <? dimindex b then word_bit i w else word_bit (i - dimindex b) v).
Proof.
  intros Hd. destruct (N.ltb_spec i (dimindex c)) as [Hc|Hc]; cbn [andb]; [|apply wb_high; lia].
  destruct (N.ltb_spec i (dimindex a + dimindex b)).
  - rewrite word_bit_concat by assumption; reflexivity.
  - unfold word_concat at 1. rewrite wb_w2w, (wb_high (word_join v w)) by lia.
    destruct (N.ltb_spec i (dimindex b)); [lia|]. rewrite Bool.andb_false_r. symmetry; apply wb_high; lia.
Qed.

Lemma testbit_ones k i : N.testbit (2 ^ k - 1) i = (i <? k).
Proof.
  rewrite N.sub_1_r, <- N.ones_equiv. destruct (N.ltb_spec i k).
  - apply N.ones_spec_low; lia.
  - apply N.ones_spec_high; lia.
Qed.

Lemma wb_sw2sw {a b : N} (w : word a) i :
  dimindex a <= dimindex b ->
  word_bit i (sw2sw w : word b) =
  (i <? dimindex b) && (if i <? dimindex a then word_bit i w else word_bit (dimindex a - 1) w).
Proof.
  intros Hab. pose proof (@dimindex_pos a) as Ha.
  rewrite word_bit_alt. destruct (N.ltb_spec i (dimindex b)) as [Hb|Hb]; [|reflexivity]. cbn [andb].
  unfold sw2sw. rewrite fcp_index_n2w, BIT_testbit by exact Hb.
  unfold SIGN_EXTEND; cbv zeta.
  pose proof (w2n_lt w) as Hw; rewrite dimword_pow in Hw.
  rewrite (N.mod_small (w2n w)) by exact Hw.
  replace (BIT (dimindex a - 1) (w2n w)) with (word_bit (dimindex a - 1) w)
    by (rewrite <- wb_fcp, fcp_index_testbit, BIT_testbit by lia; reflexivity).
  destruct (word_bit (dimindex a - 1) w) eqn:Hm.
  - replace (2 ** dimindex b - 2 ** dimindex a + w2n w) with
      (w2n w + (2 ^ (dimindex b - dimindex a) - 1) * 2 ^ dimindex a).
    2:{ rewrite N.mul_sub_distr_r, <- N.pow_add_r, N.mul_1_l.
        replace (dimindex b - dimindex a + dimindex a) with (dimindex b) by lia.
        assert (2 ^ dimindex a <= 2 ^ dimindex b) by (apply N.pow_le_mono_r; lia).
        unfold "**"; lia. }
    rewrite testbit_add_mul_pow by exact Hw.
    destruct (N.ltb_spec i (dimindex a)).
    + rewrite <- fcp_index_testbit, wb_fcp by lia; reflexivity.
    + rewrite testbit_ones. destruct (N.ltb_spec (i - dimindex a) (dimindex b - dimindex a)); [reflexivity|lia].
  - destruct (N.ltb_spec i (dimindex a)).
    + rewrite <- fcp_index_testbit, wb_fcp by lia; reflexivity.
    + apply testbit_lt_pow with (dimindex a); [exact Hw|lia].
Qed.

Lemma wb_v2w {n : N} (l : list bool) i :
  word_bit i (v2w l : word n) = (i <? dimindex n) && testbit i l.
Proof.
  rewrite word_bit_alt. destruct (N.ltb_spec i (dimindex n)); [|reflexivity].
  unfold v2w; rewrite fcp_index_FCP by assumption; reflexivity.
Qed.

Lemma testbit_nil i : testbit i [] = false.
Proof. unfold testbit; cbn [LENGTH]. destruct (N.ltb_spec i 0); [lia|reflexivity]. Qed.

Lemma testbit_cons i b l : testbit i (b :: l) = if i =? LENGTH l then b else testbit i l.
Proof.
  unfold testbit; cbn [LENGTH].
  destruct (N.eqb_spec i (LENGTH l)) as [->|Hne].
  - destruct (N.ltb_spec (LENGTH l) (SUC (LENGTH l))); [|lia]. cbn [andb].
    replace (SUC (LENGTH l) - 1 - LENGTH l) with 0 by lia. reflexivity.
  - destruct (N.ltb_spec i (SUC (LENGTH l))), (N.ltb_spec i (LENGTH l)); try lia; cbn [andb]; try reflexivity.
    replace (N.succ (LENGTH l) - 1 - i) with (SUC (LENGTH l - 1 - i)) by lia.
    unfold EL. rewrite num_rec_SUC. reflexivity.
Qed.

Lemma wb_n2w_lit {a : N} c i : word_bit i (n2w c : word a) = (i <? dimindex a) && N.testbit c i.
Proof.
  rewrite word_bit_alt. destruct (N.ltb_spec i (dimindex a)); [|reflexivity].
  rewrite fcp_index_n2w, BIT_testbit by assumption; reflexivity.
Qed.

Lemma wb_ror {a : N} (w : word a) k i :
  word_bit i (word_ror w k) = (i <? dimindex a) && word_bit ((i + k) mod dimindex a) w.
Proof.
  rewrite !word_bit_alt. destruct (N.ltb_spec i (dimindex a)); [|reflexivity]. cbn [andb].
  rewrite word_ror_def, fcp_index_FCP by assumption.
  pose proof (@dimindex_pos a). destruct (N.ltb_spec ((i + k) mod dimindex a) (dimindex a)); [reflexivity|].
  pose proof (N.mod_lt (i + k) (dimindex a)). lia.
Qed.

Lemma wb_bfi {a b : N} h l (x : word b) (w : word a) i :
  word_bit i (bit_field_insert h l x w) =
  (i <? dimindex a) && (if (l <=? i) && (i <=? h) then word_bit (i - l) x else word_bit i w).
Proof.
  rewrite word_bit_alt. destruct (N.ltb_spec i (dimindex a)); [|reflexivity]. cbn [andb].
  unfold bit_field_insert, word_modify. rewrite fcp_index_FCP by assumption.
  destruct ((l <=? i) && (i <=? h)); [|apply wb_fcp; assumption].
  rewrite word_bit_alt. destruct (N.ltb_spec (i - l) (dimindex b)); [reflexivity|].
  apply fcp_index_high. lia.
Qed.

End Bits.

(** *** A bit-blasting tactic for concrete bit indices (Galette-only)

    [wbs] rewrites [word_bit i (op ...)] for a numeral [i] into
    [word_bit]s of the operands, evaluates the closed index arithmetic and
    comparisons that this produces, and simplifies the boolean
    connectives. *)

Ltac is_pos p := match p with 1%positive => idtac | xO ?q => is_pos q | xI ?q => is_pos q end.
Ltac is_lit n := match n with 0%N => idtac | N.pos ?p => is_pos p end.
Ltac closedN e :=
  match e with
  | 0%N => idtac
  | N.pos ?p => is_pos p
  | ?x + ?y => closedN x; closedN y
  | ?x - ?y => closedN x; closedN y
  | ?x * ?y => closedN x; closedN y
  | N.add ?x ?y => closedN x; closedN y
  | N.sub ?x ?y => closedN x; closedN y
  | N.mul ?x ?y => closedN x; closedN y
  | N.pow ?x ?y => closedN x; closedN y
  | N.succ ?x => closedN x
  | N.max ?x ?y => closedN x; closedN y
  | N.min ?x ?y => closedN x; closedN y
  | N.modulo ?x ?y => closedN x; closedN y
  | N.div ?x ?y => closedN x; closedN y
  | dimindex ?x => closedN x
  | dimword ?x => closedN x
  end.
Ltac closedB e :=
  match e with
  | true => idtac | false => idtac
  | N.ltb ?x ?y => closedN x; closedN y
  | N.leb ?x ?y => closedN x; closedN y
  | N.eqb ?x ?y => closedN x; closedN y
  | N.testbit ?x ?y => closedN x; closedN y
  end.
Ltac list_len l :=
  lazymatch l with
  | nil => constr:(0%N)
  | _ :: ?t => let n := list_len t in constr:(N.succ n)
  end.

Ltac wb1 :=
  match goal with
  | |- context [N.ltb ?x ?y] => closedB (N.ltb x y); let v := eval vm_compute in (N.ltb x y) in change (N.ltb x y) with v
  | |- context [N.leb ?x ?y] => closedB (N.leb x y); let v := eval vm_compute in (N.leb x y) in change (N.leb x y) with v
  | |- context [N.eqb ?x ?y] => closedB (N.eqb x y); let v := eval vm_compute in (N.eqb x y) in change (N.eqb x y) with v
  | |- context [N.testbit ?x ?y] => closedB (N.testbit x y); let v := eval vm_compute in (N.testbit x y) in change (N.testbit x y) with v
  | |- context [LENGTH ?l] => let n := list_len l in let v := eval vm_compute in n in change (LENGTH l) with v
  | |- context [word_bit ?i _] => tryif is_lit i then fail else idtac; closedN i; let v := eval vm_compute in i in change i with v
  | |- context [@n2w ?a ?c] => tryif is_lit c then fail else idtac; closedN c; let v := eval vm_compute in c in change c with v
  | |- context [word_bit ?i (word_and ?v ?w)] => rewrite (wb_and v w i)
  | |- context [word_bit ?i (word_or ?v ?w)] => rewrite (wb_or v w i)
  | |- context [word_bit ?i (word_xor ?v ?w)] => rewrite (wb_xor v w i)
  | |- context [word_bit ?i (word_1comp ?w)] => is_lit i; rewrite (wb_not w i)
  | |- context [word_bit ?i (word_lsl ?w ?n)] => is_lit i; closedN n; rewrite (wb_lsl w n i)
  | |- context [word_bit ?i (word_lsr ?w ?n)] => is_lit i; closedN n; rewrite (wb_lsr w n i)
  | |- context [word_bit ?i (word_asr ?w ?n)] => is_lit i; closedN n; rewrite (wb_asr w n i)
  | |- context [word_bit ?i (@w2w ?a ?b ?w)] => is_lit i; rewrite (@wb_w2w a b w i)
  | |- context [word_bit ?i (@word_extract ?a ?b ?h ?l ?w)] => is_lit i; closedN h; closedN l; rewrite (@wb_extract a b w h l i)
  | |- context [word_bit ?i (@word_concat ?a ?b ?c ?v ?w)] => is_lit i; rewrite (@wb_concat a b c v w i) by (vm_compute; reflexivity)
  | |- context [word_bit ?i (@sw2sw ?a ?b ?w)] => is_lit i; rewrite (@wb_sw2sw a b w i) by (vm_compute; discriminate)
  | |- context [word_bit ?i (@v2w ?n ?l)] => is_lit i; rewrite (@wb_v2w n l i)
  | |- context [testbit ?i (?b :: ?l)] => is_lit i; rewrite (testbit_cons i b l)
  | |- context [testbit ?i []] => rewrite (testbit_nil i)
  | |- context [word_bit ?i (@n2w ?a ?c)] => is_lit i; closedN c; rewrite (@wb_n2w_lit a c i)
  | |- context [word_bit ?i (@word_ror ?a ?w ?k)] => is_lit i; closedN k; rewrite (@wb_ror a w k i)
  | |- context [word_bit ?i (@bit_field_insert ?a ?b ?h ?l ?x ?w)] => is_lit i; closedN h; closedN l;
      rewrite (@wb_bfi a b h l x w i)
  | |- context [@word_bit ?a ?i ?w] => is_lit i; closedN a;
      let c := eval vm_compute in (dimindex a <=? i) in
      lazymatch c with true => rewrite (@wb_high a w i) by (apply N.leb_le; reflexivity) end
  | |- context [word_bit ?i (@word_add ?a ?v ?w)] => fail
  end; cbn [andb orb negb xorb].

Ltac wbs := repeat wb1; rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.xorb_false_r, ?Bool.xorb_false_l.

Lemma lt_succ_cases i m : i < N.succ m -> i = m \/ i < m.
Proof. lia. Qed.

(** [idx_cases H tac]: [H : i < n] with [n] a numeral; runs [tac] on each
    goal [i := k] for the numerals [k < n]. *)
Ltac idx_cases H tac :=
  lazymatch type of H with
  | ?i < 0 => exfalso; apply (N.nlt_0_r i H)
  | ?i < ?n =>
      let m := eval vm_compute in (n - 1) in
      let H' := fresh in
      destruct (lt_succ_cases i m H) as [->|H']; [clear H; tac|clear H; idx_cases H' tac]
  end.

(** [wblast]: a word equation by bit extensionality and case analysis on
    the (concrete) bit index. *)
Ltac wblast :=
  apply word_bit_ext; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  rewrite !wb_fcp by exact Hi;
  let d := lazymatch type of Hi with _ < ?d => d end in
  let v := eval vm_compute in d in change d with v in Hi;
  idx_cases Hi ltac:(wbs; try reflexivity).


(** ** A decoding tactic (Galette-only) *)

Lemma wext_full {n : N} (x : word n) h : h + 1 = dimindex n -> (word_extract h 0 x : word n) = x.
Proof. intros H. apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi. rewrite wb_extract.
  destruct (N.ltb_spec i (dimindex n)); [|lia]. destruct (N.leb_spec (i + 0) h); [|lia]. rewrite N.add_0_r. reflexivity. Qed.

Lemma if_f {A} (c : bool) (x y z : A) : c = false -> y = z -> (if c then x else y) = z.
Proof. intros ->; auto. Qed.
Lemma if_t {A} (c : bool) (x y z : A) : c = true -> x = z -> (if c then x else y) = z.
Proof. intros ->; auto. Qed.

Ltac closed t := tryif (match t with context [?v] => is_var v end) then fail else idtac.

Ltac bfalse := cbn [andb negb orb]; rewrite ?Bool.andb_false_r; cbn [andb negb orb]; reflexivity.
Ltac btrue := cbn [andb negb orb]; reflexivity.

Ltac dec_top :=
  lazymatch goal with
  | |- (if ?c then _ else _) = _ =>
      first [ apply if_f; [bfalse|] | apply if_t; [btrue|]
            | closed c; let v := eval vm_compute in c in
              lazymatch v with true => apply if_t; [vm_compute; reflexivity|]
                          | false => apply if_f; [vm_compute; reflexivity|] end ]
  end.

Ltac dec_if :=
  match goal with
  | |- context [if ?c then _ else _] =>
      let H := fresh in
      first [ assert (H : c = false) by bfalse
            | assert (H : c = true) by btrue
            | assert (H : c = false) by (wbs; bfalse)
            | assert (H : c = true) by (wbs; btrue)
            | closed c; let v := eval vm_compute in c in
              lazymatch v with true => assert (H : c = true) by (vm_compute; reflexivity)
                          | false => assert (H : c = false) by (vm_compute; reflexivity) end ];
      rewrite H; clear H; cbv beta iota zeta
  end.

Ltac dec_closed :=
  match goal with
  | |- context [bool_decide ?P] => closed P;
      let v := eval vm_compute in (bool_decide P) in
      lazymatch v with true => change (bool_decide P) with true | false => change (bool_decide P) with false end
  | |- context [DecodeShift ?x] => closed x;
      let v := eval vm_compute in (DecodeShift x) in change (DecodeShift x) with v
  | |- context [DecodeLogicalOp ?x] => closed x;
      let v := eval vm_compute in (DecodeLogicalOp x) in change (DecodeLogicalOp x) with v
  end; cbv beta iota zeta.

Ltac last_bit l h := lazymatch l with nil => h | [word_bit ?k _] => k | _ :: ?t => last_bit t h end.

Ltac dec_v2w :=
  match goal with
  | |- context [@v2w ?n (word_bit ?h ?x :: ?l)] =>
      let lo := last_bit l h in
      replace (@v2w n (word_bit h x :: l)) with (word_extract h lo x : word n) by wblast;
      try rewrite (wext_full x h) by reflexivity
  end.

Ltac gclosed :=
  repeat (match goal with
  | |- context [@w2n ?a ?x] => closed x;
      let v := eval vm_compute in (@w2n a x) in is_lit v; change (@w2n a x) with v
  | |- context [@word_bit ?a ?k (v2w ?l)] => closed l; closed k;
      let v := eval vm_compute in (@word_bit a k (v2w l)) in change (@word_bit a k (v2w l)) with v
  end; cbv beta iota).

Ltac boolify_tac :=
  unfold boolify32;
  repeat match goal with |- context [word_bit ?k ?w] => is_lit k;
          lazymatch w with word_concat _ _ => idtac end;
          let H := fresh in eassert (H : word_bit k w = _) by (wbs; reflexivity); rewrite H; clear H end;
  reflexivity.

Ltac decode_tac :=
  match goal with |- Decode ?w = _ =>
    let Ht := fresh "Ht" in
    eassert (Ht : boolify32 w = _); [ boolify_tac | unfold Decode; rewrite Ht; clear Ht; cbv beta iota zeta ] end;
  repeat dec_top; repeat dec_if; repeat dec_closed; repeat dec_v2w;
  try (progress unfold LoadStoreImmediate, LoadStoreImmediateN; cbv beta iota zeta;
       gclosed; repeat dec_if; repeat dec_closed; gclosed).

Lemma nbd_v2w1 b : negb (bool_decide ((v2w [b] : word1) = n2w 0)) = b.
Proof. destruct b; vm_compute; reflexivity. Qed.
Lemma bd_v2w1 b : bool_decide ((v2w [b] : word1) = n2w 1) = b.
Proof. destruct b; vm_compute; reflexivity. Qed.

Ltac decode_fin := rewrite ?nbd_v2w1, ?bd_v2w1.

Lemma and0_bit {a : N} (x c : word a) k : word_and x c = n2w 0 -> word_bit k c = true -> word_bit k x = false.
Proof.
  intros H Hc. pose proof (f_equal (word_bit k) H) as E. rewrite wb_and, Hc, Bool.andb_true_r in E.
  rewrite E, wb_n2w_lit, N.bits_0. apply Bool.andb_false_r.
Qed.

Ltac and0_tac E :=
  match goal with |- context [word_bit ?k ?x] =>
    is_lit k; rewrite (and0_bit x _ k E) by (wbs; reflexivity) end.

Ltac wblast_and E :=
  apply word_bit_ext; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  rewrite !wb_fcp by exact Hi;
  let d := lazymatch type of Hi with _ < ?d => d end in
  let v := eval vm_compute in d in change d with v in Hi;
  idx_cases Hi ltac:(wbs; try reflexivity; repeat and0_tac E; wbs; reflexivity).

Ltac hclosed H :=
  repeat (match type of H with
  | context [bool_decide ?P] => closed P;
      let v := eval vm_compute in (bool_decide P) in
      lazymatch v with true => change (bool_decide P) with true in H | false => change (bool_decide P) with false in H end
  | context [@w2n ?a ?x] => closed x;
      let v := eval vm_compute in (@w2n a x) in is_lit v; change (@w2n a x) with v in H
  | context [@e_sf ?a ?x] => closed x;
      let v := eval vm_compute in (w2n (@e_sf a x)) in change (@e_sf a x) with (@n2w 1 v) in H
  | context [@w2w ?a ?b (n2w ?c)] => is_lit c;
      let v := eval vm_compute in (@w2n b (@w2w a b (n2w c))) in change (@w2w a b (n2w c)) with (@n2w b v) in H
  end; cbv beta iota in H).

Ltac enc_cases H :=
  cbv beta iota zeta in H; hclosed H;
  repeat match type of H with
  | (if ?c then _ else _) = ARM8 _ =>
      let E := fresh "E" in destruct c eqn:E; [|try discriminate H]
  | (match ?x with Some _ => _ | None => _ end) = ARM8 _ =>
      let E := fresh "E" in destruct x eqn:E; [|try discriminate H]
  end;
  repeat match goal with
  | E : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in E as [? ?]
  | E : bool_decide _ = true |- _ => apply bool_decide_spec in E
  | E : bool_decide _ = false |- _ => apply Bool.not_true_iff_false in E; rewrite bool_decide_spec in E
  end;
  injection H as <-.

Ltac v2w_closed :=
  repeat match goal with |- context [@v2w ?n ?l] => closed l;
    let v := eval vm_compute in (w2n (@v2w n l)) in
    replace (@v2w n l) with (@n2w n v) by (apply word_eq_w2n; vm_compute; reflexivity) end.

Lemma lsl_0 {a : N} (w : word a) : word_lsl w 0 = w.
Proof.
  apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi. rewrite wb_lsl, N.sub_0_r.
  destruct (N.ltb_spec i (dimindex a)); [|lia]. destruct (N.leb_spec 0 i); [|lia]. reflexivity.
Qed.

Definition lsargs {A : Type} (sz : A) (rs : bool) (memop : MemOp) (u : bool) (a : word64) (n t : word5) :=
  (sz, (rs, (memop, (AccType_NORMAL, (false, (false, (false, (false, (false, (u, (a, (n, t)))))))))))).


(** ** Decoding encoded instructions (Galette-only) *)

Lemma Decode_EncodeBitMask64 (w : word64) n s r :
  EncodeBitMask w = Some (n, (s, r)) -> exists v, DecodeBitMasks (Mw:=64) (n, (s, (r, true))) = Some (w, v).
Proof.
  unfold EncodeBitMask. destruct (EncodeBitMaskAux w) as [e [S' R]].
  set (p := if bool_decide (e = 64) then _ else _). destruct p as [immN [imms immr]].
  destruct (DecodeBitMasks _) as [[imm2 v2]|] eqn:E; [|discriminate].
  destruct (bool_decide (w = imm2)) eqn:Ew; [|discriminate]. apply bool_decide_spec in Ew; subst.
  intros H; injection H as <- <- <-. exists v2; exact E.
Qed.


Lemma imm12_lo (imm : word64) : word_and imm (word_1comp (n2w 4095)) = n2w 0 -> (w2w (word_extract 11 0 imm : word12) : word64) = imm.
Proof. intros E. wblast_and E. Qed.
Lemma imm12_hi (imm : word64) : word_and imm (word_1comp (n2w 16773120)) = n2w 0 -> word_lsl (w2w (word_extract 23 12 imm : word12) : word64) 12 = imm.
Proof. intros E. wblast_and E. Qed.

Lemma dec_NOP w : Encode (Hint SystemHintOp_NOP) = ARM8 w -> Decode w = Hint SystemHintOp_NOP.
Proof. intros H; injection H as <-. vm_compute. reflexivity. Qed.

Lemma dec_Address imm d w : Encode (Address (false, (imm, d))) = ARM8 w -> Decode w = Address (false, (imm, d)).
Proof. intros H; cbn [Encode] in H; enc_cases H. decode_tac. congruence. Qed.

Lemma dec_MoveWide op hw imm d w : Encode (Data (MoveWide_64 (n2w 1, (op, (hw, (imm, d)))))) = ARM8 w ->
  Decode w = Data (MoveWide_64 (n2w 1, (op, (hw, (imm, d))))).
Proof. intros H; injection H as <-. destruct op; decode_tac; reflexivity. Qed.

Lemma dec_LogImm opc sf imm n d w : Encode (Data (LogicalImmediate_64 (n2w 1, (opc, (sf, (imm, (n, d))))))) = ARM8 w ->
  Decode w = Data (LogicalImmediate_64 (n2w 1, (opc, (sf, (imm, (n, d)))))).
Proof.
  intros H; cbn [Encode e_data] in H.
  destruct (EncodeBitMask imm) as [[N' [imms immr]]|] eqn:E; [|discriminate H].
  destruct (Decode_EncodeBitMask64 _ _ _ _ E) as [v Hv].
  destruct opc, sf; cbn [EncodeLogicalOp] in H; try discriminate H; injection H as <-;
    decode_tac; rewrite Hv; reflexivity.
Qed.

Lemma dec_AddSubShifted sub sf m n d w :
  Encode (Data (AddSubShiftedRegister_64 (n2w 1, (sub, (sf, (ShiftType_LSL, (m, (n2w 0, (n, d))))))))) = ARM8 w ->
  Decode w = Data (AddSubShiftedRegister_64 (n2w 1, (sub, (sf, (ShiftType_LSL, (m, (n2w 0, (n, d)))))))).
Proof. intros H; injection H as <-. decode_tac; decode_fin; reflexivity. Qed.

Lemma dec_LogShift opc inv sf m n d w :
  Encode (Data (LogicalShiftedRegister_64 (n2w 1, (opc, (inv, (sf, (ShiftType_LSL, (0, (m, (n, d)))))))))) = ARM8 w ->
  Decode w = Data (LogicalShiftedRegister_64 (n2w 1, (opc, (inv, (sf, (ShiftType_LSL, (0, (m, (n, d))))))))).
Proof.
  intros H; cbn [Encode e_data] in H.
  destruct opc, sf; cbn [EncodeLogicalOp] in H; try discriminate H; injection H as <-;
    decode_tac; decode_fin; reflexivity.
Qed.

Lemma dec_AddSubImm sub sf imm n d w :
  Encode (Data (AddSubImmediate_64 (n2w 1, (sub, (sf, (imm, (n, d))))))) = ARM8 w ->
  Decode w = Data (AddSubImmediate_64 (n2w 1, (sub, (sf, (imm, (n, d)))))).
Proof.
  intros H; cbn [Encode e_data] in H.
  destruct (bool_decide (word_and imm _ = _)) eqn:E1 in H.
  - apply bool_decide_spec in E1. injection H as <-. decode_tac; decode_fin. rewrite imm12_lo by exact E1. reflexivity.
  - destruct (bool_decide (word_and imm _ = _)) eqn:E2 in H; [|discriminate H].
    apply bool_decide_spec in E2. injection H as <-. decode_tac; decode_fin. rewrite imm12_hi by exact E2. reflexivity.
Qed.

Lemma dec_Bfm ext wmask tmask R S n d w :
  Encode (Data (BitfieldMove_64 (n2w 1, (true, (ext, (wmask, (tmask, (R, (S, (n, d)))))))))) = ARM8 w ->
  Decode w = Data (BitfieldMove_64 (n2w 1, (true, (ext, (wmask, (tmask, (R, (S, (n, d))))))))).
Proof.
  intros H; cbn [Encode e_data] in H. destruct ext; enc_cases H.
  all: decode_tac; v2w_closed.
  all: match goal with H : DecodeBitMasks _ = _ |- _ => rewrite H end; congruence.
Qed.

Lemma dec_Extr imms m n d w :
  Encode (Data (ExtractRegister_64 (n2w 1, (imms, (m, (n, d)))))) = ARM8 w ->
  Decode w = Data (ExtractRegister_64 (n2w 1, (imms, (m, (n, d))))).
Proof. intros H; injection H as <-. decode_tac. reflexivity. Qed.

Lemma dec_ShiftReg sh m n d w :
  Encode (Data (Shift_64 (n2w 1, (sh, (m, (n, d)))))) = ARM8 w ->
  Decode w = Data (Shift_64 (n2w 1, (sh, (m, (n, d))))).
Proof. intros H; injection H as <-. destruct sh; decode_tac; reflexivity. Qed.

Lemma dec_Div m n d w :
  Encode (Data (Division_64 (n2w 1, (false, (m, (n, d)))))) = ARM8 w ->
  Decode w = Data (Division_64 (n2w 1, (false, (m, (n, d))))).
Proof. intros H; injection H as <-. decode_tac. reflexivity. Qed.

Lemma dec_MulHigh m n d w :
  Encode (Data (MultiplyHigh (false, (m, (n, d))))) = ARM8 w ->
  Decode w = Data (MultiplyHigh (false, (m, (n, d)))).
Proof. intros H; injection H as <-. decode_tac. reflexivity. Qed.

Lemma dec_MulAdd m a n d w :
  Encode (Data (MultiplyAddSub_64 (n2w 1, (false, (m, (a, (n, d))))))) = ARM8 w ->
  Decode w = Data (MultiplyAddSub_64 (n2w 1, (false, (m, (a, (n, d)))))).
Proof. intros H; injection H as <-. decode_tac. reflexivity. Qed.

Lemma dec_CCmpImm sub imm cond fn fz fc fv n w :
  Encode (Data (ConditionalCompareImmediate_64 (n2w 1, (sub, (imm, (cond, ((fn, (fz, (fc, fv))), n))))))) = ARM8 w ->
  Decode w = Data (ConditionalCompareImmediate_64 (n2w 1, (sub, (imm, (cond, ((fn, (fz, (fc, fv))), n)))))).
Proof.
  intros H; cbn [Encode e_data] in H; enc_cases H. decode_tac; decode_fin.
  replace (word_extract 4 0 imm : word5) with (w2w imm : word5) by wblast. congruence.
Qed.

Lemma dec_AddSubCarry sub sf m n d w :
  Encode (Data (AddSubCarry_64 (n2w 1, (sub, (sf, (m, (n, d))))))) = ARM8 w ->
  Decode w = Data (AddSubCarry_64 (n2w 1, (sub, (sf, (m, (n, d)))))).
Proof. intros H; injection H as <-. decode_tac; decode_fin. reflexivity. Qed.

Lemma dec_CSel inv inc cond m n d w :
  Encode (Data (ConditionalSelect_64 (n2w 1, (inv, (inc, (cond, (m, (n, d)))))))) = ARM8 w ->
  Decode w = Data (ConditionalSelect_64 (n2w 1, (inv, (inc, (cond, (m, (n, d))))))).
Proof. intros H; injection H as <-. decode_tac; decode_fin. reflexivity. Qed.

Lemma dec_BImm a bt w : bt = BranchType_JMP \/ bt = BranchType_CALL ->
  Encode (Branch (BranchImmediate (a, bt))) = ARM8 w -> Decode w = Branch (BranchImmediate (a, bt)).
Proof. intros Hb H; cbn [Encode e_branch] in H; destruct Hb as [->| ->]; enc_cases H; decode_tac.
  all: congruence. Qed.

Lemma dec_BCond a cond w :
  Encode (Branch (BranchConditional (a, cond))) = ARM8 w -> Decode w = Branch (BranchConditional (a, cond)).
Proof. intros H; cbn [Encode e_branch] in H; enc_cases H; decode_tac.
  all: congruence. Qed.

Lemma dec_BReg n w :
  Encode (Branch (BranchRegister (n, BranchType_JMP))) = ARM8 w -> Decode w = Branch (BranchRegister (n, BranchType_JMP)).
Proof. intros H; cbn [Encode e_branch] in H; enc_cases H; decode_tac.
  all: congruence. Qed.


Lemma ext_lsr3 (a : word64) : (word_extract 11 0 (word_lsr a 3) : word12) = word_extract 14 3 a.
Proof. wblast. Qed.
Lemma ext_lsr2 (a : word64) : (word_extract 11 0 (word_lsr a 2) : word12) = word_extract 13 2 a.
Proof. wblast. Qed.
Lemma ext_lsr1 (a : word64) : (word_extract 11 0 (word_lsr a 1) : word12) = word_extract 12 1 a.
Proof. wblast. Qed.
Lemma ext_lsr0 (a : word64) : (word_extract 11 0 (word_lsr a 0) : word12) = word_extract 11 0 a.
Proof. wblast. Qed.

Ltac ls_fin :=
  cbn [negb]; rewrite ?ext_lsr3, ?ext_lsr2, ?ext_lsr1, ?ext_lsr0 in *; rewrite ?lsl_0 in *;
  match goal with E : @eq (word _) ?x ?r |- context [?r] => is_var x; rewrite <- E end; reflexivity.

Lemma dec_LS64 memop u a n t w :
  memop <> MemOp_PREFETCH ->
  Encode (LoadStore (LoadStoreImmediate_64 (lsargs (n2w 3) false memop u a n t))) = ARM8 w ->
  exists u', Decode w = LoadStore (LoadStoreImmediate_64 (lsargs (n2w 3) false memop u' a n t)).
Proof.
  intros Hm H; unfold lsargs in *; cbn [Encode e_load_store e_LoadStoreImmediate] in H.
  destruct memop; [|clear Hm|congruence]; enc_cases H; eexists; decode_tac; ls_fin.
Qed.

Lemma dec_LS32 rs memop u a n t w :
  memop <> MemOp_PREFETCH ->
  Encode (LoadStore (LoadStoreImmediate_32 (lsargs (n2w 2) rs memop u a n t))) = ARM8 w ->
  exists u', Decode w = LoadStore (LoadStoreImmediate_32 (lsargs (n2w 2) true memop u' a n t)).
Proof.
  intros Hm H; unfold lsargs in *; cbn [Encode e_load_store e_LoadStoreImmediate] in H.
  destruct memop; [|clear Hm|congruence]; enc_cases H; eexists; decode_tac; ls_fin.
Qed.

Lemma dec_LS16 rs memop u a n t w :
  memop <> MemOp_PREFETCH ->
  Encode (LoadStore (LoadStoreImmediate_16 (lsargs (n2w 1) rs memop u a n t))) = ARM8 w ->
  exists u', Decode w = LoadStore (LoadStoreImmediate_16 (lsargs (n2w 1) true memop u' a n t)).
Proof.
  intros Hm H; unfold lsargs in *; cbn [Encode e_load_store e_LoadStoreImmediate] in H.
  destruct memop; [|clear Hm|congruence]; enc_cases H; eexists; decode_tac; ls_fin.
Qed.

Lemma dec_LS8 rs memop u a n t w :
  memop <> MemOp_PREFETCH ->
  Encode (LoadStore (LoadStoreImmediate_8 (lsargs (n2w 0) rs memop u a n t))) = ARM8 w ->
  exists u', Decode w = LoadStore (LoadStoreImmediate_8 (lsargs (n2w 0) true memop u' a n t)).
Proof.
  intros Hm H; unfold lsargs in *; cbn [Encode e_load_store e_LoadStoreImmediate] in H.
  destruct memop; [|clear Hm|congruence]; enc_cases H; eexists; decode_tac; ls_fin.
Qed.


(** ** One step of the ARMv8 model (Galette-only) *)

Record astate := mk_astate {
  aregs : word5 -> word64; apc : word64; amem : word64 -> word8; aflags : bool * (bool * (bool * bool)) }.

Definition flags_of (p : ProcState) : bool * (bool * (bool * bool)) :=
  (ProcState_N p, (ProcState_Z p, (ProcState_C p, ProcState_V p))).

Definition set_flags (f : bool * (bool * (bool * bool))) (p : ProcState) : ProcState :=
  let '(n, (z, (c, v))) := f in
  {| ProcState_C := c; ProcState_EL := ProcState_EL p; ProcState_N := n; ProcState_SPS := ProcState_SPS p;
     ProcState_V := v; ProcState_Z := z |}.

Definition obs (s : arm8_state) : astate :=
  mk_astate (arm8_state_REG s) (arm8_state_PC s) (arm8_state_MEM s) (flags_of (arm8_state_PSTATE s)).

Definition put (A : astate) (s : arm8_state) : arm8_state :=
  {| arm8_state_MEM := amem A; arm8_state_PC := arm8_state_PC s;
     arm8_state_PSTATE := set_flags (aflags A) (arm8_state_PSTATE s);
     arm8_state_REG := aregs A; arm8_state_SCTLR_EL1 := arm8_state_SCTLR_EL1 s;
     arm8_state_SCTLR_EL2 := arm8_state_SCTLR_EL2 s; arm8_state_SCTLR_EL3 := arm8_state_SCTLR_EL3 s;
     arm8_state_SP_EL0 := arm8_state_SP_EL0 s; arm8_state_SP_EL1 := arm8_state_SP_EL1 s;
     arm8_state_SP_EL2 := arm8_state_SP_EL2 s; arm8_state_SP_EL3 := arm8_state_SP_EL3 s;
     arm8_state_TCR_EL1 := arm8_state_TCR_EL1 s; arm8_state_TCR_EL2 := arm8_state_TCR_EL2 s;
     arm8_state_TCR_EL3 := arm8_state_TCR_EL3 s; arm8_state_branch_hint := arm8_state_branch_hint s;
     arm8_state_exception := arm8_state_exception s |}.

Definition rX (g : word5 -> word64) (n : word5) : word64 := if bool_decide (n = n2w 31) then n2w 0 else g n.
Definition wX (n : word5) (v : word64) (g : word5 -> word64) : word5 -> word64 :=
  if bool_decide (n = n2w 31) then g else UPDATE n v g.

Definition logop (opc : LogicalOp) (x y : word64) : word64 :=
  match opc with LogicalOp_AND => word_and x y | LogicalOp_ORR => word_or x y | LogicalOp_EOR => word_xor x y end.

(** Little-endian loads and stores of [n] bytes, recursing as
    [asmSem]'s [read_mem_word] and [write_mem_word]. *)
Definition aload (n : N) (m : word64 -> word8) : word64 -> word64 :=
  num_rec (fun _ => n2w 0)
    (fun _ r a => word_or (word_lsl (r (word_add a (n2w 1))) 8) (w2w (m a))) n.

Definition astore (n : N) : word64 -> word64 -> (word64 -> word8) -> word64 -> word8 :=
  num_rec (fun _ _ m => m)
    (fun _ r a d m => UPDATE a (w2w d) (r (word_add a (n2w 1)) (word_lsr d 8) m)) n.

Definition ls_exec (k : N) (memop : MemOp) (off : word64) (n t : word5) (A : astate) : astate :=
  let g := aregs A in let addr := word_add (rX g n) off in
  match memop with
  | MemOp_LOAD => mk_astate (wX t (aload k (amem A) addr) g) (word_add (apc A) (n2w 4)) (amem A) (aflags A)
  | MemOp_STORE => mk_astate g (word_add (apc A) (n2w 4)) (astore k addr (rX g t) (amem A)) (aflags A)
  | MemOp_PREFETCH => A
  end.

Definition aexec (i : instruction) (A : astate) : astate :=
  let g := aregs A in let pc := apc A in let m := amem A in let fl := aflags A in
  let r x := rX g x in
  let nxt g' fl' := mk_astate g' (word_add pc (n2w 4)) m fl' in
  let setfl (sf : bool) nzcv := if sf then nzcv else fl in
  match i with
  | Hint SystemHintOp_NOP => nxt g fl
  | Address (false, (imm, d)) => nxt (wX d (word_add pc imm) g) fl
  | Data (MoveWide_64 (_, (op, (hw, (imm, d))))) =>
      let pos := w2n (word_concat hw (n2w 0 : word4) : word6) in
      let s0 := bit_field_insert (pos + 15) pos imm (if bool_decide (op = MoveWideOp_K) then r d else n2w 0) in
      nxt (wX d (if bool_decide (op = MoveWideOp_N) then word_1comp s0 else s0) g) fl
  | Data (LogicalImmediate_64 (_, (opc, (sf, (imm, (n, d)))))) =>
      let res := logop opc (r n) imm in
      nxt (wX d res g) (setfl sf (word_msb res, (bool_decide (res = n2w 0), (false, false))))
  | Data (AddSubShiftedRegister_64 (_, (sub, (sf, (sh, (m', (imm6, (n, d)))))))) =>
      let v0 := ShiftValue (Nw:=64) (r m', (sh, w2n imm6)) in
      let res := AddWithCarry (Nw:=64) (r n, (if sub then word_1comp v0 else v0, sub)) in
      nxt (wX d (fst res) g) (setfl sf (snd res))
  | Data (LogicalShiftedRegister_64 (_, (opc, (inv, (sf, (sh, (amt, (m', (n, d))))))))) =>
      let v0 := ShiftValue (Nw:=64) (r m', (sh, amt)) in
      let res := logop opc (r n) (if inv then word_1comp v0 else v0) in
      nxt (wX d res g) (setfl sf (word_msb res, (bool_decide (res = n2w 0), (false, false))))
  | Data (AddSubImmediate_64 (_, (sub, (sf, (imm, (n, d)))))) =>
      let res := AddWithCarry (Nw:=64) (r n, (if sub then word_1comp imm else imm, sub)) in
      nxt (wX d (fst res) g) (setfl sf (snd res))
  | Data (BitfieldMove_64 (_, (inzero, (ext, (wmask, (tmask, (R, (S', (n, d))))))))) =>
      let v := if inzero then n2w 0 else r d in
      let v0 := r n in
      nxt (wX d (word_or (word_and (if ext then Replicate (Nw:=64) [word_bit S' v0] else v) (word_1comp tmask))
                         (word_and (word_or (word_and v (word_1comp wmask)) (word_and (word_ror v0 R) wmask)) tmask)) g) fl
  | Data (ExtractRegister_64 (_, (imms, (m', (n, d))))) =>
      nxt (wX d (v2w (shiftr (w2v (r n) ++ w2v (r m')) (w2n imms))) g) fl
  | Data (Shift_64 (_, (sh, (m', (n, d))))) =>
      nxt (wX d (ShiftValue (Nw:=64) (r n, (sh, w2n (r m') mod 64))) g) fl
  | Data (Division_64 (_, (uns, (m', (n, d))))) =>
      nxt (wX d (if bool_decide (r m' = n2w 0) then n2w 0 else if uns then word_div (r n) (r m') else word_quot (r n) (r m')) g) fl
  | Data (MultiplyHigh (sg, (m', (n, d)))) =>
      nxt (wX d (word_extract 127 64 (word_mul (ExtendWord (Mw:=64) (Nw:=128) (r n, sg)) (ExtendWord (Mw:=64) (Nw:=128) (r m', sg))) : word64) g) fl
  | Data (MultiplyAddSub_64 (_, (sub, (m', (a, (n, d)))))) =>
      nxt (wX d (if sub then word_sub (r a) (word_mul (r n) (r m')) else word_add (r a) (word_mul (r n) (r m'))) g) fl
  | Data (ConditionalCompareImmediate_64 (_, (sub, (imm, (cond, (nzcv, n)))))) =>
      nxt g (if ConditionTest (cond, fl) then snd (AddWithCarry (Nw:=64) (r n, (if sub then word_1comp imm else imm, sub))) else nzcv)
  | Data (AddSubCarry_64 (_, (sub, (sf, (m', (n, d)))))) =>
      let res := AddWithCarry (Nw:=64) (r n, (if sub then word_1comp (r m') else r m', fst (snd (snd fl)))) in
      nxt (wX d (fst res) g) (setfl sf (snd res))
  | Data (ConditionalSelect_64 (_, (inv, (inc, (cond, (m', (n, d))))))) =>
      let v := if ConditionTest (cond, fl) then r n
               else let s0 := if inv then word_1comp (r m') else r m' in if inc then word_add s0 (n2w 1) else s0 in
      nxt (wX d v g) fl
  | Branch (BranchImmediate (off, bt)) =>
      mk_astate (if bool_decide (bt = BranchType_CALL) then wX (n2w 30) (word_add pc (n2w 4)) g else g) (word_add pc off) m fl
  | Branch (BranchConditional (off, cond)) =>
      mk_astate g (if ConditionTest (cond, fl) then word_add pc off else word_add pc (n2w 4)) m fl
  | Branch (BranchRegister (n, _)) => mk_astate g (r n) m fl
  | LoadStore (LoadStoreImmediate_64 (_, (_, (memop, (_, (_, (_, (_, (_, (_, (_, (off, (n, t))))))))))))) => ls_exec 8 memop off n t A
  | LoadStore (LoadStoreImmediate_32 (_, (_, (memop, (_, (_, (_, (_, (_, (_, (_, (off, (n, t))))))))))))) => ls_exec 4 memop off n t A
  | LoadStore (LoadStoreImmediate_16 (_, (_, (memop, (_, (_, (_, (_, (_, (_, (_, (off, (n, t))))))))))))) => ls_exec 2 memop off n t A
  | LoadStore (LoadStoreImmediate_8 (_, (_, (memop, (_, (_, (_, (_, (_, (_, (_, (off, (n, t))))))))))))) => ls_exec 1 memop off n t A
  | _ => A
  end.

Lemma bdf (P : Prop) `{Decision P} : ~ P -> bool_decide P = false.
Proof. intros Hn. apply Bool.not_true_iff_false. rewrite bool_decide_spec. exact Hn. Qed.
Lemma bdt (P : Prop) `{Decision P} : P -> bool_decide P = true.
Proof. intros Hp. apply bool_decide_spec. exact Hp. Qed.

Lemma X64 n s : X (Nw:=64) n s = rX (arm8_state_REG s) n.
Proof. unfold X, rX. destruct (bool_decide _); [reflexivity|]. apply w2w_id. Qed.

Lemma wX64 v n s : write'X (Nw:=64) (v, n) s = arm8_state_REG_fupd (fun _ => wX n v (arm8_state_REG s)) s.
Proof.
  unfold write'X, wX. rewrite w2w_id. destruct (bool_decide _); [|reflexivity].
  destruct s; reflexivity.
Qed.

Definition fl_eta (s : arm8_state) := s.

Lemma SetTheFlags_put sf nzcv s :
  SetTheFlags (sf, nzcv) s = put (mk_astate (arm8_state_REG s) (arm8_state_PC s) (arm8_state_MEM s)
                                   (if sf then nzcv else flags_of (arm8_state_PSTATE s))) s.
Proof.
  destruct s as [? ? [] ? ? ? ? ? ? ? ? ? ? ? ? ?]; destruct sf, nzcv as [? [? [? ?]]]; reflexivity.
Qed.

Lemma put_REG A s g : arm8_state_REG_fupd (fun _ => g) (put A s) = put (mk_astate g (apc A) (amem A) (aflags A)) s.
Proof. reflexivity. Qed.

Lemma put_obs s : put (obs s) s = s.
Proof. destruct s as [? ? [] ? ? ? ? ? ? ? ? ? ? ? ? ?]; reflexivity. Qed.

Lemma REG_put g s : arm8_state_REG_fupd (fun _ => g) s = put (mk_astate g (arm8_state_PC s) (arm8_state_MEM s) (flags_of (arm8_state_PSTATE s))) s.
Proof. destruct s as [? ? [] ? ? ? ? ? ? ? ? ? ? ? ? ?]; reflexivity. Qed.

(** The two shapes of the effect of [Run]. *)
Definition run_shape (i : instruction) (s : arm8_state) : Prop :=
  let A' := aexec i (obs s) in
  (Run i s = put A' s /\ apc A' = word_add (arm8_state_PC s) (n2w 4)) \/
  (exists bt, Run i s = arm8_state_PC_fupd (fun _ => apc A') (arm8_state_branch_hint_fupd (fun _ => Some bt) (put A' s))).

Ltac run_pre :=
  cbn [Run dfn'Address dfn'MoveWide dfn'LogicalImmediate dfn'AddSubShiftedRegister dfn'LogicalShiftedRegister
       dfn'AddSubImmediate dfn'BitfieldMove dfn'ExtractRegister dfn'Shift dfn'Division dfn'MultiplyHigh
       dfn'MultiplyAddSub dfn'ConditionalCompareImmediate dfn'AddSubCarry dfn'ConditionalSelect
       dfn'BranchImmediate dfn'BranchConditional dfn'BranchRegister ShiftReg];
  unfold ConditionHolds; rewrite ?X64.

Section RunShape.
Variable s : arm8_state.

Lemma run_MoveWide sf op hw imm d : run_shape (Data (MoveWide_64 (sf, (op, (hw, (imm, d)))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_AddSubShifted sf sub sfl sh m n imm6 d : run_shape (Data (AddSubShiftedRegister_64 (sf, (sub, (sfl, (sh, (m, (imm6, (n, d))))))))) s.
Proof.
  left; split; [|reflexivity]. run_pre.
  destruct sub; cbv beta iota zeta;
  match goal with |- context [AddWithCarry ?x] => destruct (AddWithCarry x) as [res nzcv] eqn:E end;
  rewrite SetTheFlags_put, wX64, put_REG; cbn [aexec obs aregs apc amem aflags]; rewrite E; reflexivity.
Qed.

Lemma run_NOP : run_shape (Hint SystemHintOp_NOP) s.
Proof. left; split; [|reflexivity]. cbn [Run dfn'Hint]. try rewrite bdt by reflexivity. symmetry; apply put_obs. Qed.

Lemma run_Address imm d : run_shape (Address (false, (imm, d))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_LogImm sf opc sfl imm n d : d <> n2w 31 \/ sfl = true ->
  run_shape (Data (LogicalImmediate_64 (sf, (opc, (sfl, (imm, (n, d))))))) s.
Proof.
  intros Hd. left; split; [|reflexivity]. run_pre.
  assert (E : (bool_decide (d = n2w 31) && negb sfl)%bool = false)
    by (destruct Hd as [Hd| ->]; [rewrite (bdf _ Hd); reflexivity|destruct (bool_decide _); reflexivity]).
  rewrite E.
  rewrite SetTheFlags_put, wX64, put_REG. destruct opc; reflexivity.
Qed.

Lemma run_LogShift sf opc inv sfl sh amt m n d :
  run_shape (Data (LogicalShiftedRegister_64 (sf, (opc, (inv, (sfl, (sh, (amt, (m, (n, d)))))))))) s.
Proof.
  left; split; [|reflexivity]. run_pre. rewrite SetTheFlags_put, wX64, put_REG. destruct opc; reflexivity.
Qed.

Lemma run_AddSubImm sf sub sfl imm n d : n <> n2w 31 -> d <> n2w 31 \/ sfl = true ->
  run_shape (Data (AddSubImmediate_64 (sf, (sub, (sfl, (imm, (n, d))))))) s.
Proof.
  intros Hn Hd. left; split; [|reflexivity]. run_pre. rewrite (bdf _ Hn).
  assert (E : (bool_decide (d = n2w 31) && negb sfl)%bool = false)
    by (destruct Hd as [Hd| ->]; [rewrite (bdf _ Hd); reflexivity|destruct (bool_decide _); reflexivity]).
  destruct sub; cbv beta iota zeta;
  match goal with |- context [AddWithCarry ?x] => destruct (AddWithCarry x) as [res nzcv] eqn:E2 end;
  rewrite E, SetTheFlags_put, wX64, put_REG; cbn [aexec obs aregs apc amem aflags]; rewrite E2; reflexivity.
Qed.

Lemma run_Bfm sf inz ext wm tm R S' n d :
  run_shape (Data (BitfieldMove_64 (sf, (inz, (ext, (wm, (tm, (R, (S', (n, d)))))))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_Extr sf imms m n d : run_shape (Data (ExtractRegister_64 (sf, (imms, (m, (n, d)))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_ShiftReg sf sh m n d : run_shape (Data (Shift_64 (sf, (sh, (m, (n, d)))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_Div sf uns m n d : run_shape (Data (Division_64 (sf, (uns, (m, (n, d)))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_MulHigh sg m n d : run_shape (Data (MultiplyHigh (sg, (m, (n, d))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_MulAdd sf sub m a n d : run_shape (Data (MultiplyAddSub_64 (sf, (sub, (m, (a, (n, d))))))) s.
Proof. left; split; [|reflexivity]. run_pre. rewrite wX64, REG_put. reflexivity. Qed.

Lemma run_CCmpImm sf sub imm cond nzcv n : run_shape (Data (ConditionalCompareImmediate_64 (sf, (sub, (imm, (cond, (nzcv, n))))))) s.
Proof.
  left; split; [|reflexivity]. run_pre. cbn [aexec obs aregs apc amem aflags]; unfold flags_of.
  match goal with |- context [ConditionTest ?x] => destruct (ConditionTest x) end; [destruct sub; cbv beta iota zeta;
    match goal with |- context [AddWithCarry ?x] => destruct (AddWithCarry x) as [res fl] eqn:E2 end|];
    rewrite SetTheFlags_put; cbn [aexec obs aregs apc amem aflags]; rewrite ?E2; reflexivity.
Qed.

Lemma run_AddSubCarry sf sub sfl m n d : run_shape (Data (AddSubCarry_64 (sf, (sub, (sfl, (m, (n, d))))))) s.
Proof.
  left; split; [|reflexivity]. run_pre.
  match goal with |- context [AddWithCarry ?x] => destruct (AddWithCarry x) as [res nzcv] eqn:E2 end.
  rewrite SetTheFlags_put, wX64, put_REG; cbn [aexec obs aregs apc amem aflags]; unfold flags_of; cbn [fst snd]. rewrite E2. reflexivity.
Qed.

Lemma run_CSel sf inv inc cond m n d : run_shape (Data (ConditionalSelect_64 (sf, (inv, (inc, (cond, (m, (n, d)))))))) s.
Proof.
  left; split; [|reflexivity]. run_pre. cbn [aexec obs aregs apc amem aflags]; unfold flags_of.
  match goal with |- context [ConditionTest ?x] => destruct (ConditionTest x) end; rewrite wX64, REG_put; reflexivity.
Qed.

End RunShape.

Definition s_ok (s : arm8_state) : Prop :=
  ProcState_EL (arm8_state_PSTATE s) = n2w 0 /\ SCTLRType_E0E (arm8_state_SCTLR_EL1 s) = false /\ SCTLRType_SA0 (arm8_state_SCTLR_EL1 s) = false /\ TCR_EL1_TBI1 (arm8_state_TCR_EL1 s) = false /\ TCR_EL1_TBI0 (arm8_state_TCR_EL1 s) = false /\ arm8_state_exception s = NoException.

Lemma BranchTo_ok t bt s : s_ok s ->
  BranchTo (t, bt) s = arm8_state_PC_fupd (fun _ => t) (arm8_state_branch_hint_fupd (fun _ => Some bt) s).
Proof.
  intros (HEL & _ & _ & HT1 & HT0 & _). unfold BranchTo, Hint_Branch.
  cbn [arm8_state_branch_hint_fupd arm8_state_PSTATE arm8_state_TCR_EL1]. rewrite HEL, HT1, HT0.
  cbv beta iota zeta. rewrite bdt by reflexivity. rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma put_same A s : aregs A = arm8_state_REG s -> amem A = arm8_state_MEM s -> aflags A = flags_of (arm8_state_PSTATE s) ->
  put A s = s.
Proof. destruct A; cbn; intros -> -> ->; apply put_obs. Qed.

Lemma run_BImm off bt s : s_ok s -> run_shape (Branch (BranchImmediate (off, bt))) s.
Proof.
  intros Hok. right. exists bt. run_pre. cbn [aexec obs aregs apc amem aflags].
  destruct (bool_decide (bt = BranchType_CALL)) eqn:Eb.
  - rewrite wX64. rewrite BranchTo_ok by (destruct s; exact Hok). rewrite REG_put. reflexivity.
  - rewrite BranchTo_ok by exact Hok. rewrite (put_same _ s) by reflexivity. reflexivity.
Qed.

Lemma run_BCond off cond s : s_ok s -> run_shape (Branch (BranchConditional (off, cond))) s.
Proof.
  intros Hok. unfold run_shape; cbv zeta. run_pre. cbn [aexec obs aregs apc amem aflags]; unfold flags_of. match goal with |- context [ConditionTest ?x] => destruct (ConditionTest x) end.
  - right. exists BranchType_JMP. rewrite BranchTo_ok by exact Hok. rewrite (put_same _ s) by reflexivity. reflexivity.
  - left. rewrite (put_same _ s) by reflexivity. split; reflexivity.
Qed.

Lemma run_BReg n bt s : s_ok s -> bt <> BranchType_CALL -> run_shape (Branch (BranchRegister (n, bt))) s.
Proof.
  intros Hok Hb. right. exists bt. run_pre. rewrite (bdf _ Hb). rewrite BranchTo_ok by exact Hok.
  rewrite (put_same _ s) by reflexivity. reflexivity.
Qed.

Lemma Aligned_ok k (a : word64) : aligned k a = true -> k <= 3 -> Aligned (Nw:=64) (a, 2 ^ k) = true.
Proof.
  intros H Hk. unfold Aligned, Align. apply bdt. apply alignment.aligned_iff in H.
  apply word_eq_w2n. rewrite w2n_n2w. change (2 ** k) with (2 ^ k) in H.
  pose proof (N.div_mod (w2n a) (2 ^ k) ltac:(apply N.pow_nonzero; lia)) as E.
  rewrite H, N.add_0_r in E. rewrite <- E. symmetry. apply N.mod_small, w2n_lt.
Qed.

Lemma CheckAlignment_ok a k acc wr s : aligned k a = true -> k <= 3 -> CheckAlignment (a, (2 ^ k, (acc, wr))) s = s.
Proof. intros H Hk. unfold CheckAlignment. rewrite Aligned_ok by assumption. reflexivity. Qed.

Lemma BigEndian_ok s : s_ok s -> BigEndian s = false.
Proof. intros (HEL & HE & _). unfold BigEndian. rewrite HEL, HE. reflexivity. Qed.


(** ** Memory accesses (Galette-only) *)

(** ** Bit lists *)

Lemma LENGTH_app {A} (l1 l2 : list A) : LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2.
Proof. induction l1 as [|x l1 IH]; cbn [app LENGTH]; [lia|rewrite IH; lia]. Qed.

Lemma LENGTH_GENLIST {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, LENGTH_app, IH. cbn. lia.
Qed.

Lemma EL_GENLIST {A} `{Inhabited A} (f : N -> A) n i : i < n -> EL i (GENLIST f n) = f i.
Proof.
  induction n as [|n IH] using N.peano_ind; intros Hi; [lia|].
  pose proof (LENGTH_length (GENLIST f n)) as EL0; rewrite LENGTH_GENLIST in EL0.
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app.
  rewrite EL_nth by (rewrite LENGTH_app, LENGTH_GENLIST; cbn; lia).
  destruct (N.lt_ge_cases i n) as [Hl|Hl].
  - rewrite app_nth1 by lia.
    rewrite <- EL_nth by (rewrite LENGTH_GENLIST; exact Hl). apply IH, Hl.
  - assert (i = n) as -> by lia.
    rewrite app_nth2 by lia.
    replace (N.to_nat n - length (GENLIST f n))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma LENGTH_w2v {n : N} (x : word n) : LENGTH (w2v x) = dimindex n.
Proof. unfold w2v. apply LENGTH_GENLIST. Qed.

Lemma testbit_w2v {n : N} (x : word n) j : testbit j (w2v x) = word_bit j x.
Proof.
  unfold testbit. rewrite LENGTH_w2v, word_bit_alt. cbv zeta.
  destruct (N.ltb_spec j (dimindex n)); [|reflexivity]. cbn [andb].
  unfold w2v. rewrite EL_GENLIST by lia. f_equal. lia.
Qed.

Lemma testbit_app j (l1 l2 : list bool) :
  testbit j (l1 ++ l2) = if j <? LENGTH l2 then testbit j l2 else testbit (j - LENGTH l2) l1.
Proof.
  pose proof (LENGTH_length l1) as E1. pose proof (LENGTH_length l2) as E2.
  unfold testbit. rewrite LENGTH_app. cbv zeta.
  destruct (N.ltb_spec j (LENGTH l2)) as [H2|H2].
  - destruct (N.ltb_spec j (LENGTH l1 + LENGTH l2)); [|lia]. cbn [andb].
    rewrite !EL_nth by (rewrite ?LENGTH_app; lia).
    rewrite app_nth2 by lia. f_equal. lia.
  - destruct (N.ltb_spec (j - LENGTH l2) (LENGTH l1)) as [H1|H1].
    + destruct (N.ltb_spec j (LENGTH l1 + LENGTH l2)); [|lia]. cbn [andb].
      rewrite !EL_nth by (rewrite ?LENGTH_app; lia).
      rewrite app_nth1 by lia. f_equal. lia.
    + destruct (N.ltb_spec j (LENGTH l1 + LENGTH l2)); [lia|]. reflexivity.
Qed.

(** ** Loads *)

Definition mem_list (m : word64 -> word8) (a : word64) (k : N) : list bool :=
  num_rec [] (fun n l => w2v (m (word_add a (n2w n))) ++ l) k.

Lemma LENGTH_mem_list m a k : LENGTH (mem_list m a k) = 8 * k.
Proof.
  induction k as [|k IH] using N.peano_ind; [reflexivity|].
  unfold mem_list; rewrite num_rec_SUC; fold (mem_list m a k). rewrite LENGTH_app, IH, LENGTH_w2v.
  change (dimindex 8) with 8. lia.
Qed.

Lemma testbit_mem_list m a k j :
  testbit j (mem_list m a k) = (j <? 8 * k) && word_bit (j mod 8) (m (word_add a (n2w (j / 8)))).
Proof.
  induction k as [|k IH] using N.peano_ind.
  - unfold mem_list; rewrite num_rec_0. unfold testbit; cbn [LENGTH]. destruct (N.ltb_spec j 0); [lia|].
    destruct (N.ltb_spec j (8 * 0)); [lia|reflexivity].
  - unfold mem_list; rewrite num_rec_SUC; fold (mem_list m a k). rewrite testbit_app, LENGTH_mem_list.
    destruct (N.ltb_spec j (8 * k)) as [Hj|Hj].
    + rewrite IH. destruct (N.ltb_spec j (8 * k)), (N.ltb_spec j (8 * N.succ k)); try lia. reflexivity.
    + rewrite testbit_w2v. destruct (N.ltb_spec j (8 * N.succ k)) as [Hj'|Hj']; cbn [andb].
      * assert (E : j / 8 = k) by (symmetry; apply N.div_unique with (j - 8 * k); lia).
        assert (E' : j mod 8 = j - 8 * k) by (symmetry; apply N.mod_unique with k; lia).
        rewrite E, E'. reflexivity.
      * apply wb_high. change (dimindex 8) with 8. lia.
Qed.

Lemma add_n2w_0 {a : N} (w : word a) : word_add w (n2w 0) = w.
Proof. apply (proj1 lemmas.WORD_ADD_0). Qed.

Lemma add_n2w_add {a : N} (w : word a) p q : word_add (word_add w (n2w p)) (n2w q) = word_add w (n2w (p + q)).
Proof. rewrite <- lemmas.WORD_ADD_ASSOC, lemmas.word_add_n2w. reflexivity. Qed.

Lemma aload_SUC n m a :
  aload (SUC n) m a = word_or (word_lsl (aload n m (word_add a (n2w 1))) 8) (w2w (m a)).
Proof. unfold aload; rewrite num_rec_SUC; reflexivity. Qed.

Lemma aload_bit n m a j : n <= 8 ->
  word_bit j (aload n m a) = (j <? 8 * n) && word_bit (j mod 8) (m (word_add a (n2w (j / 8)))).
Proof.
  revert a j; induction n as [|n IH] using N.peano_ind; intros a j Hn.
  - unfold aload; rewrite num_rec_0, wb_n2w_lit, N.bits_0, Bool.andb_false_r.
    destruct (N.ltb_spec j (8 * 0)); [lia|reflexivity].
  - rewrite aload_SUC, wb_or, wb_lsl, wb_w2w, IH by lia.
    change (dimindex 64) with 64. change (dimindex 8) with 8.
    destruct (N.ltb_spec j 8) as [H8|H8].
    + destruct (N.leb_spec 8 j); [lia|]. destruct (N.ltb_spec j 64); [|lia].
      destruct (N.ltb_spec j (8 * N.succ n)); [|lia]. cbn [andb orb].
      rewrite N.mod_small, N.div_small, add_n2w_0 by lia. reflexivity.
    + destruct (N.leb_spec 8 j); [|lia].
      rewrite (wb_high (m a) j) by (change (dimindex 8) with 8; lia).
      destruct (N.ltb_spec j 64) as [H64|H64]; cbn [andb orb]; rewrite ?Bool.andb_false_r, ?Bool.orb_false_r.
      * replace ((j - 8) mod 8) with (j mod 8).
        2:{ replace j with ((j - 8) + 1 * 8) at 1 by lia. rewrite N.Div0.mod_add. reflexivity. }
        rewrite add_n2w_add.
        replace (1 + (j - 8) / 8) with (j / 8).
        2:{ replace j with ((j - 8) + 1 * 8) at 1 by lia. rewrite N.div_add by lia. lia. }
        destruct (N.ltb_spec (j - 8) (8 * n)), (N.ltb_spec j (8 * N.succ n)); try lia; reflexivity.
      * destruct (N.ltb_spec j (8 * N.succ n)); [lia|reflexivity].
Qed.

Lemma load_eq {w : N} m a k : k <= 8 -> 8 * k <= dimindex w ->
  (w2w (v2w (mem_list m a k) : word w) : word64) = aload k m a.
Proof.
  intros Hk Hw. apply word_bit_ext; intros j Hj. rewrite !wb_fcp by exact Hj.
  rewrite wb_w2w, aload_bit by exact Hk. rewrite wb_v2w, testbit_mem_list.
  change (dimindex 64) with 64 in *. destruct (N.ltb_spec j 64); [|lia]. cbn [andb].
  destruct (N.ltb_spec j (8 * k)); [|rewrite ?Bool.andb_false_r; reflexivity].
  destruct (N.ltb_spec j (dimindex w)); [reflexivity|lia].
Qed.

Lemma load_eq2 {w : N} m a k : k <= 4 -> 8 * k <= dimindex w -> dimindex w <= 32 ->
  (w2w (w2w (v2w (mem_list m a k) : word w) : word32) : word64) = aload k m a.
Proof.
  intros Hk Hw Hw2. apply word_bit_ext; intros j Hj. rewrite !wb_fcp by exact Hj.
  rewrite !wb_w2w, aload_bit by lia. rewrite wb_v2w, testbit_mem_list.
  change (dimindex 64) with 64 in *. change (dimindex 32) with 32 in *.
  destruct (N.ltb_spec j 64); [|lia]. cbn [andb].
  destruct (N.ltb_spec j (8 * k)); [|rewrite ?Bool.andb_false_r; reflexivity].
  destruct (N.ltb_spec j (dimindex w)); [|lia]. destruct (N.ltb_spec j 32); [reflexivity|lia].
Qed.

Lemma XW {W : N} n s : X (Nw:=W) n s = w2w (rX (arm8_state_REG s) n).
Proof.
  unfold X, rX. destruct (bool_decide _); [|reflexivity].
  apply word_bit_ext; intros j Hj. rewrite !wb_fcp by exact Hj.
  rewrite wb_w2w, !wb_n2w_lit, N.bits_0, !Bool.andb_false_r. reflexivity.
Qed.

Lemma wXW {W : N} (v : word W) n s : write'X (Nw:=W) (v, n) s = arm8_state_REG_fupd (fun _ => wX n (w2w v) (arm8_state_REG s)) s.
Proof.
  unfold write'X, wX. destruct (bool_decide _); [|reflexivity].
  destruct s; reflexivity.
Qed.

Lemma Mem_k {W : N} a k acc s : s_ok s -> k <= 3 -> aligned k a = true ->
  Mem (Nw:=W) (a, (2 ^ k, acc)) s = (v2w (mem_list (arm8_state_MEM s) a (2 ^ k)), s).
Proof.
  intros Hok Hk Hal. unfold Mem. rewrite CheckAlignment_ok by assumption.
  assert (Hk' : k < 4) by lia. clear Hk Hal.
  idx_cases Hk' ltac:(unfold FOR; cbn - [w2v v2w BigEndian]; rewrite BigEndian_ok by exact Hok; reflexivity).
Qed.

(** ** Stores *)

Definition store_f (k : N) (a : word64) (bytes : N -> word8) (m : word64 -> word8) : word64 -> word8 :=
  num_rec m (fun i m' => UPDATE (word_add a (n2w i)) (bytes i) m') k.

Lemma MEM_fupd_MEM_fupd f g s : arm8_state_MEM_fupd f (arm8_state_MEM_fupd g s) = arm8_state_MEM_fupd (fun x => f (g x)) s.
Proof. destruct s; reflexivity. Qed.

Lemma write'Mem_k {W : N} (v : word W) a k acc s : s_ok s -> k <= 3 -> aligned k a = true ->
  write'Mem (Nw:=W) (v, (a, (2 ^ k, acc))) s =
  arm8_state_MEM_fupd (fun _ => store_f (2 ^ k) a (fun i => v2w (field (8 * i + 7) (8 * i) (w2v v))) (arm8_state_MEM s)) s.
Proof.
  intros Hok Hk Hal. unfold write'Mem. rewrite CheckAlignment_ok by assumption. rewrite BigEndian_ok by exact Hok.
  assert (Hk' : k < 4) by lia. clear Hk Hal.
  idx_cases Hk' ltac:(unfold FOR; cbn - [w2v v2w field UPDATE]; rewrite ?MEM_fupd_MEM_fupd; reflexivity).
Qed.

Lemma n2w_sub_add (x a : word64) : word_add a (n2w (w2n (word_sub x a))) = x.
Proof. rewrite n2w_w2n. rewrite lemmas.WORD_ADD_COMM. apply lemmas.WORD_SUB_ADD. Qed.

Lemma add_n2w_eq (a x : word64) i : i < 2 ^ 64 -> (word_add a (n2w i) = x <-> w2n (word_sub x a) = i).
Proof.
  intros Hi. split.
  - intros <-. rewrite lemmas.WORD_ADD_SUB2, w2n_n2w. apply N.mod_small. exact Hi.
  - intros <-. apply n2w_sub_add.
Qed.

Lemma store_f_char k a bytes m x : k <= 2 ^ 64 ->
  store_f k a bytes m x = if w2n (word_sub x a) <? k then bytes (w2n (word_sub x a)) else m x.
Proof.
  intros Hk. induction k as [|k IH] using N.peano_ind.
  - destruct (N.ltb_spec (w2n (word_sub x a)) 0); [lia|reflexivity].
  - unfold store_f; rewrite num_rec_SUC; fold (store_f k a bytes m). unfold UPDATE.
    destruct (decide _) as [E|E].
    + apply add_n2w_eq in E; [|lia]. rewrite E. destruct (N.ltb_spec k (N.succ k)); [reflexivity|lia].
    + rewrite IH by lia. rewrite add_n2w_eq in E by lia.
      destruct (N.ltb_spec (w2n (word_sub x a)) k), (N.ltb_spec (w2n (word_sub x a)) (N.succ k)); try lia; reflexivity.
Qed.

Lemma astore_SUC n a d m :
  astore (SUC n) a d m = UPDATE a (w2w d) (astore n (word_add a (n2w 1)) (word_lsr d 8) m).
Proof. unfold astore; rewrite num_rec_SUC; reflexivity. Qed.

Lemma sub_add1 (x a : word64) : x <> a -> w2n (word_sub x (word_add a (n2w 1))) = w2n (word_sub x a) - 1 /\ w2n (word_sub x a) <> 0.
Proof.
  intros Hne. assert (H0 : w2n (word_sub x a) <> 0).
  { intros E. apply lemmas.w2n_eq_0 in E. apply Hne. rewrite lemmas.WORD_EQ_SUB_ZERO in E. exact E. }
  split; [|exact H0].
  rewrite lemmas.WORD_SUB_PLUS, lemmas.word_sub_w2n.
  - rewrite w2n_n2w. reflexivity.
  - apply lemmas.WORD_LS. change (w2n (n2w 1 : word64)) with 1. lia.
Qed.

Lemma lsr_0 {a : N} (w : word a) : word_lsr w 0 = w.
Proof.
  apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi. rewrite wb_lsr, N.add_0_r.
  destruct (N.ltb_spec i (dimindex a)); [reflexivity|lia].
Qed.

Lemma astore_char k : forall a d m x, k <= 8 ->
  astore k a d m x = if w2n (word_sub x a) <? k then w2w (word_lsr d (8 * w2n (word_sub x a))) else m x.
Proof.
  induction k as [|k IH] using N.peano_ind; intros a d m x Hk.
  - destruct (N.ltb_spec (w2n (word_sub x a)) 0); [lia|reflexivity].
  - rewrite astore_SUC. unfold UPDATE. destruct (decide (a = x)) as [<-|Hne].
    + rewrite lemmas.WORD_SUB_REFL, w2n_n2w, N.Div0.mod_0_l. rewrite N.mul_0_r, lsr_0. destruct (N.ltb_spec 0 (N.succ k)); [reflexivity|lia].
    + rewrite IH by lia. destruct (sub_add1 x a (not_eq_sym Hne)) as [E1 E2]. rewrite E1.
      rewrite lemmas.LSR_ADD.
      destruct (N.ltb_spec (w2n (word_sub x a) - 1) k), (N.ltb_spec (w2n (word_sub x a)) (N.succ k)); try lia; [|reflexivity].
      do 2 f_equal. lia.
Qed.

Ltac fcp_wb :=
  repeat match goal with |- context [@fcp_index ?a ?w ?k] =>
    rewrite (@wb_fcp a w k) by (vm_compute; reflexivity) end.

Ltac store_eq_tac :=
  apply functional_extensionality; intros x;
  rewrite store_f_char by (cbn; lia); rewrite astore_char by lia;
  match goal with |- context [N.ltb (w2n (word_sub x ?a)) ?k] =>
    destruct (N.ltb_spec (w2n (word_sub x a)) k) as [Ht|Ht]; [|reflexivity];
    revert Ht; generalize (w2n (word_sub x a)); intros t Ht;
    idx_cases Ht ltac:(unfold field, fixwidth, shiftr, w2v; cbn - [fcp_index w2w word_lsr v2w];
                     wblast; fcp_wb; wbs; reflexivity) end.

Lemma store_eq64 (v : word64) a m :
  store_f 8 a (fun i => v2w (field (8 * i + 7) (8 * i) (w2v v))) m = astore 8 a v m.
Proof. store_eq_tac. Qed.
Lemma store_eq32 (v : word64) a m :
  store_f 4 a (fun i => v2w (field (8 * i + 7) (8 * i) (w2v (w2w v : word32)))) m = astore 4 a v m.
Proof. store_eq_tac. Qed.
Lemma store_eq16 (v : word64) a m :
  store_f 2 a (fun i => v2w (field (8 * i + 7) (8 * i) (w2v (w2w v : word16)))) m = astore 2 a v m.
Proof. store_eq_tac. Qed.
Lemma store_eq8 (v : word64) a m :
  store_f 1 a (fun i => v2w (field (8 * i + 7) (8 * i) (w2v (w2w v : word8)))) m = astore 1 a v m.
Proof. store_eq_tac. Qed.


Lemma ExtendWord_u {M W : N} (v : word M) : ExtendWord (Mw:=M) (Nw:=W) (v, false) = w2w v.
Proof. reflexivity. Qed.

Ltac run_ls Hok Hn Hal :=
  cbn [Run dfn'LoadStoreImmediate LoadStoreSingle lsargs]; rewrite (bdf _ Hn); cbn [andb];
  rewrite ?X64, ?XW;
  match goal with |- context [word_len ?z / 8] => let v := eval vm_compute in (word_len z / 8) in change (word_len z / 8) with v end;
  match goal with
  | |- context [Mem (?addr, (8, ?acc))] => change 8 with (2 ^ 3)
  | |- context [Mem (?addr, (4, ?acc))] => change 4 with (2 ^ 2)
  | |- context [Mem (?addr, (2, ?acc))] => change 2 with (2 ^ 1)
  | |- context [Mem (?addr, (1, ?acc))] => change 1 with (2 ^ 0)
  | _ => idtac
  end.

Lemma MEM_put m s : arm8_state_MEM_fupd (fun _ => m) s = put (mk_astate (arm8_state_REG s) (arm8_state_PC s) m (flags_of (arm8_state_PSTATE s))) s.
Proof. destruct s as [? ? [] ? ? ? ? ? ? ? ? ? ? ? ? ?]; reflexivity. Qed.

Ltac ls_mem_fin Hok Hal :=
  match goal with
  | |- context [Mem (?addr, (word_len ?z / 8, ?acc))] =>
      let v := eval vm_compute in (N.log2 (word_len z / 8)) in
      change (word_len z / 8) with (2 ^ v); rewrite Mem_k by (exact Hok || lia || exact Hal); cbv beta iota zeta
  | |- context [write'Mem (?x, (?addr, (word_len ?z / 8, ?acc)))] =>
      let v := eval vm_compute in (N.log2 (word_len z / 8)) in
      change (word_len z / 8) with (2 ^ v); rewrite write'Mem_k by (exact Hok || lia || exact Hal); cbv beta iota zeta
  end.

Section RunMem.
Variable s : arm8_state.
Hypothesis Hok : s_ok s.

Lemma run_LS64 memop u off n t : n <> n2w 31 -> memop <> MemOp_PREFETCH ->
  aligned 3 (word_add (rX (arm8_state_REG s) n) off) = true ->
  run_shape (LoadStore (LoadStoreImmediate_64 (lsargs (n2w 3) false memop u off n t))) s.
Proof.
  intros Hn Hm Hal. left; split; [|destruct memop; [reflexivity|reflexivity|congruence]].
  cbn [Run dfn'LoadStoreImmediate LoadStoreSingle lsargs]; rewrite (bdf _ Hn); cbn [andb]. rewrite ?X64.
  destruct memop; [|clear Hm|congruence]; ls_mem_fin Hok Hal.
  - rewrite ExtendWord_u, wXW, REG_put. cbn [aexec ls_exec obs aregs amem]. rewrite w2w_id, load_eq by (cbn; lia). reflexivity.
  - rewrite store_eq64, MEM_put. reflexivity.
Qed.

Ltac run_lsW Hok Hn Hm Hal steq :=
  left; split; [|destruct Hm as [-> | ->]; reflexivity];
  cbn [Run dfn'LoadStoreImmediate LoadStoreSingle lsargs]; rewrite (bdf _ Hn); cbn [andb]; rewrite ?X64, ?XW;
  destruct Hm as [-> | ->]; ls_mem_fin Hok Hal;
  [ match goal with |- context [if ?rs then _ else _] => destruct rs end;
    rewrite !ExtendWord_u, wXW, REG_put; cbn [aexec ls_exec obs aregs amem];
    first [ rewrite load_eq2 by (cbn; lia) | rewrite w2w_id, load_eq by (cbn; lia) ]; reflexivity
  | rewrite steq, MEM_put; reflexivity ].

Lemma run_LS32 rs memop u off n t : n <> n2w 31 -> memop = MemOp_LOAD \/ memop = MemOp_STORE ->
  aligned 2 (word_add (rX (arm8_state_REG s) n) off) = true ->
  run_shape (LoadStore (LoadStoreImmediate_32 (lsargs (n2w 2) rs memop u off n t))) s.
Proof. intros Hn Hm Hal. run_lsW Hok Hn Hm Hal store_eq32. Qed.

Lemma run_LS16 rs memop u off n t : n <> n2w 31 -> memop = MemOp_LOAD \/ memop = MemOp_STORE ->
  aligned 1 (word_add (rX (arm8_state_REG s) n) off) = true ->
  run_shape (LoadStore (LoadStoreImmediate_16 (lsargs (n2w 1) rs memop u off n t))) s.
Proof. intros Hn Hm Hal. run_lsW Hok Hn Hm Hal store_eq16. Qed.

Lemma run_LS8 rs memop u off n t : n <> n2w 31 -> memop = MemOp_LOAD \/ memop = MemOp_STORE ->
  run_shape (LoadStore (LoadStoreImmediate_8 (lsargs (n2w 0) rs memop u off n t))) s.
Proof.
  intros Hn Hm. assert (Hal : aligned 0 (word_add (rX (arm8_state_REG s) n) off) = true) by apply alignment.aligned_0.
  run_lsW Hok Hn Hm Hal store_eq8.
Qed.
End RunMem.


(** ** Fetching and the effect of [Next] (Galette-only) *)

Definition bytes_at (s : arm8_state) (w : word32) : Prop :=
  let pc := arm8_state_PC s in let m := arm8_state_MEM s in
  m pc = (word_extract 7 0 w : word8) /\ m (word_add pc (n2w 1)) = (word_extract 15 8 w : word8) /\
  m (word_add pc (n2w 2)) = (word_extract 23 16 w : word8) /\ m (word_add pc (n2w 3)) = (word_extract 31 24 w : word8).

Lemma fetch_word m pc (w : word32) :
  m pc = (word_extract 7 0 w : word8) -> m (word_add pc (n2w 1)) = (word_extract 15 8 w : word8) ->
  m (word_add pc (n2w 2)) = (word_extract 23 16 w : word8) -> m (word_add pc (n2w 3)) = (word_extract 31 24 w : word8) ->
  (v2w (mem_list m pc 4) : word32) = w.
Proof.
  intros H0 H1 H2 H3. apply word_bit_ext; intros j Hj. rewrite !wb_fcp by exact Hj.
  rewrite wb_v2w, testbit_mem_list. change (dimindex 32) with 32 in Hj.
  idx_cases Hj ltac:(wbs; rewrite ?add_n2w_0, ?H0, ?H1, ?H2, ?H3; wbs; reflexivity).
Qed.

Lemma s_ok_bh s v : s_ok (arm8_state_branch_hint_fupd (fun _ => v) s) <-> s_ok s.
Proof. destruct s; reflexivity. Qed.

Lemma s_ok_put A s : s_ok (put A s) <-> s_ok s.
Proof. destruct s as [? ? [] ? ? ? ? ? ? ? ? ? ? ? ? ?], A as [? ? ? [? [? [? ?]]]]; reflexivity. Qed.

Lemma s_ok_PC s f : s_ok (arm8_state_PC_fupd f s) <-> s_ok s.
Proof. destruct s; reflexivity. Qed.

Lemma astate_eta (A : astate) : A = mk_astate (aregs A) (apc A) (amem A) (aflags A).
Proof. destruct A; reflexivity. Qed.

Lemma flags_set f p : flags_of (set_flags f p) = f.
Proof. destruct f as [? [? [? ?]]]; reflexivity. Qed.

Lemma obs_PC_put p A s : obs (arm8_state_PC_fupd (fun _ => p) (put A s)) = mk_astate (aregs A) p (amem A) (aflags A).
Proof. unfold obs; cbn. rewrite flags_set. reflexivity. Qed.

Lemma obs_PC_bh_put p v A s :
  obs (arm8_state_PC_fupd (fun _ => p) (arm8_state_branch_hint_fupd (fun _ => v) (put A s))) = mk_astate (aregs A) p (amem A) (aflags A).
Proof. unfold obs; cbn. rewrite flags_set. reflexivity. Qed.

Lemma Fetch_ok s w : s_ok s -> aligned 2 (arm8_state_PC s) = true -> bytes_at s w ->
  Fetch (arm8_state_branch_hint_fupd (fun _ => None) s) = (w, arm8_state_branch_hint_fupd (fun _ => None) s).
Proof.
  intros Hok Hal (H0 & H1 & H2 & H3). unfold Fetch. change 4 with (2 ^ 2).
  rewrite Mem_k by (try apply s_ok_bh; try exact Hok; try exact Hal; lia).
  f_equal. apply fetch_word; assumption.
Qed.

Lemma Next_shape s w i :
  s_ok s -> aligned 2 (arm8_state_PC s) = true -> bytes_at s w -> Decode w = i ->
  run_shape i (arm8_state_branch_hint_fupd (fun _ => None) s) ->
  exists s', NextStateARM8 s = Some s' /\ s_ok s' /\ obs s' = aexec i (obs s).
Proof.
  intros Hok Hal Hb Hd Hs. unfold NextStateARM8, Next. rewrite (Fetch_ok s w Hok Hal Hb). cbv beta iota zeta.
  rewrite Hd. unfold run_shape in Hs. cbv zeta in Hs.
  change (obs (arm8_state_branch_hint_fupd (fun _ => None) s)) with (obs s) in Hs.
  destruct Hs as [[Hr Hpc]|[bt Hr]]; rewrite Hr; clear Hr.
  - cbn [put arm8_state_branch_hint arm8_state_branch_hint_fupd IS_SOME negb arm8_state_PC_fupd arm8_state_exception].
    pose proof Hok as (HEL & HE0 & HSA & HT1 & HT0 & Hex). rewrite Hex, bdt by reflexivity.
    eexists; split; [reflexivity|]. split.
    + rewrite ?s_ok_PC, ?s_ok_bh, ?s_ok_put, ?s_ok_bh. exact Hok.
    + rewrite obs_PC_put. change (arm8_state_PC (arm8_state_branch_hint_fupd (fun _ => None) s)) with (arm8_state_PC s) in Hpc.
      change (arm8_state_PC (put ?A ?s)) with (arm8_state_PC s). change (arm8_state_PC (arm8_state_branch_hint_fupd (fun _ => None) s)) with (arm8_state_PC s).
      rewrite <- Hpc. symmetry; apply astate_eta.
  - cbn [put arm8_state_branch_hint arm8_state_branch_hint_fupd IS_SOME negb arm8_state_PC_fupd arm8_state_exception].
    pose proof Hok as (HEL & HE0 & HSA & HT1 & HT0 & Hex). rewrite Hex, bdt by reflexivity.
    eexists; split; [reflexivity|]. split.
    + rewrite ?s_ok_PC, ?s_ok_bh, ?s_ok_put, ?s_ok_bh. exact Hok.
    + rewrite obs_PC_bh_put. symmetry; apply astate_eta.
Qed.


(** ** The step theorem (Galette-only) *)

Definition supported (i : instruction) : Prop :=
  match i with
  | Hint op => op = SystemHintOp_NOP
  | Address (page, _) => page = false
  | Data (MoveWide_64 (sf, _)) => sf = n2w 1
  | Data (LogicalImmediate_64 (sf, (_, (sfl, (_, (_, d)))))) => sf = n2w 1 /\ (d <> n2w 31 \/ sfl = true)
  | Data (AddSubShiftedRegister_64 (sf, (_, (_, (sh, (_, (imm6, _))))))) => sf = n2w 1 /\ sh = ShiftType_LSL /\ imm6 = n2w 0
  | Data (LogicalShiftedRegister_64 (sf, (_, (_, (_, (sh, (amt, _))))))) => sf = n2w 1 /\ sh = ShiftType_LSL /\ amt = 0
  | Data (AddSubImmediate_64 (sf, (_, (sfl, (_, (n, d)))))) => sf = n2w 1 /\ n <> n2w 31 /\ (d <> n2w 31 \/ sfl = true)
  | Data (BitfieldMove_64 (sf, (inz, _))) => sf = n2w 1 /\ inz = true
  | Data (ExtractRegister_64 (sf, _)) => sf = n2w 1
  | Data (Shift_64 (sf, _)) => sf = n2w 1
  | Data (Division_64 (sf, (uns, _))) => sf = n2w 1 /\ uns = false
  | Data (MultiplyHigh (sg, _)) => sg = false
  | Data (MultiplyAddSub_64 (sf, (sub, _))) => sf = n2w 1 /\ sub = false
  | Data (ConditionalCompareImmediate_64 (sf, _)) => sf = n2w 1
  | Data (AddSubCarry_64 (sf, _)) => sf = n2w 1
  | Data (ConditionalSelect_64 (sf, _)) => sf = n2w 1
  | Branch (BranchImmediate (_, bt)) => bt = BranchType_JMP \/ bt = BranchType_CALL
  | Branch (BranchConditional _) => True
  | Branch (BranchRegister (_, bt)) => bt = BranchType_JMP
  | LoadStore (LoadStoreImmediate_64 x) => exists memop u off n t,
      x = lsargs (n2w 3) false memop u off n t /\ n <> n2w 31 /\ (memop = MemOp_LOAD \/ memop = MemOp_STORE)
  | LoadStore (LoadStoreImmediate_32 x) => exists rs memop u off n t,
      x = lsargs (n2w 2) rs memop u off n t /\ n <> n2w 31 /\ (memop = MemOp_LOAD \/ memop = MemOp_STORE)
  | LoadStore (LoadStoreImmediate_16 x) => exists rs memop u off n t,
      x = lsargs (n2w 1) rs memop u off n t /\ n <> n2w 31 /\ (memop = MemOp_LOAD \/ memop = MemOp_STORE)
  | LoadStore (LoadStoreImmediate_8 x) => exists rs memop u off n t,
      x = lsargs (n2w 0) rs memop u off n t /\ n <> n2w 31 /\ (memop = MemOp_LOAD \/ memop = MemOp_STORE)
  | _ => False
  end.

Definition mem_ok (i : instruction) (A : astate) : Prop :=
  match i with
  | LoadStore (LoadStoreImmediate_64 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) =>
      aligned 3 (word_add (rX (aregs A) n) off) = true
  | LoadStore (LoadStoreImmediate_32 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) =>
      aligned 2 (word_add (rX (aregs A) n) off) = true
  | LoadStore (LoadStoreImmediate_16 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) =>
      aligned 1 (word_add (rX (aregs A) n) off) = true
  | _ => True
  end.

Lemma step_of s w i i' : s_ok s -> aligned 2 (arm8_state_PC s) = true -> bytes_at s w -> Decode w = i' ->
  aexec i' (obs s) = aexec i (obs s) -> run_shape i' (arm8_state_branch_hint_fupd (fun _ => None) s) ->
  exists s', NextStateARM8 s = Some s' /\ s_ok s' /\ obs s' = aexec i (obs s).
Proof.
  intros Hok Hal Hb Hd He Hr. rewrite <- He. exact (Next_shape s w i' Hok Hal Hb Hd Hr).
Qed.

Theorem step_thm s i w :
  supported i -> s_ok s -> aligned 2 (arm8_state_PC s) = true -> Encode i = ARM8 w -> bytes_at s w ->
  mem_ok i (obs s) ->
  exists s', NextStateARM8 s = Some s' /\ s_ok s' /\ obs s' = aexec i (obs s).
Proof.
  intros Hsup Hok Hal He Hb Hm.
  assert (Hok' : s_ok (arm8_state_branch_hint_fupd (fun _ => None) s)) by (apply s_ok_bh; exact Hok).
  destruct i as [p|[p|p|p|p|p|p|p]|p|p|[p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p]|p|p|[p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p]|p| |p| ];
    cbn [supported] in Hsup; try contradiction.
  all: repeat match goal with p : _ * _ |- _ => destruct p end; cbv beta iota zeta in Hsup.
  all: repeat match type of Hsup with
         | _ /\ _ => let H1 := fresh "Hs" in destruct Hsup as [H1 Hsup]; try subst
         | exists _, _ => let x := fresh "x" in destruct Hsup as [x Hsup]
         end; try subst.
  all: lazymatch type of He with
       | Encode (Data ?x) = _ =>
           lazymatch x with
           | MoveWide_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_MoveWide; exact He|reflexivity|apply run_MoveWide]
           | LogicalImmediate_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_LogImm; exact He|reflexivity|apply run_LogImm; assumption]
           | AddSubShiftedRegister_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_AddSubShifted; exact He|reflexivity|apply run_AddSubShifted]
           | LogicalShiftedRegister_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_LogShift; exact He|reflexivity|apply run_LogShift]
           | AddSubImmediate_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_AddSubImm; exact He|reflexivity|apply run_AddSubImm; assumption]
           | BitfieldMove_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_Bfm; exact He|reflexivity|apply run_Bfm]
           | ExtractRegister_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_Extr; exact He|reflexivity|apply run_Extr]
           | Shift_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_ShiftReg; exact He|reflexivity|apply run_ShiftReg]
           | Division_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_Div; exact He|reflexivity|apply run_Div]
           | MultiplyHigh _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_MulHigh; exact He|reflexivity|apply run_MulHigh]
           | MultiplyAddSub_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_MulAdd; exact He|reflexivity|apply run_MulAdd]
           | ConditionalCompareImmediate_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_CCmpImm; exact He|reflexivity|apply run_CCmpImm]
           | AddSubCarry_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_AddSubCarry; exact He|reflexivity|apply run_AddSubCarry]
           | ConditionalSelect_64 _ => eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_CSel; exact He|reflexivity|apply run_CSel]
           end
       | Encode (Address _) = _ => eapply step_of; [exact Hok|exact Hal|exact Hb|apply dec_Address, He|reflexivity|apply run_Address]
       | Encode (Branch (BranchConditional _)) = _ =>
           eapply step_of; [exact Hok|exact Hal|exact Hb|apply dec_BCond, He|reflexivity|apply run_BCond, Hok']
       | Encode (Branch (BranchImmediate _)) = _ =>
           eapply step_of; [exact Hok|exact Hal|exact Hb|eapply dec_BImm; [exact Hsup|exact He]|reflexivity|apply run_BImm, Hok']
       | Encode (Branch (BranchRegister _)) = _ =>
           eapply step_of; [exact Hok|exact Hal|exact Hb|apply dec_BReg, He|reflexivity|apply run_BReg; [exact Hok'|discriminate]]
       | Encode (Hint _) = _ => eapply step_of; [exact Hok|exact Hal|exact Hb|apply dec_NOP, He|reflexivity|apply run_NOP]
       | Encode (LoadStore ?x) = _ =>
           match goal with H : (_, _) = lsargs _ _ _ _ _ _ _ |- _ => unfold lsargs in H; inversion H; subst; clear H end;
           cbn [mem_ok obs aregs] in Hm;
           let Hmp := fresh "Hmp" in
           lazymatch type of Hsup with ?mo = MemOp_LOAD \/ _ =>
             assert (Hmp : mo <> MemOp_PREFETCH) by (destruct Hsup as [-> | ->]; discriminate) end;
           lazymatch x with
           | LoadStoreImmediate_64 _ => destruct (dec_LS64 _ _ _ _ _ _ Hmp He) as [u' Hd];
               eapply step_of; [exact Hok|exact Hal|exact Hb|exact Hd|reflexivity|apply run_LS64; try assumption]
           | LoadStoreImmediate_32 _ => destruct (dec_LS32 _ _ _ _ _ _ _ Hmp He) as [u' Hd];
               eapply step_of; [exact Hok|exact Hal|exact Hb|exact Hd|reflexivity|apply run_LS32; try assumption]
           | LoadStoreImmediate_16 _ => destruct (dec_LS16 _ _ _ _ _ _ _ Hmp He) as [u' Hd];
               eapply step_of; [exact Hok|exact Hal|exact Hb|exact Hd|reflexivity|apply run_LS16; try assumption]
           | LoadStoreImmediate_8 _ => destruct (dec_LS8 _ _ _ _ _ _ _ Hmp He) as [u' Hd];
               eapply step_of; [exact Hok|exact Hal|exact Hb|exact Hd|reflexivity|apply run_LS8; try assumption]
           end
       end.
Qed.


(** ** Simulation along a path of ARMv8 instructions (Galette-only) *)

Definition rv_rel (dom : word64 -> Prop) (ms : arm8_state) (A : astate) : Prop :=
  arm8_ok ms = true /\ arm8_state_REG ms = aregs A /\ arm8_state_PC ms = apc A /\
  (forall a, dom a -> arm8_state_MEM ms a = amem A a) /\ flags_of (arm8_state_PSTATE ms) = aflags A.

Lemma arm8_ok_iff s : arm8_ok s = true <-> s_ok s /\ aligned 2 (arm8_state_PC s) = true.
Proof.
  unfold arm8_ok, s_ok. rewrite !Bool.andb_true_iff, !bool_decide_spec, !Bool.negb_true_iff. tauto.
Qed.

Definition acc_ok (dom : word64 -> Prop) (i : instruction) (A : astate) : Prop :=
  let in_dom k n off := forall j, j < k -> dom (word_add (word_add (rX (aregs A) n) off) (n2w j)) in
  match i with
  | LoadStore (LoadStoreImmediate_64 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) => in_dom 8 n off
  | LoadStore (LoadStoreImmediate_32 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) => in_dom 4 n off
  | LoadStore (LoadStoreImmediate_16 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) => in_dom 2 n off
  | LoadStore (LoadStoreImmediate_8 (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, (off, (n, _))))))))))))) => in_dom 1 n off
  | _ => True
  end.

Definition step_pre (dom : word64 -> Prop) (A : astate) (i : instruction) : Prop :=
  supported i /\ (exists w, Encode i = ARM8 w) /\ bytes_in_memory (apc A) (arm8_encode i) (amem A) dom /\
  mem_ok i A /\ acc_ok dom i A /\ aligned 2 (apc (aexec i A)) = true.

Lemma arm8_proj_eq dom ms1 ms2 :
  arm8_proj dom ms1 = arm8_proj dom ms2 ->
  arm8_ok ms1 = arm8_ok ms2 /\ arm8_state_REG ms1 = arm8_state_REG ms2 /\
  arm8_state_PC ms1 = arm8_state_PC ms2 /\
  (forall a, dom a -> arm8_state_MEM ms1 a = arm8_state_MEM ms2 a) /\
  arm8_state_PSTATE ms1 = arm8_state_PSTATE ms2.
Proof.
  unfold arm8_proj; intros H; injection H; intros Hpc Hm Hg He Ht Hs Hp.
  pose proof (proj1 (set_sep.fun2set_eq (arm8_state_MEM ms1) (arm8_state_MEM ms2) dom) Hm) as Hm'.
  unfold arm8_ok. rewrite Hpc, Hp, Hs, Ht, He. auto.
Qed.

Lemma rv_rel_env dom env i ms A :
  interference_ok env (arm8_proj dom) -> rv_rel dom ms A -> rv_rel dom (env i ms) A.
Proof.
  intros Hi (H1 & H2 & H3 & H4 & H5). destruct (arm8_proj_eq dom (env i ms) ms (Hi i ms)) as (E1 & E2 & E3 & E4 & E5).
  unfold rv_rel. rewrite E1, E2, E3, E5. split; [exact H1|split; [exact H2|split; [exact H3|split; [|exact H5]]]].
  intros a Ha; rewrite E4 by exact Ha; apply H4, Ha.
Qed.

Lemma aload_cong dom n m m' p :
  (forall k, k < n -> dom (word_add p (n2w k))) -> (forall a, dom a -> m a = m' a) ->
  aload n m p = aload n m' p.
Proof.
  revert p; induction n as [|n IH] using N.peano_ind; intros p Hd Hm; [reflexivity|].
  rewrite !aload_SUC. f_equal.
  - f_equal. apply IH; [|exact Hm]. intros k Hk. rewrite add_n2w_add. apply Hd. lia.
  - f_equal. apply Hm. rewrite <- (add_n2w_0 p). apply Hd. lia.
Qed.

Lemma astore_cong dom n p d m m' x : (forall a, dom a -> m a = m' a) -> dom x ->
  astore n p d m x = astore n p d m' x.
Proof.
  revert p d; induction n as [|n IH] using N.peano_ind; intros p d Hm Hx; [apply Hm, Hx|].
  rewrite !astore_SUC. unfold UPDATE. destruct (decide (p = x)); [reflexivity|]. apply IH; assumption.
Qed.

Lemma astore_out dom n p d m x : (forall k, k < n -> dom (word_add p (n2w k))) -> ~ dom x ->
  astore n p d m x = m x.
Proof.
  revert p d; induction n as [|n IH] using N.peano_ind; intros p d Hd Hx; [reflexivity|].
  rewrite !astore_SUC. unfold UPDATE. destruct (decide (p = x)) as [<-|].
  - exfalso. apply Hx. rewrite <- (add_n2w_0 p). apply Hd. lia.
  - apply IH; [|exact Hx]. intros k Hk. rewrite add_n2w_add. apply Hd. lia.
Qed.

Ltac inst_cases i :=
  destruct i as [p|[p|p|p|p|p|p|p]|p|p|[p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p]|p|p|[p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p|p]|p| |p| ];
  repeat match goal with p : _ * _ |- _ => destruct p end.

Lemma aexec_cong dom i A B :
  aregs A = aregs B -> apc A = apc B -> aflags A = aflags B -> (forall a, dom a -> amem A a = amem B a) ->
  acc_ok dom i A ->
  aregs (aexec i A) = aregs (aexec i B) /\ apc (aexec i A) = apc (aexec i B) /\ aflags (aexec i A) = aflags (aexec i B) /\
  (forall a, dom a -> amem (aexec i A) a = amem (aexec i B) a).
Proof.
  destruct A as [gA pA mA fA], B as [gB pB mB fB]; cbn [aregs apc amem aflags]; intros -> -> -> Hm Hacc.
  inst_cases i.
  all: cbn [aexec acc_ok aregs apc amem aflags] in *; unfold ls_exec in *.
  all: try (split; [reflexivity|split; [reflexivity|split; [reflexivity|exact Hm]]]).
  all: repeat match goal with
       | |- context [match ?m with MemOp_LOAD => _ | MemOp_STORE => _ | MemOp_PREFETCH => _ end] => destruct m
       | |- context [if ?b then _ else _] => destruct b
       | |- context [match ?p with SystemHintOp_NOP => _ | _ => _ end] => destruct p
       end; cbn [aregs apc amem aflags].
  all: try (split; [reflexivity|split; [reflexivity|split; [reflexivity|exact Hm]]]).
  all: try (split; [erewrite aload_cong; [reflexivity|exact Hacc|exact Hm]|split; [reflexivity|split; [reflexivity|exact Hm]]]).
  all: split; [reflexivity|split; [reflexivity|split; [reflexivity|intros ad Ha; exact (astore_cong dom _ _ _ _ _ _ Hm Ha)]]].
Qed.

Lemma aexec_out dom i A x : acc_ok dom i A -> ~ dom x -> amem (aexec i A) x = amem A x.
Proof.
  destruct A as [g pc m fl]; intros Hacc Hx.
  inst_cases i; cbn [aexec acc_ok aregs apc amem aflags] in *; unfold ls_exec in *; try reflexivity.
  all: repeat match goal with
       | |- context [match ?m with MemOp_LOAD => _ | MemOp_STORE => _ | MemOp_PREFETCH => _ end] => destruct m
       | |- context [if ?b then _ else _] => destruct b
       | |- context [match ?p with SystemHintOp_NOP => _ | _ => _ end] => destruct p
       end; cbn [aregs apc amem aflags]; try reflexivity.
  all: apply astore_out with dom; assumption.
Qed.

Lemma mem_ok_regs i A B : aregs A = aregs B -> mem_ok i A -> mem_ok i B.
Proof. destruct A, B; cbn; intros ->; auto. Qed.

Lemma acc_ok_regs dom i A B : aregs A = aregs B -> acc_ok dom i A -> acc_ok dom i B.
Proof. destruct A, B; cbn; intros ->; auto. Qed.

Lemma bytes_at_intro dom ms A i w :
  rv_rel dom ms A -> Encode i = ARM8 w -> bytes_in_memory (apc A) (arm8_encode i) (amem A) dom -> bytes_at ms w.
Proof.
  intros (_ & _ & Hpc & Hm & _) He Hb. unfold arm8_encode in Hb; rewrite He in Hb; cbn [bytes_in_memory] in Hb.
  destruct Hb as (E0 & D0 & E1 & D1 & E2 & D2 & E3 & D3 & _).
  rewrite !add_n2w_add in *. cbn [N.add] in *.
  unfold bytes_at. rewrite Hpc. rewrite !Hm by assumption. auto.
Qed.

Lemma one_step dom ms A i :
  rv_rel dom ms A -> step_pre dom A i ->
  rv_rel dom (arm8_next ms) (aexec i A) /\
  (forall x, ~ dom x -> arm8_state_MEM (arm8_next ms) x = arm8_state_MEM ms x).
Proof.
  intros Hr (Hsup & [w He] & Hb & Hmo & Hacc & Hal).
  pose proof Hr as (Hok & Hg & Hpc & Hm & Hf).
  pose proof Hok as Hok'. apply arm8_ok_iff in Hok' as (Hs & Hpal).
  assert (Hg' : aregs A = aregs (obs ms)) by exact (eq_sym Hg).
  destruct (step_thm ms i w Hsup Hs Hpal He (bytes_at_intro dom ms A i w Hr He Hb) (mem_ok_regs i A (obs ms) Hg' Hmo))
    as (s' & Hn & Hs' & Ho).
  unfold arm8_next. rewrite Hn. cbn [THE].
  destruct (aexec_cong dom i (obs ms) A Hg Hpc Hf (fun a Ha => Hm a Ha)
             (acc_ok_regs dom i A (obs ms) Hg' Hacc)) as (E1 & E2 & E3 & E4).
  split.
  - split; [|split; [|split; [|split]]].
    + apply arm8_ok_iff. split; [exact Hs'|]. change (arm8_state_PC s') with (apc (obs s')).
      rewrite Ho, E2. exact Hal.
    + change (arm8_state_REG s') with (aregs (obs s')). rewrite Ho. exact E1.
    + change (arm8_state_PC s') with (apc (obs s')). rewrite Ho. exact E2.
    + intros a Ha. change (arm8_state_MEM s') with (amem (obs s')). rewrite Ho. apply E4, Ha.
    + change (flags_of (arm8_state_PSTATE s')) with (aflags (obs s')). rewrite Ho. exact E3.
  - intros x Hx. change (arm8_state_MEM s') with (amem (obs s')). rewrite Ho.
    apply aexec_out with dom; [|exact Hx]. exact (acc_ok_regs dom i A (obs ms) Hg' Hacc).
Qed.


Fixpoint arun (A : astate) (l : list instruction) : astate :=
  match l with [] => A | i :: l' => arun (aexec i A) l' end.

Fixpoint run_ok (dom : word64 -> Prop) (A : astate) (l : list instruction) (PA : astate -> Prop) : Prop :=
  match l with
  | [] => True
  | [i] => step_pre dom A i
  | i :: l' => step_pre dom A i /\ PA (aexec i A) /\ run_ok dom (aexec i A) l' PA
  end.

Section Path.
Variable dom : word64 -> Prop.
Variable env : N -> arm8_state -> arm8_state.
Hypothesis Henv : interference_ok env (arm8_proj dom).

Lemma path_asserts (P Q : arm8_state -> Prop) (PA QA : astate -> Prop) :
  (forall ms A, rv_rel dom ms A -> PA A -> P ms) ->
  (forall ms A, rv_rel dom ms A -> QA A -> Q ms) ->
  forall l ms A (f : N -> N), l <> [] ->
  rv_rel dom ms A -> run_ok dom A l PA -> QA (arun A l) ->
  asserts (LENGTH l - 1) (fun k s => env (f k) (arm8_next s)) ms P Q.
Proof.
  intros HP HQ l; induction l as [|i l IH]; intros ms A f Hne Hr Hrun HQA; [congruence|].
  destruct l as [|i' l'].
  - cbn [LENGTH]. replace (SUC 0 - 1) with 0 by lia. unfold asserts; rewrite num_rec_0.
    cbn [run_ok] in Hrun. destruct (one_step dom ms A i Hr Hrun) as [Hr' _].
    apply HQ with (aexec i A); [apply rv_rel_env; assumption|exact HQA].
  - cbn [LENGTH] in *. replace (SUC (SUC (LENGTH l')) - 1) with (SUC (LENGTH l')) by lia.
    unfold asserts; rewrite num_rec_SUC; fold (asserts (LENGTH l') (fun k s => env (f k) (arm8_next s))).
    cbv zeta. destruct Hrun as (Hs & HPA & Hrun).
    destruct (one_step dom ms A i Hr Hs) as [Hr' _].
    pose proof (rv_rel_env dom env (f (SUC (LENGTH l'))) _ _ Henv Hr') as Hr''.
    set (ms' := env (f (SUC (LENGTH l'))) (arm8_next ms)) in *.
    split; [apply HP with (aexec i A); assumption|].
    replace (LENGTH l') with (LENGTH (i' :: l') - 1) by (cbn [LENGTH]; lia).
    apply IH with (aexec i A); [discriminate|exact Hr''|exact Hrun|exact HQA].
Qed.

Fixpoint run_ok2 (A : astate) (l : list instruction) : Prop :=
  match l with
  | [] => True
  | i :: l' => step_pre dom A i /\ run_ok2 (aexec i A) l'
  end.

Lemma run_ok_ok2 l A PA : run_ok dom A l PA -> run_ok2 A l.
Proof.
  revert A; induction l as [|i l IH]; intros A H; [exact Logic.I|].
  destruct l as [|i' l']; cbn [run_ok run_ok2] in *; [split; [exact H|exact Logic.I]|].
  destruct H as (H1 & _ & H3). split; [exact H1|]. apply IH, H3.
Qed.

Lemma path_asserts2 :
  forall l ms A (g : N -> N), rv_rel dom ms A -> run_ok2 A l ->
  asserts2 (LENGTH l) (fun k => env (g k)) arm8_next ms
    (fun ms1 ms2 => forall x, x NOTIN dom -> arm8_state_MEM ms1 x = arm8_state_MEM ms2 x).
Proof.
  intros l; induction l as [|i l IH]; intros ms A g Hr Hrun; [exact Logic.I|].
  cbn [LENGTH]. unfold asserts2; rewrite num_rec_SUC.
  fold (asserts2 (LENGTH l) (fun k => env (g k)) arm8_next).
  destruct Hrun as (Hs & Hrun). destruct (one_step dom ms A i Hr Hs) as [Hr' Hout].
  split.
  - intros x Hx. symmetry. apply Hout, Hx.
  - apply IH with (aexec i A); [apply rv_rel_env; assumption|exact Hrun].
Qed.

End Path.

Definition PA_of (s1 : asm_state 64) (i : asm.asm 64) (A : astate) : Prop :=
  amem A = s1.(mem) /\ apc A IN all_pcs (LENGTH (arm8_enc i)) s1.(pc) 2.

Definition QA_of (s2 : asm_state 64) (A : astate) : Prop :=
  apc A = s2.(pc) /\ (forall a, a IN s2.(mem_domain) -> amem A a = s2.(mem) a) /\
  (forall r, r < 32 -> ~ list.MEM r [18; 26; 31] -> aregs A (n2w r) = s2.(regs) r).

Definition A0_of (s1 : asm_state 64) (ms : arm8_state) : astate :=
  mk_astate (arm8_state_REG ms) s1.(pc) s1.(mem) (flags_of (arm8_state_PSTATE ms)).

Lemma enc_sim s1 i s2 ms (l : list instruction) :
  asm_step arm8_config s1 i s2 -> target_state_rel arm8_target s1 ms -> l <> [] ->
  run_ok s1.(mem_domain) (A0_of s1 ms) l (PA_of s1 i) -> QA_of s2 (arun (A0_of s1 ms) l) ->
  exists n, forall env,
    interference_ok env (proj arm8_target s1.(mem_domain)) ->
    let pcs := all_pcs (LENGTH (encode (config arm8_target) i)) s1.(pc) in
    asserts n (fun k s => env (n - k) (next arm8_target s)) ms
      (fun ms' => state_ok arm8_target ms' /\
         (forall pc0, pc0 IN pcs 0 -> get_byte arm8_target ms' pc0 = get_byte arm8_target ms pc0) /\
         get_pc arm8_target ms' IN pcs (code_alignment (config arm8_target)))
      (fun ms' => target_state_rel arm8_target s2 ms') /\
    asserts2 (n + 1) (fun k => env (n + 1 - k)) (next arm8_target) ms
      (fun ms1 ms2 => forall x, x NOTIN s1.(mem_domain) ->
         get_byte arm8_target ms1 x = get_byte arm8_target ms2 x).
Proof.
  intros Hstep Hrel Hne Hrun HQA.
  pose proof Hstep as (Hb & _ & _ & _ & Hasm & _ & _).
  assert (Hr0 : rv_rel s1.(mem_domain) ms (A0_of s1 ms)).
  { destruct Hrel as (Hok & Hpc & Hm & _). split; [exact Hok|split; [reflexivity|split; [exact Hpc|split; [|reflexivity]]]].
    intros a Ha; apply Hm, Ha. }
  assert (Hdom : s2.(mem_domain) = s1.(mem_domain)) by (rewrite <- Hasm; apply asm_consts).
  exists (LENGTH l - 1). intros env Henv. cbv zeta.
  unfold arm8_target in *; cbn [config next get_byte state_ok get_pc proj] in *.
  split.
  - refine (path_asserts s1.(mem_domain) env Henv _ _ (PA_of s1 i) (QA_of s2) _ _ l ms (A0_of s1 ms) _ Hne Hr0 Hrun HQA).
    + intros ms' A' (Hok & Hg & Hpc & Hm & _) (HmA & HpcA). cbv beta. split; [exact Hok|split].
      * intros pc0 Hpc0. assert (Hd : pc0 IN s1.(mem_domain)).
        { apply (bytes_in_memory_all_pcs _ _ 0 _ _ Hb), Hpc0. }
        rewrite Hm by exact Hd. rewrite HmA.
        destruct Hrel as (_ & _ & Hm0 & _). symmetry; apply Hm0, Hd.
      * rewrite Hpc. exact HpcA.
    + intros ms' A' (Hok & Hg & Hpc & Hm & _) (HpcA & HmA & HrA).
      unfold target_state_rel; cbn [config next get_byte state_ok get_pc get_reg get_fp_reg proj
        reg_count avoid_regs fp_reg_count arm8_config]; cbv beta.
      split; [exact Hok|split; [rewrite Hpc; exact HpcA|split; [|split]]].
      * intros ad Had. cbn. rewrite Hm by (rewrite <- Hdom; exact Had). apply HmA, Had.
      * intros r (Hr & Hav). cbn in Hr, Hav |- *. rewrite Hg. apply HrA; assumption.
      * intros r Hr. cbn in Hr. lia.
  - replace (LENGTH l - 1 + 1) with (LENGTH l) by (destruct l; [congruence|cbn [LENGTH]; lia]).
    refine (path_asserts2 s1.(mem_domain) env Henv l ms (A0_of s1 ms) _ Hr0 _).
    apply run_ok_ok2 with (PA_of s1 i). exact Hrun.
Qed.


(** ** From a simulating path to [encoder_correct]'s obligation (Galette-only) *)

Definition nonmem (i : instruction) : bool :=
  match i with LoadStore _ | Branch _ => false | _ => true end.

Lemma nonmem_props i A : supported i -> nonmem i = true ->
  apc (aexec i A) = word_add (apc A) (n2w 4) /\ amem (aexec i A) = amem A /\ mem_ok i A /\ (forall dom, acc_ok dom i A).
Proof.
  destruct A as [g pc m fl]; intros Hs Hn.
  inst_cases i; cbn [supported] in Hs; try contradiction; cbn [nonmem] in Hn; try discriminate Hn;
    cbv beta iota zeta in Hs; subst;
    cbn [aexec aregs apc amem aflags mem_ok acc_ok];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [aregs apc amem aflags]; repeat split.
Qed.


Definition alu_ok (i : instruction) : Prop := supported i /\ nonmem i = true /\ exists w, Encode i = ARM8 w.

Lemma arm8_enc_flat i : arm8_enc i = FLAT (MAP arm8_encode (arm8_ast i)).
Proof. reflexivity. Qed.

Lemma LENGTH_arm8_encode i : LENGTH (arm8_encode i) = 4.
Proof. unfold arm8_encode. destruct (Encode i); reflexivity. Qed.

Lemma LENGTH_FLAT_encode l : LENGTH (FLAT (MAP arm8_encode l)) = 4 * LENGTH l.
Proof.
  induction l as [|i l IH]; [reflexivity|].
  cbn [MAP FLAT List.concat List.map]. rewrite LENGTH_app, IH, LENGTH_arm8_encode. cbn [LENGTH]. lia.
Qed.

Lemma aligned_add4 (pc : word64) k : aligned 2 pc = true -> aligned 2 (word_add pc (n2w (4 * k))) = true.
Proof.
  intros H. assert (Ha : aligned 2 (n2w (4 * k) : word64)).
  { apply alignment.MOD_0_aligned. change (2 ** 2) with 4. rewrite N.mul_comm. apply N.Div0.mod_mul. }
  rewrite (proj1 (alignment.aligned_add_sub 2 pc (n2w (4 * k)) Ha)). exact H.
Qed.

Lemma alu_run_gen s1 i dom : aligned 2 s1.(pc) = true ->
  forall l k A, l <> [] -> Forall alu_ok l ->
  bytes_in_memory (word_add s1.(pc) (n2w (4 * k))) (FLAT (MAP arm8_encode l)) s1.(mem) dom ->
  apc A = word_add s1.(pc) (n2w (4 * k)) -> amem A = s1.(mem) ->
  4 * k + 4 * LENGTH l <= LENGTH (arm8_enc i) ->
  run_ok dom A l (PA_of s1 i) /\ apc (arun A l) = word_add s1.(pc) (n2w (4 * (k + LENGTH l))) /\
  amem (arun A l) = s1.(mem).
Proof.
  intros Hal l; induction l as [|j l IH]; intros k A Hne Hall Hb Hpc Hm Hlen; [congruence|].
  inversion Hall as [|? ? Hj Hall']; subst. destruct Hj as (Hs & Hn & Henc).
  destruct (nonmem_props j A Hs Hn) as (Hpc' & Hm' & Hmo & Hacc).
  cbn [MAP FLAT List.concat List.map] in Hb. apply bytes_in_memory_APPEND in Hb as [Hb1 Hb2].
  rewrite LENGTH_arm8_encode, add_n2w_add in Hb2. replace (4 * k + 4) with (4 * (k + 1)) in Hb2 by lia.
  assert (Hst : step_pre dom A j).
  { split; [exact Hs|split; [exact Henc|split; [rewrite Hpc, Hm; exact Hb1|split; [exact Hmo|split; [apply Hacc|]]]]].
    rewrite Hpc', Hpc, add_n2w_add. replace (4 * k + 4) with (4 * (k + 1)) by lia. apply aligned_add4, Hal. }
  destruct l as [|j' l'].
  - cbn [run_ok arun LENGTH]. split; [exact Hst|]. rewrite Hpc', Hm', Hpc, add_n2w_add.
    split; [f_equal; f_equal; lia|exact Hm].
  - destruct (IH (k + 1) (aexec j A) ltac:(discriminate) Hall' Hb2) as (Hr & Hp & Hmm).
    + rewrite Hpc', Hpc, add_n2w_add. f_equal; f_equal; lia.
    + rewrite Hm'; exact Hm.
    + cbn [LENGTH] in *. lia.
    + cbn [run_ok arun LENGTH] in *. split; [split; [exact Hst|split; [|exact Hr]]|].
      * split; [rewrite Hm'; exact Hm|]. rewrite Hpc', Hpc, add_n2w_add.
        exists (k + 1). split; [f_equal; f_equal; change (2 ** 2) with 4; lia|].
        change (2 ** 2) with 4. cbn [LENGTH] in Hlen. lia.
      * split; [rewrite Hp; f_equal; f_equal; lia|exact Hmm].
Qed.

Lemma alu_run s1 i dom l A : aligned 2 s1.(pc) = true -> arm8_ast i = l -> l <> [] ->
  Forall alu_ok l -> bytes_in_memory s1.(pc) (arm8_enc i) s1.(mem) dom ->
  apc A = s1.(pc) -> amem A = s1.(mem) ->
  run_ok dom A l (PA_of s1 i) /\ apc (arun A l) = word_add s1.(pc) (n2w (LENGTH (arm8_enc i))) /\
  amem (arun A l) = s1.(mem).
Proof.
  intros Hal Hl Hne Hall Hb Hpc Hm.
  rewrite arm8_enc_flat, Hl in Hb |- *. rewrite LENGTH_FLAT_encode.
  rewrite <- (add_n2w_0 s1.(pc)) in Hb, Hpc. change 0 with (4 * 0) in Hb, Hpc.
  destruct (alu_run_gen s1 i dom Hal l 0 A Hne Hall Hb Hpc Hm) as (H1 & H2 & H3).
  - rewrite arm8_enc_flat, Hl, LENGTH_FLAT_encode. lia.
  - split; [exact H1|split; [rewrite H2; f_equal; f_equal; lia|exact H3]].
Qed.

Definition enc_goal s1 i s2 ms : Prop :=
  exists n, forall env,
    interference_ok env (proj arm8_target s1.(mem_domain)) ->
    let pcs := all_pcs (LENGTH (encode (config arm8_target) i)) s1.(pc) in
    asserts n (fun k s => env (n - k) (next arm8_target s)) ms
      (fun ms' => state_ok arm8_target ms' /\
         (forall pc0, pc0 IN pcs 0 -> get_byte arm8_target ms' pc0 = get_byte arm8_target ms pc0) /\
         get_pc arm8_target ms' IN pcs (code_alignment (config arm8_target)))
      (fun ms' => target_state_rel arm8_target s2 ms') /\
    asserts2 (n + 1) (fun k => env (n + 1 - k)) (next arm8_target) ms
      (fun ms1 ms2 => forall x, x NOTIN s1.(mem_domain) ->
         get_byte arm8_target ms1 x = get_byte arm8_target ms2 x).

Lemma n2w5_eq a b : a < 32 -> b < 32 -> ((n2w a : word5) = n2w b <-> a = b).
Proof.
  intros Ha Hb; split; [|intros ->; reflexivity]. intros H. apply (f_equal w2n) in H.
  rewrite !w2n_n2w in H. change (dimword 5) with 32 in H. rewrite !N.mod_small in H by assumption. exact H.
Qed.

Lemma rX_n2w g r : r < 31 -> rX g (n2w r) = g (n2w r).
Proof.
  intros H1. unfold rX. destruct (bool_decide _) eqn:E; [|reflexivity].
  apply bool_decide_spec, n2w5_eq in E; lia.
Qed.

Lemma rX_31 g : rX g (n2w 31) = n2w 0.
Proof. reflexivity. Qed.

Lemma wX_n2w r v g x : r < 31 -> x < 32 ->
  wX (n2w r) v g (n2w x) = if r =? x then v else g (n2w x).
Proof.
  intros H1 H3. unfold wX. destruct (bool_decide _) eqn:E.
  - apply bool_decide_spec, n2w5_eq in E; lia.
  - unfold UPDATE. destruct (decide _) as [D|D]; [apply n2w5_eq in D; [|lia|lia]|];
      destruct (N.eqb_spec r x); try reflexivity; try lia. subst. congruence.
Qed.

Lemma wX_31 v g : wX (n2w 31) v g = g.
Proof. reflexivity. Qed.

Lemma reg_ok_iff r : reg_ok r arm8_config = true <-> r < 32 /\ r <> 18 /\ r <> 26 /\ r <> 31.
Proof.
  unfold reg_ok; cbn [reg_count avoid_regs arm8_config]. rewrite Bool.andb_true_iff, Bool.negb_true_iff.
  cbn [list.MEM]. rewrite N.ltb_lt.
  unfold bool_decide; repeat (destruct (decide _)); cbn [orb]; split; intros; intuition (try discriminate; try lia).
Qed.

Lemma avoid_iff r : ~ (list.MEM r [18; 26; 31] = true) <-> r <> 18 /\ r <> 26 /\ r <> 31.
Proof.
  cbn [list.MEM]. unfold bool_decide; repeat (destruct (decide _)); cbn [orb]; split; intros; intuition (try discriminate; try lia).
Qed.

Lemma hyp_facts s1 i s2 ms :
  asm_step arm8_config s1 i s2 -> target_state_rel arm8_target s1 ms ->
  aligned 2 s1.(pc) = true /\ s1.(be) = false /\
  asmSem.asm i (word_add s1.(pc) (n2w (LENGTH (arm8_enc i)))) s1 = s2 /\ s2.(failed) = false /\
  asm_ok i arm8_config = true /\
  (forall r, r < 32 -> r <> 18 -> r <> 26 -> r <> 31 -> arm8_state_REG ms (n2w r) = s1.(regs) r).
Proof.
  intros (Hb & _ & Hbe & _ & Hasm & Hf & Hok) (Hrok & Hpc & _ & Hr & _).
  unfold arm8_target in *; cbn [state_ok get_pc get_reg config reg_count avoid_regs arm8_config] in *.
  split; [|split; [exact Hbe|split; [exact Hasm|split; [destruct (failed s2) eqn:E; [exfalso; apply Hf; reflexivity|reflexivity]|split; [exact Hok|]]]]].
  - apply arm8_ok_iff in Hrok as [_ Ha]. rewrite <- Hpc. exact Ha.
  - intros r H0 H1 H2 H3. apply (Hr r). split; [exact H0|]. apply avoid_iff. tauto.
Qed.

Lemma sim_alu s1 i s2 ms l :
  asm_step arm8_config s1 i s2 -> target_state_rel arm8_target s1 ms ->
  arm8_ast i = l -> l <> [] -> Forall alu_ok l ->
  s2.(pc) = word_add s1.(pc) (n2w (LENGTH (arm8_enc i))) -> s2.(mem) = s1.(mem) ->
  (forall r, r < 32 -> r <> 18 -> r <> 26 -> r <> 31 ->
     aregs (arun (A0_of s1 ms) l) (n2w r) = s2.(regs) r) ->
  enc_goal s1 i s2 ms.
Proof.
  intros Hs Hr Hl Hne Hall Hpc2 Hm Hregs.
  destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & _ & Hasm & _).
  pose proof Hs as (Hb & _).
  destruct (alu_run s1 i s1.(mem_domain) l (A0_of s1 ms) Hal Hl Hne Hall Hb eq_refl eq_refl)
    as (Hrun & Hpc & Hmem).
  apply (enc_sim s1 i s2 ms l Hs Hr Hne Hrun).
  split; [|split].
  - rewrite Hpc, Hpc2. reflexivity.
  - intros a Ha. rewrite Hmem, Hm. reflexivity.
  - intros r Hr0 Hav. apply avoid_iff in Hav as (H0 & H2 & H3). apply Hregs; assumption.
Qed.

Ltac eqb_simp :=
  repeat match goal with
  | |- context [N.eqb ?a ?a] => rewrite (N.eqb_refl a)
  | |- context [N.eqb ?a ?b] => rewrite (proj2 (N.eqb_neq a b)) by lia
  | |- context [N.eqb ?a ?b] => rewrite (proj2 (N.eqb_eq a b)) by lia
  end; cbv iota.

Ltac regs_simp :=
  repeat (first [ match goal with |- context [rX ?g (n2w 31)] => rewrite (rX_31 g) end
                | match goal with |- context [wX (n2w 31) ?v ?g] => rewrite (wX_31 v g) end
                | match goal with |- context [rX ?g (n2w ?r)] => rewrite (rX_n2w g r) by lia end
                | match goal with |- context [wX (n2w ?r) ?v ?g (n2w ?x)] => rewrite (wX_n2w r v g x) by lia end ];
          eqb_simp).


(** ** Flags of [AddWithCarry] (Galette-only) *)

(** ** Flags of [AddWithCarry] *)

Lemma bd_iff (P Q : Prop) `{Decision P} `{Decision Q} : (P <-> Q) -> bool_decide P = bool_decide Q.
Proof.
  intros Hi. destruct (bool_decide Q) eqn:E.
  - apply bdt, Hi. apply bool_decide_spec in E. exact E.
  - apply bdf. intros HP. apply Hi, (bdt Q) in HP. congruence.
Qed.

Lemma w2n_1comp (y : word64) : w2n (word_1comp y) = 2 ^ 64 - 1 - w2n y.
Proof.
  unfold word_1comp. rewrite w2n_n2w. change (dimword 64) with (2 ^ 64). pose proof (w2n_lt y) as H.
  change (dimword 64) with (2 ^ 64) in H. apply N.mod_small. lia.
Qed.

Lemma sub_as_add (x y : word64) : (n2w (w2n x + w2n (word_1comp y) + 1) : word64) = word_sub x y.
Proof.
  rewrite <- !lemmas.word_add_n2w, !n2w_w2n.
  rewrite <- lemmas.WORD_ADD_ASSOC, <- lemmas.WORD_NEG. reflexivity.
Qed.

Lemma w2i_1comp (y : word64) : w2i (word_1comp y) = (- w2i y - 1)%Z.
Proof.
  rewrite !w2i_msb_eq, !word_msb_Z, w2n_1comp. pose proof (w2n_lt y) as H. change (dimword 64) with (2 ^ 64) in *.
  change (words.INT_MIN 64) with (2 ^ 63).
  rewrite N2Z.inj_sub by (cbn; lia). rewrite N2Z.inj_sub by (cbn; lia).
  set (Y := Z.of_N (w2n y)). assert (0 <= Y < 2 ^ 64)%Z by (subst Y; cbn in *; lia).
  change (Z.of_N (2 ^ 64)) with (2 ^ 64)%Z. change (Z.of_N (2 ^ 63)) with (2 ^ 63)%Z. change (Z.of_N 1) with 1%Z.
  destruct (Z.leb_spec (2 ^ 63) (2 ^ 64 - 1 - Y)), (Z.leb_spec (2 ^ 63) Y); lia.
Qed.

Lemma awc_sub (x y : word64) : AddWithCarry (Nw:=64) (x, (word_1comp y, true)) =
  (word_sub x y, (word_msb (word_sub x y), (bool_decide (x = y), (negb (word_lo x y),
    negb (bool_decide (w2i (word_sub x y) = (w2i x - w2i y)%Z)))))).
Proof.
  unfold AddWithCarry. cbv zeta. rewrite sub_as_add. f_equal. f_equal. f_equal.
  - destruct (bool_decide (x = y)) eqn:E.
    + apply bool_decide_spec in E; subst. apply bdt. apply word_sub_eq_0. reflexivity.
    + apply bdf. intros E'. apply (proj1 (word_sub_eq_0 _ _)) in E'. rewrite (bdt _ E') in E. discriminate.
  - f_equal.
    + f_equal. rewrite lemmas.word_lo_w2n. pose proof (w2n_sub_cases x y) as E. rewrite w2n_1comp.
      pose proof (w2n_lt x); pose proof (w2n_lt y). change (dimword 64) with (2 ^ 64) in *.
      destruct (N.ltb_spec (w2n x) (w2n y)).
      * apply bdt. apply N2Z.inj. rewrite E. destruct (Z.ltb_spec (Z.of_N (w2n x) - Z.of_N (w2n y)) 0); [|lia].
        rewrite !N2Z.inj_add, N2Z.inj_sub, N2Z.inj_sub by (change (2 ** 64) with 18446744073709551616 in *; lia).
        change (Z.of_N (2 ** 64)) with 18446744073709551616%Z. change (Z.of_N 1) with 1%Z. lia.
      * apply bdf. intros E2. apply (f_equal Z.of_N) in E2. rewrite E in E2.
        rewrite !N2Z.inj_add, N2Z.inj_sub, N2Z.inj_sub in E2 by (change (2 ** 64) with 18446744073709551616 in *; lia).
        change (Z.of_N (2 ** 64)) with 18446744073709551616%Z in *. change (Z.of_N 1) with 1%Z in *.
        destruct (Z.ltb_spec (Z.of_N (w2n x) - Z.of_N (w2n y)) 0); lia.
    + f_equal. rewrite w2i_1comp. apply bd_iff. split; intros; lia.
Qed.

Lemma msb_w2i (w : word64) : word_msb w = (w2i w <? 0)%Z.
Proof.
  rewrite w2i_msb_eq. pose proof (w2n_lt w). change (dimword 64) with (2 ^ 64) in *.
  destruct (word_msb w); symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; cbn in *; lia.
Qed.

Lemma lt_flags (x y : word64) :
  negb (bool_decide (word_msb (word_sub x y) = negb (bool_decide (w2i (word_sub x y) = (w2i x - w2i y)%Z)))) = word_lt x y.
Proof.
  rewrite word_lt_Z. pose proof (sub_overflow x y) as Ho. rewrite !msb_w2i in *.
  pose proof (w2i_bounds x); pose proof (w2i_bounds y); pose proof (w2i_bounds (word_sub x y)).
  change (INT_MIN 64) with (-9223372036854775808)%Z in *. change (INT_MAX 64) with 9223372036854775807%Z in *.
  destruct (bool_decide (w2i (word_sub x y) = (w2i x - w2i y)%Z)) eqn:E.
  - apply bool_decide_spec in E. rewrite E. cbn [negb].
    destruct (Z.ltb_spec (w2i x - w2i y) 0), (Z.ltb_spec (w2i x) (w2i y)); try lia; reflexivity.
  - apply Bool.not_true_iff_false in E. rewrite bool_decide_spec in E. apply Ho in E as [E1 E2]. cbn [negb].
    destruct (Z.ltb_spec (w2i x) 0), (Z.ltb_spec (w2i y) 0), (Z.ltb_spec (w2i (word_sub x y)) 0),
      (Z.ltb_spec (w2i x) (w2i y)); try congruence; try lia; reflexivity.
Qed.

Lemma cond_EQ n z c v : ConditionTest (n2w 0, (n, (z, (c, v)))) = z.
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.
Lemma cond_NE n z c v : ConditionTest (n2w 1, (n, (z, (c, v)))) = negb z.
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.
Lemma cond_CS n z c v : ConditionTest (n2w 2, (n, (z, (c, v)))) = c.
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.
Lemma cond_CC n z c v : ConditionTest (n2w 3, (n, (z, (c, v)))) = negb c.
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.
Lemma cond_VC n z c v : ConditionTest (n2w 7, (n, (z, (c, v)))) = negb v.
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.
Lemma cond_GE n z c v : ConditionTest (n2w 10, (n, (z, (c, v)))) = bool_decide (n = v).
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.
Lemma cond_LT n z c v : ConditionTest (n2w 11, (n, (z, (c, v)))) = negb (bool_decide (n = v)).
Proof. destruct n, z, c, v; vm_compute; reflexivity. Qed.

Lemma awc_gen (x y : word64) c : AddWithCarry (Nw:=64) (x, (y, c)) =
  let s := w2n x + w2n y + (if c then 1 else 0) in
  (n2w s, (word_msb (n2w s : word64), (bool_decide ((n2w s : word64) = n2w 0), (2 ^ 64 <=? s,
     negb (bool_decide (w2i (n2w s : word64) = (w2i x + w2i y + if c then 1 else 0)%Z)))))).
Proof.
  unfold AddWithCarry; cbv zeta. f_equal. f_equal. f_equal. f_equal. f_equal.
  pose proof (w2n_lt x); pose proof (w2n_lt y). change (dimword 64) with (2 ^ 64) in *.
  rewrite w2n_n2w. change (dimword 64) with (2 ^ 64).
  destruct (N.leb_spec (2 ^ 64) (w2n x + w2n y + (if c then 1 else 0))).
  - rewrite bdf; [reflexivity|]. intros E. rewrite N.Div0.mod_eq in E.
    assert (1 <= (w2n x + w2n y + (if c then 1 else 0)) / 2 ^ 64) by (apply N.div_le_lower_bound; cbn in *; lia).
    lia.
  - rewrite bdt; [reflexivity|]. apply N.mod_small. exact H1.
Qed.

Lemma awc_add (x y : word64) : fst (AddWithCarry (Nw:=64) (x, (y, false))) = word_add x y.
Proof. unfold AddWithCarry; cbn [fst]. rewrite N.add_0_r. reflexivity. Qed.

Lemma awc_add_V (x y : word64) : snd (snd (snd (snd (AddWithCarry (Nw:=64) (x, (y, false)))))) =
  negb (Z.eqb (w2i (word_add x y)) (w2i x + w2i y)).
Proof.
  unfold AddWithCarry; cbn [fst snd]. rewrite N.add_0_r, Z.add_0_r. f_equal.
  destruct (Z.eqb_spec (w2i (word_add x y)) (w2i x + w2i y)) as [E|E]; [apply bdt|apply bdf]; exact E.
Qed.


(** ** Shifts, [ror], [mul_long] and [Decode_EncodeBitMask] *)

(** Reflection of a check over the 64 bit positions. *)
Fixpoint all_below (n : nat) (f : N -> bool) : bool :=
  match n with O => true | Datatypes.S m => f (N.of_nat m) && all_below m f end.

Lemma all_below_spec n f : all_below n f = true -> forall i, i < N.of_nat n -> f i = true.
Proof.
  induction n as [|m IH]; intros H i Hi; [lia|]. cbn [all_below] in H. apply Bool.andb_true_iff in H as [H1 H2].
  destruct (N.eq_dec i (N.of_nat m)) as [->|Hne]; [exact H1|]. apply IH; [exact H2|lia].
Qed.

Definition lsl_chk (T W : word64) (k n : N) : bool :=
  all_below 64 (fun i => Bool.eqb (word_bit i (word_and T W)) (n <=? i) && (if n <=? i then (i + k) mod 64 =? i - n else true)).

Lemma lsl_from_chk T W k n (x : word64) : lsl_chk T W k n = true ->
  word_and (word_and T W) (word_ror x k) = word_lsl x n.
Proof.
  intros H. apply word_bit_ext; intros i Hi. change (dimindex 64) with 64 in Hi.
  pose proof (all_below_spec _ _ H i Hi) as Hc. cbv beta in Hc. apply Bool.andb_true_iff in Hc as [H1 H2].
  apply Bool.eqb_prop in H1.
  rewrite !wb_fcp by exact Hi. rewrite (wb_and _ (word_ror x k)), H1, wb_ror, wb_lsl. change (dimindex 64) with 64.
  destruct (N.ltb_spec i 64); [|lia]. destruct (N.leb_spec n i); cbn [andb]; [|reflexivity].
  apply N.eqb_eq in H2. rewrite H2. reflexivity.
Qed.

Definition lsr_chk (T W : word64) (n : N) : bool :=
  all_below 64 (fun i => Bool.eqb (word_bit i (word_and T W)) (i + n <? 64) && (if i + n <? 64 then (i + n) mod 64 =? i + n else true)).

Lemma lsr_from_chk T W n (x : word64) : lsr_chk T W n = true ->
  word_and (word_and T W) (word_ror x n) = word_lsr x n.
Proof.
  intros H. apply word_bit_ext; intros i Hi. change (dimindex 64) with 64 in Hi.
  pose proof (all_below_spec _ _ H i Hi) as Hc. cbv beta in Hc. apply Bool.andb_true_iff in Hc as [H1 H2].
  apply Bool.eqb_prop in H1.
  rewrite !wb_fcp by exact Hi. rewrite (wb_and _ (word_ror x n)), H1, wb_ror, wb_lsr. change (dimindex 64) with 64.
  destruct (N.ltb_spec i 64); [|lia]. destruct (N.ltb_spec (i + n) 64); cbn [andb].
  - apply N.eqb_eq in H2. rewrite H2. reflexivity.
  - symmetry. apply wb_high. change (dimindex 64) with 64. lia.
Qed.

Ltac dbm_lit H :=
  match type of H with DecodeBitMasks ?args = Some (?wm, ?tm) =>
    let v := eval vm_compute in (match DecodeBitMasks (Mw:=64) args with Some (a, b) => (w2n a, w2n b) | None => (0, 0) end) in
    lazymatch v with (?A, ?B) =>
      let E := fresh in
      assert (E : DecodeBitMasks (Mw:=64) args = Some (n2w A, n2w B))
        by (vm_compute; f_equal; f_equal; apply word_eq_w2n; reflexivity);
      rewrite E in H; injection H as <- <-; clear E
    end
  end.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "lsl" *)
Theorem lsl : forall (r q : word6) n (x wmask tmask : word64),
  n < 64 /\ Abbrev (r = n2w ((64 - n) mod 64)) /\ Abbrev (q = word_add r (n2w 63)) /\
  DecodeBitMasks (Mw:=64) (n2w 1, (q, (r, false))) = Some (wmask, tmask) ->
  word_and (word_and tmask wmask) (word_ror x (w2n r)) = word_lsl x n.
Proof.
  intros r q n x wmask tmask (Hn & Hr & Hq & Hd). unfold Abbrev in *. subst q r.
  apply lsl_from_chk. revert Hd.
  idx_cases Hn ltac:(intros Hd; dbm_lit Hd; vm_compute; reflexivity).
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "lsr" *)
Theorem lsr : forall n (x wmask tmask : word64),
  n < 64 /\ DecodeBitMasks (Mw:=64) (n2w 1, (n2w 63, (n2w n, false))) = Some (wmask, tmask) ->
  word_and (word_and tmask wmask) (word_ror x n) = word_lsr x n.
Proof.
  intros n x wmask tmask (Hn & Hd). apply lsr_from_chk. revert Hd.
  idx_cases Hn ltac:(intros Hd; dbm_lit Hd; vm_compute; reflexivity).
Qed.

(** HOL's statement has an unused variable [x] of a free type ['a],
    which is the type parameter [A] here. *)
(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "asr2" *)
Theorem asr2 {A : Type} : forall n (x : A) (wmask tmask : word64),
  n < 64 /\ DecodeBitMasks (Mw:=64) (n2w 1, (n2w 63, (n2w n, false))) = Some (wmask, tmask) ->
  (n2w (18446744073709551616 - 2 ^ (64 - MIN n 64)) : word64) = word_and (n2w 0xFFFFFFFFFFFFFFFF) (word_1comp tmask).
Proof.
  intros n x wmask tmask (Hn & Hd). revert Hd.
  idx_cases Hn ltac:(intros Hd; dbm_lit Hd; apply word_eq_w2n; vm_compute; reflexivity).
Qed.

Lemma testbit_pow_diff k i : k <= 64 ->
  N.testbit (2 ^ 64 - 2 ^ k) i = (k <=? i) && (i <? 64).
Proof.
  intros Hk. replace (2 ^ 64 - 2 ^ k) with ((2 ^ (64 - k) - 1) * 2 ^ k).
  2:{ rewrite N.mul_sub_distr_r, <- N.pow_add_r, N.mul_1_l. replace (64 - k + k) with 64 by lia. reflexivity. }
  destruct (N.leb_spec k i).
  - replace i with ((i - k) + k) at 1 by lia. rewrite N.mul_pow2_bits_add, testbit_ones.
    destruct (N.ltb_spec (i - k) (64 - k)), (N.ltb_spec i 64); try lia; reflexivity.
  - apply N.mul_pow2_bits_low. lia.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "asr" *)
Theorem asr : forall n (w : word64),
  word_asr w n =
  if word_bit 63 w then word_or (n2w (dimword 64 - 2 ^ (dimindex 64 - MIN n (dimindex 64)))) (word_lsr w n)
  else word_lsr w n.
Proof.
  intros n w. change (dimindex 64) with 64. change (dimword 64) with (2 ^ 64).
  apply word_bit_ext; intros i Hi. change (dimindex 64) with 64 in Hi. rewrite !wb_fcp by (destruct (word_bit 63 w); exact Hi).
  rewrite wb_asr. change (dimindex 64) with 64. change (64 - 1) with 63. destruct (N.ltb_spec i 64); [|lia]. cbn [andb].
  destruct (word_bit 63 w) eqn:E.
  - rewrite wb_or, wb_lsr, wb_n2w_lit. change (dimindex 64) with 64.
    rewrite testbit_pow_diff by (unfold MIN; destruct (N.ltb_spec n 64); lia).
    destruct (N.ltb_spec i 64); [|lia]. cbn [andb].
    unfold MIN. destruct (N.ltb_spec n 64), (N.ltb_spec (i + n) 64), (N.leb_spec (64 - n) i), (N.leb_spec (64 - 64) i);
      cbn [orb andb]; try rewrite E; try reflexivity; try lia.
  - rewrite wb_lsr. change (dimindex 64) with 64. destruct (N.ltb_spec i 64); [|lia]. cbn [andb].
    destruct (N.ltb_spec (i + n) 64); [reflexivity|].
    symmetry. apply wb_high. change (dimindex 64) with 64. lia.
Qed.

Lemma testbit_shiftr i (L : list bool) m : m <= LENGTH L -> testbit i (shiftr L m) = testbit (i + m) L.
Proof.
  intros Hm. pose proof (LENGTH_length L) as EL0.
  assert (Hlen : LENGTH (TAKE (LENGTH L - m) L) = LENGTH L - m).
  { rewrite LENGTH_length, TAKE_firstn, List.length_firstn. lia. }
  unfold testbit, shiftr. rewrite Hlen. cbv zeta.
  destruct (N.ltb_spec i (LENGTH L - m)) as [H1|H1].
  2:{ destruct (N.ltb_spec (i + m) (LENGTH L)); [lia|reflexivity]. }
  destruct (N.ltb_spec (i + m) (LENGTH L)); [|lia]. cbn [andb].
  rewrite !EL_nth by lia. rewrite TAKE_firstn, List.nth_firstn.
  destruct (Nat.ltb_spec (N.to_nat (LENGTH L - m - 1 - i)) (N.to_nat (LENGTH L - m))); [|lia].
  f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "ror" *)
Theorem ror : forall (w : word64) n,
  n < 64 -> (v2w (shiftr (w2v w ++ w2v w) n) : word64) = word_ror w n.
Proof.
  intros w n Hn. apply word_bit_ext; intros i Hi. change (dimindex 64) with 64 in Hi.
  rewrite !wb_fcp by exact Hi. rewrite wb_v2w, wb_ror.
  rewrite testbit_shiftr by (rewrite LENGTH_app, LENGTH_w2v; change (dimindex 64) with 64; lia).
  rewrite testbit_app, LENGTH_w2v, !testbit_w2v. change (dimindex 64) with 64.
  destruct (N.ltb_spec i 64); [|lia]. cbn [andb].
  destruct (N.ltb_spec (i + n) 64).
  - rewrite N.mod_small by lia. reflexivity.
  - replace ((i + n) mod 64) with (i + n - 64); [reflexivity|].
    apply N.mod_unique with 1; lia.
Qed.

Lemma w2n_mul128 (a b : word64) : w2n (word_mul (w2w a : word 128) (w2w b)) = w2n a * w2n b.
Proof.
  unfold word_mul. rewrite w2n_n2w, !w2n_w2w. change (dimindex 64 <=? dimindex 128) with true. cbv iota.
  pose proof (w2n_lt a); pose proof (w2n_lt b). change (dimword 64) with (2 ^ 64) in *.
  change (dimword 128) with (2 ^ 64 * 2 ^ 64). apply N.mod_small. apply N.mul_lt_mono; assumption.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "mul_long" *)
Theorem mul_long : forall a b : word64,
  n2w ((w2n a * w2n b) / 18446744073709551616) = (word_extract 127 64 (word_mul (w2w a : word 128) (w2w b)) : word64).
Proof.
  intros a b. apply word_bit_ext; intros j Hj. change (dimindex 64) with 64 in Hj.
  rewrite fcp_index_n2w by exact Hj. rewrite BIT_testbit.
  rewrite wb_fcp by exact Hj. rewrite wb_extract, word_bit_alt, fcp_index_testbit, w2n_mul128.
  change 18446744073709551616 with (2 ^ 64). rewrite N.div_pow2_bits.
  change (dimindex 64) with 64; change (dimindex 128) with 128.
  destruct (N.ltb_spec j 64), (N.leb_spec (j + 64) 127), (N.ltb_spec (j + 64) 128); try lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "Decode_EncodeBitMask" *)
Theorem Decode_EncodeBitMask :
  (forall (w : word32) n s r, EncodeBitMask w = Some (n, (s, r)) ->
     exists v, DecodeBitMasks (Mw:=32) (n, (s, (r, true))) = Some (w, v)) /\
  (forall (w : word64) n s r, EncodeBitMask w = Some (n, (s, r)) ->
     exists v, DecodeBitMasks (Mw:=64) (n, (s, (r, true))) = Some (w, v)).
Proof.
  split; intros w n s r; unfold EncodeBitMask; destruct (EncodeBitMaskAux w) as [e [S' R]];
    set (p := if bool_decide (e = 64) then _ else _); destruct p as [immN [imms immr]];
    destruct (DecodeBitMasks _) as [[imm2 v2]|] eqn:E; try discriminate;
    destruct (bool_decide (w = imm2)) eqn:Ew; try discriminate; apply bool_decide_spec in Ew; subst;
    intros H; injection H as <- <- <-; exists v2; exact E.
Qed.


(** ** Skip, constants and register binops (Galette-only) *)

Ltac pos_simp :=
  repeat match goal with |- context [w2n (@word_concat ?a ?b ?c (@n2w ?a ?k) (@n2w ?b 0))] =>
    let v := eval vm_compute in (w2n (@word_concat a b c (@n2w a k) (@n2w b 0))) in
    change (w2n (@word_concat a b c (@n2w a k) (@n2w b 0))) with v end.

Lemma bfi_mov_imm (i : word64) imm16 hw : arm8_enc_mov_imm i = Some (imm16, hw) ->
  bit_field_insert (w2n (word_concat hw (n2w 0 : word4) : word6) + 15) (w2n (word_concat hw (n2w 0 : word4) : word6))
    imm16 (n2w 0 : word64) = i.
Proof.
  unfold arm8_enc_mov_imm. intros H.
  repeat match type of H with (if bool_decide ?P then _ else _) = _ =>
    let E := fresh "E" in destruct (bool_decide P) eqn:E; [apply bool_decide_spec in E|] end; try discriminate H;
  injection H as <- <-; pos_simp; match goal with E : word_and _ _ = n2w 0 |- _ => wblast_and E end.
Qed.

Lemma movk4 (i x : word64) :
  bit_field_insert (w2n (word_concat (n2w 3 : word2) (n2w 0 : word4) : word6) + 15) (w2n (word_concat (n2w 3 : word2) (n2w 0 : word4) : word6)) (word_extract 63 48 i : word16)
  (bit_field_insert (w2n (word_concat (n2w 2 : word2) (n2w 0 : word4) : word6) + 15) (w2n (word_concat (n2w 2 : word2) (n2w 0 : word4) : word6)) (word_extract 47 32 i : word16)
  (bit_field_insert (w2n (word_concat (n2w 1 : word2) (n2w 0 : word4) : word6) + 15) (w2n (word_concat (n2w 1 : word2) (n2w 0 : word4) : word6)) (word_extract 31 16 i : word16)
  (bit_field_insert (w2n (word_concat (n2w 0 : word2) (n2w 0 : word4) : word6) + 15) (w2n (word_concat (n2w 0 : word2) (n2w 0 : word4) : word6)) (word_extract 15 0 i : word16) x))) = i.
Proof. pos_simp. wblast. Qed.

Lemma dec_eqb {A} (a b : N) (x y : A) : (if decide (a = b) then x else y) = (if a =? b then x else y).
Proof. destruct (decide (a = b)), (N.eqb_spec a b); congruence. Qed.

Ltac fin_regs Hg :=
  unfold UPDATE; rewrite ?dec_eqb; eqb_simp;
  repeat (match goal with
  | |- context [N.eqb ?a ?b] => destruct (N.eqb_spec a b); [first [subst a | subst b | idtac]|]
  end; eqb_simp); try lia; rewrite ?Hg by lia;
  try (lazymatch goal with
       | |- ?x = ?x => reflexivity
       | |- context [aload] => fail
       | |- context [astore] => fail
       | _ => reflexivity end).

Ltac and_facts H :=
  repeat match type of H with
  | (_ && _)%bool = true => apply Bool.andb_true_iff in H; let H1 := fresh "Hok" in destruct H as [H1 H]; and_facts H1
  | reg_ok _ _ = true => apply reg_ok_iff in H
  end.

Lemma nbd_true (P : Prop) `{Decision P} : negb (bool_decide P) = true -> ~ P.
Proof. intros H1 H2. apply (proj2 (bool_decide_spec P)) in H2. rewrite H2 in H1. discriminate. Qed.

Ltac neq_facts :=
  repeat match goal with
  | H : negb (bool_decide _) = true |- _ => apply nbd_true in H
  | H : true = true |- _ => clear H
  end.

Ltac isa_simp H :=
  repeat match type of H with
  | context [bool_decide (ISA arm8_config = ?y)] =>
      let v := eval vm_compute in (bool_decide (ISA arm8_config = y)) in
      change (bool_decide (ISA arm8_config = y)) with v in H
  | context [list.MEM (ISA arm8_config) ?l] =>
      let v := eval vm_compute in (list.MEM (ISA arm8_config) l) in
      change (list.MEM (ISA arm8_config) l) with v in H
  | context [ISA arm8_config] => change (ISA arm8_config) with ARMv8 in H
  end; cbn [implb orb andb] in H.

Ltac asm_unfold :=
  cbn [arun aexec aregs apc amem aflags A0_of asmSem.asm inst arith_upd binop_upd upd_reg upd_pc
       set_regs set_pc regs read_reg reg_imm word_shift assert set_failed fst snd].

Ltac supp_tac :=
  cbn [supported]; repeat split; try reflexivity; try discriminate;
  try (left; reflexivity); try (right; reflexivity); try (left; intros E; apply n2w5_eq in E; lia);
  try (intros E; apply n2w5_eq in E; lia).

Ltac alu_ok1 enc := split; [supp_tac|split; [reflexivity|enc]].
Ltac alu_ok_tac enc := repeat (apply Forall_cons; [alu_ok1 enc|]); apply Forall_nil.
Ltac enc_refl := eexists; reflexivity.

Lemma sim_skip s1 s2 ms :
  asm_step arm8_config s1 (Inst Skip) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst Skip) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  apply sim_alu with [NoOperation]; [exact Hs|exact Hr|reflexivity|discriminate|alu_ok_tac enc_refl| | |].
  - rewrite <- Hasm. reflexivity.
  - rewrite <- Hasm. reflexivity.
  - intros r H0 H1 H2 H3. rewrite <- Hasm. cbn [arun aexec aregs A0_of NoOperation]. apply Hg; assumption.
Qed.

Lemma sim_const s1 s2 ms r i :
  asm_step arm8_config s1 (Inst (Const r i)) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Const r i)) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok] in Hok. apply reg_ok_iff in Hok.
  destruct (arm8_enc_mov_imm i) as [[imm16 hw]|] eqn:E1.
  { apply sim_alu with [Data (MoveWide_64 (n2w 1, (MoveWideOp_Z, (hw, (imm16, n2w r)))))];
      [exact Hs|exact Hr|cbn [arm8_ast]; rewrite E1; reflexivity|discriminate|alu_ok_tac enc_refl
      |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r' H0 H1 H2 H3; rewrite <- Hasm; asm_unfold. repeat dec_closed. regs_simp.
    rewrite (bfi_mov_imm _ _ _ E1). fin_regs Hg. }
  destruct (arm8_enc_mov_imm (word_1comp i)) as [[imm16 hw]|] eqn:E2.
  { apply sim_alu with [Data (MoveWide_64 (n2w 1, (MoveWideOp_N, (hw, (imm16, n2w r)))))];
      [exact Hs|exact Hr|cbn [arm8_ast]; rewrite E1, E2; reflexivity|discriminate|alu_ok_tac enc_refl
      |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r' H0 H1 H2 H3; rewrite <- Hasm; asm_unfold. repeat dec_closed. regs_simp.
    rewrite (bfi_mov_imm _ _ _ E2), lemmas.WORD_NOT_NOT. fin_regs Hg. }
  destruct (EncodeBitMask i) as [[N' [imms immr]]|] eqn:E3.
  { apply sim_alu with [Data (LogicalImmediate_64 (n2w 1, (LogicalOp_ORR, (false, (i, (n2w 31, n2w r))))))];
      [exact Hs|exact Hr|cbn [arm8_ast]; rewrite E1, E2, E3; reflexivity|discriminate|
       alu_ok_tac ltac:(eexists; cbn [Encode e_data]; rewrite E3; reflexivity)
      |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r' H0 H1 H2 H3; rewrite <- Hasm; asm_unfold. cbn [logop]. regs_simp.
    rewrite (proj1 (proj2 (proj2 (lemmas.WORD_OR_CLAUSES _)))). fin_regs Hg. }
  apply sim_alu with [Data (MoveWide_64 (n2w 1, (MoveWideOp_K, (n2w 0, (word_extract 15 0 i, n2w r)))));
                      Data (MoveWide_64 (n2w 1, (MoveWideOp_K, (n2w 1, (word_extract 31 16 i, n2w r)))));
                      Data (MoveWide_64 (n2w 1, (MoveWideOp_K, (n2w 2, (word_extract 47 32 i, n2w r)))));
                      Data (MoveWide_64 (n2w 1, (MoveWideOp_K, (n2w 3, (word_extract 63 48 i, n2w r)))))];
    [exact Hs|exact Hr|cbn [arm8_ast]; rewrite E1, E2, E3; reflexivity|discriminate|alu_ok_tac enc_refl
    |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r' H0 H1 H2 H3; rewrite <- Hasm; asm_unfold. repeat dec_closed. regs_simp.
  rewrite movk4. fin_regs Hg.
Qed.

Ltac val_simp :=
  cbn [ShiftValue logop bop_enc fst snd]; gclosed; rewrite ?lsl_0, ?awc_sub, ?awc_add; cbn [fst snd].

Lemma sim_binop_reg s1 s2 ms b r1 r2 r3 :
  asm_step arm8_config s1 (Inst (Arith (Binop b r1 r2 (Reg r3)))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (Binop b r1 r2 (Reg r3)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok reg_imm_ok two_reg_arith arm8_config implb] in Hok. and_facts Hok.
  destruct b.
  all: eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  all: intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp; fin_regs Hg.
Qed.


(** ** Immediate binops (Galette-only) *)

Lemma bdf' (P : Prop) (d : Decision P) : ~ P -> @bool_decide P d = false.
Proof. intros Hn. apply Bool.not_true_iff_false. rewrite bool_decide_spec. exact Hn. Qed.
Lemma bdt' (P : Prop) (d : Decision P) : P -> @bool_decide P d = true.
Proof. intros Hp. apply bool_decide_spec. exact Hp. Qed.

Lemma bd_Zeq (x y : Z) : bool_decide (x = y) = Z.eqb x y.
Proof. destruct (Z.eqb_spec x y); [apply bdt|apply bdf]; assumption. Qed.

Lemma awc_add_full (x y : word64) : AddWithCarry (Nw:=64) (x, (y, false)) =
  (word_add x y, (word_msb (word_add x y), (bool_decide (word_add x y = n2w 0), (2 ^ 64 <=? w2n x + w2n y,
    negb (Z.eqb (w2i (word_add x y)) (w2i x + w2i y)))))).
Proof.
  rewrite awc_gen. cbv zeta. rewrite N.add_0_r, Z.add_0_r, bd_Zeq. reflexivity.
Qed.

Lemma vimm_addsub (b : binop) (i : word64) : (b = Add \/ b = Sub) -> valid_immediate (inl b) i = true ->
  word_and i (word_1comp (n2w 4095)) = n2w 0 \/ word_and i (word_1comp (n2w 16773120)) = n2w 0.
Proof.
  intros Hb. unfold valid_immediate. rewrite bdt by (destruct Hb as [-> | ->]; cbv; tauto).
  rewrite Bool.orb_true_iff, !bool_decide_spec, !(lemmas.WORD_AND_COMM i). tauto.
Qed.

Lemma vimm_cmp c (i : word64) : c <> Test -> c <> NotTest -> valid_immediate (inr c) i = true ->
  word_and i (word_1comp (n2w 4095)) = n2w 0 \/ word_and i (word_1comp (n2w 16773120)) = n2w 0.
Proof.
  intros H1 H2. unfold valid_immediate. rewrite bdt by (destruct c; try congruence; cbv; tauto).
  rewrite Bool.orb_true_iff, !bool_decide_spec, !(lemmas.WORD_AND_COMM i). tauto.
Qed.

Lemma enc_addsubimm sub sf i n d : (word_and i (word_1comp (n2w 4095)) = n2w 0 \/ word_and i (word_1comp (n2w 16773120)) = n2w 0) ->
  exists w, Encode (Data (AddSubImmediate_64 (n2w 1, (sub, (sf, (i, (n, d))))))) = ARM8 w.
Proof.
  intros [H|H]; cbn [Encode e_data].
  - rewrite (bdt _ H). eexists; reflexivity.
  - destruct (bool_decide (word_and i _ = _)); [eexists; reflexivity|]. rewrite (bdt _ H). eexists; reflexivity.
Qed.

Lemma vimm_logic b (i : word64) : (b = And \/ b = Or \/ b = Xor) -> valid_immediate (inl b) i = true ->
  exists v, EncodeBitMask i = Some v.
Proof.
  intros Hb. unfold valid_immediate. rewrite bdf by (destruct Hb as [-> | [-> | ->]]; cbv; intuition discriminate).
  destruct (EncodeBitMask i); [eexists; reflexivity|discriminate].
Qed.

Lemma vimm_test c (i : word64) : (c = Test \/ c = NotTest) -> valid_immediate (inr c) i = true ->
  exists v, EncodeBitMask i = Some v.
Proof.
  intros Hb. unfold valid_immediate. rewrite bdf by (destruct Hb as [-> | ->]; cbv; intuition discriminate).
  destruct (EncodeBitMask i); [eexists; reflexivity|discriminate].
Qed.

Lemma enc_logimm opc sf i n d v : EncodeBitMask i = Some v -> EncodeLogicalOp (opc, sf) <> None ->
  exists w, Encode (Data (LogicalImmediate_64 (n2w 1, (opc, (sf, (i, (n, d))))))) = ARM8 w.
Proof.
  intros H Ho. cbn [Encode e_data]. rewrite H. destruct v as [? [? ?]].
  destruct (EncodeLogicalOp _); [eexists; reflexivity|congruence].
Qed.

Lemma xor_m1 (x : word64) : word_or (n2w 0) (word_1comp x) = word_xor x (word_2comp (n2w 1)).
Proof.
  replace (word_2comp (n2w 1) : word64) with (n2w 18446744073709551615 : word64) by (apply word_eq_w2n; vm_compute; reflexivity).
  wblast; destruct (word_bit _ x); reflexivity.
Qed.

Lemma sim_binop_imm s1 s2 ms b r1 r2 w :
  asm_step arm8_config s1 (Inst (Arith (Binop b r1 r2 (Imm w)))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (Binop b r1 r2 (Imm w)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok two_reg_arith arm8_config implb] in Hok.
  apply Bool.andb_true_iff in Hok as [Hok Himm]. and_facts Hok.
  cbn [reg_imm_ok valid_imm arm8_config] in Himm.
  destruct b;
    try (rewrite (bdf (inl _ = inl Xor)) in Himm by discriminate; cbn [andb orb] in Himm).
  - pose proof (vimm_addsub Add w ltac:(auto) Himm) as Hv.
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate
       |alu_ok_tac ltac:(apply enc_addsubimm; exact Hv)|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp; fin_regs Hg.
  - pose proof (vimm_addsub Sub w ltac:(auto) Himm) as Hv.
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate
       |alu_ok_tac ltac:(apply enc_addsubimm; exact Hv)|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp; fin_regs Hg.
  - destruct (vimm_logic And w ltac:(auto) Himm) as [v Hv].
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate
       |alu_ok_tac ltac:(eapply enc_logimm; [exact Hv|discriminate])|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp; fin_regs Hg.
  - destruct (vimm_logic Or w ltac:(auto) Himm) as [v Hv].
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate
       |alu_ok_tac ltac:(eapply enc_logimm; [exact Hv|discriminate])|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp; fin_regs Hg.
  - destruct (decide (w = word_2comp (n2w 1))) as [Ew|Ew].
    + subst w.
      eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; rewrite bdt' by reflexivity; reflexivity|discriminate
         |alu_ok_tac enc_refl|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
      intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp. rewrite xor_m1. fin_regs Hg.
    + rewrite (bdf' _ _ Ew), Bool.andb_false_r in Himm. cbn [orb] in Himm.
      destruct (vimm_logic Xor w ltac:(auto) Himm) as [v Hv].
      eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; rewrite (bdf' _ _ Ew); reflexivity|discriminate
         |alu_ok_tac ltac:(eapply enc_logimm; [exact Hv|discriminate])|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
      intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; val_simp; regs_simp; fin_regs Hg.
Qed.


(** ** Shifts by registers, division, long multiplication, carry and overflow (Galette-only) *)

Lemma sim_shift_reg s1 s2 ms sh r1 r2 r3 :
  asm_step arm8_config s1 (Inst (Arith (asm.Shift sh r1 r2 (Reg r3)))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (asm.Shift sh r1 r2 (Reg r3)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok two_reg_arith arm8_config implb] in Hok. and_facts Hok.
  assert (Hlt : w2n (s1.(regs) r3) < 64).
  { rewrite <- Hasm in Hf. cbn [asmSem.asm inst arith_upd assert set_failed upd_pc set_pc failed read_reg] in Hf.
    apply Bool.orb_false_iff in Hf as [Hf _]. apply Bool.negb_false_iff, N.ltb_lt in Hf. exact Hf. }
  eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp. rewrite !(Hg r3) by lia.
  rewrite (N.mod_small (w2n (regs s1 r3))) by exact Hlt.
  destruct sh; cbn [arm8_shv ShiftValue]; fin_regs Hg.
Qed.

Lemma sim_div s1 s2 ms r1 r2 r3 :
  asm_step arm8_config s1 (Inst (Arith (Div r1 r2 r3))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (Div r1 r2 r3))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok arm8_config] in Hok. and_facts Hok.
  assert (Hq : bool_decide (s1.(regs) r3 = n2w 0) = false).
  { rewrite <- Hasm in Hf. cbn [asmSem.asm inst arith_upd assert set_failed upd_pc set_pc failed read_reg] in Hf.
    apply Bool.orb_false_iff in Hf as [Hf _]. apply Bool.negb_false_iff, Bool.negb_true_iff in Hf. exact Hf. }
  eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp. rewrite !(Hg r3) by lia. rewrite Hq.
  fin_regs Hg.
Qed.

Lemma sim_longmul s1 s2 ms r1 r2 r3 r4 :
  asm_step arm8_config s1 (Inst (Arith (LongMul r1 r2 r3 r4))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (LongMul r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok arm8_config] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; rewrite ?ExtendWord_u; regs_simp.
  rewrite ?(proj2 lemmas.WORD_ADD_0). fin_regs Hg.
  all: first [ rewrite <- mul_long; change (dimword 64) with 18446744073709551616; reflexivity
             | unfold word_mul; reflexivity ].
Qed.

Lemma bfi_zero : bit_field_insert (0 + 15) 0 (n2w 0 : word16) (n2w 0 : word64) = n2w 0.
Proof. apply word_eq_w2n. vm_compute. reflexivity. Qed.

Lemma pos0 : w2n (word_concat (n2w 0 : word2) (n2w 0 : word4) : word6) = 0.
Proof. reflexivity. Qed.

Lemma carry0 (x : word64) : (2 ^ 64 <=? w2n x + w2n (n2w 0 : word64)) = false.
Proof. pose proof (w2n_lt x). change (dimword 64) with (2 ^ 64) in H. apply N.leb_gt. change (w2n (n2w 0 : word64)) with 0. lia. Qed.

Lemma carry0' (x : word64) : (2 ^ 64 <=? w2n x + w2n (n2w 0 : word64) + 0) = false.
Proof. rewrite N.add_0_r. apply carry0. Qed.

Lemma carry_val (c : bool) : (n2w (w2n (n2w 0 : word64) + w2n (n2w 0 : word64) + (if c then 1 else 0)) : word64) = (if c then n2w 1 else n2w 0 : word64).
Proof. destruct c; reflexivity. Qed.

Ltac flag_simp :=
  cbn [ShiftValue logop bop_enc fst snd]; gclosed; rewrite ?lsl_0;
  rewrite ?awc_sub, ?awc_add_full; cbn [fst snd];
  rewrite ?cond_EQ, ?cond_NE, ?cond_CS, ?cond_CC, ?cond_VC, ?cond_GE, ?cond_LT.

Lemma sim_addoverflow s1 s2 ms r1 r2 r3 r4 :
  asm_step arm8_config s1 (Inst (Arith (AddOverflow r1 r2 r3 r4))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (AddOverflow r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok arm8_config two_reg_arith] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; unfold read_reg; flag_simp; regs_simp.
  rewrite Bool.negb_involutive, (proj2 lemmas.WORD_ADD_0). fin_regs Hg.
  destruct (Z.eqb _ _); reflexivity.
Qed.

Lemma sim_suboverflow s1 s2 ms r1 r2 r3 r4 :
  asm_step arm8_config s1 (Inst (Arith (SubOverflow r1 r2 r3 r4))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (SubOverflow r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok arm8_config two_reg_arith] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; unfold read_reg; flag_simp; regs_simp.
  rewrite Bool.negb_involutive, (proj2 lemmas.WORD_ADD_0), bd_Zeq. fin_regs Hg.
  destruct (Z.eqb _ _); reflexivity.
Qed.

Lemma sim_addcarry s1 s2 ms r1 r2 r3 r4 :
  asm_step arm8_config s1 (Inst (Arith (AddCarry r1 r2 r3 r4))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (AddCarry r1 r2 r3 r4))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok arm8_config two_reg_arith] in Hok. isa_simp Hok. and_facts Hok. neq_facts.
  eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
  intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; unfold read_reg.
  repeat dec_closed. rewrite awc_sub. cbn [fst snd]. rewrite cond_EQ.
  rewrite pos0, bfi_zero. regs_simp. rewrite ?(@lemmas.WORD_SUB_RZERO 64). rewrite !awc_gen. cbv zeta. cbn [fst snd].
  rewrite ?carry0, ?carry_val. fin_regs Hg.
  all: match goal with |- context [bool_decide (regs ?s ?x = n2w 0)] => destruct (bool_decide (regs s x = n2w 0)) end;
       cbn [fst snd]; rewrite ?carry0'; change (dimword 64) with (2 ** 64); reflexivity.
Qed.


(** ** Shifts by immediates (Galette-only) *)

Lemma hsb7 (s : word6) : HighestSetBit (Nw:=7) (word_concat (n2w 1 : word1) (word_1comp s) : word7) = 6%Z.
Proof.
  rewrite <- (n2w_w2n s). pose proof (w2n_lt s) as Hk. change (dimword 6) with 64 in Hk.
  revert Hk. generalize (w2n s). intros k Hk. idx_cases Hk ltac:(vm_compute; reflexivity).
Qed.

Lemma dbm_some (s r : word6) : exists wm tm, DecodeBitMasks (Mw:=64) (n2w 1, (s, (r, false))) = Some (wm, tm).
Proof. unfold DecodeBitMasks. rewrite hsb7. cbv beta iota zeta. eexists; eexists; reflexivity. Qed.

Lemma bfm0 (tm wm x : word64) R :
  word_or (word_and (n2w 0) (word_1comp tm)) (word_and (word_or (word_and (n2w 0) (word_1comp wm)) (word_and (word_ror x R) wm)) tm) =
  word_and (word_and tm wm) (word_ror x R).
Proof.
  apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi.
  repeat (rewrite ?wb_or, ?wb_and); rewrite !wb_n2w_lit, N.bits_0, !Bool.andb_false_r. cbn [orb andb].
  destruct (word_bit i tm), (word_bit i wm), (word_bit i (word_ror x R)); reflexivity.
Qed.

Lemma rep64 (b : bool) : Replicate (Nw:=64) [b] = (if b then n2w 18446744073709551615 else n2w 0 : word64).
Proof. destruct b; apply word_eq_w2n; vm_compute; reflexivity. Qed.

Lemma bfm1 (b : bool) (tm wm x : word64) R :
  word_or (word_and (if b then n2w 18446744073709551615 else n2w 0 : word64) (word_1comp tm))
    (word_and (word_or (word_and (n2w 0) (word_1comp wm)) (word_and (word_ror x R) wm)) tm) =
  if b then word_or (word_and (n2w 18446744073709551615) (word_1comp tm)) (word_and (word_and tm wm) (word_ror x R))
  else word_and (word_and tm wm) (word_ror x R).
Proof.
  destruct b; [|apply bfm0]. apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi.
  repeat (rewrite ?wb_or, ?wb_and); rewrite !wb_n2w_lit, N.bits_0, !Bool.andb_false_r. cbn [orb andb].
  destruct (word_bit i tm), (word_bit i wm), (word_bit i (word_ror x R)), (word_bit i (word_1comp tm)); reflexivity.
Qed.

Lemma e_sf1 : e_sf (Nw:=64) (n2w 1) = (n2w 1 : word1).
Proof. apply word_eq_w2n; vm_compute; reflexivity. Qed.

Lemma enc_bfm ext wm tm R S' n d : R < 64 -> S' < 64 ->
  DecodeBitMasks (Mw:=64) (n2w 1, (n2w S', (n2w R, false))) = Some (wm, tm) ->
  exists w, Encode (Data (BitfieldMove_64 (n2w 1, (true, (ext, (wm, (tm, (R, (S', (n, d)))))))))) = ARM8 w.
Proof.
  intros HR HS HD. cbn [Encode e_data]. rewrite e_sf1. destruct ext; cbv beta iota zeta;
  rewrite (bdt' (R = w2n (n2w R : word6))) by (rewrite w2n_n2w; symmetry; apply N.mod_small; exact HR);
  rewrite (bdt' (S' = w2n (n2w S' : word6))) by (rewrite w2n_n2w; symmetry; apply N.mod_small; exact HS);
  rewrite (bdt' (DecodeBitMasks _ = _)) by exact HD; cbn [andb]; eexists; reflexivity.
Qed.

Lemma neg6 n : n < 64 -> word_2comp (n2w n : word6) = n2w ((64 - n) mod 64).
Proof.
  intros Hn. apply word_eq_w2n. unfold word_2comp. rewrite !w2n_n2w. change (dimword 6) with 64.
  rewrite (N.mod_small n 64) by exact Hn. rewrite N.Div0.mod_mod. reflexivity.
Qed.

Lemma sim_shift_imm s1 s2 ms sh r1 r2 w :
  asm_step arm8_config s1 (Inst (Arith (asm.Shift sh r1 r2 (Imm w)))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (Arith (asm.Shift sh r1 r2 (Imm w)))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok arith_ok two_reg_arith arm8_config implb] in Hok.
  apply Bool.andb_true_iff in Hok as [Hok Himm]. apply Bool.andb_true_iff in Himm as [Hz Hw].
  apply N.ltb_lt in Hw. change (dimindex 64) with 64 in Hw. and_facts Hok.
  set (n := w2n w) in *.
  destruct sh.
  - (* Lsl *)
    destruct (dbm_some (word_sub (n2w 63) (n2w n)) (word_2comp (n2w n))) as (wm & tm & E).
    assert (Hr6 : w2n (word_2comp (n2w n : word6)) < 64) by (pose proof (w2n_lt (word_2comp (n2w n : word6))); exact H).
    assert (Hs6 : w2n (word_sub (n2w 63) (n2w n : word6)) < 64) by (pose proof (w2n_lt (word_sub (n2w 63) (n2w n : word6))); exact H).
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; fold n; cbv zeta; rewrite E; reflexivity|discriminate
       |alu_ok_tac ltac:(apply enc_bfm; [exact Hr6|exact Hs6|rewrite !n2w_w2n; exact E])
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp. rewrite bfm0.
    rewrite (lsl _ (word_add (word_2comp (n2w n)) (n2w 63)) n _ wm tm).
    + fin_regs Hg.
    + split; [exact Hw|split; [unfold Abbrev; apply neg6, Hw|split; [unfold Abbrev; reflexivity|]]].
      replace (word_add (word_2comp (n2w n)) (n2w 63) : word6) with (word_sub (n2w 63) (n2w n) : word6)
        by (unfold word_sub; apply lemmas.WORD_ADD_COMM). exact E.
  - (* Lsr *)
    destruct (dbm_some (n2w 63) (n2w n)) as (wm & tm & E).
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; fold n; cbv zeta; rewrite E; reflexivity|discriminate
       |alu_ok_tac ltac:(apply enc_bfm; [exact Hw|lia|exact E])
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp. rewrite bfm0.
    rewrite (lsr n _ wm tm) by (split; [exact Hw|exact E]). fin_regs Hg.
  - (* Asr *)
    destruct (dbm_some (n2w 63) (n2w n)) as (wm & tm & E).
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; fold n; cbv zeta; rewrite E; reflexivity|discriminate
       |alu_ok_tac ltac:(apply enc_bfm; [exact Hw|lia|exact E])
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp. rewrite (bdt' (ast.Asr = ast.Asr)) by reflexivity. rewrite rep64, bfm1.
    rewrite (lsr n _ wm tm) by (split; [exact Hw|exact E]).
    rewrite <- (asr2 (A:=unit) n tt wm tm) by (split; [exact Hw|exact E]).
    rewrite (asr n). change (dimword 64) with 18446744073709551616. change (dimindex 64) with 64.
    fin_regs Hg.
  - (* Ror *)
    eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; reflexivity|discriminate|alu_ok_tac enc_refl
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp.
    rewrite (w2n_n2w n), (N.mod_small n) by (change (dimword 6) with 64; exact Hw).
    rewrite ror by exact Hw. fin_regs Hg.
Qed.


(** ** Jumps, calls and [Loc] (Galette-only) *)

Lemma word_le_w2i {a : N} (x y : word a) : word_le x y = true <-> (w2i x <= w2i y)%Z.
Proof. rewrite word_le_Z. apply Z.leb_le. Qed.

Lemma sw2sw_w2w_id {a b : N} (c : word a) :
  dimindex b <= dimindex a -> (INT_MIN b <= w2i c <= INT_MAX b)%Z ->
  (sw2sw (w2w c : word b) : word a) = c.
Proof.
  intros Hd Hr. replace (w2w c : word b) with (w2w (i2w (w2i c) : word a) : word b) by (rewrite i2w_w2i; reflexivity).
  rewrite (w2w_i2w (a := b) (b := a)) by exact Hd.
  rewrite sw2sw_i2w by (split; [lia|split; [lia|exact Hd]]). apply i2w_w2i.
Qed.

Lemma aligned_wb {a : N} p (w : word a) i : aligned p w = true -> i < p -> word_bit i w = false.
Proof.
  intros H Hi. apply alignment.aligned_bits with (i := i) in H; [|exact Hi].
  rewrite word_bit_alt, fcp_index_testbit, H. apply Bool.andb_false_r.
Qed.

Ltac al_bits Hal :=
  repeat match goal with |- context [word_bit ?k ?a] =>
    is_lit k; let H := fresh in assert (H : word_bit k a = false) by (apply (aligned_wb _ _ _ Hal); lia);
    rewrite H; clear H end.

Lemma br26 (a : word64) : (word_le jump_min a && word_le a jump_max)%bool = true -> aligned 2 a = true ->
  a = sw2sw (word_concat (word_extract 27 2 a : word 26) (n2w 0 : word2) : word 28).
Proof.
  intros H Hal. apply Bool.andb_true_iff in H as [H1 H2]. apply word_le_w2i in H1, H2.
  change (w2i jump_min) with (-134217728)%Z in H1. change (w2i jump_max) with 134217727%Z in H2.
  transitivity (sw2sw (w2w a : word 28) : word64); [symmetry; apply sw2sw_w2w_id; [vm_compute; discriminate|cbn; lia]|].
  f_equal. apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi. change (dimindex 28) with 28 in Hi.
  idx_cases Hi ltac:(wbs; al_bits Hal; reflexivity).
Qed.

Lemma aligned_add (x y : word64) k : aligned k x = true -> aligned k y = true -> aligned k (word_add x y) = true.
Proof. intros Hx Hy. rewrite (proj1 (alignment.aligned_add_sub k x y Hy)). exact Hx. Qed.

Lemma enc_bimm (a : word64) bt : (bt = BranchType_JMP \/ bt = BranchType_CALL) ->
  a = sw2sw (word_concat (word_extract 27 2 a : word 26) (n2w 0 : word2) : word 28) ->
  exists w, Encode (Branch (BranchImmediate (a, bt))) = ARM8 w.
Proof.
  intros Hbt Ha. cbn [Encode e_branch]. rewrite (bdt' _ _ Ha).
  rewrite (bdt' (bt IN _)) by (destruct Hbt as [-> | ->]; cbv; tauto). eexists; reflexivity.
Qed.

Ltac bytes1 Hb := rewrite arm8_enc_flat in Hb; cbn [arm8_ast MAP FLAT List.map List.concat] in Hb; rewrite ?app_nil_r in Hb.

Lemma sim_jump s1 s2 ms a :
  asm_step arm8_config s1 (Jump a) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Jump a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _). cbn [asm_ok] in Hok. unfold jump_offset_ok, offset_ok in Hok.
  cbn [arm8_config jump_offset code_alignment] in Hok. apply Bool.andb_true_iff in Hok as [Hrg Ha].
  bytes1 Hb.
  apply (enc_sim s1 _ s2 ms [Branch (BranchImmediate (a, BranchType_JMP))] Hs Hr); [discriminate| |].
  - cbn [run_ok]. split; [left; reflexivity|split; [apply enc_bimm; [left; reflexivity|apply br26; assumption]|]].
    split; [exact Hb|split; [exact Logic.I|split; [exact Logic.I|]]].
    cbn [aexec apc A0_of]. apply aligned_add; assumption.
  - unfold QA_of; cbn [arun aexec aregs apc amem A0_of]. rewrite (bdf' (BranchType_JMP = BranchType_CALL)) by discriminate.
    rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs]. split; [reflexivity|split; [reflexivity|]].
    intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). apply Hg; lia.
Qed.

Lemma sim_call s1 s2 ms a :
  asm_step arm8_config s1 (Call a) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Call a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & Hlr & _). cbn [link_reg arm8_config] in Hlr.
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [_ Hok]. unfold jump_offset_ok, offset_ok in Hok.
  cbn [arm8_config jump_offset code_alignment] in Hok. apply Bool.andb_true_iff in Hok as [Hrg Ha].
  bytes1 Hb.
  apply (enc_sim s1 _ s2 ms [Branch (BranchImmediate (a, BranchType_CALL))] Hs Hr); [discriminate| |].
  - cbn [run_ok]. split; [right; reflexivity|split; [apply enc_bimm; [right; reflexivity|apply br26; assumption]|]].
    split; [exact Hb|split; [exact Logic.I|split; [exact Logic.I|]]].
    cbn [aexec apc A0_of]. apply aligned_add; assumption.
  - unfold QA_of; cbn [arun aexec aregs apc amem A0_of]. rewrite (bdt' (BranchType_CALL = BranchType_CALL)) by reflexivity.
    rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc upd_reg set_regs set_pc pc mem regs lr].
    rewrite Hlr. split; [reflexivity|split; [reflexivity|]].
    intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). regs_simp. fin_regs Hg.
    rewrite arm8_enc_flat, LENGTH_FLAT_encode. reflexivity.
Qed.

Lemma sim_jumpreg s1 s2 ms r :
  asm_step arm8_config s1 (JumpReg r) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (JumpReg r) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _ & _ & Halign & _). cbn [code_alignment arm8_config] in Halign.
  cbn [asm_ok] in Hok. apply reg_ok_iff in Hok.
  assert (Har : aligned 2 (s1.(regs) r) = true).
  { rewrite <- Hasm in Hf. cbn [asmSem.asm upd_pc set_pc assert set_failed failed read_reg] in Hf.
    rewrite Halign in Hf. apply Bool.orb_false_iff in Hf as [Hf _]. apply Bool.negb_false_iff in Hf. exact Hf. }
  bytes1 Hb.
  apply (enc_sim s1 _ s2 ms [Branch (BranchRegister (n2w r, BranchType_JMP))] Hs Hr); [discriminate| |].
  - cbn [run_ok]. split; [reflexivity|split; [eexists; reflexivity|]].
    split; [exact Hb|split; [exact Logic.I|split; [exact Logic.I|]]].
    cbn [aexec apc aregs A0_of]. regs_simp. rewrite Hg by lia. exact Har.
  - unfold QA_of; cbn [arun aexec aregs apc amem A0_of]. regs_simp. rewrite Hg by lia.
    rewrite <- Hasm. cbn [asmSem.asm upd_pc set_pc assert set_failed pc mem regs read_reg].
    split; [reflexivity|split; [reflexivity|]].
    intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). apply Hg; lia.
Qed.

Lemma loc21 (i : word64) : (word_le (sw2sw (INT_MINw : word20)) i && word_le i (sw2sw (INT_MAXw : word20)))%bool = true ->
  sw2sw (word_concat (word_extract 20 2 i : word 19) (word_extract 1 0 i : word2) : word21) = i.
Proof.
  intros H. apply Bool.andb_true_iff in H as [H1 H2]. apply word_le_w2i in H1, H2.
  change (w2i (sw2sw (INT_MINw : word20) : word64)) with (-524288)%Z in H1.
  change (w2i (sw2sw (INT_MAXw : word20) : word64)) with 524287%Z in H2.
  transitivity (sw2sw (w2w i : word21) : word64); [|apply sw2sw_w2w_id; [vm_compute; discriminate|cbn; lia]].
  f_equal. wblast.
Qed.

Lemma sim_loc s1 s2 ms r w :
  asm_step arm8_config s1 (Loc r w) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Loc r w) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok Hw]. apply reg_ok_iff in Hok.
  destruct (word_le (sw2sw (INT_MINw : word20)) w && word_le w (sw2sw (INT_MAXw : word20)))%bool eqn:Er.
  - eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; rewrite Er; reflexivity|discriminate
       |alu_ok_tac ltac:(cbn [Encode]; rewrite (bdt' _ _ (loc21 w Er)); eexists; reflexivity)
       |rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r' H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; regs_simp; fin_regs Hg.
  - eapply sim_alu; [exact Hs|exact Hr|cbn [arm8_ast]; rewrite Er; reflexivity|discriminate
       |alu_ok_tac enc_refl|rewrite <- Hasm; reflexivity|rewrite <- Hasm; reflexivity|].
    intros r' H0 H1 H2 H3; rewrite <- Hasm; asm_unfold; unfold temp. repeat dec_closed. regs_simp. val_simp.
    rewrite movk4, (proj1 lemmas.WORD_ADD_0). fin_regs Hg.
Qed.


(** ** Conditional jumps (Galette-only) *)

Lemma cj21 (a : word64) : cjump_offset_ok arm8_config a = true ->
  word_sub a (n2w 4) = sw2sw (word_concat (word_extract 20 2 (word_sub a (n2w 4)) : word 19) (n2w 0 : word2) : word21) /\
  aligned 2 a = true.
Proof.
  unfold cjump_offset_ok, offset_ok; cbn [arm8_config cjump_offset code_alignment].
  rewrite !Bool.andb_true_iff. intros ((H1 & H2) & H3). split; [|exact H3].
  apply word_le_w2i in H1, H2.
  change (w2i cjump_min) with (-1048572)%Z in H1. change (w2i cjump_max) with 1048579%Z in H2.
  assert (Hs : w2i (word_sub a (n2w 4)) = (w2i a - 4)%Z).
  { rewrite <- word_sub_i2w. change (w2i (n2w 4 : word64)) with 4%Z. apply w2i_i2w.
    change (INT_MIN 64) with (-9223372036854775808)%Z. change (INT_MAX 64) with 9223372036854775807%Z. lia. }
  assert (Hal : aligned 2 (word_sub a (n2w 4)) = true).
  { rewrite (proj2 (alignment.aligned_add_sub 2 a (n2w 4) ltac:(reflexivity))). exact H3. }
  transitivity (sw2sw (w2w (word_sub a (n2w 4)) : word21) : word64);
    [symmetry; apply sw2sw_w2w_id; [vm_compute; discriminate|cbn; lia]|].
  f_equal. apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi. change (dimindex 21) with 21 in Hi.
  idx_cases Hi ltac:(wbs; al_bits Hal; reflexivity).
Qed.

Lemma cmp_flags c (x y : word64) :
  ConditionTest (cmp_cond c,
    if asmSem.is_test c then (word_msb (word_and x y), (bool_decide (word_and x y = n2w 0), (false, false)))
    else (word_msb (word_sub x y), (bool_decide (x = y), (negb (word_lo x y),
          negb (bool_decide (w2i (word_sub x y) = (w2i x - w2i y)%Z)))))) = word_cmp c x y.
Proof.
  destruct c; cbv beta iota delta [cmp_cond asmSem.is_test word_cmp]; repeat dec_closed; cbn [orb];
    rewrite ?cond_EQ, ?cond_NE, ?cond_CS, ?cond_CC, ?cond_GE, ?cond_LT, ?Bool.negb_involutive; try reflexivity;
    first [ apply lt_flags | rewrite <- lt_flags, Bool.negb_involutive; reflexivity ].
Qed.

Lemma cmp_flags_t c (x y : word64) : asmSem.is_test c = true ->
  ConditionTest (cmp_cond c, (word_msb (word_and x y), (bool_decide (word_and x y = n2w 0), (false, false)))) = word_cmp c x y.
Proof. intros Et. rewrite <- cmp_flags, Et. reflexivity. Qed.

Lemma cmp_flags_f c (x y : word64) : asmSem.is_test c = false ->
  ConditionTest (cmp_cond c, (word_msb (word_sub x y), (bool_decide (x = y), (negb (word_lo x y),
          negb (bool_decide (w2i (word_sub x y) = (w2i x - w2i y)%Z)))))) = word_cmp c x y.
Proof. intros Et. rewrite <- cmp_flags, Et. reflexivity. Qed.

Lemma enc_bcond (a : word64) c : cjump_offset_ok arm8_config a = true ->
  exists w, Encode (Branch (BranchConditional (word_sub a (n2w 4), c))) = ARM8 w.
Proof.
  intros H. destruct (cj21 a H) as [E _]. cbn [Encode e_branch]. rewrite (bdt' _ _ E). eexists; reflexivity.
Qed.

Lemma pcs4 i (pc : word64) : 8 <= LENGTH (arm8_enc i) -> word_add pc (n2w 4) IN all_pcs (LENGTH (arm8_enc i)) pc 2.
Proof. intros H. exists 1. change (2 ** 2) with 4. split; [reflexivity|lia]. Qed.

Lemma add_sub4 (pc a : word64) : word_add (word_add pc (n2w 4)) (word_sub a (n2w 4)) = word_add pc a.
Proof.
  rewrite <- lemmas.WORD_ADD_ASSOC. f_equal. rewrite lemmas.WORD_ADD_COMM. apply lemmas.WORD_SUB_ADD.
Qed.

Lemma add44 (pc : word64) : word_add (word_add pc (n2w 4)) (n2w 4) = word_add pc (n2w 8).
Proof. apply add_n2w_add. Qed.

Ltac jc_tac Hs Hr Hb Et ii a c I1 :=
  let Hl := fresh "Hl" in
  assert (Hl : arm8_ast ii = [I1; Branch (BranchConditional (word_sub a (n2w 4), cmp_cond c))])
    by (cbn [arm8_ast]; rewrite Et; reflexivity);
  let Hlen := fresh "Hlen" in
  assert (Hlen : LENGTH (arm8_enc ii) = 8) by (rewrite arm8_enc_flat, Hl, LENGTH_FLAT_encode; reflexivity);
  cbn [encode arm8_config] in Hb; rewrite arm8_enc_flat, Hl in Hb; cbn [MAP FLAT List.map List.concat] in Hb; rewrite ?app_nil_r in Hb;
  let Hb1 := fresh "Hb1" in let Hb2 := fresh "Hb2" in
  apply bytes_in_memory_APPEND in Hb as [Hb1 Hb2]; rewrite LENGTH_arm8_encode in Hb2;
  apply (enc_sim _ _ _ _ [I1; Branch (BranchConditional (word_sub a (n2w 4), cmp_cond c))] Hs Hr); [discriminate| |].

Lemma sim_jc_reg s1 s2 ms c r1 r2 a :
  asm_step arm8_config s1 (JumpCmp c r1 (Reg r2) a) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (JumpCmp c r1 (Reg r2) a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hcj Hok]. unfold cmp_ok in Hok. cbn [reg_imm_ok] in Hok. and_facts Hok.
  destruct (cj21 a Hcj) as [Ha4 Haa].
  destruct (asmSem.is_test c) eqn:Et.
  - jc_tac Hs Hr Hb Et (JumpCmp c r1 (Reg r2) a) a c
      constr:(Data (LogicalShiftedRegister_64 (n2w 1, (LogicalOp_AND, (false, (true, (ShiftType_LSL, (0, (n2w r2, (n2w r1, n2w 31)))))))))).
    + cbn [run_ok]. split; [|split].
      * split; [supp_tac|split; [eexists; reflexivity|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc A0_of]. apply (aligned_add4 _ 1), Hal.
      * split; [reflexivity|]. cbn [aexec apc A0_of]. apply pcs4. rewrite Hlen. lia.
      * split; [reflexivity|split; [apply enc_bcond, Hcj|split; [exact Hb2|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc aflags A0_of]. destruct (ConditionTest _).
        -- rewrite add_sub4. apply aligned_add; assumption.
        -- rewrite add44. apply (aligned_add4 _ 2), Hal.
    + unfold QA_of; cbn [arun aexec aregs apc amem aflags A0_of]. val_simp. regs_simp.
      rewrite !Hg by lia.
      rewrite cmp_flags_t by exact Et.
      rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs read_reg reg_imm]. rewrite Hlen.
      split; [destruct (word_cmp _ _ _); [apply add_sub4|apply add44]|split; [intros ad Had; destruct (word_cmp _ _ _); reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). destruct (word_cmp _ _ _); apply Hg; lia.
  - jc_tac Hs Hr Hb Et (JumpCmp c r1 (Reg r2) a) a c
      constr:(Data (AddSubShiftedRegister_64 (n2w 1, (true, (true, (ShiftType_LSL, (n2w r2, (n2w 0, (n2w r1, n2w 31))))))))).
    + cbn [run_ok]. split; [|split].
      * split; [supp_tac|split; [eexists; reflexivity|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc A0_of]. apply (aligned_add4 _ 1), Hal.
      * split; [reflexivity|]. cbn [aexec apc A0_of]. apply pcs4. rewrite Hlen. lia.
      * split; [reflexivity|split; [apply enc_bcond, Hcj|split; [exact Hb2|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc aflags A0_of]. destruct (ConditionTest _).
        -- rewrite add_sub4. apply aligned_add; assumption.
        -- rewrite add44. apply (aligned_add4 _ 2), Hal.
    + unfold QA_of; cbn [arun aexec aregs apc amem aflags A0_of]. val_simp. regs_simp. rewrite !Hg by lia.
      rewrite cmp_flags_f by exact Et.
      rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs read_reg reg_imm]. rewrite Hlen.
      split; [destruct (word_cmp _ _ _); [apply add_sub4|apply add44]|split; [intros ad Had; destruct (word_cmp _ _ _); reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). destruct (word_cmp _ _ _); apply Hg; lia.
Qed.

Lemma test_iff c : asmSem.is_test c = true <-> c = Test \/ c = NotTest.
Proof. destruct c; cbv; intuition (try discriminate; try congruence). Qed.

Lemma sim_jc_imm s1 s2 ms c r1 i a :
  asm_step arm8_config s1 (JumpCmp c r1 (Imm i) a) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (JumpCmp c r1 (Imm i) a) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hcj Hok]. unfold cmp_ok in Hok. cbn [reg_imm_ok] in Hok.
  apply Bool.andb_true_iff in Hok as [Hok Himm]. and_facts Hok.
  rewrite (bdf' (inr c = inl Xor)) in Himm by discriminate. cbn [andb orb valid_imm arm8_config] in Himm.
  destruct (cj21 a Hcj) as [Ha4 Haa].
  destruct (asmSem.is_test c) eqn:Et.
  - destruct (vimm_test c i (proj1 (test_iff c) Et) Himm) as [v Hv].
    jc_tac Hs Hr Hb Et (JumpCmp c r1 (Imm i) a) a c
      constr:(Data (LogicalImmediate_64 (n2w 1, (LogicalOp_AND, (true, (i, (n2w r1, n2w 31))))))).
    + cbn [run_ok]. split; [|split].
      * split; [supp_tac|split; [eapply enc_logimm; [exact Hv|discriminate]|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc A0_of]. apply (aligned_add4 _ 1), Hal.
      * split; [reflexivity|]. cbn [aexec apc A0_of]. apply pcs4. rewrite Hlen. lia.
      * split; [reflexivity|split; [apply enc_bcond, Hcj|split; [exact Hb2|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc aflags A0_of]. destruct (ConditionTest _).
        -- rewrite add_sub4. apply aligned_add; assumption.
        -- rewrite add44. apply (aligned_add4 _ 2), Hal.
    + unfold QA_of; cbn [arun aexec aregs apc amem aflags A0_of]. val_simp. regs_simp. rewrite !Hg by lia.
      rewrite cmp_flags_t by exact Et.
      rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs read_reg reg_imm]. rewrite Hlen.
      split; [destruct (word_cmp _ _ _); [apply add_sub4|apply add44]|split; [intros ad Had; destruct (word_cmp _ _ _); reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). destruct (word_cmp _ _ _); apply Hg; lia.
  - assert (Hnt : c <> Test /\ c <> NotTest) by (split; intros ->; discriminate Et).
    pose proof (vimm_cmp c i (proj1 Hnt) (proj2 Hnt) Himm) as Hv.
    jc_tac Hs Hr Hb Et (JumpCmp c r1 (Imm i) a) a c
      constr:(Data (AddSubImmediate_64 (n2w 1, (true, (true, (i, (n2w r1, n2w 31))))))).
    + cbn [run_ok]. split; [|split].
      * split; [supp_tac|split; [apply enc_addsubimm, Hv|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc A0_of]. apply (aligned_add4 _ 1), Hal.
      * split; [reflexivity|]. cbn [aexec apc A0_of]. apply pcs4. rewrite Hlen. lia.
      * split; [reflexivity|split; [apply enc_bcond, Hcj|split; [exact Hb2|split; [exact Logic.I|split; [exact Logic.I|]]]]].
        cbn [aexec apc aflags A0_of]. destruct (ConditionTest _).
        -- rewrite add_sub4. apply aligned_add; assumption.
        -- rewrite add44. apply (aligned_add4 _ 2), Hal.
    + unfold QA_of; cbn [arun aexec aregs apc amem aflags A0_of]. val_simp. regs_simp. rewrite !Hg by lia.
      rewrite cmp_flags_f by exact Et.
      rewrite <- Hasm. cbn [asmSem.asm jump_to_offset upd_pc set_pc pc mem regs read_reg reg_imm]. rewrite Hlen.
      split; [destruct (word_cmp _ _ _); [apply add_sub4|apply add44]|split; [intros ad Had; destruct (word_cmp _ _ _); reflexivity|]].
      intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). destruct (word_cmp _ _ _); apply Hg; lia.
Qed.


(** ** Memory instructions: the ASM side (Galette-only) *)

Lemma rmw_facts n : forall (ad : word64) s, s.(be) = false ->
  fst (read_mem_word ad n s) = aload n s.(mem) ad /\
  (snd (read_mem_word ad n s)).(regs) = s.(regs) /\ (snd (read_mem_word ad n s)).(mem) = s.(mem) /\
  (snd (read_mem_word ad n s)).(mem_domain) = s.(mem_domain) /\
  ((snd (read_mem_word ad n s)).(failed) = false ->
   s.(failed) = false /\ forall k, k < n -> s.(mem_domain) (word_add ad (n2w k))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros ad s Hbe.
  - cbn. split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
    intros Hf0; split; [exact Hf0|intros; lia].
  - rewrite (proj2 (read_mem_word_def ad n s)). rewrite Hbe.
    destruct (IH (word_add ad (n2w 1)) s Hbe) as (H1 & H2 & H3 & H4 & H5).
    destruct (read_mem_word (word_add ad (n2w 1)) n s) as [w s1] eqn:E. cbn [fst snd] in *.
    cbn [assert set_failed regs mem mem_domain failed]. unfold read_mem. rewrite aload_SUC, H1, H3.
    split; [reflexivity|split; [exact H2|split; [reflexivity|split; [exact H4|]]]].
    intros Hf. apply Bool.orb_false_iff in Hf as [Hd Hf]. apply H5 in Hf as [Hf Hk].
    split; [exact Hf|]. intros k Hk'.
    destruct (N.eq_dec k 0) as [->|Hk0].
    + rewrite add_n2w_0. destruct (classical_dec _) as [Hin|]; [rewrite <- H4; exact Hin|discriminate Hd].
    + replace k with (1 + (k - 1)) by lia. rewrite <- add_n2w_add. apply Hk. lia.
Qed.

Lemma wmw_facts n : forall (ad : word64) w s, s.(be) = false ->
  (write_mem_word ad n w s).(mem) = astore n ad w s.(mem) /\
  (write_mem_word ad n w s).(regs) = s.(regs) /\ (write_mem_word ad n w s).(mem_domain) = s.(mem_domain) /\
  ((write_mem_word ad n w s).(failed) = false ->
   s.(failed) = false /\ forall k, k < n -> s.(mem_domain) (word_add ad (n2w k))).
Proof.
  induction n as [|n IH] using N.peano_ind; intros ad w s Hbe.
  - cbn. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
    intros Hf0; split; [exact Hf0|intros; lia].
  - rewrite (proj2 (write_mem_word_def ad n w s)). rewrite Hbe. cbv zeta.
    destruct (IH (word_add ad (n2w 1)) (word_lsr w 8) s Hbe) as (H1 & H2 & H3 & H4).
    cbn [assert set_failed upd_mem set_mem regs mem mem_domain failed].
    rewrite H1, astore_SUC. split; [reflexivity|split; [exact H2|split; [exact H3|]]].
    intros Hf. apply Bool.orb_false_iff in Hf as [Hd Hf]. apply H4 in Hf as [Hf Hk].
    split; [exact Hf|]. intros k Hk'.
    destruct (N.eq_dec k 0) as [->|Hk0].
    + rewrite add_n2w_0. destruct (classical_dec _) as [Hin|]; [rewrite <- H3; exact Hin|discriminate Hd].
    + replace k with (1 + (k - 1)) by lia. rewrite <- add_n2w_add. apply Hk. lia.
Qed.

Lemma load_facts n r1 r2 w pc' s1 s2 :
  s1.(be) = false -> upd_pc pc' (mem_load n r1 (Addr r2 w) s1) = s2 -> s2.(failed) = false ->
  s2.(pc) = pc' /\ s2.(mem) = s1.(mem) /\
  s2.(regs) = UPDATE r1 (aload n s1.(mem) (word_add (s1.(regs) r2) w)) s1.(regs) /\
  aligned (LOG2 n) (word_add (s1.(regs) r2) w) = true /\
  (forall k, k < n -> s1.(mem_domain) (word_add (word_add (s1.(regs) r2) w) (n2w k))).
Proof.
  intros Hbe <- Hf. unfold mem_load, addr, read_reg in *. cbv zeta in *. rewrite Hbe in *.
  pose proof (rmw_facts n (word_add (regs s1 r2) w) s1 Hbe) as (R1 & R2 & R3 & R4 & R5).
  destruct (read_mem_word (word_add (regs s1 r2) w) n s1) as [v s'] eqn:E. cbn [fst snd] in *.
  cbn [upd_pc set_pc assert set_failed upd_reg set_regs failed regs mem pc mem_domain] in Hf |- *.
  apply Bool.orb_false_iff in Hf as [Hal Hf]. apply Bool.negb_false_iff in Hal.
  apply R5 in Hf as [_ Hdom]. subst v. rewrite R2, R3.
  split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [exact Hal|exact Hdom]]]].
Qed.

Lemma store_facts n r1 r2 w pc' s1 s2 :
  s1.(be) = false -> upd_pc pc' (mem_store n r1 (Addr r2 w) s1) = s2 -> s2.(failed) = false ->
  s2.(pc) = pc' /\ s2.(mem) = astore n (word_add (s1.(regs) r2) w) (s1.(regs) r1) s1.(mem) /\
  s2.(regs) = s1.(regs) /\
  aligned (LOG2 n) (word_add (s1.(regs) r2) w) = true /\
  (forall k, k < n -> s1.(mem_domain) (word_add (word_add (s1.(regs) r2) w) (n2w k))).
Proof.
  intros Hbe <- Hf. unfold mem_store, addr, read_reg in *. cbv zeta in *. rewrite Hbe in *.
  pose proof (wmw_facts n (word_add (regs s1 r2) w) (regs s1 r1) s1 Hbe) as (W1 & W2 & W3 & W4).
  cbn [upd_pc set_pc assert set_failed failed regs mem pc mem_domain] in Hf |- *.
  apply Bool.orb_false_iff in Hf as [Hal Hf]. apply Bool.negb_false_iff in Hal.
  apply W4 in Hf as [_ Hdom].
  split; [reflexivity|split; [exact W1|split; [exact W2|split; [exact Hal|exact Hdom]]]].
Qed.


(** ** Memory instructions (Galette-only) *)

Definition msize (m : memop) : N :=
  match m with Load | Store => 8 | Load32 | Store32 => 4 | Load16 | Store16 => 2 | Load8 | Store8 => 1 end.
Definition mshift (m : memop) : N :=
  match m with Load | Store => 3 | Load32 | Store32 => 2 | Load16 | Store16 => 1 | Load8 | Store8 => 0 end.
Lemma log2_msize m : LOG2 (msize m) = mshift m.
Proof. destruct m; reflexivity. Qed.
Definition mop (m : memop) : MemOp := if is_load m then MemOp_LOAD else MemOp_STORE.

Definition mkls (m : memop) (u : bool) (off : word64) (n t : word5) : instruction :=
  match m with
  | Load | Store => LoadStore (LoadStoreImmediate_64 (lsargs (n2w 3) false (mop m) u off n t))
  | Load32 | Store32 => LoadStore (LoadStoreImmediate_32 (lsargs (n2w 2) true (mop m) u off n t))
  | Load16 | Store16 => LoadStore (LoadStoreImmediate_16 (lsargs (n2w 1) true (mop m) u off n t))
  | Load8 | Store8 => LoadStore (LoadStoreImmediate_8 (lsargs (n2w 0) false (mop m) u off n t))
  end.

Definition scaled (k : N) (a : word64) : word64 := word_lsl (w2w (word_extract 11 0 (word_lsr a k) : word12)) k.

Lemma ast_mem m r1 r2 a : arm8_ast (Inst (asm.Mem m r1 (Addr r2 a))) =
  let u := negb (word_msb a) in
  if bool_decide (msize m = 1) then [mkls m u a (n2w r2) (n2w r1)]
  else if (negb (bool_decide (a = sw2sw (word_extract 8 0 a : word 9))) &&
           implb u (negb (bool_decide (a = scaled (mshift m) a))))%bool then
    let '(b, c) := if u then (word_sub a (n2w 0xFF), n2w 0xFF) else (word_sub (word_2comp a) (n2w 0x100), word_2comp (n2w 0x100)) in
    [Data (AddSubImmediate_64 (n2w 1, (negb u, (false, (b, (n2w r2, temp)))))); mkls m u c temp (n2w r1)]
  else [mkls m u a (n2w r2) (n2w r1)].
Proof. destruct m; reflexivity. Qed.

Lemma supp_mkls m u off n t : n <> n2w 31 -> supported (mkls m u off n t).
Proof.
  intros Hn. destruct m; cbn [mkls supported mop is_load];
    repeat eexists; try exact Hn; first [left; reflexivity|right; reflexivity].
Qed.

Lemma aexec_mkls m u off n t A : aexec (mkls m u off n t) A = ls_exec (msize m) (mop m) off n t A.
Proof. destruct m; reflexivity. Qed.

Lemma memok_mkls m u off n t A : aligned (mshift m) (word_add (rX (aregs A) n) off) = true ->
  mem_ok (mkls m u off n t) A.
Proof. destruct m; cbn; auto. Qed.

Lemma accok_mkls dom m u off n t A :
  (forall j, j < msize m -> dom (word_add (word_add (rX (aregs A) n) off) (n2w j))) -> acc_ok dom (mkls m u off n t) A.
Proof. destruct m; cbn; auto. Qed.

Lemma enc_mkls m u off n t : (u = true /\ off = scaled (mshift m) off) \/ off = sw2sw (word_extract 8 0 off : word 9) ->
  exists w, Encode (mkls m u off n t) = ARM8 w.
Proof.
  intros H. destruct m; cbn [mkls lsargs mop is_load Encode e_load_store e_LoadStoreImmediate mshift] in *; unfold scaled in H;
    cbv beta iota zeta;
    repeat match goal with |- context [bool_decide ?P] => closed P;
      let v := eval vm_compute in (bool_decide P) in
      lazymatch v with true => change (bool_decide P) with true | false => change (bool_decide P) with false end end;
    cbv beta iota;
    repeat match goal with |- context [@w2n ?a ?x] => closed x;
      let v := eval vm_compute in (@w2n a x) in is_lit v; change (@w2n a x) with v end;
    repeat match goal with |- context [@w2w ?a ?b (n2w ?c)] => is_lit c;
      let v := eval vm_compute in (@w2n b (@w2w a b (n2w c))) in change (@w2w a b (n2w c)) with (@n2w b v) end;
    (destruct H as [[-> Hs]|Hi];
     [rewrite (bdt' _ _ Hs); eexists; reflexivity
     |destruct (_ && _)%bool; [eexists; reflexivity|rewrite (bdt' _ _ Hi); eexists; reflexivity]]).
Qed.

Lemma lt4096_and (x : word64) : w2n x < 4096 -> word_and x (word_1comp (n2w 4095)) = n2w 0.
Proof.
  intros H. apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi.
  rewrite wb_and, wb_not, !wb_n2w_lit, N.bits_0, Bool.andb_false_r. change (dimindex 64) with 64 in *.
  destruct (N.ltb_spec i 64); [|lia]. cbn [andb].
  destruct (N.ltb_spec i 12).
  - assert (Hi' : i < 12) by assumption. clear -Hi'. idx_cases Hi' ltac:(rewrite Bool.andb_false_r; reflexivity).
  - rewrite word_bit_alt, fcp_index_testbit, (testbit_lt_pow (w2n x) 12 i) by (cbn; lia).
    rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma w2i_nonneg (x : word64) : word_msb x = false -> w2i x = Z.of_N (w2n x).
Proof. intros H. rewrite w2i_msb_eq, H. reflexivity. Qed.

Lemma imm9_iff (a : word64) : (-256 <= w2i a <= 255)%Z -> a = sw2sw (word_extract 8 0 a : word 9).
Proof.
  intros H. symmetry. replace (word_extract 8 0 a : word 9) with (w2w a : word 9) by wblast.
  apply sw2sw_w2w_id; [vm_compute; discriminate|cbn; lia].
Qed.

Lemma not_imm9 (a : word64) : a <> sw2sw (word_extract 8 0 a : word 9) -> (w2i a < -256 \/ 255 < w2i a)%Z.
Proof. intros H. destruct (Z.lt_ge_cases (w2i a) (-256)); [left; exact H0|]. destruct (Z.lt_ge_cases 255 (w2i a)); [right; exact H1|]. exfalso. apply H, imm9_iff. lia. Qed.

Lemma scaled0 (a : word64) : word_msb a = false -> (w2i a <= 4095)%Z -> a = scaled 0 a.
Proof.
  intros Hm Hr. rewrite w2i_nonneg in Hr by exact Hm. unfold scaled. rewrite lsl_0, lsr_0.
  assert (Hlt : w2n a < 4096) by lia. symmetry.
  apply word_bit_ext; intros i Hi. rewrite !wb_fcp by exact Hi. rewrite wb_w2w, wb_extract.
  change (dimindex 64) with 64 in *. change (dimindex 12) with 12. rewrite N.add_0_r.
  destruct (N.ltb_spec i 64); [|lia]. cbn [andb].
  destruct (N.ltb_spec i 12), (N.leb_spec i 11); try lia; cbn [andb]; [reflexivity|].
  rewrite word_bit_alt, fcp_index_testbit, (testbit_lt_pow (w2n a) 12 i) by (cbn; lia). rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma mem_off m (w : word64) :
  (if list.MEM m [asm.Load; asm.Store; Load32; Store32] then addr_offset_ok arm8_config w
   else if list.MEM m [Load16; Store16] then (hw_offset_ok arm8_config w && negb (bool_decide (ISA arm8_config = Ag32)))%bool
   else byte_offset_ok arm8_config w) = true ->
  (if msize m =? 1 then (-256 <= w2i w <= 4095)%Z else (-4351 <= w2i w <= 4350)%Z).
Proof.
  intros H. unfold addr_offset_ok, hw_offset_ok, byte_offset_ok, offset_ok in H.
  destruct m; cbn [list.MEM msize arm8_config addr_offset hw_offset byte_offset] in H |- *;
    repeat match type of H with context [bool_decide ?P] => closed P;
      let v := eval vm_compute in (bool_decide P) in change (bool_decide P) with v in H end;
    cbn [orb andb negb N.eqb] in H |- *; rewrite ?Bool.andb_true_r in H;
    repeat match type of H with ((?a && ?b) && ?c)%bool = true => apply Bool.andb_true_iff in H as [H _] end;
    apply Bool.andb_true_iff in H as [H1 H2]; apply word_le_w2i in H1, H2;
    match type of H1 with (w2i ?x <= _)%Z => let v := eval vm_compute in (w2i x) in change (w2i x) with v in H1 end;
    match type of H2 with (_ <= w2i ?x)%Z => let v := eval vm_compute in (w2i x) in change (w2i x) with v in H2 end;
    cbn [Pos.eqb]; lia.
Qed.

Lemma asm_Load r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem asm.Load r1 a)) pc' s = upd_pc pc' (mem_load 8 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Load8 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem Load8 r1 a)) pc' s = upd_pc pc' (mem_load 1 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Load16 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem Load16 r1 a)) pc' s = upd_pc pc' (mem_load 2 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Load32 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem Load32 r1 a)) pc' s = upd_pc pc' (mem_load 4 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem asm.Store r1 a)) pc' s = upd_pc pc' (mem_store 8 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store8 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem Store8 r1 a)) pc' s = upd_pc pc' (mem_store 1 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store16 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem Store16 r1 a)) pc' s = upd_pc pc' (mem_store 2 r1 a s).
Proof. reflexivity. Qed.
Lemma asm_Store32 r1 a pc' (s : asm_state 64) : asmSem.asm (Inst (asm.Mem Store32 r1 a)) pc' s = upd_pc pc' (mem_store 4 r1 a s).
Proof. reflexivity. Qed.

Lemma mem_facts m r1 r2 w pc' s1 s2 : be s1 = false -> asmSem.asm (Inst (asm.Mem m r1 (Addr r2 w))) pc' s1 = s2 ->
  failed s2 = false ->
  s2.(pc) = pc' /\ aligned (mshift m) (word_add (s1.(regs) r2) w) = true /\
  (forall k, k < msize m -> s1.(mem_domain) (word_add (word_add (s1.(regs) r2) w) (n2w k))) /\
  (if is_load m then s2.(mem) = s1.(mem) /\ s2.(regs) = UPDATE r1 (aload (msize m) s1.(mem) (word_add (s1.(regs) r2) w)) s1.(regs)
   else s2.(mem) = astore (msize m) (word_add (s1.(regs) r2) w) (s1.(regs) r1) s1.(mem) /\ s2.(regs) = s1.(regs)).
Proof.
  intros Hbe Hasm Hf. rewrite <- (log2_msize m).
  destruct m;
    first [ rewrite asm_Load in Hasm | rewrite asm_Load8 in Hasm | rewrite asm_Load16 in Hasm | rewrite asm_Load32 in Hasm
          | rewrite asm_Store in Hasm | rewrite asm_Store8 in Hasm | rewrite asm_Store16 in Hasm | rewrite asm_Store32 in Hasm ];
    cbn [is_load msize];
    lazymatch type of Hasm with
    | upd_pc _ (mem_load _ _ _ _) = _ => destruct (load_facts _ _ _ _ _ _ _ Hbe Hasm Hf) as (F1 & F2 & F3 & F4 & F5)
    | upd_pc _ (mem_store _ _ _ _) = _ => destruct (store_facts _ _ _ _ _ _ _ Hbe Hasm Hf) as (F1 & F2 & F3 & F4 & F5)
    end;
    exact (conj F1 (conj F4 (conj F5 (conj F2 F3)))).
Qed.

Lemma LENGTH_enc1 i x : arm8_ast i = [x] -> LENGTH (arm8_enc i) = 4.
Proof. intros H. rewrite arm8_enc_flat, H, LENGTH_FLAT_encode. reflexivity. Qed.
Lemma LENGTH_enc2 i x y : arm8_ast i = [x; y] -> LENGTH (arm8_enc i) = 8.
Proof. intros H. rewrite arm8_enc_flat, H, LENGTH_FLAT_encode. reflexivity. Qed.

Lemma mop_cases m : mop m = MemOp_LOAD \/ mop m = MemOp_STORE.
Proof. unfold mop; destruct (is_load m); auto. Qed.

Lemma ls_exec_pc k m off n t A : apc (ls_exec k (mop m) off n t A) = word_add (apc A) (n2w 4).
Proof. unfold ls_exec, mop. destruct (is_load m); reflexivity. Qed.

Lemma ls_exec_regs k m off n t A :
  aregs (ls_exec k (mop m) off n t A) = if is_load m then wX t (aload k (amem A) (word_add (rX (aregs A) n) off)) (aregs A) else aregs A.
Proof. unfold ls_exec, mop. destruct (is_load m); reflexivity. Qed.

Lemma ls_exec_mem k m off n t A :
  amem (ls_exec k (mop m) off n t A) = if is_load m then amem A else astore k (word_add (rX (aregs A) n) off) (rX (aregs A) t) (amem A).
Proof. unfold ls_exec, mop. destruct (is_load m); reflexivity. Qed.

Lemma sim_mem_single s1 s2 ms m r1 r2 w u :
  asm_step arm8_config s1 (Inst (asm.Mem m r1 (Addr r2 w))) s2 -> target_state_rel arm8_target s1 ms ->
  arm8_ast (Inst (asm.Mem m r1 (Addr r2 w))) = [mkls m u w (n2w r2) (n2w r1)] ->
  (u = true /\ w = scaled (mshift m) w) \/ w = sw2sw (word_extract 8 0 w : word 9) ->
  enc_goal s1 (Inst (asm.Mem m r1 (Addr r2 w))) s2 ms.
Proof.
  intros Hs Hr Hl Henc. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok inst_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok _]. and_facts Hok.
  destruct (mem_facts _ _ _ _ _ _ _ Hbe Hasm Hf) as (F1 & F4 & F5 & F23).
  assert (Had : word_add (rX (arm8_state_REG ms) (n2w r2)) w = word_add (s1.(regs) r2) w) by (regs_simp; rewrite Hg by lia; reflexivity).
  cbn [encode arm8_config] in Hb. rewrite arm8_enc_flat, Hl in Hb. cbn [MAP FLAT List.map List.concat] in Hb. rewrite app_nil_r in Hb.
  apply (enc_sim s1 _ s2 ms [mkls m u w (n2w r2) (n2w r1)] Hs Hr); [discriminate| |].
  - cbn [run_ok]. split; [apply supp_mkls; intros E; apply n2w5_eq in E; lia|split; [apply enc_mkls, Henc|]].
    split; [exact Hb|split; [apply memok_mkls; cbn [aregs A0_of]; rewrite Had; exact F4|split]].
    + apply accok_mkls. cbn [aregs A0_of]. rewrite Had. exact F5.
    + rewrite aexec_mkls, ls_exec_pc. apply (aligned_add4 _ 1), Hal.
  - unfold QA_of; cbn [arun]. rewrite aexec_mkls, ls_exec_pc, ls_exec_regs, ls_exec_mem. cbn [aregs apc amem A0_of].
    rewrite Had. rewrite (LENGTH_enc1 _ _ Hl) in F1.
    destruct (is_load m); destruct F23 as [F2 F3]; (split; [rewrite F1; reflexivity|split]).
    + intros ad Had'. rewrite F2. reflexivity.
    + intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). rewrite F3. regs_simp. fin_regs Hg.
    + intros ad Had'. rewrite F2. regs_simp. rewrite Hg by lia. reflexivity.
    + intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). rewrite F3. apply Hg; lia.
Qed.

Lemma sim_mem_two s1 s2 ms m r1 r2 w u b c :
  asm_step arm8_config s1 (Inst (asm.Mem m r1 (Addr r2 w))) s2 -> target_state_rel arm8_target s1 ms ->
  arm8_ast (Inst (asm.Mem m r1 (Addr r2 w))) =
    [Data (AddSubImmediate_64 (n2w 1, (negb u, (false, (b, (n2w r2, temp)))))); mkls m u c temp (n2w r1)] ->
  word_and b (word_1comp (n2w 4095)) = n2w 0 -> c = sw2sw (word_extract 8 0 c : word 9) ->
  (forall x : word64, word_add (fst (AddWithCarry (Nw:=64) (x, (if negb u then word_1comp b else b, negb u)))) c = word_add x w) ->
  enc_goal s1 (Inst (asm.Mem m r1 (Addr r2 w))) s2 ms.
Proof.
  intros Hs Hr Hl Hb12 Hc Hadr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  pose proof Hs as (Hb & _).
  cbn [asm_ok inst_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok _]. and_facts Hok.
  destruct (mem_facts _ _ _ _ _ _ _ Hbe Hasm Hf) as (F1 & F4 & F5 & F23).
  set (A1 := aexec (Data (AddSubImmediate_64 (n2w 1, (negb u, (false, (b, (n2w r2, temp))))))) (A0_of s1 ms)).
  assert (Had : word_add (rX (aregs A1) temp) c = word_add (s1.(regs) r2) w).
  { subst A1. cbn [aexec aregs A0_of]. unfold temp. regs_simp. rewrite Hg by lia. destruct u; apply Hadr. }
  assert (Hlen : LENGTH (arm8_enc (Inst (asm.Mem m r1 (Addr r2 w)))) = 8) by (apply (LENGTH_enc2 _ _ _ Hl)).
  cbn [encode arm8_config] in Hb. rewrite arm8_enc_flat, Hl in Hb. cbn [MAP FLAT List.map List.concat] in Hb. rewrite app_nil_r in Hb.
  apply bytes_in_memory_APPEND in Hb as [Hb1 Hb2]. rewrite LENGTH_arm8_encode in Hb2.
  apply (enc_sim s1 _ s2 ms [Data (AddSubImmediate_64 (n2w 1, (negb u, (false, (b, (n2w r2, temp)))))); mkls m u c temp (n2w r1)] Hs Hr);
    [discriminate| |].
  - cbn [run_ok]. fold A1. split; [|split].
    + split; [unfold temp; supp_tac|split; [apply enc_addsubimm; left; exact Hb12|split; [exact Hb1|split; [exact Logic.I|split; [exact Logic.I|]]]]].
      cbn [aexec apc A0_of]. apply (aligned_add4 _ 1), Hal.
    + split; [subst A1; destruct u; reflexivity|]. subst A1. cbn [aexec apc A0_of]. apply pcs4. rewrite Hlen. lia.
    + split; [apply supp_mkls; unfold temp; intros E; apply n2w5_eq in E; lia|split; [apply enc_mkls; right; exact Hc|]].
      split; [subst A1; destruct u; exact Hb2|split; [apply memok_mkls; rewrite Had; exact F4|split]].
      * apply accok_mkls. rewrite Had. exact F5.
      * rewrite aexec_mkls, ls_exec_pc. subst A1. cbn [aexec apc A0_of]. rewrite add44. apply (aligned_add4 _ 2), Hal.
  - unfold QA_of; cbn [arun]. fold A1. rewrite aexec_mkls, ls_exec_pc, ls_exec_regs, ls_exec_mem. rewrite Had.
    assert (HA1 : apc A1 = word_add s1.(pc) (n2w 4) /\ amem A1 = s1.(mem) /\
                  forall r, r < 32 -> r <> 26 -> r <> 31 -> aregs A1 (n2w r) = arm8_state_REG ms (n2w r))
      by (subst A1; cbn [aexec apc amem aregs A0_of]; unfold temp; split; [reflexivity|split; [reflexivity|]];
          intros r H0 H1 H2; regs_simp; reflexivity).
    destruct HA1 as (HA1p & HA1m & HA1r). rewrite HA1p, HA1m, add44. rewrite Hlen in F1.
    destruct (is_load m); destruct F23 as [F2 F3]; (split; [rewrite F1; reflexivity|split]).
    + intros ad Had'. rewrite F2. reflexivity.
    + intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). rewrite F3. regs_simp. fin_regs Hg.
      rewrite HA1r by lia. apply Hg; lia.
    + intros ad Had'. rewrite F2. regs_simp. rewrite HA1r by lia. rewrite Hg by lia. reflexivity.
    + intros r' H0 Hav; apply avoid_iff in Hav as (H1 & H2 & H3). rewrite F3. rewrite HA1r by lia. apply Hg; lia.
Qed.

Lemma neg_i2w {a : N} j : word_2comp (i2w j : word a) = i2w (- j).
Proof. rewrite lemmas.WORD_NEG_MUL. apply MULT_MINUS_ONE. Qed.

Lemma sub_i2w {a : N} x y : word_sub (i2w x : word a) (i2w y) = i2w (x - y).
Proof. unfold word_sub. rewrite neg_i2w, word_i2w_add. reflexivity. Qed.

Lemma b12_of (k : Z) : (0 <= k < 4096)%Z -> word_and (i2w k : word64) (word_1comp (n2w 4095)) = n2w 0.
Proof.
  intros Hk. apply lt4096_and. apply N2Z.inj_lt. rewrite w2n_i2w. change (Z.of_N (dimword 64)) with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. change (Z.of_N 4096) with 4096%Z. lia.
Qed.

Lemma sim_mem s1 s2 ms m r1 r2 w :
  asm_step arm8_config s1 (Inst (asm.Mem m r1 (Addr r2 w))) s2 -> target_state_rel arm8_target s1 ms ->
  enc_goal s1 (Inst (asm.Mem m r1 (Addr r2 w))) s2 ms.
Proof.
  intros Hs Hr. destruct (hyp_facts _ _ _ _ Hs Hr) as (Hal & Hbe & Hasm & Hf & Hok & Hg).
  cbn [asm_ok inst_ok] in Hok. apply Bool.andb_true_iff in Hok as [_ Hoff].
  pose proof (mem_off m w Hoff) as Hw.
  pose proof (ast_mem m r1 r2 w) as Hast. cbv zeta in Hast.
  pose proof (msb_w2i w) as Hmsb.
  destruct (bool_decide (msize m = 1)) eqn:E1.
  { apply bool_decide_spec in E1. rewrite E1 in Hw. cbn [N.eqb Pos.eqb] in Hw.
    apply (sim_mem_single _ _ _ _ _ _ _ (negb (word_msb w)) Hs Hr Hast).
    assert (Hm0 : mshift m = 0) by (destruct m; cbn in E1 |- *; congruence). rewrite Hm0.
    destruct (word_msb w) eqn:Em; cbn [negb].
    - right. apply imm9_iff. symmetry in Hmsb. apply Z.ltb_lt in Hmsb. lia.
    - left. split; [reflexivity|]. apply scaled0; [exact Em|lia]. }
  assert (Hw' : (-4351 <= w2i w <= 4350)%Z) by (destruct m; cbn in E1, Hw |- *; try discriminate E1; exact Hw).
  destruct (negb (bool_decide (w = sw2sw (word_extract 8 0 w : word 9))) &&
            implb (negb (word_msb w)) (negb (bool_decide (w = scaled (mshift m) w))))%bool eqn:E2.
  - apply Bool.andb_true_iff in E2 as [E2 _]. apply Bool.negb_true_iff in E2.
    assert (Hn9 : w <> sw2sw (word_extract 8 0 w : word 9)) by (intros E; rewrite (bdt' _ _ E) in E2; discriminate E2).
    apply not_imm9 in Hn9.
    destruct (word_msb w) eqn:Em; cbn [negb] in Hast.
    + symmetry in Hmsb. apply Z.ltb_lt in Hmsb.
      apply (sim_mem_two _ _ _ _ _ _ _ false _ _ Hs Hr Hast).
      * rewrite <- (i2w_w2i w), <- (i2w_pos 256), neg_i2w, sub_i2w. apply b12_of. change (Z.of_N 256) with 256%Z. lia.
      * apply word_eq_w2n; vm_compute; reflexivity.
      * intros x. cbn [negb]. rewrite awc_sub. cbn [fst].
        rewrite <- (i2w_w2i x), <- (i2w_w2i w), <- (i2w_pos 256), !neg_i2w, !sub_i2w, !word_i2w_add. f_equal. lia.
    + symmetry in Hmsb. apply Z.ltb_ge in Hmsb.
      apply (sim_mem_two _ _ _ _ _ _ _ true _ _ Hs Hr Hast).
      * rewrite <- (i2w_w2i w), <- (i2w_pos 255), sub_i2w. apply b12_of. change (Z.of_N 255) with 255%Z. lia.
      * apply word_eq_w2n; vm_compute; reflexivity.
      * intros x. cbn [negb]. rewrite awc_add.
        rewrite <- (i2w_w2i x), <- (i2w_w2i w), <- (i2w_pos 255), !sub_i2w, !word_i2w_add. f_equal. lia.
  - try rewrite E1 in Hast; try rewrite E2 in Hast.
    apply (sim_mem_single _ _ _ _ _ _ _ (negb (word_msb w)) Hs Hr Hast).
    apply Bool.andb_false_iff in E2 as [E2|E2].
    + apply Bool.negb_false_iff, bool_decide_spec in E2. right; exact E2.
    + destruct (negb (word_msb w)); cbn [implb] in E2; [|discriminate E2].
      apply Bool.negb_false_iff, bool_decide_spec in E2. left; split; [reflexivity|exact E2].
Qed.


(** ** Encoding lengths and the main theorems *)

Lemma ast_nonempty i : arm8_ast i <> [].
Proof.
  destruct i as [ii| a | c r ri a | a | r | r a]; cbn [arm8_ast].
  - destruct ii as [| r w | ar | m r [r2 w] | f]; cbn [arm8_ast].
    + discriminate.
    + repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; try discriminate;
        repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
    + destruct ar as [b r1 r2 [r3|w]|sh r1 r2 [r3|w]|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4];
        try destruct b; try destruct sh; cbn [arm8_ast];
        repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; try discriminate;
        repeat match goal with |- context [if ?c then _ else _] => destruct c end; try discriminate.
    + destruct m; cbn [arm8_ast]; try discriminate;
        unfold arm8_load_store_ast, arm8_load_store_ast32, arm8_load_store_ast16; cbv zeta;
        repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
    + discriminate.
  - discriminate.
  - destruct ri; discriminate.
  - discriminate.
  - discriminate.
  - repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

Lemma len_enc_ast i : LENGTH (arm8_enc i) = 4 * LENGTH (arm8_ast i).
Proof. rewrite arm8_enc_flat. apply LENGTH_FLAT_encode. Qed.

Lemma range_true (x y a : word64) : (word_le x a && word_le a y)%bool = true -> (w2i x <= w2i a <= w2i y)%Z.
Proof. rewrite Bool.andb_true_iff, !word_le_w2i. tauto. Qed.

Lemma range_false (x y a : word64) : (word_le x a && word_le a y)%bool = false -> (w2i a < w2i x \/ w2i y < w2i a)%Z.
Proof.
  intros H. destruct (word_le x a) eqn:E1, (word_le a y) eqn:E2; try discriminate.
  - right. rewrite word_le_Z in E2. apply Z.leb_gt in E2. lia.
  - left. rewrite word_le_Z in E1. apply Z.leb_gt in E1. lia.
  - left. rewrite word_le_Z in E1. apply Z.leb_gt in E1. lia.
Qed.

Ltac range_facts :=
  unfold is_true in *;
  repeat match goal with
  | H : (word_le _ _ && word_le _ _)%bool = true |- _ => apply range_true in H
  | H : (word_le _ _ && word_le _ _)%bool = false |- _ => apply range_false in H
  | H : word_le _ _ = true |- _ => apply word_le_w2i in H
  | H : word_lt _ _ = true |- _ => rewrite word_lt_Z in H; apply Z.ltb_lt in H
  end;
  change (w2i (@sw2sw 20 64 (@word_L 20))) with (-524288)%Z in *;
  change (w2i (@sw2sw 20 64 (@word_H 20))) with 524287%Z in *;
  change (w2i (@n2w 64 0)) with 0%Z in *.

Ltac mono_tac :=
  unfold offset_monotonic; cbn [encode arm8_config]; rewrite !len_enc_ast; intros _;
  split; intros H;
  repeat match type of H with _ /\ _ => let H' := fresh in destruct H as [H' H] end;
  cbn [arm8_ast];
  repeat match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end;
  cbn [LENGTH]; try lia; range_facts; lia.

Lemma arm8_enc_ok : enc_ok arm8_config.
Proof.
  split; [reflexivity|split; [|split; [|split; [|split]]]].
  - intros w. cbn [encode arm8_config code_alignment]. rewrite len_enc_ast. split.
    + change (2 ** 2) with 4. rewrite N.mul_comm. apply N.Div0.mod_mul.
    + pose proof (ast_nonempty w). destruct (arm8_ast w); [congruence|cbn [LENGTH]; lia].
  - intros w1 w2. mono_tac.
  - intros cmp r ri w1 w2. destruct ri; mono_tac.
  - intros w1 w2. mono_tac.
  - intros w1 w2 r. mono_tac.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "length_arm8_encode" *)
Theorem length_arm8_encode : forall i, LENGTH (arm8_encode i) = 4.
Proof. exact LENGTH_arm8_encode. Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "length_arm8_enc" *)
Theorem length_arm8_enc : forall l, LENGTH (LIST_BIND l arm8_encode) = 4 * LENGTH l.
Proof. exact LENGTH_FLAT_encode. Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encode_not_nil" *)
Theorem arm8_encode_not_nil : forall i, arm8_encode i <> [].
Proof. intros i. unfold arm8_encode. destruct (Encode i); discriminate. Qed.

(** HOL's [arm8_encoding] after its [SIMP_RULE] (the second declaration of
    the name in the script; the first is the [local] form with
    [let l = arm8_enc i in ...], not ported separately). *)
(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoding" 309 *)
Theorem arm8_encoding : forall i,
  LENGTH (FLAT (MAP arm8_encode (arm8_ast i))) MOD 4 = 0 /\ FLAT (MAP arm8_encode (arm8_ast i)) <> [].
Proof.
  intros i. rewrite LENGTH_FLAT_encode. split.
  - rewrite N.mul_comm. apply N.Div0.mod_mul.
  - pose proof (ast_nonempty i). destruct (arm8_ast i) as [|x l]; [congruence|].
    cbn [MAP FLAT List.map List.concat]. unfold arm8_encode. destruct (Encode x); discriminate.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_target_ok" *)
Theorem arm8_target_ok : target_ok arm8_target.
Proof.
  split; [exact arm8_enc_ok|].
  intros ms1 ms2 s Hp. unfold arm8_target in *; cbn [proj state_ok get_pc get_byte] in *.
  destruct (arm8_proj_eq _ _ _ Hp) as (E1 & E2 & E3 & E4 & E5).
  split; [|split; [exact E1|split; [exact E3|exact E4]]].
  unfold target_state_rel; cbn [state_ok get_pc get_byte get_reg get_fp_reg config].
  rewrite E1, E3, E2.
  split; intros (H1 & H2 & H3 & H4 & H5); (split; [exact H1|split; [exact H2|split; [|split; [exact H4|intros i Hi; cbn [fp_reg_count arm8_config] in Hi; lia]]]]);
    intros ad Had; [rewrite <- E4 by exact Had|rewrite E4 by exact Had]; apply H3, Had.
Qed.

Lemma ltb0 x : (x <? 0) = false.
Proof. apply N.ltb_ge. lia. Qed.

Lemma sim_all s1 i s2 ms :
  asm_step arm8_config s1 i s2 -> target_state_rel arm8_target s1 ms -> enc_goal s1 i s2 ms.
Proof.
  intros Hs Hr.
  destruct i as [ii| a | c r ri a | a | r | r a].
  - destruct ii as [| r w | ar | m r [r2 w] | f].
    + apply sim_skip; assumption.
    + apply sim_const; assumption.
    + destruct ar as [b r1 r2 [r3|w]|sh r1 r2 [r3|w]|r1 r2 r3|r1 r2 r3 r4|r1 r2 r3 r4 r5|r1 r2 r3 r4|r1 r2 r3 r4|r1 r2 r3 r4].
      * apply sim_binop_reg; assumption.
      * apply sim_binop_imm; assumption.
      * apply sim_shift_reg; assumption.
      * apply sim_shift_imm; assumption.
      * apply sim_div; assumption.
      * apply sim_longmul; assumption.
      * exfalso. destruct (hyp_facts _ _ _ _ Hs Hr) as (_ & _ & _ & _ & Hok & _).
        cbn [asm_ok inst_ok arith_ok] in Hok. isa_simp Hok. discriminate Hok.
      * apply sim_addcarry; assumption.
      * apply sim_addoverflow; assumption.
      * apply sim_suboverflow; assumption.
    + apply sim_mem; assumption.
    + exfalso. destruct (hyp_facts _ _ _ _ Hs Hr) as (_ & _ & _ & _ & Hok & _).
      cbn [asm_ok inst_ok] in Hok. destruct f; cbn [fp_ok] in Hok; unfold fp_reg_ok in Hok;
        cbn [fp_reg_count arm8_config] in Hok; rewrite ?ltb0, ?Bool.andb_false_r in Hok; discriminate Hok.
  - apply sim_jump; assumption.
  - destruct ri; [apply sim_jc_reg|apply sim_jc_imm]; assumption.
  - apply sim_call; assumption.
  - apply sim_jumpreg; assumption.
  - apply sim_loc; assumption.
Qed.

(*! HOL "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct" *)
Theorem arm8_encoder_correct : encoder_correct arm8_target.
Proof.
  split; [exact arm8_target_ok|].
  intros s1 i s2 ms [Hs Hr]. exact (sim_all s1 i s2 ms Hs Hr).
Qed.

