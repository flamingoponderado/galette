(** * CakeML [word_gcFunctions]: the garbage collector as functions on words

    Port of the definitions of
    [cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml] (the shallow
    embedding of the GC that [stack_alloc]'s GC code implements) and of
    [word_gc_fun_LENGTH].

    Notes:
    - HOL tuples nest to the right, so HOL's [(a,b,c)] is [(a, (b, c))].
    - HOL's boolean results built with [IN dm] (a set) are booleans
      [⌜x IN dm⌝]; HOL's [T]/[F] are [true]/[false].
    - HOL's recursions on a word ([memcpy], the [*_move_list]s) and on a
      [num] counter ([*_loop], [*_data], [*_refs], [*_ref_list]) run on a
      fuel ([*_f], Galette-only) of the length of the recursion; HOL's
      equations are the tagged [*_def] theorems.
    - Not ported: [refs_to_addresses] (on [gc_shared]'s heap elements, not
      ported), the [*_IMP_EVERY2] lemmas (on [word_simpProof]'s
      [is_gc_word_const], not ported; [word_gc_fun_LENGTH] is proved
      directly) and the [*_has_fp_ops] simp lemmas. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words byte alignment.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang data_to_word.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem.
Import wordLang (word_loc, Word, Loc).
Open Scope N_scope.

Section GC.
Context {a : N}.
Local Abbreviation mem := (word a -> word_loc a).
Local Abbreviation dom := (word a -> Prop).
Local Open Scope word_scope.

(** ** Moving one object *)

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "ptr_to_addr_def" *)
Definition ptr_to_addr (conf : config) (base w : word a) : word a :=
  base + ((w >>> shift_length conf) * bytes_in_word).

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "update_addr_def" *)
Definition update_addr (conf : config) (fwd_ptr old_addr : word a) : word a :=
  (fwd_ptr << shift_length conf) || (small_shift_length conf - 1 -- 0) old_addr.

Fixpoint memcpy_f (fuel : nat) (w a0 b : word a) (m : mem) (dm : dom) : word a * (mem * bool) :=
  match fuel with
  | O => (b, (m, true))
  | Datatypes.S fuel =>
      if decide (w = n2w 0) then (b, (m, true)) else
        let '(b1, (m1, c1)) :=
          memcpy_f fuel (w - n2w 1) (a0 + bytes_in_word) (b + bytes_in_word) ((b =+ m a0) m) dm in
        (b1, (m1, andb c1 (andb ⌜a0 IN dm⌝ ⌜b IN dm⌝)))
  end.

(** HOL's [memcpy w a b m dm] (Galette-only fuel wrapper; see [memcpy_def]). *)
Definition memcpy (w a0 b : word a) (m : mem) (dm : dom) : word a * (mem * bool) :=
  memcpy_f (Datatypes.S (N.to_nat (w2n w))) w a0 b m dm.

(** Galette-only. *)
Lemma w2n_sub1 (w : word a) : w <> n2w 0 -> w2n (w - n2w 1) = (w2n w - 1)%N.
Proof.
  intros H. pose proof (w2n_lt w) as Hl.
  assert (Hw : w2n w <> 0%N) by (intros E; apply H; apply w2n_eq_0, E).
  rewrite <- (n2w_w2n w) at 1. rewrite <- n2w_sub by lia.
  rewrite w2n_n2w; apply N.mod_small; lia.
Qed.

Lemma memcpy_f_fuel : forall f1 f2 (w a0 b : word a) m dm,
  (N.to_nat (w2n w) < f1)%nat -> (N.to_nat (w2n w) < f2)%nat ->
  memcpy_f f1 w a0 b m dm = memcpy_f f2 w a0 b m dm.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] w a0 b m dm H1 H2; try lia.
  cbn [memcpy_f]; destruct (decide (w = n2w 0)) as [E|E]; [reflexivity|].
  rewrite (IH f2); [reflexivity| |]; rewrite w2n_sub1 by exact E;
    assert (w2n w <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "memcpy_def" *)
Theorem memcpy_def : forall (w a0 b : word a) m dm,
  memcpy w a0 b m dm =
  if decide (w = n2w 0) then (b, (m, true)) else
    let '(b1, (m1, c1)) :=
      memcpy (w - n2w 1) (a0 + bytes_in_word) (b + bytes_in_word) ((b =+ m a0) m) dm in
    (b1, (m1, andb c1 (andb ⌜a0 IN dm⌝ ⌜b IN dm⌝))).
Proof.
  intros w a0 b m dm; unfold memcpy at 1; cbn [memcpy_f].
  destruct (decide (w = n2w 0)) as [E|E]; [reflexivity|].
  unfold memcpy; rewrite (memcpy_f_fuel _ (Datatypes.S (N.to_nat (w2n (w - n2w 1))))); [reflexivity| |lia].
  rewrite w2n_sub1 by exact E; assert (w2n w <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "decode_length_def" *)
Definition decode_length (conf : config) (w : word a) : word a :=
  w >>> (dimindex a - len_size conf).

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_def" *)
Definition word_gc_move (conf : config)
    (x : word_loc a * (word a * (word a * (word a * (mem * dom)))))
    : word_loc a * (word a * (word a * (mem * bool))) :=
  let '(w0, (i, (pa, (old, (m, dm))))) := x in
  match w0 with
  | Loc l1 l2 => (Loc l1 l2, (i, (pa, (m, (l2 =? 0)%N))))
  | Word w =>
      if decide ((w && n2w 1) = n2w 0) then (Word w, (i, (pa, (m, true)))) else
        let c := ⌜ptr_to_addr conf old w IN dm⌝ in
        let v := m (ptr_to_addr conf old w) in
        if is_fwd_ptr v then
          (Word (update_addr conf (theWord v >>> 2) w), (i, (pa, (m, c))))
        else
          let header_addr := ptr_to_addr conf old w in
          let c := andb c (andb ⌜header_addr IN dm⌝ (isWord (m header_addr))) in
          let len := decode_length conf (theWord (m header_addr)) in
          let v := i + len + n2w 1 in
          let '(pa1, (m1, c1)) := memcpy (len + n2w 1) header_addr pa m dm in
          let c := andb c (andb ⌜header_addr IN dm⌝ c1) in
          let m1 := (header_addr =+ Word (i << 2)) m1 in
          (Word (update_addr conf i w), (v, (pa1, (m1, c))))
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_def" *)
Definition word_gen_gc_partial_move (conf : config)
    (x : word_loc a * (word a * (word a * (word a * (mem * (dom * (word a * word a)))))))
    : word_loc a * (word a * (word a * (mem * bool))) :=
  let '(w0, (i, (pa, (old, (m, (dm, (gs, rs))))))) := x in
  match w0 with
  | Loc l1 l2 => (Loc l1 l2, (i, (pa, (m, (l2 =? 0)%N))))
  | Word w =>
      if decide ((w && n2w 1) = n2w 0) then (Word w, (i, (pa, (m, true)))) else
        let header_addr := ptr_to_addr conf old w in
        let tmp := header_addr - old in
        if orb (tmp <+ gs) (rs <=+ tmp) then (Word w, (i, (pa, (m, true)))) else
          let c := ⌜ptr_to_addr conf old w IN dm⌝ in
          let v := m (ptr_to_addr conf old w) in
          if is_fwd_ptr v then
            (Word (update_addr conf (theWord v >>> 2) w), (i, (pa, (m, c))))
          else
            let c := andb c (andb ⌜header_addr IN dm⌝ (isWord (m header_addr))) in
            let len := decode_length conf (theWord (m header_addr)) in
            let v := i + len + n2w 1 in
            let '(pa1, (m1, c1)) := memcpy (len + n2w 1) header_addr pa m dm in
            let c := andb c (andb ⌜header_addr IN dm⌝ c1) in
            let m1 := (header_addr =+ Word (i << 2)) m1 in
            (Word (update_addr conf i w), (v, (pa1, (m1, c))))
  end.

(** ** Roots *)

Fixpoint word_gc_move_roots_f (conf : config) (ws : list (word_loc a)) (i pa old : word a)
    (m : mem) (dm : dom) : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  match ws with
  | [] => ([], (i, (pa, (m, true))))
  | w :: ws =>
      let '(w1, (i1, (pa1, (m1, c1)))) := word_gc_move conf (w, (i, (pa, (old, (m, dm))))) in
      let '(ws2, (i2, (pa2, (m2, c2)))) := word_gc_move_roots_f conf ws i1 pa1 old m1 dm in
      (w1 :: ws2, (i2, (pa2, (m2, andb c1 c2))))
  end.

(** HOL's [word_gc_move_roots] (Galette-only wrapper; see [word_gc_move_roots_def]). *)
Definition word_gc_move_roots (conf : config)
    (x : list (word_loc a) * (word a * (word a * (word a * (mem * dom)))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(ws, (i, (pa, (old, (m, dm))))) := x in word_gc_move_roots_f conf ws i pa old m dm.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_roots_def" *)
Theorem word_gc_move_roots_def : forall conf i pa old m dm w ws,
  word_gc_move_roots conf ([], (i, (pa, (old, (m, dm))))) = ([], (i, (pa, (m, true)))) /\
  word_gc_move_roots conf (w :: ws, (i, (pa, (old, (m, dm))))) =
    let '(w1, (i1, (pa1, (m1, c1)))) := word_gc_move conf (w, (i, (pa, (old, (m, dm))))) in
    let '(ws2, (i2, (pa2, (m2, c2)))) := word_gc_move_roots conf (ws, (i1, (pa1, (old, (m1, dm))))) in
    (w1 :: ws2, (i2, (pa2, (m2, andb c1 c2)))).
Proof. intros; split; reflexivity. Qed.

Fixpoint word_gen_gc_partial_move_roots_f (conf : config) (ws : list (word_loc a)) (i pa old : word a)
    (m : mem) (dm : dom) (gs rs : word a) : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  match ws with
  | [] => ([], (i, (pa, (m, true))))
  | w :: ws =>
      let '(w1, (i1, (pa1, (m1, c1)))) :=
        word_gen_gc_partial_move conf (w, (i, (pa, (old, (m, (dm, (gs, rs))))))) in
      let '(ws2, (i2, (pa2, (m2, c2)))) := word_gen_gc_partial_move_roots_f conf ws i1 pa1 old m1 dm gs rs in
      (w1 :: ws2, (i2, (pa2, (m2, andb c1 c2))))
  end.

Definition word_gen_gc_partial_move_roots (conf : config)
    (x : list (word_loc a) * (word a * (word a * (word a * (mem * (dom * (word a * word a)))))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(ws, (i, (pa, (old, (m, (dm, (gs, rs))))))) := x in
  word_gen_gc_partial_move_roots_f conf ws i pa old m dm gs rs.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_roots_def" *)
Theorem word_gen_gc_partial_move_roots_def : forall conf i pa old m dm gs rs w ws,
  word_gen_gc_partial_move_roots conf ([], (i, (pa, (old, (m, (dm, (gs, rs))))))) =
    ([], (i, (pa, (m, true)))) /\
  word_gen_gc_partial_move_roots conf (w :: ws, (i, (pa, (old, (m, (dm, (gs, rs))))))) =
    let '(w1, (i1, (pa1, (m1, c1)))) :=
      word_gen_gc_partial_move conf (w, (i, (pa, (old, (m, (dm, (gs, rs))))))) in
    let '(ws2, (i2, (pa2, (m2, c2)))) :=
      word_gen_gc_partial_move_roots conf (ws, (i1, (pa1, (old, (m1, (dm, (gs, rs))))))) in
    (w1 :: ws2, (i2, (pa2, (m2, andb c1 c2)))).
Proof. intros; split; reflexivity. Qed.

(** ** Lists of words in memory *)

Fixpoint word_gc_move_list_f (fuel : nat) (conf : config) (a0 l i pa old : word a) (m : mem) (dm : dom)
    : word a * (word a * (word a * (mem * bool))) :=
  match fuel with
  | O => (a0, (i, (pa, (m, true))))
  | Datatypes.S fuel =>
      if decide (l = n2w 0) then (a0, (i, (pa, (m, true)))) else
        let w := m a0 in
        let '(w1, (i1, (pa1, (m1, c1)))) := word_gc_move conf (w, (i, (pa, (old, (m, dm))))) in
        let m1 := (a0 =+ w1) m1 in
        let '(a2, (i2, (pa2, (m2, c2)))) :=
          word_gc_move_list_f fuel conf (a0 + bytes_in_word) (l - n2w 1) i1 pa1 old m1 dm in
        (a2, (i2, (pa2, (m2, andb ⌜a0 IN dm⌝ (andb c1 c2)))))
  end.

(** HOL's [word_gc_move_list] (Galette-only fuel wrapper; see [word_gc_move_list_def]). *)
Definition word_gc_move_list (conf : config)
    (x : word a * (word a * (word a * (word a * (word a * (mem * dom))))))
    : word a * (word a * (word a * (mem * bool))) :=
  let '(a0, (l, (i, (pa, (old, (m, dm)))))) := x in
  word_gc_move_list_f (Datatypes.S (N.to_nat (w2n l))) conf a0 l i pa old m dm.

Lemma word_gc_move_list_f_fuel : forall f1 f2 conf (a0 l i pa old : word a) m dm,
  (N.to_nat (w2n l) < f1)%nat -> (N.to_nat (w2n l) < f2)%nat ->
  word_gc_move_list_f f1 conf a0 l i pa old m dm = word_gc_move_list_f f2 conf a0 l i pa old m dm.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] conf a0 l i pa old m dm H1 H2; try lia.
  cbn [word_gc_move_list_f]; destruct (decide (l = n2w 0)) as [E|E]; [reflexivity|].
  destruct (word_gc_move conf _) as [w1 [i1 [pa1 [m1 c1]]]].
  rewrite (IH f2); [reflexivity| |]; rewrite w2n_sub1 by exact E;
    assert (w2n l <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_list_def" *)
Theorem word_gc_move_list_def : forall conf (a0 l i pa old : word a) m dm,
  word_gc_move_list conf (a0, (l, (i, (pa, (old, (m, dm)))))) =
  if decide (l = n2w 0) then (a0, (i, (pa, (m, true)))) else
    let w := m a0 in
    let '(w1, (i1, (pa1, (m1, c1)))) := word_gc_move conf (w, (i, (pa, (old, (m, dm))))) in
    let m1 := (a0 =+ w1) m1 in
    let '(a2, (i2, (pa2, (m2, c2)))) :=
      word_gc_move_list conf (a0 + bytes_in_word, (l - n2w 1, (i1, (pa1, (old, (m1, dm)))))) in
    (a2, (i2, (pa2, (m2, andb ⌜a0 IN dm⌝ (andb c1 c2))))).
Proof.
  intros; unfold word_gc_move_list at 1; cbn [word_gc_move_list_f].
  destruct (decide (l = n2w 0)) as [E|E]; [reflexivity|].
  cbv zeta. destruct (word_gc_move conf _) as [w1 [i1 [pa1 [m1 c1]]]].
  unfold word_gc_move_list.
  rewrite (word_gc_move_list_f_fuel _ (Datatypes.S (N.to_nat (w2n (l - n2w 1))))); [reflexivity| |lia].
  rewrite w2n_sub1 by exact E; assert (w2n l <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

Fixpoint word_gen_gc_partial_move_list_f (fuel : nat) (conf : config) (a0 l i pa old : word a)
    (m : mem) (dm : dom) (gs rs : word a) : word a * (word a * (word a * (mem * bool))) :=
  match fuel with
  | O => (a0, (i, (pa, (m, true))))
  | Datatypes.S fuel =>
      if decide (l = n2w 0) then (a0, (i, (pa, (m, true)))) else
        let w := m a0 in
        let '(w1, (i1, (pa1, (m1, c1)))) :=
          word_gen_gc_partial_move conf (w, (i, (pa, (old, (m, (dm, (gs, rs))))))) in
        let m1 := (a0 =+ w1) m1 in
        let '(a2, (i2, (pa2, (m2, c2)))) :=
          word_gen_gc_partial_move_list_f fuel conf (a0 + bytes_in_word) (l - n2w 1) i1 pa1 old m1 dm gs rs in
        (a2, (i2, (pa2, (m2, andb ⌜a0 IN dm⌝ (andb c1 c2)))))
  end.

Definition word_gen_gc_partial_move_list (conf : config)
    (x : word a * (word a * (word a * (word a * (word a * (mem * (dom * (word a * word a))))))))
    : word a * (word a * (word a * (mem * bool))) :=
  let '(a0, (l, (i, (pa, (old, (m, (dm, (gs, rs)))))))) := x in
  word_gen_gc_partial_move_list_f (Datatypes.S (N.to_nat (w2n l))) conf a0 l i pa old m dm gs rs.

Lemma word_gen_gc_partial_move_list_f_fuel : forall f1 f2 conf (a0 l i pa old : word a) m dm gs rs,
  (N.to_nat (w2n l) < f1)%nat -> (N.to_nat (w2n l) < f2)%nat ->
  word_gen_gc_partial_move_list_f f1 conf a0 l i pa old m dm gs rs =
  word_gen_gc_partial_move_list_f f2 conf a0 l i pa old m dm gs rs.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] conf a0 l i pa old m dm gs rs H1 H2; try lia.
  cbn [word_gen_gc_partial_move_list_f]; destruct (decide (l = n2w 0)) as [E|E]; [reflexivity|].
  destruct (word_gen_gc_partial_move conf _) as [w1 [i1 [pa1 [m1 c1]]]].
  rewrite (IH f2); [reflexivity| |]; rewrite w2n_sub1 by exact E;
    assert (w2n l <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_list_def" *)
Theorem word_gen_gc_partial_move_list_def : forall conf (a0 l i pa old : word a) m dm gs rs,
  word_gen_gc_partial_move_list conf (a0, (l, (i, (pa, (old, (m, (dm, (gs, rs)))))))) =
  if decide (l = n2w 0) then (a0, (i, (pa, (m, true)))) else
    let w := m a0 in
    let '(w1, (i1, (pa1, (m1, c1)))) :=
      word_gen_gc_partial_move conf (w, (i, (pa, (old, (m, (dm, (gs, rs))))))) in
    let m1 := (a0 =+ w1) m1 in
    let '(a2, (i2, (pa2, (m2, c2)))) :=
      word_gen_gc_partial_move_list conf
        (a0 + bytes_in_word, (l - n2w 1, (i1, (pa1, (old, (m1, (dm, (gs, rs)))))))) in
    (a2, (i2, (pa2, (m2, andb ⌜a0 IN dm⌝ (andb c1 c2))))).
Proof.
  intros; unfold word_gen_gc_partial_move_list at 1; cbn [word_gen_gc_partial_move_list_f].
  destruct (decide (l = n2w 0)) as [E|E]; [reflexivity|].
  cbv zeta. destruct (word_gen_gc_partial_move conf _) as [w1 [i1 [pa1 [m1 c1]]]].
  unfold word_gen_gc_partial_move_list.
  rewrite (word_gen_gc_partial_move_list_f_fuel _ (Datatypes.S (N.to_nat (w2n (l - n2w 1)))));
    [reflexivity| |lia].
  rewrite w2n_sub1 by exact E; assert (w2n l <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

(** ** The Cheney loop *)

(** Galette-only. *)
Lemma to_nat_pred (k : N) : k <> 0%N -> N.to_nat k = Datatypes.S (N.to_nat (k - 1)).
Proof. intros H; lia. Qed.

Fixpoint word_gc_move_loop_f (k : nat) (conf : config) (pb i pa old : word a) (m : mem) (dm : dom)
    (c : bool) : word a * (word a * (mem * bool)) :=
  if decide (pb = pa) then (i, (pa, (m, c))) else
  match k with
  | O => (i, (pa, (m, false)))
  | Datatypes.S k =>
      let w := m pb in
      let c := andb c (andb ⌜pb IN dm⌝ (isWord w)) in
      let len := decode_length conf (theWord w) in
      if word_bit 2 (theWord w) then
        let pb := pb + (len + n2w 1) * bytes_in_word in
        word_gc_move_loop_f k conf pb i pa old m dm c
      else
        let pb := pb + bytes_in_word in
        let '(pb, (i1, (pa1, (m1, c1)))) := word_gc_move_list conf (pb, (len, (i, (pa, (old, (m, dm)))))) in
        word_gc_move_loop_f k conf pb i1 pa1 old m1 dm (andb c c1)
  end.

(** HOL's [word_gc_move_loop] (Galette-only fuel wrapper; see [word_gc_move_loop_def]). *)
Definition word_gc_move_loop (k : N) (conf : config)
    (x : word a * (word a * (word a * (word a * (mem * (dom * bool))))))
    : word a * (word a * (mem * bool)) :=
  let '(pb, (i, (pa, (old, (m, (dm, c)))))) := x in
  word_gc_move_loop_f (N.to_nat k) conf pb i pa old m dm c.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_move_loop_def" *)
Theorem word_gc_move_loop_def : forall k conf (pb i pa old : word a) m dm c,
  word_gc_move_loop k conf (pb, (i, (pa, (old, (m, (dm, c)))))) =
  if decide (pb = pa) then (i, (pa, (m, c))) else
  if (k =? 0)%N then (i, (pa, (m, false))) else
    let w := m pb in
    let c := andb c (andb ⌜pb IN dm⌝ (isWord w)) in
    let len := decode_length conf (theWord w) in
    if word_bit 2 (theWord w) then
      let pb := pb + (len + n2w 1) * bytes_in_word in
      word_gc_move_loop (k - 1) conf (pb, (i, (pa, (old, (m, (dm, c))))))
    else
      let pb := pb + bytes_in_word in
      let '(pb, (i1, (pa1, (m1, c1)))) := word_gc_move_list conf (pb, (len, (i, (pa, (old, (m, dm)))))) in
      word_gc_move_loop (k - 1) conf (pb, (i1, (pa1, (old, (m1, (dm, andb c c1)))))).
Proof.
  intros; unfold word_gc_move_loop.
  destruct (N.eqb_spec k 0) as [->|Hk]; [|rewrite (to_nat_pred k Hk)];
    cbn [word_gc_move_loop_f N.to_nat N.eqb Pos.to_nat]; destruct (decide (pb = pa)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_full_gc_def" *)
Definition word_full_gc (conf : config)
    (x : list (word_loc a) * (word a * (word a * (mem * dom))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(all_roots, (new, (old, (m, dm)))) := x in
  let '(rs, (i1, (pa1, (m1, c1)))) := word_gc_move_roots conf (all_roots, (n2w 0, (new, (old, (m, dm))))) in
  let '(i1, (pa1, (m1, c2))) := word_gc_move_loop (dimword a) conf (new, (i1, (pa1, (old, (m1, (dm, c1)))))) in
  (rs, (i1, (pa1, (m1, c2)))).

(** HOL's boolean [<=>] definition; here a [Prop]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_assum_def" *)
Definition word_gc_fun_assum (conf : config) (s : fmap store_name (word_loc a)) : Prop :=
  (Globals INSERT CurrHeap INSERT OtherHeap INSERT HeapLength INSERT
   TriggerGC INSERT GenStart INSERT EndOfHeap INSERT {}) SUBSET FDOM s /\
  isWord (FAPPLY s OtherHeap) /\
  isWord (FAPPLY s CurrHeap) /\
  isWord (FAPPLY s TriggerGC) /\
  isWord (FAPPLY s HeapLength) /\
  isWord (FAPPLY s GenStart) /\
  isWord (FAPPLY s EndOfHeap) /\
  isWord (FAPPLY s Globals) /\
  good_dimindex a /\
  len_size conf <> 0%N /\
  (len_size conf + 2 < dimindex a)%N /\
  (shift_length conf < dimindex a)%N.

(** HOL's boolean [<=>] definition; here a [Prop]. *)
(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_can_do_partial_def" *)
Definition word_gen_gc_can_do_partial (gen_sizes : list N) (s : fmap store_name (word_loc a)) : Prop :=
  gen_sizes <> [] /\
  let allo := theWord (FAPPLY s AllocSize) in
  let trig := theWord (FAPPLY s TriggerGC) in
  let endh := theWord (FAPPLY s EndOfHeap) in
  is_true (allo <=+ endh - trig).

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "new_trig_def" *)
Definition new_trig (heap_space alloc_pref : word a) (gs : list N) : word a :=
  let a0 := w2n alloc_pref in
  let g := w2n (get_gen_size gs : word a) in
  let h := w2n heap_space in
  if (a0 <=? g)%N then n2w (MIN h g) else
  if (h <? a0)%N then n2w h else
  if byte_aligned alloc_pref then alloc_pref else n2w h.

Fixpoint word_gen_gc_partial_move_ref_list_f (k : nat) (conf : config) (pb i pa old : word a)
    (m : mem) (dm : dom) (c : bool) (gs rs re : word a) : word a * (word a * (mem * bool)) :=
  if decide (pb = re) then (i, (pa, (m, c))) else
  match k with
  | O => (i, (pa, (m, false)))
  | Datatypes.S k =>
      let w := m pb in
      let c := andb c (andb ⌜pb IN dm⌝ (isWord w)) in
      let len := decode_length conf (theWord w) in
      let pb := pb + bytes_in_word in
      let '(pb, (i1, (pa1, (m1, c1)))) :=
        word_gen_gc_partial_move_list conf (pb, (len, (i, (pa, (old, (m, (dm, (gs, rs)))))))) in
      word_gen_gc_partial_move_ref_list_f k conf pb i1 pa1 old m1 dm (andb c c1) gs rs re
  end.

Definition word_gen_gc_partial_move_ref_list (k : N) (conf : config)
    (x : word a * (word a * (word a * (word a * (mem * (dom * (bool * (word a * (word a * word a)))))))))
    : word a * (word a * (mem * bool)) :=
  let '(pb, (i, (pa, (old, (m, (dm, (c, (gs, (rs, re))))))))) := x in
  word_gen_gc_partial_move_ref_list_f (N.to_nat k) conf pb i pa old m dm c gs rs re.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_ref_list_def" *)
Theorem word_gen_gc_partial_move_ref_list_def : forall k conf (pb i pa old : word a) m dm c gs rs re,
  word_gen_gc_partial_move_ref_list k conf (pb, (i, (pa, (old, (m, (dm, (c, (gs, (rs, re))))))))) =
  if decide (pb = re) then (i, (pa, (m, c))) else
  if (k =? 0)%N then (i, (pa, (m, false))) else
    let w := m pb in
    let c := andb c (andb ⌜pb IN dm⌝ (isWord w)) in
    let len := decode_length conf (theWord w) in
    let pb := pb + bytes_in_word in
    let '(pb, (i1, (pa1, (m1, c1)))) :=
      word_gen_gc_partial_move_list conf (pb, (len, (i, (pa, (old, (m, (dm, (gs, rs)))))))) in
    word_gen_gc_partial_move_ref_list (k - 1) conf
      (pb, (i1, (pa1, (old, (m1, (dm, (andb c c1, (gs, (rs, re))))))))).
Proof.
  intros; unfold word_gen_gc_partial_move_ref_list.
  destruct (N.eqb_spec k 0) as [->|Hk]; [|rewrite (to_nat_pred k Hk)];
    cbn [word_gen_gc_partial_move_ref_list_f N.to_nat N.eqb Pos.to_nat]; destruct (decide (pb = re)); reflexivity.
Qed.

Fixpoint word_gen_gc_partial_move_data_f (conf : config) (k : nat) (h2a i pa old : word a)
    (m : mem) (dm : dom) (gs rs : word a) : word a * (word a * (mem * bool)) :=
  if decide (h2a = pa) then (i, (pa, (m, true))) else
  match k with
  | O => (i, (pa, (m, false)))
  | Datatypes.S k =>
      let c := ⌜h2a IN dm⌝ in
      let v := m h2a in
      let c := andb c (isWord v) in
      let l := decode_length conf (theWord v) in
      if word_bit 2 (theWord v) then
        let h2a := h2a + (l + n2w 1) * bytes_in_word in
        let '(i, (pa, (m, c2))) := word_gen_gc_partial_move_data_f conf k h2a i pa old m dm gs rs in
        (i, (pa, (m, andb c c2)))
      else
        let '(h2a, (i, (pa, (m, c1)))) :=
          word_gen_gc_partial_move_list conf (h2a + bytes_in_word, (l, (i, (pa, (old, (m, (dm, (gs, rs)))))))) in
        let '(i, (pa, (m, c2))) := word_gen_gc_partial_move_data_f conf k h2a i pa old m dm gs rs in
        (i, (pa, (m, andb c (andb c1 c2))))
  end.

Definition word_gen_gc_partial_move_data (conf : config) (k : N)
    (x : word a * (word a * (word a * (word a * (mem * (dom * (word a * word a)))))))
    : word a * (word a * (mem * bool)) :=
  let '(h2a, (i, (pa, (old, (m, (dm, (gs, rs))))))) := x in
  word_gen_gc_partial_move_data_f conf (N.to_nat k) h2a i pa old m dm gs rs.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_move_data_def" *)
Theorem word_gen_gc_partial_move_data_def : forall conf k (h2a i pa old : word a) m dm gs rs,
  word_gen_gc_partial_move_data conf k (h2a, (i, (pa, (old, (m, (dm, (gs, rs))))))) =
  if decide (h2a = pa) then (i, (pa, (m, true))) else
  if (k =? 0)%N then (i, (pa, (m, false))) else
    let c := ⌜h2a IN dm⌝ in
    let v := m h2a in
    let c := andb c (isWord v) in
    let l := decode_length conf (theWord v) in
    if word_bit 2 (theWord v) then
      let h2a := h2a + (l + n2w 1) * bytes_in_word in
      let '(i, (pa, (m, c2))) := word_gen_gc_partial_move_data conf (k - 1) (h2a, (i, (pa, (old, (m, (dm, (gs, rs))))))) in
      (i, (pa, (m, andb c c2)))
    else
      let '(h2a, (i, (pa, (m, c1)))) :=
        word_gen_gc_partial_move_list conf (h2a + bytes_in_word, (l, (i, (pa, (old, (m, (dm, (gs, rs)))))))) in
      let '(i, (pa, (m, c2))) := word_gen_gc_partial_move_data conf (k - 1) (h2a, (i, (pa, (old, (m, (dm, (gs, rs))))))) in
      (i, (pa, (m, andb c (andb c1 c2)))).
Proof.
  intros; unfold word_gen_gc_partial_move_data.
  destruct (N.eqb_spec k 0) as [->|Hk]; [|rewrite (to_nat_pred k Hk)];
    cbn [word_gen_gc_partial_move_data_f N.to_nat N.eqb Pos.to_nat]; destruct (decide (h2a = pa)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_def" *)
Definition word_gen_gc_partial (conf : config)
    (x : list (word_loc a) * (word a * (word a * (word a * (mem * (dom * (word a * word a)))))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(roots, (curr, (new, (len, (m, (dm, (gs, rs))))))) := x in
  let refs_end := curr + len in
  let gen_start := gs >>> word_shift a in
  let '(roots, (i, (pa, (m, c1)))) :=
    word_gen_gc_partial_move_roots conf (roots, (gen_start, (new, (curr, (m, (dm, (gs, rs))))))) in
  let '(i, (pa, (m, c2))) :=
    word_gen_gc_partial_move_ref_list (dimword a) conf
      (curr + rs, (i, (pa, (curr, (m, (dm, (c1, (gs, (rs, refs_end))))))))) in
  let '(i, (pa, (m, c3))) :=
    word_gen_gc_partial_move_data conf (dimword a) (new, (i, (pa, (curr, (m, (dm, (gs, rs))))))) in
  (roots, (i, (pa, (m, andb c2 c3)))).

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_partial_full_def" *)
Definition word_gen_gc_partial_full (conf : config)
    (x : list (word_loc a) * (word a * (word a * (word a * (mem * (dom * (word a * word a)))))))
    : list (word_loc a) * (word a * (word a * (mem * bool))) :=
  let '(roots, (curr, (new, (len, (m, (dm, (gs, rs))))))) := x in
  let '(roots, (i, (pa, (m, c1)))) := word_gen_gc_partial conf (roots, (curr, (new, (len, (m, (dm, (gs, rs))))))) in
  let cpy_length := (pa - new) >>> word_shift a in
  let '(b1, (m, c2)) := memcpy cpy_length new (curr + gs) m dm in
  (roots, (i, (b1, (m, andb c1 c2)))).

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "is_ref_header_def" *)
Definition is_ref_header (v : word a) : bool := ⌜(v && n2w 12) = n2w 8⌝.

(** ** The generational collector *)

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_def" *)
Definition word_gen_gc_move (conf : config)
    (x : word_loc a * (word a * (word a * (word a * (word a * (word a * (mem * dom)))))))
    : word_loc a * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  let '(w0, (i, (pa, (ib, (pb, (old, (m, dm))))))) := x in
  match w0 with
  | Loc l1 l2 => (Loc l1 l2, (i, (pa, (ib, (pb, (m, (l2 =? 0)%N))))))
  | Word w =>
      if decide ((n2w 1 && w) = n2w 0) then (Word w, (i, (pa, (ib, (pb, (m, true)))))) else
        let c := ⌜ptr_to_addr conf old w IN dm⌝ in
        let v := m (ptr_to_addr conf old w) in
        let c := andb c (isWord v) in
        if is_fwd_ptr v then
          (Word (update_addr conf (theWord v >>> 2) w), (i, (pa, (ib, (pb, (m, c))))))
        else
          let header_addr := ptr_to_addr conf old w in
          let c := andb c (andb ⌜header_addr IN dm⌝ (isWord (m header_addr))) in
          let len := decode_length conf (theWord (m header_addr)) in
          if is_ref_header (theWord v) then
            let v := ib - (len + n2w 1) in
            let pb1 := pb - (len + n2w 1) * bytes_in_word in
            let '(_, (m1, c1)) := memcpy (len + n2w 1) header_addr pb1 m dm in
            let c := andb c (andb ⌜header_addr IN dm⌝ c1) in
            let m1 := (header_addr =+ Word (v << 2)) m1 in
            (Word (update_addr conf v w), (i, (pa, (v, (pb1, (m1, c))))))
          else
            let v := i + len + n2w 1 in
            let '(pa1, (m1, c1)) := memcpy (len + n2w 1) header_addr pa m dm in
            let c := andb c (andb ⌜header_addr IN dm⌝ c1) in
            let m1 := (header_addr =+ Word (i << 2)) m1 in
            (Word (update_addr conf i w), (v, (pa1, (ib, (pb, (m1, c))))))
  end.

Fixpoint word_gen_gc_move_roots_f (conf : config) (ws : list (word_loc a)) (i pa ib pb old : word a)
    (m : mem) (dm : dom) : list (word_loc a) * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  match ws with
  | [] => ([], (i, (pa, (ib, (pb, (m, true))))))
  | w :: ws =>
      let '(w1, (i1, (pa1, (ib, (pb, (m1, c1)))))) :=
        word_gen_gc_move conf (w, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
      let '(ws2, (i2, (pa2, (ib, (pb, (m2, c2)))))) := word_gen_gc_move_roots_f conf ws i1 pa1 ib pb old m1 dm in
      (w1 :: ws2, (i2, (pa2, (ib, (pb, (m2, andb c1 c2))))))
  end.

Definition word_gen_gc_move_roots (conf : config)
    (x : list (word_loc a) * (word a * (word a * (word a * (word a * (word a * (mem * dom)))))))
    : list (word_loc a) * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  let '(ws, (i, (pa, (ib, (pb, (old, (m, dm))))))) := x in word_gen_gc_move_roots_f conf ws i pa ib pb old m dm.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_roots_def" *)
Theorem word_gen_gc_move_roots_def : forall conf i pa ib pb old m dm w ws,
  word_gen_gc_move_roots conf ([], (i, (pa, (ib, (pb, (old, (m, dm))))))) =
    ([], (i, (pa, (ib, (pb, (m, true)))))) /\
  word_gen_gc_move_roots conf (w :: ws, (i, (pa, (ib, (pb, (old, (m, dm))))))) =
    let '(w1, (i1, (pa1, (ib, (pb, (m1, c1)))))) :=
      word_gen_gc_move conf (w, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
    let '(ws2, (i2, (pa2, (ib, (pb, (m2, c2)))))) :=
      word_gen_gc_move_roots conf (ws, (i1, (pa1, (ib, (pb, (old, (m1, dm))))))) in
    (w1 :: ws2, (i2, (pa2, (ib, (pb, (m2, andb c1 c2)))))).
Proof. intros; split; reflexivity. Qed.

Fixpoint word_gen_gc_move_list_f (fuel : nat) (conf : config) (a0 l i pa ib pb old : word a) (m : mem)
    (dm : dom) : word a * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  match fuel with
  | O => (a0, (i, (pa, (ib, (pb, (m, true))))))
  | Datatypes.S fuel =>
      if decide (l = n2w 0) then (a0, (i, (pa, (ib, (pb, (m, true)))))) else
        let w := m a0 in
        let '(w1, (i1, (pa1, (ib, (pb, (m1, c1)))))) :=
          word_gen_gc_move conf (w, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
        let m1 := (a0 =+ w1) m1 in
        let '(a2, (i2, (pa2, (ib, (pb, (m2, c2)))))) :=
          word_gen_gc_move_list_f fuel conf (a0 + bytes_in_word) (l - n2w 1) i1 pa1 ib pb old m1 dm in
        (a2, (i2, (pa2, (ib, (pb, (m2, andb ⌜a0 IN dm⌝ (andb c1 c2)))))))
  end.

Definition word_gen_gc_move_list (conf : config)
    (x : word a * (word a * (word a * (word a * (word a * (word a * (word a * (mem * dom))))))))
    : word a * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  let '(a0, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) := x in
  word_gen_gc_move_list_f (Datatypes.S (N.to_nat (w2n l))) conf a0 l i pa ib pb old m dm.

Lemma word_gen_gc_move_list_f_fuel : forall f1 f2 conf (a0 l i pa ib pb old : word a) m dm,
  (N.to_nat (w2n l) < f1)%nat -> (N.to_nat (w2n l) < f2)%nat ->
  word_gen_gc_move_list_f f1 conf a0 l i pa ib pb old m dm =
  word_gen_gc_move_list_f f2 conf a0 l i pa ib pb old m dm.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] conf a0 l i pa ib pb old m dm H1 H2; try lia.
  cbn [word_gen_gc_move_list_f]; destruct (decide (l = n2w 0)) as [E|E]; [reflexivity|].
  destruct (word_gen_gc_move conf _) as [w1 [i1 [pa1 [ib1 [pb1 [m1 c1]]]]]].
  rewrite (IH f2); [reflexivity| |]; rewrite w2n_sub1 by exact E;
    assert (w2n l <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_list_def" *)
Theorem word_gen_gc_move_list_def : forall conf (a0 l i pa ib pb old : word a) m dm,
  word_gen_gc_move_list conf (a0, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) =
  if decide (l = n2w 0) then (a0, (i, (pa, (ib, (pb, (m, true)))))) else
    let w := m a0 in
    let '(w1, (i1, (pa1, (ib, (pb, (m1, c1)))))) :=
      word_gen_gc_move conf (w, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
    let m1 := (a0 =+ w1) m1 in
    let '(a2, (i2, (pa2, (ib, (pb, (m2, c2)))))) :=
      word_gen_gc_move_list conf (a0 + bytes_in_word, (l - n2w 1, (i1, (pa1, (ib, (pb, (old, (m1, dm)))))))) in
    (a2, (i2, (pa2, (ib, (pb, (m2, andb ⌜a0 IN dm⌝ (andb c1 c2))))))).
Proof.
  intros; unfold word_gen_gc_move_list at 1; cbn [word_gen_gc_move_list_f].
  destruct (decide (l = n2w 0)) as [E|E]; [reflexivity|].
  cbv zeta. destruct (word_gen_gc_move conf _) as [w1 [i1 [pa1 [ib1 [pb1 [m1 c1]]]]]].
  unfold word_gen_gc_move_list.
  rewrite (word_gen_gc_move_list_f_fuel _ (Datatypes.S (N.to_nat (w2n (l - n2w 1))))); [reflexivity| |lia].
  rewrite w2n_sub1 by exact E; assert (w2n l <> 0%N) by (intros Z; apply E, w2n_eq_0, Z); lia.
Qed.

Fixpoint word_gen_gc_move_data_f (conf : config) (k : nat) (h2a i pa ib pb old : word a)
    (m : mem) (dm : dom) : word a * (word a * (word a * (word a * (mem * bool)))) :=
  if decide (h2a = pa) then (i, (pa, (ib, (pb, (m, true))))) else
  match k with
  | O => (i, (pa, (ib, (pb, (m, false)))))
  | Datatypes.S k =>
      let c := ⌜h2a IN dm⌝ in
      let v := m h2a in
      let c := andb c (isWord v) in
      let l := decode_length conf (theWord v) in
      if word_bit 2 (theWord v) then
        let h2a := h2a + (l + n2w 1) * bytes_in_word in
        let '(i, (pa, (ib, (pb, (m, c2))))) := word_gen_gc_move_data_f conf k h2a i pa ib pb old m dm in
        (i, (pa, (ib, (pb, (m, andb c c2)))))
      else
        let '(h2a, (i, (pa, (ib, (pb, (m, c1)))))) :=
          word_gen_gc_move_list conf (h2a + bytes_in_word, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
        let '(i, (pa, (ib, (pb, (m, c2))))) := word_gen_gc_move_data_f conf k h2a i pa ib pb old m dm in
        (i, (pa, (ib, (pb, (m, andb c (andb c1 c2))))))
  end.

Definition word_gen_gc_move_data (conf : config) (k : N)
    (x : word a * (word a * (word a * (word a * (word a * (word a * (mem * dom)))))))
    : word a * (word a * (word a * (word a * (mem * bool)))) :=
  let '(h2a, (i, (pa, (ib, (pb, (old, (m, dm))))))) := x in
  word_gen_gc_move_data_f conf (N.to_nat k) h2a i pa ib pb old m dm.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_data_def" *)
Theorem word_gen_gc_move_data_def : forall conf k (h2a i pa ib pb old : word a) m dm,
  word_gen_gc_move_data conf k (h2a, (i, (pa, (ib, (pb, (old, (m, dm))))))) =
  if decide (h2a = pa) then (i, (pa, (ib, (pb, (m, true))))) else
  if (k =? 0)%N then (i, (pa, (ib, (pb, (m, false))))) else
    let c := ⌜h2a IN dm⌝ in
    let v := m h2a in
    let c := andb c (isWord v) in
    let l := decode_length conf (theWord v) in
    if word_bit 2 (theWord v) then
      let h2a := h2a + (l + n2w 1) * bytes_in_word in
      let '(i, (pa, (ib, (pb, (m, c2))))) :=
        word_gen_gc_move_data conf (k - 1) (h2a, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
      (i, (pa, (ib, (pb, (m, andb c c2)))))
    else
      let '(h2a, (i, (pa, (ib, (pb, (m, c1)))))) :=
        word_gen_gc_move_list conf (h2a + bytes_in_word, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
      let '(i, (pa, (ib, (pb, (m, c2))))) :=
        word_gen_gc_move_data conf (k - 1) (h2a, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
      (i, (pa, (ib, (pb, (m, andb c (andb c1 c2)))))).
Proof.
  intros; unfold word_gen_gc_move_data.
  destruct (N.eqb_spec k 0) as [->|Hk]; [|rewrite (to_nat_pred k Hk)];
    cbn [word_gen_gc_move_data_f N.to_nat N.eqb Pos.to_nat]; destruct (decide (h2a = pa)); reflexivity.
Qed.

Fixpoint word_gen_gc_move_refs_f (conf : config) (k : nat) (r2a r1a i pa ib pb old : word a)
    (m : mem) (dm : dom) : word a * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  if decide (r2a = r1a) then (r2a, (i, (pa, (ib, (pb, (m, true)))))) else
  match k with
  | O => (r2a, (i, (pa, (ib, (pb, (m, false))))))
  | Datatypes.S k =>
      let c := ⌜r2a IN dm⌝ in
      let v := m r2a in
      let c := andb c (isWord v) in
      let l := decode_length conf (theWord v) in
      let '(r2a, (i, (pa, (ib, (pb, (m, c1)))))) :=
        word_gen_gc_move_list conf (r2a + bytes_in_word, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
      let '(r2a, (i, (pa, (ib, (pb, (m, c2)))))) := word_gen_gc_move_refs_f conf k r2a r1a i pa ib pb old m dm in
      (r2a, (i, (pa, (ib, (pb, (m, andb c (andb c1 c2)))))))
  end.

Definition word_gen_gc_move_refs (conf : config) (k : N)
    (x : word a * (word a * (word a * (word a * (word a * (word a * (word a * (mem * dom))))))))
    : word a * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  let '(r2a, (r1a, (i, (pa, (ib, (pb, (old, (m, dm)))))))) := x in
  word_gen_gc_move_refs_f conf (N.to_nat k) r2a r1a i pa ib pb old m dm.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_refs_def" *)
Theorem word_gen_gc_move_refs_def : forall conf k (r2a r1a i pa ib pb old : word a) m dm,
  word_gen_gc_move_refs conf k (r2a, (r1a, (i, (pa, (ib, (pb, (old, (m, dm)))))))) =
  if decide (r2a = r1a) then (r2a, (i, (pa, (ib, (pb, (m, true)))))) else
  if (k =? 0)%N then (r2a, (i, (pa, (ib, (pb, (m, false)))))) else
    let c := ⌜r2a IN dm⌝ in
    let v := m r2a in
    let c := andb c (isWord v) in
    let l := decode_length conf (theWord v) in
    let '(r2a, (i, (pa, (ib, (pb, (m, c1)))))) :=
      word_gen_gc_move_list conf (r2a + bytes_in_word, (l, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
    let '(r2a, (i, (pa, (ib, (pb, (m, c2)))))) :=
      word_gen_gc_move_refs conf (k - 1) (r2a, (r1a, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
    (r2a, (i, (pa, (ib, (pb, (m, andb c (andb c1 c2))))))).
Proof.
  intros; unfold word_gen_gc_move_refs.
  destruct (N.eqb_spec k 0) as [->|Hk]; [|rewrite (to_nat_pred k Hk)];
    cbn [word_gen_gc_move_refs_f N.to_nat N.eqb Pos.to_nat]; destruct (decide (r2a = r1a)); reflexivity.
Qed.

Fixpoint word_gen_gc_move_loop_f (conf : config) (k : nat) (pax i pa ib pb pbx old : word a)
    (m : mem) (dm : dom) : word a * (word a * (word a * (word a * (mem * bool)))) :=
  if decide (pbx = pb) then
    if decide (pax = pa) then (i, (pa, (ib, (pb, (m, true))))) else
      let '(i, (pa, (ib, (pb, (m, c1))))) :=
        word_gen_gc_move_data conf (dimword a) (pax, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
      match k with
      | O => (i, (pa, (ib, (pb, (m, false)))))
      | Datatypes.S k =>
          let '(i, (pa, (ib, (pb, (m, c2))))) := word_gen_gc_move_loop_f conf k pa i pa ib pb pbx old m dm in
          (i, (pa, (ib, (pb, (m, andb c1 c2)))))
      end
  else
    let '(pbx, (i, (pa, (ib, (pb', (m, c1)))))) :=
      word_gen_gc_move_refs conf (dimword a) (pb, (pbx, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
    match k with
    | O => (i, (pa, (ib, (pb, (m, false)))))
    | Datatypes.S k =>
        let '(i, (pa, (ib, (pb, (m, c2))))) := word_gen_gc_move_loop_f conf k pax i pa ib pb' pb old m dm in
        (i, (pa, (ib, (pb, (m, andb c1 c2)))))
    end.

Definition word_gen_gc_move_loop (conf : config) (k : N)
    (x : word a * (word a * (word a * (word a * (word a * (word a * (word a * (mem * dom))))))))
    : word a * (word a * (word a * (word a * (mem * bool)))) :=
  let '(pax, (i, (pa, (ib, (pb, (pbx, (old, (m, dm)))))))) := x in
  word_gen_gc_move_loop_f conf (N.to_nat k) pax i pa ib pb pbx old m dm.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_move_loop_def" *)
Theorem word_gen_gc_move_loop_def : forall conf k (pax i pa ib pb pbx old : word a) m dm,
  word_gen_gc_move_loop conf k (pax, (i, (pa, (ib, (pb, (pbx, (old, (m, dm)))))))) =
  if decide (pbx = pb) then
    if decide (pax = pa) then (i, (pa, (ib, (pb, (m, true))))) else
      let '(i, (pa, (ib, (pb, (m, c1))))) :=
        word_gen_gc_move_data conf (dimword a) (pax, (i, (pa, (ib, (pb, (old, (m, dm))))))) in
      if (k =? 0)%N then (i, (pa, (ib, (pb, (m, false))))) else
        let '(i, (pa, (ib, (pb, (m, c2))))) :=
          word_gen_gc_move_loop conf (k - 1) (pa, (i, (pa, (ib, (pb, (pbx, (old, (m, dm)))))))) in
        (i, (pa, (ib, (pb, (m, andb c1 c2)))))
  else
    let '(pbx, (i, (pa, (ib, (pb', (m, c1)))))) :=
      word_gen_gc_move_refs conf (dimword a) (pb, (pbx, (i, (pa, (ib, (pb, (old, (m, dm)))))))) in
    if (k =? 0)%N then (i, (pa, (ib, (pb, (m, false))))) else
      let '(i, (pa, (ib, (pb, (m, c2))))) :=
        word_gen_gc_move_loop conf (k - 1) (pax, (i, (pa, (ib, (pb', (pb, (old, (m, dm)))))))) in
      (i, (pa, (ib, (pb, (m, andb c1 c2))))).
Proof.
  intros; unfold word_gen_gc_move_loop.
  destruct (N.eqb_spec k 0) as [->|Hk]; [|rewrite (to_nat_pred k Hk)];
    cbn [word_gen_gc_move_loop_f N.to_nat N.eqb Pos.to_nat];
    destruct (decide (pbx = pb)); [destruct (decide (pax = pa))| |destruct (decide (pax = pa))|];
    try reflexivity;
    match goal with |- context [let '(_, _) := ?e in _] => destruct e as [? [? [? [? [? ?]]]]] end;
    reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gen_gc_def" *)
Definition word_gen_gc (conf : config)
    (x : list (word_loc a) * (word a * (word a * (word a * (mem * dom)))))
    : list (word_loc a) * (word a * (word a * (word a * (word a * (mem * bool))))) :=
  let '(roots, (curr, (new, (len, (m, dm))))) := x in
  let new_end := new + len in
  let len := len >>> word_shift a in
  let '(roots, (i, (pa, (ib, (pb, (m, c1)))))) :=
    word_gen_gc_move_roots conf (roots, (n2w 0, (new, (len, (new_end, (curr, (m, dm))))))) in
  let '(i, (pa, (ib, (pb, (m, c2))))) :=
    word_gen_gc_move_loop conf (w2n len) (new, (i, (pa, (ib, (pb, (new_end, (curr, (m, dm)))))))) in
  (roots, (i, (pa, (ib, (pb, (m, andb c1 c2)))))).

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "glob_real_def" *)
Definition glob_real (c : config) (curr : word a) (w : word_loc a) : word_loc a :=
  match w with
  | Word w => Word (curr + (w >>> shift_length c << word_shift a))
  | w => w
  end.

(** ** The GC function *)

Local Open Scope fmap_scope.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_def" *)
Definition word_gc_fun (conf : config) : gc_fun_type a :=
  fun '(roots, (m, (dm, s))) =>
    let c1 := ⌜word_gc_fun_assum conf s⌝ in
    let new := theWord (FAPPLY s OtherHeap) in
    let old := theWord (FAPPLY s CurrHeap) in
    let len := theWord (FAPPLY s HeapLength) in
    let all_roots := FAPPLY s Globals :: roots in
    match gc_kind conf with
    | gc_kind_None =>
        let s1 := s |++ [(NextFree, Word old); (TriggerGC, Word old); (EndOfHeap, Word old)] in
        if c1 then SOME (roots, (m, s1)) else NONE
    | Simple =>
        let '(roots1, (i1, (pa1, (m1, c2)))) := word_full_gc conf (all_roots, (new, (old, (m, dm)))) in
        let s1 := s |++ [(CurrHeap, Word new);
                         (OtherHeap, Word old);
                         (NextFree, Word pa1);
                         (TriggerGC, Word (new + len));
                         (EndOfHeap, Word (new + len));
                         (Globals, HD roots1);
                         (GlobReal, glob_real conf new (HD roots1))] in
        if andb c1 c2 then SOME (TL roots1, (m1, s1)) else NONE
    | Generational gen_sizes =>
        if negb c1 then NONE else
        if ⌜word_gen_gc_can_do_partial gen_sizes s⌝ then
          let gs := theWord (FAPPLY s GenStart) in
          let rs := theWord (FAPPLY s EndOfHeap) - theWord (FAPPLY s CurrHeap) in
          let len := theWord (FAPPLY s HeapLength) in
          let endh := theWord (FAPPLY s EndOfHeap) in
          let '(roots1, (i1, (pa1, (m1, c2)))) :=
            word_gen_gc_partial_full conf (all_roots, (old, (new, (len, (m, (dm, (gs, rs))))))) in
          let a0 := theWord (FAPPLY s AllocSize) in
          let s1 := s |++ [(CurrHeap, Word old);
                           (OtherHeap, Word new);
                           (NextFree, Word pa1);
                           (GenStart, Word (pa1 - old));
                           (TriggerGC, Word (pa1 + new_trig (endh - pa1) a0 gen_sizes));
                           (Globals, HD roots1);
                           (GlobReal, glob_real conf old (HD roots1));
                           (Temp (n2w 0), Word (n2w 0));
                           (Temp (n2w 1), Word (n2w 0))] in
          let c3 := andb (a0 <=+ endh - pa1) (a0 <=+ new_trig (endh - pa1) a0 gen_sizes) in
          if andb c2 c3 then SOME (TL roots1, (m1, s1)) else NONE
        else
          let '(roots1, (i1, (pa1, (ib1, (pb1, (m1, c2)))))) :=
            word_gen_gc conf (all_roots, (old, (new, (len, (m, dm))))) in
          let a0 := theWord (FAPPLY s AllocSize) in
          let s1 := s |++ [(CurrHeap, Word new);
                           (OtherHeap, Word old);
                           (NextFree, Word pa1);
                           (GenStart, Word (pa1 - new));
                           (TriggerGC, Word (pa1 + new_trig (pb1 - pa1) a0 gen_sizes));
                           (EndOfHeap, Word pb1);
                           (Globals, HD roots1);
                           (GlobReal, glob_real conf new (HD roots1));
                           (Temp (n2w 0), Word (n2w 0));
                           (Temp (n2w 1), Word (n2w 0));
                           (Temp (n2w 2), Word (n2w 0));
                           (Temp (n2w 3), Word (n2w 0));
                           (Temp (n2w 4), Word (n2w 0));
                           (Temp (n2w 5), Word (n2w 0));
                           (Temp (n2w 6), Word (n2w 0))] in
          if c2 then SOME (TL roots1, (m1, s1)) else NONE
    end.

(** Galette-only: the root moves preserve the number of roots. *)
Lemma word_gc_move_roots_f_LENGTH conf : forall ws (i pa old : word a) m dm,
  LENGTH (fst (word_gc_move_roots_f conf ws i pa old m dm)) = LENGTH ws.
Proof.
  induction ws as [|w ws IH]; intros; cbn [word_gc_move_roots_f]; [reflexivity|].
  destruct (word_gc_move conf _) as [w1 [i1 [pa1 [m1 c1]]]].
  specialize (IH i1 pa1 old m1 dm).
  destruct (word_gc_move_roots_f conf ws i1 pa1 old m1 dm) as [ws2 [i2 [pa2 [m2 c2]]]].
  cbn [fst] in *; rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

Lemma word_gen_gc_partial_move_roots_f_LENGTH conf : forall ws (i pa old : word a) m dm gs rs,
  LENGTH (fst (word_gen_gc_partial_move_roots_f conf ws i pa old m dm gs rs)) = LENGTH ws.
Proof.
  induction ws as [|w ws IH]; intros; cbn [word_gen_gc_partial_move_roots_f]; [reflexivity|].
  destruct (word_gen_gc_partial_move conf _) as [w1 [i1 [pa1 [m1 c1]]]].
  specialize (IH i1 pa1 old m1 dm gs rs).
  destruct (word_gen_gc_partial_move_roots_f conf ws i1 pa1 old m1 dm gs rs) as [ws2 [i2 [pa2 [m2 c2]]]].
  cbn [fst] in *; rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

Lemma word_gen_gc_move_roots_f_LENGTH conf : forall ws (i pa ib pb old : word a) m dm,
  LENGTH (fst (word_gen_gc_move_roots_f conf ws i pa ib pb old m dm)) = LENGTH ws.
Proof.
  induction ws as [|w ws IH]; intros; cbn [word_gen_gc_move_roots_f]; [reflexivity|].
  destruct (word_gen_gc_move conf _) as [w1 [i1 [pa1 [ib1 [pb1 [m1 c1]]]]]].
  specialize (IH i1 pa1 ib1 pb1 old m1 dm).
  destruct (word_gen_gc_move_roots_f conf ws i1 pa1 ib1 pb1 old m1 dm) as [ws2 [i2 [pa2 [ib2 [pb2 [m2 c2]]]]]].
  cbn [fst] in *; rewrite !LENGTH_length in *; cbn [length]; lia.
Qed.

Lemma LENGTH_TL_cons {B} (l : list B) n : LENGTH l = (n + 1)%N -> LENGTH (TL l) = n.
Proof. destruct l; rewrite !LENGTH_length; cbn [TL length]; lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml" "word_gc_fun_LENGTH" *)
Theorem word_gc_fun_LENGTH : forall c (xs : list (word_loc a)) m dm s zs m1 s1,
  word_gc_fun c (xs, (m, (dm, s))) = SOME (zs, (m1, s1)) -> LENGTH xs = LENGTH zs.
Proof.
  intros c xs m dm s zs m1 s1 H; unfold word_gc_fun in H; cbv zeta in H.
  destruct (gc_kind c) as [| |gens].
  - destruct (⌜word_gc_fun_assum c s⌝); [|discriminate]. injection H as <- _ _; reflexivity.
  - unfold word_full_gc, word_gc_move_roots in H.
    pose proof (word_gc_move_roots_f_LENGTH c (FAPPLY s Globals :: xs) (n2w 0)
      (theWord (FAPPLY s OtherHeap)) (theWord (FAPPLY s CurrHeap)) m dm) as HL.
    destruct (word_gc_move_roots_f _ _ _ _ _ _ _) as [rs [i1 [pa1 [m1' c1]]]].
    destruct (word_gc_move_loop _ _ _) as [i2 [pa2 [m2 c2]]].
    destruct (andb _ _); [|discriminate]. injection H as <- _ _.
    cbn [fst] in HL; symmetry; apply LENGTH_TL_cons; rewrite HL, !LENGTH_length; cbn [length]; lia.
  - destruct (negb _); [discriminate|].
    destruct (⌜word_gen_gc_can_do_partial gens s⌝).
    + unfold word_gen_gc_partial_full, word_gen_gc_partial, word_gen_gc_partial_move_roots in H.
      match type of H with context [word_gen_gc_partial_move_roots_f ?cc ?ws ?i ?pa ?old ?mm ?d ?g ?r] =>
        pose proof (word_gen_gc_partial_move_roots_f_LENGTH cc ws i pa old mm d g r) as HL;
        destruct (word_gen_gc_partial_move_roots_f cc ws i pa old mm d g r) as [rs [i1 [pa1 [m1' c1]]]] end.
      destruct (word_gen_gc_partial_move_ref_list _ _ _) as [i2 [pa2 [m2 c2]]].
      destruct (word_gen_gc_partial_move_data _ _ _) as [i3 [pa3 [m3 c3]]].
      destruct (memcpy _ _ _ _ _) as [b1 [m4 c4]].
      destruct (andb _ _); [|discriminate]. injection H as <- _ _.
      cbn [fst] in HL; symmetry; apply LENGTH_TL_cons; rewrite HL, !LENGTH_length; cbn [length]; lia.
    + unfold word_gen_gc, word_gen_gc_move_roots in H.
      match type of H with context [word_gen_gc_move_roots_f ?cc ?ws ?i ?pa ?ib ?pb ?old ?mm ?d] =>
        pose proof (word_gen_gc_move_roots_f_LENGTH cc ws i pa ib pb old mm d) as HL;
        destruct (word_gen_gc_move_roots_f cc ws i pa ib pb old mm d) as [rs [i1 [pa1 [ib1 [pb1 [m1' c1]]]]]] end.
      destruct (word_gen_gc_move_loop _ _ _) as [i2 [pa2 [ib2 [pb2 [m2 c2]]]]].
      destruct (andb _ _); [|discriminate]. injection H as <- _ _.
      cbn [fst] in HL; symmetry; apply LENGTH_TL_cons; rewrite HL, !LENGTH_length; cbn [length]; lia.
Qed.

End GC.
