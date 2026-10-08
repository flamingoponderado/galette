(** * CakeML [mlstring]: the string type of CakeML's basis

    HOL: [Datatype: mlstring = implode string], with [strlit] an overload of
    the constructor [implode] (CakeML writes [strlit s] or [«...»]).  Here
    [implode] is the constructor and [strlit] an abbreviation of it; HOL
    [string] is [list ascii] (see [theories/HOL/src/string/string.v]), so
    HOL's [«abc»] is [strlit "abc"] with ["abc"] in [hol_string_scope].
    [s1 ^ s2] is [strcat s1 s2] in [mlstring_scope] (Rocq reserves [^] as
    right-associative, HOL's is left-associative; harmless since [strcat] is
    associative).

    HOL [num] is [N].  The HOL definitions by recursion on [SUC len]
    ([explode_aux], [translate_aux], [tokens_aux], [fields_aux],
    [isStringThere_aux], [isSubstring_aux], [collate_aux]) and on
    [len - 1] ([compare_aux]) use [num_rec]; HOL's equations are the tagged
    [_def] theorems.

    Executable versions: [explode] is the projection, [translate] maps over
    the character list, and [compare] is [string_compare] (lexicographic
    [list_compare char_compare]); HOL defines them through the quadratic
    [strsub] loops, and their HOL definitions are the tagged [_def]
    theorems.

    Not ported: [substring_def] is stated with [rich_list]'s [SEG] (the
    definition here uses [TAKE]/[DROP], which agree with [SEG] in range, and
    is untagged); [splitl_aux_def]/[splitl_def], [str_findi_def],
    [tokens_alt_aux_def], [fields_alt_aux_def] and the theorems relating
    [tokens]/[fields]/[splitl] to [TOKENS]/[FIELDS]/[SPLITP] (need
    [rich_list]); [concatWith_def] (needs [mllist]'s [intersperse]);
    [TotOrd_compare], [good_cmp_compare], [StrongLinearOrder_*],
    [transitive_*], [total_*], [antisymmetric_*], [implode_BIJ]/[explode_BIJ],
    [mlstring_lt_inv_image] (need [toto]/[comparison]/[relation]/[pred_set];
    [mlstring_lt_string_lt] below is the pointwise form of
    [mlstring_lt_inv_image]); [collate_thm] (needs [mllist]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
Open Scope N_scope.
Open Scope hol_string_scope.

(** ** List helpers (Galette infrastructure) *)

Lemma LENGTH_TAKE_le {A} n (l : list A) : n <= LENGTH l -> LENGTH (TAKE n l) = n.
Proof. intros H; rewrite TAKE_firstn, !LENGTH_length in *; rewrite length_firstn; lia. Qed.

Lemma LENGTH_DROP {A} n (l : list A) : LENGTH (DROP n l) = LENGTH l - n.
Proof. rewrite DROP_skipn, !LENGTH_length, length_skipn; lia. Qed.

Lemma DROP_EL_CONS {A} `{Inhabited A} n (l : list A) :
  n < LENGTH l -> DROP n l = EL n l :: DROP (n + 1) l.
Proof.
  intros Hn; rewrite !DROP_skipn, EL_nth by exact Hn; rewrite LENGTH_length in Hn.
  replace (N.to_nat (n + 1)) with (S (N.to_nat n)) by lia.
  assert (Hn' : (N.to_nat n < length l)%nat) by lia; clear Hn.
  generalize (N.to_nat n) as k, Hn'; clear n Hn'.
  induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; auto.
  apply IH; lia.
Qed.

Lemma DROP_LENGTH_TOO_LONG {A} n (l : list A) : LENGTH l <= n -> DROP n l = [].
Proof. intros H; rewrite DROP_skipn; apply skipn_all2; rewrite LENGTH_length in H; lia. Qed.

Lemma DROP_0 {A} (l : list A) : DROP 0 l = l.
Proof. destruct l; reflexivity. Qed.

(** ** The type *)

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring" *)
Inductive mlstring : Type := implode (s : string).

Abbreviation strlit := implode.

#[global] Instance mlstring_eq_dec : EqDecision mlstring.
Proof.
  intros [s] [t]; destruct (decide (s = t)) as [->|n]; [left; reflexivity|right; congruence].
Defined.

#[global] Instance mlstring_inhabited : Inhabited mlstring := implode [].

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlen_def" *)
Definition strlen (s : mlstring) : N := match s with implode s => LENGTH s end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strsub_def" *)
Definition strsub (s : mlstring) (n : N) : ascii := match s with implode s => EL n s end.

(** HOL [substring_def] (untagged, see the header):
    [substring (strlit s) off len = strlit (if off + len <= LENGTH s then
    SEG len off s else if off <= LENGTH s then DROP off s else "")]. *)
Definition substring (s : mlstring) (off len : N) : mlstring :=
  match s with
  | implode s =>
      implode (if off + len <=? LENGTH s then TAKE len (DROP off s)
               else if off <=? LENGTH s then DROP off s else [])
  end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "concat_def" *)
Definition concat (l : list mlstring) : mlstring :=
  implode (FLAT (MAP (fun s => match s with implode x => x end) l)).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "concat_nil" *)
Theorem concat_nil : concat [] = strlit "".
Proof. reflexivity. Qed.

Definition explode_aux (s : mlstring) (n len : N) : string :=
  num_rec (fun _ => []) (fun _ r n => strsub s n :: r (n + 1)) len n.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_aux_def" *)
Theorem explode_aux_def : forall s n len,
  explode_aux s n 0 = [] /\
  explode_aux s n (SUC len) = strsub s n :: explode_aux s (n + 1) len.
Proof. intros; split; [reflexivity|]. unfold explode_aux; rewrite num_rec_SUC; reflexivity. Qed.

(** HOL [explode]: the projection ([explode_def] below). *)
Definition explode (s : mlstring) : string := match s with implode s => s end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_aux_thm" *)
Theorem explode_aux_thm : forall max n ls,
  n + max = LENGTH ls -> explode_aux (strlit ls) n max = DROP n ls.
Proof.
  intros max; induction max as [|max IH] using N.peano_ind; intros n ls H.
  - rewrite (proj1 (explode_aux_def _ _ 0)), DROP_LENGTH_TOO_LONG by lia; reflexivity.
  - rewrite (proj2 (explode_aux_def _ _ _)), IH by lia.
    rewrite (DROP_EL_CONS n ls) by lia; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_def" *)
Theorem explode_def : forall s, explode s = explode_aux s 0 (strlen s).
Proof.
  intros [s]; cbn [explode strlen]; rewrite explode_aux_thm by lia.
  symmetry; apply DROP_0.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_thm" *)
Theorem explode_thm : forall ls, explode (strlit ls) = ls.
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_implode" *)
Theorem explode_implode : forall x, explode (implode x) = x.
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "implode_explode" *)
Theorem implode_explode : forall x, implode (explode x) = x.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_11" *)
Theorem explode_11 : forall s1 s2, explode s1 = explode s2 <-> s1 = s2.
Proof. intros [] []; cbn; split; congruence. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "LENGTH_explode" *)
Theorem LENGTH_explode : forall s, LENGTH (explode s) = strlen s.
Proof. intros []; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "concat_thm" *)
Theorem concat_thm : forall l, concat l = implode (FLAT (MAP explode l)).
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlen_implode" *)
Theorem strlen_implode : forall s, strlen (implode s) = LENGTH s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlen_substring" *)
Theorem strlen_substring : forall s i j,
  strlen (substring s i j) =
  if i + j <=? strlen s then j else if i <=? strlen s then strlen s - i else 0.
Proof.
  intros [s] i j; cbn [substring strlen].
  destruct (N.leb_spec (i + j) (LENGTH s)).
  - apply LENGTH_TAKE_le; rewrite LENGTH_DROP; lia.
  - destruct (N.leb_spec i (LENGTH s)); [apply LENGTH_DROP|reflexivity].
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "extract_def" *)
Definition extract (s : mlstring) (i : N) (opt : option N) : mlstring :=
  if strlen s <=? i then implode []
  else match opt with
       | Some x => substring s i (MIN (strlen s - i) x)
       | None => substring s i (strlen s - i)
       end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlen_extract_le" *)
Theorem strlen_extract_le : forall s x y, strlen (extract s x y) <= strlen s - x.
Proof.
  intros s x y; unfold extract.
  destruct (N.leb_spec (strlen s) x); [cbn; lia|].
  destruct y as [y|]; rewrite strlen_substring; rewrite ?MIN_min;
    repeat match goal with |- context [?a <=? ?b] => destruct (N.leb_spec a b) end; lia.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "substring_full" *)
Theorem substring_full : forall s, substring s 0 (strlen s) = s.
Proof.
  intros [s]; cbn [substring strlen]; rewrite N.add_0_l, N.leb_refl, DROP_0, TAKE_firstn.
  rewrite LENGTH_length, Nat2N.id, firstn_all; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "substring_too_long" *)
Theorem substring_too_long : forall s i j, strlen s <= i -> substring s i j = strlit "".
Proof.
  intros [s] i j; cbn [substring strlen]; intros H.
  destruct (N.leb_spec (i + j) (LENGTH s)).
  - assert (j = 0) as -> by lia; rewrite TAKE_firstn; reflexivity.
  - destruct (N.leb_spec i (LENGTH s)); [|reflexivity].
    rewrite DROP_LENGTH_TOO_LONG by lia; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "substring_0" *)
Theorem substring_0 : forall s i, substring s i 0 = strlit "".
Proof.
  intros [s] i; cbn [substring]; rewrite N.add_0_r, TAKE_firstn.
  destruct (N.leb_spec i (LENGTH s)); reflexivity.
Qed.

(** ** Concatenation *)

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strcat_def" *)
Definition strcat (s1 s2 : mlstring) : mlstring := concat [s1; s2].

Declare Scope mlstring_scope.
Delimit Scope mlstring_scope with mlstring.
Bind Scope mlstring_scope with mlstring.
Infix "^" := strcat : mlstring_scope.
Open Scope mlstring_scope.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strcat_thm" *)
Theorem strcat_thm : forall s1 s2, strcat s1 s2 = implode (explode s1 ++ explode s2).
Proof. intros [s1] [s2]; unfold strcat, concat; cbn; rewrite app_nil_r; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "concat_cons" *)
Theorem concat_cons : forall h t, concat (h :: t) = strcat h (concat t).
Proof. intros [h] t; rewrite strcat_thm; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strcat_assoc" *)
Theorem strcat_assoc : forall s1 s2 s3, s1 ^ (s2 ^ s3) = (s1 ^ s2) ^ s3.
Proof. intros [] [] []; rewrite !strcat_thm; cbn; rewrite app_assoc; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strcat_o" *)
Theorem strcat_o : forall x y, (fun z => strcat x (strcat y z)) = strcat (x ^ y).
Proof. intros x y; apply functional_extensionality; intros z; apply strcat_assoc. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strcat_nil" *)
Theorem strcat_nil : forall s, strcat (strlit "") s = s /\ strcat s (strlit "") = s.
Proof.
  intros [s]; rewrite !strcat_thm; cbn; split; [reflexivity|].
  rewrite app_nil_r; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_common_prefix" *)
Theorem mlstring_common_prefix : forall s t1 t2, s ^ t1 = s ^ t2 <-> t1 = t2.
Proof.
  intros [s] [t1] [t2]; rewrite !strcat_thm; cbn; split; [|congruence].
  intros H; injection H as H; apply app_inv_head in H; congruence.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_common_suffix" *)
Theorem mlstring_common_suffix : forall s t1 t2, t1 ^ s = t2 ^ s <-> t1 = t2.
Proof.
  intros [s] [t1] [t2]; rewrite !strcat_thm; cbn; split; [|congruence].
  intros H; injection H as H; apply app_inv_tail in H; congruence.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "concat_append" *)
Theorem concat_append : forall xs ys, concat (xs ++ ys) = concat xs ^ concat ys.
Proof.
  intros xs ys; induction xs as [|x xs IH]; cbn [app].
  - symmetry; apply strcat_nil.
  - rewrite !concat_cons, IH; apply strcat_assoc.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "implode_STRCAT" *)
Theorem implode_STRCAT : forall l1 l2, implode (STRCAT l1 l2) = implode l1 ^ implode l2.
Proof. intros; rewrite strcat_thm; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_strcat" *)
Theorem explode_strcat : forall s1 s2, explode (strcat s1 s2) = explode s1 ++ explode s2.
Proof. intros; rewrite strcat_thm; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlen_strcat" *)
Theorem strlen_strcat : forall s1 s2, strlen (strcat s1 s2) = strlen s1 + strlen s2.
Proof. intros [] []; rewrite strcat_thm; apply STRLEN_CAT. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlit_STRCAT" *)
Theorem strlit_STRCAT : forall a b, strlit a ^ strlit b = strlit (a ++ b).
Proof. intros; rewrite strcat_thm; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "concat_sing" *)
Theorem concat_sing : forall x, concat [x] = x.
Proof. intros [x]; unfold concat; cbn; rewrite app_nil_r; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "chr_to_str_def" *)
Definition chr_to_str (c : ascii) : mlstring := implode [c].

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "explode_toString" *)
Theorem explode_toString : forall c, explode (chr_to_str c) = [c].
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlen_toString" *)
Theorem strlen_toString : forall c, strlen (chr_to_str c) = 1.
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "substring_1_strsub" *)
Theorem substring_1_strsub : forall s i, i < strlen s -> substring s i 1 = chr_to_str (strsub s i).
Proof.
  intros [s] i; cbn [substring strlen strsub]; unfold chr_to_str; intros H.
  replace (i + 1 <=? LENGTH s) with true by (symmetry; apply N.leb_le; lia).
  rewrite (DROP_EL_CONS i s H), TAKE_firstn; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "substring_add" *)
Theorem substring_add : forall s i x y,
  i + x + y <= strlen s -> substring s i (x + y) = substring s i x ^ substring s (i + x) y.
Proof.
  intros [s] i x y H; cbn [substring strlen] in *.
  replace (i + (x + y) <=? LENGTH s) with true by (symmetry; apply N.leb_le; lia).
  replace (i + x <=? LENGTH s) with true by (symmetry; apply N.leb_le; lia).
  replace (i + x + y <=? LENGTH s) with true by (symmetry; apply N.leb_le; lia).
  rewrite strlit_STRCAT, !TAKE_firstn, !DROP_skipn; f_equal.
  rewrite !N2Nat.inj_add.
  replace (N.to_nat i + N.to_nat x)%nat with (N.to_nat x + N.to_nat i)%nat by lia.
  rewrite <- skipn_skipn.
  generalize (skipn (N.to_nat i) s) as l; intros l.
  generalize (N.to_nat x) as a, (N.to_nat y) as b; intros a b.
  revert l; induction a as [|a IH]; intros [|h l]; cbn; auto.
  - destruct b; reflexivity.
  - f_equal; apply IH.
Qed.

(** ** [translate] *)

Definition translate_aux (f : ascii -> ascii) (s : mlstring) (n len : N) : string :=
  num_rec (fun _ => []) (fun _ r n => f (strsub s n) :: r (n + 1)) len n.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "translate_aux_def" *)
Theorem translate_aux_def : forall f s n len,
  translate_aux f s n 0 = [] /\
  translate_aux f s n (SUC len) = f (strsub s n) :: translate_aux f s (n + 1) len.
Proof. intros; split; [reflexivity|]. unfold translate_aux; rewrite num_rec_SUC; reflexivity. Qed.

(** HOL [translate] (computed by mapping; [translate_def] below). *)
Definition translate (f : ascii -> ascii) (s : mlstring) : mlstring := implode (MAP f (explode s)).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "translate_thm" *)
Theorem translate_thm : forall f s, translate f s = implode (MAP f (explode s)).
Proof. reflexivity. Qed.

Lemma translate_aux_thm f s n len :
  n + len = strlen s -> translate_aux f s n len = MAP f (DROP n (explode s)).
Proof.
  destruct s as [s]; cbn [strlen explode]; revert n.
  induction len as [|len IH] using N.peano_ind; intros n H.
  - rewrite (proj1 (translate_aux_def _ _ _ 0)), DROP_LENGTH_TOO_LONG by lia; reflexivity.
  - rewrite (proj2 (translate_aux_def _ _ _ _)), IH by lia.
    rewrite (DROP_EL_CONS n s) by lia; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "translate_def" *)
Theorem translate_def : forall f s, translate f s = implode (translate_aux f s 0 (strlen s)).
Proof. intros f s; rewrite translate_aux_thm by lia; rewrite DROP_0; reflexivity. Qed.

(** ** [tokens] and [fields] *)

Definition tokens_aux (f : ascii -> bool) (s : mlstring) (ss : string) (n len : N)
  : list mlstring :=
  num_rec
    (fun ss _ => match ss with [] => [] | h :: t => [implode (REVERSE (h :: t))] end)
    (fun _ r ss n =>
       match ss with
       | [] => if f (strsub s n) then r [] (n + 1) else r [strsub s n] (n + 1)
       | h :: t =>
           if f (strsub s n) then implode (REVERSE (h :: t)) :: r [] (n + 1)
           else r (strsub s n :: h :: t) (n + 1)
       end) len ss n.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "tokens_aux_def" *)
Theorem tokens_aux_def : forall f s h t n len,
  tokens_aux f s [] n 0 = [] /\
  tokens_aux f s (h :: t) n 0 = [implode (REVERSE (h :: t))] /\
  tokens_aux f s [] n (SUC len) =
    (if f (strsub s n) then tokens_aux f s [] (n + 1) len
     else tokens_aux f s [strsub s n] (n + 1) len) /\
  tokens_aux f s (h :: t) n (SUC len) =
    (if f (strsub s n) then implode (REVERSE (h :: t)) :: tokens_aux f s [] (n + 1) len
     else tokens_aux f s (strsub s n :: h :: t) (n + 1) len).
Proof.
  intros; unfold tokens_aux; rewrite !num_rec_SUC; repeat split; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "tokens_def" *)
Definition tokens (f : ascii -> bool) (s : mlstring) : list mlstring := tokens_aux f s [] 0 (strlen s).

Definition fields_aux (f : ascii -> bool) (s : mlstring) (ss : string) (n len : N)
  : list mlstring :=
  num_rec (fun ss _ => [implode (REVERSE ss)])
    (fun _ r ss n =>
       if f (strsub s n) then implode (REVERSE ss) :: r [] (n + 1)
       else r (strsub s n :: ss) (n + 1)) len ss n.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "fields_aux_def" *)
Theorem fields_aux_def : forall f s ss n len,
  fields_aux f s ss n 0 = [implode (REVERSE ss)] /\
  fields_aux f s ss n (SUC len) =
    (if f (strsub s n) then implode (REVERSE ss) :: fields_aux f s [] (n + 1) len
     else fields_aux f s (strsub s n :: ss) (n + 1) len).
Proof. intros; unfold fields_aux; rewrite !num_rec_SUC; split; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "fields_def" *)
Definition fields (f : ascii -> bool) (s : mlstring) : list mlstring := fields_aux f s [] 0 (strlen s).

(** ** Substring tests *)

Definition isStringThere_aux (s1 s2 : mlstring) (s1i s2i len : N) : bool :=
  num_rec (fun _ _ => true)
    (fun _ r s1i s2i =>
       if decide (strsub s1 s1i = strsub s2 s2i) then r (s1i + 1) (s2i + 1) else false)
    len s1i s2i.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isStringThere_aux_def" *)
Theorem isStringThere_aux_def : forall s1 s2 s1i s2i len,
  isStringThere_aux s1 s2 s1i s2i 0 = true /\
  isStringThere_aux s1 s2 s1i s2i (SUC len) =
    (if decide (strsub s1 s1i = strsub s2 s2i)
     then isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len else false).
Proof. intros; unfold isStringThere_aux; rewrite !num_rec_SUC; split; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isPrefix_def" *)
Definition isPrefix (s1 s2 : mlstring) : bool :=
  if strlen s1 <=? strlen s2 then isStringThere_aux s1 s2 0 0 (strlen s1) else false.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isSuffix_def" *)
Definition isSuffix (s1 s2 : mlstring) : bool :=
  if strlen s1 <=? strlen s2
  then isStringThere_aux s1 s2 0 (strlen s2 - strlen s1) (strlen s1)
  else false.

Definition isSubstring_aux (s1 s2 : mlstring) (lens1 n len : N) : bool :=
  num_rec (fun _ => false)
    (fun _ r n => if isStringThere_aux s1 s2 0 n lens1 then true else r (n + 1)) len n.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isSubstring_aux_def" *)
Theorem isSubstring_aux_def : forall s1 s2 lens1 n len,
  isSubstring_aux s1 s2 lens1 n 0 = false /\
  isSubstring_aux s1 s2 lens1 n (SUC len) =
    (if isStringThere_aux s1 s2 0 n lens1 then true
     else isSubstring_aux s1 s2 lens1 (n + 1) len).
Proof. intros; unfold isSubstring_aux; rewrite !num_rec_SUC; split; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isSubstring_def" *)
Definition isSubstring (s1 s2 : mlstring) : bool :=
  if strlen s1 <=? strlen s2
  then isSubstring_aux s1 s2 (strlen s1) 0 (strlen s2 - strlen s1 + 1)
  else false.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "exists_mlstring" *)
Theorem exists_mlstring : forall P : mlstring -> Prop, (exists x, P x) <-> (exists s, P (strlit s)).
Proof. intros P; split; [intros [[s] H]; eauto|intros [s H]; eauto]. Qed.

Lemma isStringThere_aux_shift c1 s1 c2 s2 i j len :
  isStringThere_aux (strlit (c1 :: s1)) (strlit (c2 :: s2)) (SUC i) (SUC j) len =
  isStringThere_aux (strlit s1) (strlit s2) i j len.
Proof.
  revert i j; induction len as [|len IH] using N.peano_ind; intros i j; [reflexivity|].
  rewrite !(proj2 (isStringThere_aux_def _ _ _ _ _)).
  cbn [strsub]; rewrite !EL_SUC; cbn [TL].
  rewrite <- IH, !N.add_1_r; reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isprefix_thm" *)
Theorem isprefix_thm : forall s1 s2, isPrefix s1 s2 <-> isPREFIX (explode s1) (explode s2).
Proof.
  intros [s] [t]; unfold isPrefix; cbn [strlen explode].
  destruct (N.leb_spec (LENGTH s) (LENGTH t)) as [Hle|Hlt].
  - revert t Hle; induction s as [|c s IH]; intros [|d t] Hle; cbn [LENGTH] in Hle; try lia;
      try (split; reflexivity).
    cbn [LENGTH isPREFIX].
    rewrite (proj2 (isStringThere_aux_def (strlit (STRING c s)) (strlit (STRING d t)) 0 0 (LENGTH s))).
    change (0 + 1) with (SUC 0); rewrite isStringThere_aux_shift.
    change (strsub (strlit (STRING c s)) 0) with c; change (strsub (strlit (STRING d t)) 0) with d.
    unfold is_true; rewrite andb_true_iff, bool_decide_spec.
    destruct (decide (c = d)) as [->|n].
    + fold (is_true (isStringThere_aux (strlit s) (strlit t) 0 0 (LENGTH s))).
      fold (is_true (isPREFIX s t)).
      rewrite IH by lia; tauto.
    + split; [discriminate|intros [? _]; contradiction].
  - split; [discriminate|].
    intros H; apply isPREFIX_STRCAT in H as [s3 ->].
    rewrite STRLEN_CAT in Hlt; lia.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "isprefix_strcat" *)
Theorem isprefix_strcat : forall s1 s2, isPrefix s1 s2 <-> exists s3, s2 = s1 ^ s3.
Proof.
  intros [s1] [s2]; rewrite isprefix_thm, isPREFIX_STRCAT; cbn [explode].
  split.
  - intros [s3 ->]; exists (strlit s3); rewrite strlit_STRCAT; reflexivity.
  - intros [[s3] H]; rewrite strlit_STRCAT in H; injection H as ->; eauto.
Qed.

(** ** Orderings *)

Definition compare_aux (s1 s2 : mlstring) (ord : ordering) (start len : N) : ordering :=
  num_rec (fun _ => ord)
    (fun _ r start =>
       if char_lt (strsub s2 start) (strsub s1 start) then GREATER
       else if char_lt (strsub s1 start) (strsub s2 start) then LESS
       else r (start + 1)) len start.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "compare_aux_def" *)
Theorem compare_aux_def : forall s1 s2 ord start len,
  compare_aux s1 s2 ord start len =
  if len =? 0 then ord
  else if char_lt (strsub s2 start) (strsub s1 start) then GREATER
  else if char_lt (strsub s1 start) (strsub s2 start) then LESS
  else compare_aux s1 s2 ord (start + 1) (len - 1).
Proof.
  intros s1 s2 ord start len; destruct (N.zero_or_succ len) as [->|[m ->]]; [reflexivity|].
  unfold compare_aux at 1; rewrite num_rec_SUC.
  replace (SUC m =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  rewrite N.sub_1_r, N.pred_succ; reflexivity.
Qed.

(** HOL [compare] (computed as [string_compare]; [compare_def] below). *)
Definition compare (s1 s2 : mlstring) : ordering := string_compare (explode s1) (explode s2).

Lemma compare_aux_SUC s1 s2 ord start len :
  compare_aux s1 s2 ord start (SUC len) =
  if char_lt (strsub s2 start) (strsub s1 start) then GREATER
  else if char_lt (strsub s1 start) (strsub s2 start) then LESS
  else compare_aux s1 s2 ord (start + 1) len.
Proof.
  rewrite compare_aux_def.
  replace (SUC len =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  rewrite N.sub_1_r, N.pred_succ; reflexivity.
Qed.

Lemma compare_aux_shift c1 s1 c2 s2 ord i len :
  compare_aux (strlit (c1 :: s1)) (strlit (c2 :: s2)) ord (SUC i) len =
  compare_aux (strlit s1) (strlit s2) ord i len.
Proof.
  revert i; induction len as [|len IH] using N.peano_ind; intros i; [reflexivity|].
  rewrite !compare_aux_SUC; cbn [strsub]; rewrite !EL_SUC; cbn [TL].
  rewrite N.add_succ_l, IH; reflexivity.
Qed.

Lemma char_compare_lt c d :
  char_compare c d = if char_lt d c then GREATER else if char_lt c d then LESS else EQUAL.
Proof.
  unfold char_compare, num_compare, char_lt.
  destruct (N.eqb_spec (ORD c) (ORD d)), (N.ltb_spec (ORD d) (ORD c)), (N.ltb_spec (ORD c) (ORD d));
    reflexivity || lia.
Qed.

Lemma char_compare_EQUAL c d : char_compare c d = EQUAL <-> c = d.
Proof.
  rewrite char_compare_lt; unfold char_lt.
  destruct (N.ltb_spec (ORD d) (ORD c)); [split; [discriminate|intros ->; lia]|].
  destruct (N.ltb_spec (ORD c) (ORD d)); [split; [discriminate|intros ->; lia]|].
  split; [intros _; apply ORD_11; lia|reflexivity].
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "compare_def" *)
Theorem compare_def : forall s1 s2,
  compare s1 s2 =
  if strlen s1 <? strlen s2 then compare_aux s1 s2 LESS 0 (strlen s1)
  else if strlen s2 <? strlen s1 then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2).
Proof.
  intros [s] [t]; unfold compare, string_compare; cbn [strlen explode]; revert t.
  induction s as [|c s IH]; intros [|d t]; cbn [LENGTH list_compare].
  - reflexivity.
  - rewrite (proj2 (N.ltb_lt 0 (SUC (LENGTH t)))) by lia; reflexivity.
  - rewrite (proj2 (N.ltb_ge (SUC (LENGTH s)) 0)) by lia.
    rewrite (proj2 (N.ltb_lt 0 (SUC (LENGTH s)))) by lia; reflexivity.
  - rewrite !compare_aux_SUC; change (0 + 1) with (SUC 0); rewrite !compare_aux_shift.
    change (strsub (strlit (c :: s)) 0) with c; change (strsub (strlit (d :: t)) 0) with d.
    replace (SUC (LENGTH s) <? SUC (LENGTH t)) with (LENGTH s <? LENGTH t)
      by (destruct (N.ltb_spec (LENGTH s) (LENGTH t)), (N.ltb_spec (SUC (LENGTH s)) (SUC (LENGTH t)));
          reflexivity || lia).
    replace (SUC (LENGTH t) <? SUC (LENGTH s)) with (LENGTH t <? LENGTH s)
      by (destruct (N.ltb_spec (LENGTH t) (LENGTH s)), (N.ltb_spec (SUC (LENGTH t)) (SUC (LENGTH s)));
          reflexivity || lia).
    rewrite char_compare_lt, IH.
    destruct (char_lt d c), (char_lt c d), (LENGTH s <? LENGTH t), (LENGTH t <? LENGTH s);
      reflexivity.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_def" *)
Definition mlstring_lt (s1 s2 : mlstring) : bool := bool_decide (compare s1 s2 = LESS).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_le_def" *)
Definition mlstring_le (s1 s2 : mlstring) : bool := bool_decide (compare s1 s2 <> GREATER).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_gt_def" *)
Definition mlstring_gt (s1 s2 : mlstring) : bool := bool_decide (compare s1 s2 = GREATER).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_ge_def" *)
Definition mlstring_ge (s1 s2 : mlstring) : bool := bool_decide (compare s1 s2 <> LESS).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "compare_thm" *)
Theorem compare_thm : forall s1 s2,
  compare s1 s2 = if mlstring_lt s1 s2 then LESS else if mlstring_le s1 s2 then EQUAL else GREATER.
Proof.
  intros s1 s2; unfold mlstring_lt, mlstring_le, bool_decide.
  destruct (compare s1 s2); reflexivity.
Qed.

Lemma string_compare_lt s t : string_compare s t = LESS <-> string_lt s t = true.
Proof.
  unfold string_compare; revert t; induction s as [|c s IH]; intros [|d t];
    cbn [list_compare string_lt]; try (split; congruence).
  unfold char_lt; rewrite orb_true_iff, andb_true_iff, bool_decide_spec, N.ltb_lt.
  rewrite char_compare_lt; unfold char_lt.
  destruct (N.ltb_spec (ORD d) (ORD c)) as [Hdc|Hdc].
  { split; [discriminate|intros [Hlt|[Heq _]]; [lia|subst; lia]]. }
  destruct (N.ltb_spec (ORD c) (ORD d)) as [Hcd|Hcd]; [split; auto|].
  assert (c = d) as <- by (apply ORD_11; lia).
  rewrite IH; split; [intros Hs; right; auto|intros [Hlt|[_ Hs]]; [lia|auto]].
Qed.

Lemma string_compare_sym s t : string_compare t s = invert_comparison (string_compare s t).
Proof.
  unfold string_compare; revert t; induction s as [|c s IH]; intros [|d t];
    cbn [list_compare invert_comparison]; auto.
  rewrite !char_compare_lt; unfold char_lt.
  destruct (N.ltb_spec (ORD d) (ORD c)), (N.ltb_spec (ORD c) (ORD d)); auto; lia.
Qed.

Lemma string_compare_eq s t : string_compare s t = EQUAL <-> s = t.
Proof. apply compare_equal, char_compare_EQUAL. Qed.

(** Pointwise form of HOL [mlstring_lt_inv_image]
    ([mlstring_lt = inv_image string_lt explode]). *)
Lemma mlstring_lt_string_lt s1 s2 : mlstring_lt s1 s2 = string_lt (explode s1) (explode s2).
Proof.
  unfold mlstring_lt, compare; destruct (string_lt (explode s1) (explode s2)) eqn:E.
  - apply bool_decide_spec, string_compare_lt, E.
  - destruct (bool_decide _) eqn:F; auto.
    apply bool_decide_spec, string_compare_lt in F; congruence.
Qed.

Lemma compare_eq s1 s2 : compare s1 s2 = EQUAL <-> s1 = s2.
Proof. unfold compare; rewrite string_compare_eq; apply explode_11. Qed.

Lemma compare_sym s1 s2 : compare s2 s1 = invert_comparison (compare s1 s2).
Proof. apply string_compare_sym. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_antisym" *)
Theorem mlstring_lt_antisym : forall s t, ~ (mlstring_lt s t /\ mlstring_lt t s).
Proof. intros s t; rewrite !mlstring_lt_string_lt; apply string_lt_antisym. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_cases" *)
Theorem mlstring_lt_cases : forall s t, s = t \/ mlstring_lt s t \/ mlstring_lt t s.
Proof.
  intros s t; rewrite !mlstring_lt_string_lt.
  destruct (string_lt_cases (explode s) (explode t)) as [H|H]; auto.
  left; apply explode_11, H.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_nonrefl" *)
Theorem mlstring_lt_nonrefl : forall s, ~ mlstring_lt s s.
Proof. intros s; rewrite mlstring_lt_string_lt; apply string_lt_nonrefl. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_lt_trans" *)
Theorem mlstring_lt_trans : forall s1 s2 s3, mlstring_lt s1 s2 /\ mlstring_lt s2 s3 -> mlstring_lt s1 s3.
Proof. intros s1 s2 s3; rewrite !mlstring_lt_string_lt; apply string_lt_trans. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_le_thm" *)
Theorem mlstring_le_thm : forall s1 s2, mlstring_le s1 s2 <-> s1 = s2 \/ mlstring_lt s1 s2.
Proof.
  intros s1 s2; unfold mlstring_le, mlstring_lt, is_true; rewrite !bool_decide_spec.
  rewrite <- compare_eq; destruct (compare s1 s2); split; intuition congruence.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_gt_thm" *)
Theorem mlstring_gt_thm : forall s1 s2, mlstring_gt s1 s2 <-> mlstring_lt s2 s1.
Proof.
  intros s1 s2; unfold mlstring_gt, mlstring_lt, is_true; rewrite !bool_decide_spec.
  rewrite (compare_sym s1 s2); destruct (compare s1 s2); cbn; split; congruence.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "mlstring_ge_thm" *)
Theorem mlstring_ge_thm : forall s1 s2, mlstring_ge s1 s2 <-> mlstring_le s2 s1.
Proof.
  intros s1 s2; unfold mlstring_ge, mlstring_le, is_true; rewrite !bool_decide_spec.
  rewrite (compare_sym s1 s2); destruct (compare s1 s2); cbn; split; congruence.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "char_lt_total" *)
Theorem char_lt_total : forall c1 c2, ~ char_lt c1 c2 /\ ~ char_lt c2 c1 -> c1 = c2.
Proof.
  intros c1 c2 [H1 H2]; unfold char_lt, is_true in *; rewrite N.ltb_lt in H1, H2.
  apply ORD_11; lia.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "string_lt_total" *)
Theorem string_lt_total : forall s1 s2, ~ string_lt s1 s2 /\ ~ string_lt s2 s1 -> s1 = s2.
Proof. intros s1 s2 [H1 H2]; destruct (string_lt_cases s1 s2) as [H|[H|H]]; tauto. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "strlit_le_strlit" *)
Theorem strlit_le_strlit : forall s1 s2, mlstring_le (strlit s1) (strlit s2) <-> string_le s1 s2.
Proof.
  intros s1 s2; rewrite mlstring_le_thm, mlstring_lt_string_lt; cbn [explode].
  unfold string_le, is_true; rewrite orb_true_iff, bool_decide_spec; split;
    (intros [H|H]; [left; congruence|right; exact H]).
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "fast_lt_def" *)
Definition fast_lt (s1 s2 : mlstring) : bool :=
  if strlen s1 =? strlen s2 then mlstring_lt s1 s2 else strlen s1 <? strlen s2.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "fast_le_def" *)
Definition fast_le (s1 s2 : mlstring) : bool :=
  if strlen s1 =? strlen s2 then mlstring_le s1 s2 else strlen s1 <=? strlen s2.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "fast_gt_def" *)
Definition fast_gt (s1 s2 : mlstring) : bool :=
  if strlen s1 =? strlen s2 then mlstring_gt s1 s2 else strlen s2 <? strlen s1.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "fast_ge_def" *)
Definition fast_ge (s1 s2 : mlstring) : bool :=
  if strlen s1 =? strlen s2 then mlstring_ge s1 s2 else strlen s2 <=? strlen s1.

Definition collate_aux (f : ascii -> ascii -> ordering) (s1 s2 : mlstring) (ord : ordering)
  (n len : N) : ordering :=
  num_rec (fun _ => ord)
    (fun _ r n =>
       if decide (f (strsub s1 n) (strsub s2 n) = EQUAL) then r (n + 1)
       else f (strsub s1 n) (strsub s2 n)) len n.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "collate_aux_def" *)
Theorem collate_aux_def : forall f s1 s2 ord n len,
  collate_aux f s1 s2 ord n 0 = ord /\
  collate_aux f s1 s2 ord n (SUC len) =
    (if decide (f (strsub s1 n) (strsub s2 n) = EQUAL) then collate_aux f s1 s2 ord (n + 1) len
     else f (strsub s1 n) (strsub s2 n)).
Proof. intros; unfold collate_aux; rewrite !num_rec_SUC; split; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "collate_def" *)
Definition collate (f : ascii -> ascii -> ordering) (s1 s2 : mlstring) : ordering :=
  if strlen s1 <? strlen s2 then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if strlen s2 <? strlen s1 then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2).

(** ** Escaping *)

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "char_escape_seq_def" *)
Definition char_escape_seq (c : ascii) : option mlstring :=
  if decide (c = "009"%char) then Some (strlit "\t")
  else if decide (c = "010"%char) then Some (strlit "\n")
  else if decide (c = "\"%char) then Some (strlit "\\")
  else if decide (c = """"%char) then Some (strlit "\""")
  else None.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "char_escaped_def" *)
Definition char_escaped (c : ascii) : string :=
  match char_escape_seq c with None => [c] | Some s => explode s end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "escape_str_def" *)
Definition escape_str (s : mlstring) : mlstring :=
  implode ("""" ++ FLAT (MAP char_escaped (explode s)) ++ """").

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "escape_char_def" *)
Definition escape_char (c : ascii) : mlstring := implode ("#""" ++ char_escaped c ++ """").

Lemma ALL_DISTINCT_MAP_inj {A B} `{EqDecision A} `{EqDecision B} (f : A -> B) l :
  (forall x y, f x = f y -> x = y) -> ALL_DISTINCT (MAP f l) = ALL_DISTINCT l.
Proof.
  intros Hf; induction l as [|h t IH]; [reflexivity|]; cbn [MAP List.map ALL_DISTINCT].
  rewrite IH; f_equal; f_equal.
  destruct (MEM h t) eqn:E1, (MEM (f h) (MAP f t)) eqn:E2; auto.
  - apply MEM_In in E1; apply (in_map f) in E1; apply MEM_In in E1; congruence.
  - apply MEM_In, in_map_iff in E2 as (x & Hx & Hin); apply Hf in Hx; subst.
    apply MEM_In in Hin; congruence.
Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "ALL_DISTINCT_MAP_implode" *)
Theorem ALL_DISTINCT_MAP_implode : forall ls, ALL_DISTINCT ls -> ALL_DISTINCT (MAP implode ls).
Proof. intros ls H; rewrite ALL_DISTINCT_MAP_inj; [exact H|congruence]. Qed.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "ALL_DISTINCT_MAP_explode" *)
Theorem ALL_DISTINCT_MAP_explode : forall ls, ALL_DISTINCT (MAP explode ls) <-> ALL_DISTINCT ls.
Proof. intros ls; rewrite ALL_DISTINCT_MAP_inj; [reflexivity|]. intros x y; apply explode_11. Qed.

(** ** Optimising [mlstring] [app_list]s *)

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "app_list_ann" *)
Inductive app_list_ann (A : Type) : Type :=
| BigList (l : list A)
| BigAppend (l1 l2 : app_list_ann A)
| Small (l : app_list A).
Arguments BigList {A} l.
Arguments BigAppend {A} l1 l2.
Arguments Small {A} l.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "sum_sizes_def" *)
Fixpoint sum_sizes (l : list mlstring) (k : N) : N :=
  match l with [] => k | l :: ls => sum_sizes ls (strlen l + k) end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "make_app_list_ann_def" *)
Fixpoint make_app_list_ann (input : app_list mlstring) : app_list_ann mlstring * N :=
  match input with
  | Nil => (Small input, 0)
  | Append l1 l2 =>
      let (x1, n1) := make_app_list_ann l1 in
      let (x2, n2) := make_app_list_ann l2 in
      let n := n1 + n2 in
      if n <? 2048 then (Small input, n) else (BigAppend x1 x2, n)
  | List ls =>
      let n := sum_sizes ls 0 in
      if n <? 2048 then (Small input, n) else (BigList ls, n)
  end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "shrink_def" *)
Fixpoint shrink (a : app_list_ann mlstring) : app_list mlstring :=
  match a with
  | Small t => List [concat (append t)]
  | BigList ls => List ls
  | BigAppend l1 l2 => Append (shrink l1) (shrink l2)
  end.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "str_app_list_opt_def" *)
Definition str_app_list_opt (l : app_list mlstring) : app_list mlstring :=
  let (t, n) := make_app_list_ann l in shrink t.

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "str_app_list_opt_thm" *)
Theorem str_app_list_opt_thm : forall l,
  concat (append (str_app_list_opt l)) = concat (append l).
Proof.
  assert (H : forall l, concat (append (shrink (fst (make_app_list_ann l)))) = concat (append l)).
  { induction l as [ls|l1 IH1 l2 IH2|]; cbn [make_app_list_ann].
    - destruct (sum_sizes ls 0 <? 2048); cbn [fst shrink];
        rewrite ?(proj1 (proj2 (append_thm (@Nil mlstring) Nil _))); [apply concat_sing|reflexivity].
    - destruct (make_app_list_ann l1) as [x1 n1], (make_app_list_ann l2) as [x2 n2].
      cbn [fst] in IH1, IH2.
      destruct (n1 + n2 <? 2048); cbn [fst shrink].
      + rewrite (proj1 (proj2 (append_thm (@Nil mlstring) Nil _))); apply concat_sing.
      + rewrite !(proj1 (append_thm _ _ [])), !concat_append, IH1, IH2; reflexivity.
    - reflexivity. }
  intros l; unfold str_app_list_opt.
  specialize (H l); destruct (make_app_list_ann l); exact H.
Qed.

(** ** Conversions *)

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "char_to_word8_def" *)
Definition char_to_word8 (c : ascii) : word8 := n2w (ORD c).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "word8_to_char_def" *)
Definition word8_to_char (w : word8) : ascii := CHR (w2n w).

(*! HOL "cakeml/basis/pure/mlstringScript.sml" "empty_ffi_def" *)
Definition empty_ffi (s : mlstring) : unit := tt.
