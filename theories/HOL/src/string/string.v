(** * HOL4 [string]: 8-bit characters and strings

    Carriers (AGENTS.md): HOL [char] is Rocq [ascii]; HOL [string] is HOL's
    own type abbreviation [char list], i.e. [list ascii] (not Rocq's
    [String.string]).  HOL's overloads on strings are abbreviations of the
    list constants: [STRING] = [CONS], [EMPTYSTRING] = [[]],
    [STRLEN] = [LENGTH], [STRCAT] = [APPEND], [CONCAT] = [FLAT].
    [IMPLODE]/[EXPLODE] are HOL's identity functions on [char list].

    - HOL [char] is an abstract type in bijection ([CHR]/[ORD]) with the
      numbers below 256; Rocq [ascii] has exactly 256 values.  [ORD] is
      [N_of_ascii] and [CHR] is [ascii_of_N], which keeps the low 8 bits of
      its argument (HOL leaves [CHR n] unspecified for [n >= 256]).
    - String literals: ["abc"] in [hol_string_scope] (delimiter [%hstring])
      is the [list ascii] ['a'; 'b'; 'c'], via a [String Notation] (Galette
      infrastructure).  The printer only prints non-empty character lists
      as string literals, so [[] : list nat] still prints as [[]] (and the
      empty HOL string prints as [[]] too).

    Not ported (need [rich_list] / [relation] / [pred_set]): [SUBSTRING_def]
    ([SEG]), [EXTRACT_def], [TOKENS_def], [FIELDS_def] ([SPLITP]),
    [WF_char_lt], [RC_char_lt], [string_lt_LLEX], [not_WF_string_lt],
    [UNIV_IMAGE_CHR_count_256], [FINITE_UNIV_char], [INFINITE_STR_UNIV],
    [TOKENS_APPEND], [TOKENS_NIL], [TOKENS_FRONT], [isPREFIX_IND]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Stdlib Require Strings.Byte.
Open Scope N_scope.

(** ** String literals (Galette infrastructure) *)

Inductive hol_string_lit : Type :=
| hsl_nil
| hsl_cons (a : ascii) (s : hol_string_lit).

Fixpoint hsl_of_bytes (l : list Byte.byte) : hol_string_lit :=
  match l with [] => hsl_nil | b :: l => hsl_cons (ascii_of_byte b) (hsl_of_bytes l) end.

Fixpoint hsl_to_bytes (s : hol_string_lit) : list Byte.byte :=
  match s with hsl_nil => [] | hsl_cons a s => byte_of_ascii a :: hsl_to_bytes s end.

Definition hsl_print (s : hol_string_lit) : option (list Byte.byte) :=
  match s with hsl_nil => None | _ => Some (hsl_to_bytes s) end.

Declare Scope hol_string_scope.
Delimit Scope hol_string_scope with hstring.
#[warnings="-via-type-mismatch"]
String Notation list hsl_of_bytes hsl_print
  (via hol_string_lit mapping [[nil] => hsl_nil, [cons] => hsl_cons]) : hol_string_scope.
Open Scope hol_string_scope.

(** ** Characters *)

(** HOL [ORD] (the representation function of [char]). *)
Definition ORD (c : ascii) : N := N_of_ascii c.

(** HOL [CHR] (the abstraction function of [char]); the low 8 bits. *)
Definition CHR (n : N) : ascii := ascii_of_N n.

Lemma ORD_lt_256 : forall c, ORD c < 256.
Proof. intros [[] [] [] [] [] [] [] []]; vm_compute; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "CHR_ORD" *)
Theorem CHR_ORD : forall a, CHR (ORD a) = a.
Proof. exact ascii_N_embedding. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "ORD_CHR_RWT" *)
Theorem ORD_CHR_RWT : forall r, r < 256 -> ORD (CHR r) = r.
Proof. exact N_ascii_embedding. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "ORD_CHR" *)
Theorem ORD_CHR : forall r, r < 256 <-> ORD (CHR r) = r.
Proof.
  intros r; split; [apply ORD_CHR_RWT|].
  intros H; rewrite <- H; apply ORD_lt_256.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "ORD_11" *)
Theorem ORD_11 : forall a a', ORD a = ORD a' <-> a = a'.
Proof.
  intros a a'; split; [|intros ->; reflexivity].
  intros H; rewrite <- (CHR_ORD a), <- (CHR_ORD a'), H; reflexivity.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "CHR_11" *)
Theorem CHR_11 : forall r r', r < 256 -> r' < 256 -> CHR r = CHR r' <-> r = r'.
Proof.
  intros r r' Hr Hr'; split; [|intros ->; reflexivity].
  intros H; rewrite <- (ORD_CHR_RWT r Hr), <- (ORD_CHR_RWT r' Hr'), H; reflexivity.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "ORD_ONTO" *)
Theorem ORD_ONTO : forall r, r < 256 <-> exists a, r = ORD a.
Proof.
  intros r; split.
  - intros H; exists (CHR r); symmetry; apply ORD_CHR_RWT, H.
  - intros [a ->]; apply ORD_lt_256.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "CHR_ONTO" *)
Theorem CHR_ONTO : forall a, exists r, a = CHR r /\ r < 256.
Proof. intros a; exists (ORD a); split; [symmetry; apply CHR_ORD|apply ORD_lt_256]. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "ORD_BOUND" *)
Theorem ORD_BOUND : forall c, ORD c < 256.
Proof. exact ORD_lt_256. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "char_nchotomy" *)
Theorem char_nchotomy : forall c, exists n, c = CHR n.
Proof. intros c; exists (ORD c); symmetry; apply CHR_ORD. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "ranged_char_nchotomy" *)
Theorem ranged_char_nchotomy : forall c, exists n, c = CHR n /\ n < 256.
Proof. exact CHR_ONTO. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "CHAR_EQ_THM" *)
Theorem CHAR_EQ_THM : forall c1 c2, c1 = c2 <-> ORD c1 = ORD c2.
Proof. intros c1 c2; symmetry; apply ORD_11. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "CHAR_INDUCT_THM" *)
Theorem CHAR_INDUCT_THM : forall P : ascii -> Prop,
  (forall n, n < 256 -> P (CHR n)) -> forall c, P c.
Proof. intros P H c; rewrite <- (CHR_ORD c); apply H, ORD_lt_256. Qed.

(** ** Character classes *)

(*! HOL "HOL/src/string/stringScript.sml" "isLower_def" *)
Definition isLower (c : ascii) : bool := (97 <=? ORD c) && (ORD c <=? 122).

(*! HOL "HOL/src/string/stringScript.sml" "isUpper_def" *)
Definition isUpper (c : ascii) : bool := (65 <=? ORD c) && (ORD c <=? 90).

(*! HOL "HOL/src/string/stringScript.sml" "isDigit_def" *)
Definition isDigit (c : ascii) : bool := (48 <=? ORD c) && (ORD c <=? 57).

(*! HOL "HOL/src/string/stringScript.sml" "isAlpha_def" *)
Definition isAlpha (c : ascii) : bool := isLower c || isUpper c.

(*! HOL "HOL/src/string/stringScript.sml" "isHexDigit_def" *)
Definition isHexDigit (c : ascii) : bool :=
  (48 <=? ORD c) && (ORD c <=? 57) ||
  (97 <=? ORD c) && (ORD c <=? 102) ||
  (65 <=? ORD c) && (ORD c <=? 70).

(*! HOL "HOL/src/string/stringScript.sml" "isAlphaNum_def" *)
Definition isAlphaNum (c : ascii) : bool := isAlpha c || isDigit c.

(*! HOL "HOL/src/string/stringScript.sml" "isPrint_def" *)
Definition isPrint (c : ascii) : bool := (32 <=? ORD c) && (ORD c <? 127).

(*! HOL "HOL/src/string/stringScript.sml" "isAlphaNum_isPrint" *)
Theorem isAlphaNum_isPrint : forall x, isAlphaNum x -> isPrint x.
Proof. intros [[] [] [] [] [] [] [] []]; vm_compute; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "isHexDigit_isAlphaNum" *)
Theorem isHexDigit_isAlphaNum : forall x, isHexDigit x -> isAlphaNum x.
Proof. intros [[] [] [] [] [] [] [] []]; vm_compute; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "isHexDigit_isPrint" *)
Theorem isHexDigit_isPrint : forall x, isHexDigit x -> isPrint x.
Proof. intros x H; apply isAlphaNum_isPrint, isHexDigit_isAlphaNum, H. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "isSpace_def" *)
Definition isSpace (c : ascii) : bool := (ORD c =? 32) || (9 <=? ORD c) && (ORD c <=? 13).

(*! HOL "HOL/src/string/stringScript.sml" "isGraph_def" *)
Definition isGraph (c : ascii) : bool := isPrint c && negb (isSpace c).

(*! HOL "HOL/src/string/stringScript.sml" "isPunct_def" *)
Definition isPunct (c : ascii) : bool := isGraph c && negb (isAlphaNum c).

(*! HOL "HOL/src/string/stringScript.sml" "isAscii_def" *)
Definition isAscii (c : ascii) : bool := ORD c <=? 127.

(*! HOL "HOL/src/string/stringScript.sml" "isCntrl_def" *)
Definition isCntrl (c : ascii) : bool := (ORD c <? 32) || (127 <=? ORD c).

(*! HOL "HOL/src/string/stringScript.sml" "toLower_def" *)
Definition toLower (c : ascii) : ascii := if isUpper c then CHR (ORD c + 32) else c.

(*! HOL "HOL/src/string/stringScript.sml" "toUpper_def" *)
Definition toUpper (c : ascii) : ascii := if isLower c then CHR (ORD c - 32) else c.

(*! HOL "HOL/src/string/stringScript.sml" "char_lt_def" *)
Definition char_lt (a b : ascii) : bool := ORD a <? ORD b.

(*! HOL "HOL/src/string/stringScript.sml" "char_le_def" *)
Definition char_le (a b : ascii) : bool := ORD a <=? ORD b.

(*! HOL "HOL/src/string/stringScript.sml" "char_gt_def" *)
Definition char_gt (a b : ascii) : bool := ORD b <? ORD a.

(*! HOL "HOL/src/string/stringScript.sml" "char_ge_def" *)
Definition char_ge (a b : ascii) : bool := ORD b <=? ORD a.

(*! HOL "HOL/src/string/stringScript.sml" "char_compare_def" *)
Definition char_compare (c1 c2 : ascii) : ordering := num_compare (ORD c1) (ORD c2).

(*! HOL "HOL/src/string/stringScript.sml" "char_size_def" *)
Definition char_size (c : ascii) : N := 0.

(** ** Strings *)

Abbreviation string := (list ascii).
Abbreviation STRING := (@cons ascii).
Abbreviation EMPTYSTRING := (@nil ascii).
Abbreviation STRLEN := (@LENGTH ascii).
Abbreviation STRCAT := (@List.app ascii).
Abbreviation CONCAT := (@List.concat ascii).

(*! HOL "HOL/src/string/stringScript.sml" "string_compare_def" *)
Definition string_compare : string -> string -> ordering := list_compare char_compare.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_def" *)
Fixpoint IMPLODE (l : list ascii) : string :=
  match l with [] => EMPTYSTRING | c :: cs => STRING c (IMPLODE cs) end.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_def" *)
Fixpoint EXPLODE (s : string) : list ascii :=
  match s with [] => [] | c :: s => c :: EXPLODE s end.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_EXPLODE_I" *)
Theorem IMPLODE_EXPLODE_I : forall s, EXPLODE s = s /\ IMPLODE s = s.
Proof. induction s as [|c s [IH1 IH2]]; cbn; [split; reflexivity|]. rewrite IH1, IH2; split; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_EQNS" *)
Theorem EXPLODE_EQNS : forall c s, EXPLODE EMPTYSTRING = [] /\ EXPLODE (STRING c s) = c :: EXPLODE s.
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_EQNS" *)
Theorem IMPLODE_EQNS : forall c cs, IMPLODE [] = EMPTYSTRING /\ IMPLODE (c :: cs) = STRING c (IMPLODE cs).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_EXPLODE" *)
Theorem IMPLODE_EXPLODE : forall s, IMPLODE (EXPLODE s) = s.
Proof. intros s; rewrite (proj1 (IMPLODE_EXPLODE_I s)); apply IMPLODE_EXPLODE_I. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_IMPLODE" *)
Theorem EXPLODE_IMPLODE : forall cs, EXPLODE (IMPLODE cs) = cs.
Proof. intros cs; rewrite (proj2 (IMPLODE_EXPLODE_I cs)); apply IMPLODE_EXPLODE_I. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_ONTO" *)
Theorem EXPLODE_ONTO : forall cs, exists s, cs = EXPLODE s.
Proof. intros cs; exists (IMPLODE cs); symmetry; apply EXPLODE_IMPLODE. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_ONTO" *)
Theorem IMPLODE_ONTO : forall s, exists cs, s = IMPLODE cs.
Proof. intros s; exists (EXPLODE s); symmetry; apply IMPLODE_EXPLODE. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_11" *)
Theorem EXPLODE_11 : forall s1 s2, EXPLODE s1 = EXPLODE s2 <-> s1 = s2.
Proof. intros s1 s2; rewrite !(proj1 (IMPLODE_EXPLODE_I _)); reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_11" *)
Theorem IMPLODE_11 : forall cs1 cs2, IMPLODE cs1 = IMPLODE cs2 <-> cs1 = cs2.
Proof. intros s1 s2; rewrite !(proj2 (IMPLODE_EXPLODE_I _)); reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_EQ_EMPTYSTRING" *)
Theorem IMPLODE_EQ_EMPTYSTRING : forall l,
  (IMPLODE l = EMPTYSTRING <-> l = []) /\ (EMPTYSTRING = IMPLODE l <-> l = []).
Proof. intros [|c l]; cbn; repeat split; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_EQ_NIL" *)
Theorem EXPLODE_EQ_NIL : forall s,
  (EXPLODE s = [] <-> s = EMPTYSTRING) /\ ([] = EXPLODE s <-> s = EMPTYSTRING).
Proof. intros [|c s]; cbn; repeat split; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_EQ_THM" *)
Theorem EXPLODE_EQ_THM : forall s h t,
  (h :: t = EXPLODE s <-> s = STRING h (IMPLODE t)) /\
  (EXPLODE s = h :: t <-> s = STRING h (IMPLODE t)).
Proof.
  intros s h t; rewrite (proj1 (IMPLODE_EXPLODE_I s)), (proj2 (IMPLODE_EXPLODE_I t)).
  split; split; congruence.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_EQ_THM" *)
Theorem IMPLODE_EQ_THM : forall c s l,
  (STRING c s = IMPLODE l <-> l = c :: EXPLODE s) /\
  (IMPLODE l = STRING c s <-> l = c :: EXPLODE s).
Proof.
  intros c s l; rewrite (proj1 (IMPLODE_EXPLODE_I s)), (proj2 (IMPLODE_EXPLODE_I l)).
  split; split; congruence.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "IMPLODE_STRING" *)
Theorem IMPLODE_STRING : forall clist, IMPLODE clist = FOLDR STRING EMPTYSTRING clist.
Proof. induction clist; cbn; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRING_ACYCLIC" *)
Theorem STRING_ACYCLIC : forall s c, STRING c s <> s /\ s <> STRING c s.
Proof.
  induction s as [|c' s IH]; intros c; split; try discriminate; intros H;
    injection H as H1 H2; destruct (IH c') as [IH1 IH2]; congruence.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "SUB_def" *)
Definition SUB (p : string * N) : ascii := let (s, n) := p in EL n s.

(*! HOL "HOL/src/string/stringScript.sml" "STR_def" *)
Definition STR (c : ascii) : string := [c].

(*! HOL "HOL/src/string/stringScript.sml" "TOCHAR_def" *)
Definition TOCHAR (s : string) : ascii := match s with [c] => c | _ => ARB end.

(*! HOL "HOL/src/string/stringScript.sml" "TRANSLATE_def" *)
Definition TRANSLATE (f : ascii -> string) (s : string) : string := CONCAT (MAP f s).

(*! HOL "HOL/src/string/stringScript.sml" "DEST_STRING_def" *)
Definition DEST_STRING (s : string) : option (ascii * string) :=
  match s with [] => None | c :: rst => Some (c, rst) end.

(*! HOL "HOL/src/string/stringScript.sml" "DEST_STRING_LEMS" *)
Theorem DEST_STRING_LEMS : forall c t s,
  (DEST_STRING s = None <-> s = EMPTYSTRING) /\ (DEST_STRING s = Some (c, t) <-> s = STRING c t).
Proof. intros c t [|c' s]; cbn; repeat split; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "EXPLODE_DEST_STRING" *)
Theorem EXPLODE_DEST_STRING : forall s,
  EXPLODE s = match DEST_STRING s with None => [] | Some (c, t) => c :: EXPLODE t end.
Proof. intros [|c s]; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRLEN_EXPLODE_THM" *)
Theorem STRLEN_EXPLODE_THM : forall s, STRLEN s = LENGTH (EXPLODE s).
Proof. intros s; rewrite (proj1 (IMPLODE_EXPLODE_I s)); reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRLEN_EQ_0" *)
Theorem STRLEN_EQ_0 : forall l, STRLEN l = 0 <-> l = EMPTYSTRING.
Proof. intros [|c l]; cbn [LENGTH]; split; try congruence; lia. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRLEN_THM" *)
Theorem STRLEN_THM : STRLEN EMPTYSTRING = 0 /\ (forall h t, STRLEN (STRING h t) = SUC (STRLEN t)).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRLEN_DEF" 529 *)
Theorem STRLEN_DEF : STRLEN EMPTYSTRING = 0 /\ (forall h t, STRLEN (STRING h t) = SUC (STRLEN t)).
Proof. exact STRLEN_THM. Qed.

(** ** Concatenation *)

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_def" *)
Theorem STRCAT_def :
  (forall l, STRCAT EMPTYSTRING l = l) /\
  (forall l1 l2 h, STRCAT (STRING h l1) l2 = STRING h (STRCAT l1 l2)).
Proof. split; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_EQNS" *)
Theorem STRCAT_EQNS : forall s c s1 s2,
  STRCAT EMPTYSTRING s = s /\ STRCAT s EMPTYSTRING = s /\
  STRCAT (STRING c s1) s2 = STRING c (STRCAT s1 s2).
Proof. intros s; repeat split; auto using app_nil_r. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_ASSOC" *)
Theorem STRCAT_ASSOC : forall l1 l2 l3, STRCAT l1 (STRCAT l2 l3) = STRCAT (STRCAT l1 l2) l3.
Proof. intros; apply app_assoc. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_11" *)
Theorem STRCAT_11 :
  (forall l1 l2 l3, STRCAT l1 l2 = STRCAT l1 l3 <-> l2 = l3) /\
  (forall l1 l2 l3, STRCAT l2 l1 = STRCAT l3 l1 <-> l2 = l3).
Proof.
  split; intros l1 l2 l3; (split; [|intros ->; reflexivity]); intros H.
  - eapply app_inv_head; eassumption.
  - eapply app_inv_tail; eassumption.
Qed.

Lemma STRLEN_STRCAT l1 l2 : STRLEN (STRCAT l1 l2) = STRLEN l1 + STRLEN l2.
Proof. rewrite !LENGTH_length, length_app; lia. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_ACYCLIC" *)
Theorem STRCAT_ACYCLIC : forall s s1,
  (s = STRCAT s s1 <-> s1 = EMPTYSTRING) /\ (s = STRCAT s1 s <-> s1 = EMPTYSTRING).
Proof.
  intros s s1; split; split; intros H.
  - apply (f_equal STRLEN) in H; rewrite STRLEN_STRCAT in H.
    apply STRLEN_EQ_0; lia.
  - subst; symmetry; apply app_nil_r.
  - apply (f_equal STRLEN) in H; rewrite STRLEN_STRCAT in H.
    apply STRLEN_EQ_0; lia.
  - subst; reflexivity.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_EXPLODE" *)
Theorem STRCAT_EXPLODE : forall s1 s2, STRCAT s1 s2 = FOLDR STRING s2 (EXPLODE s1).
Proof. induction s1; cbn; congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRCAT_EQ_EMPTY" *)
Theorem STRCAT_EQ_EMPTY : forall l1 l2, STRCAT l1 l2 = EMPTYSTRING <-> l1 = EMPTYSTRING /\ l2 = EMPTYSTRING.
Proof. intros [|c l1] [|d l2]; cbn; split; intuition congruence. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "STRLEN_CAT" *)
Theorem STRLEN_CAT : forall l1 l2, STRLEN (STRCAT l1 l2) = STRLEN l1 + STRLEN l2.
Proof. exact STRLEN_STRCAT. Qed.

(** ** Prefixes *)

(*! HOL "HOL/src/string/stringScript.sml" "isPREFIX_DEF" *)
Theorem isPREFIX_DEF : forall s1 s2 : string,
  isPREFIX s1 s2 =
  match DEST_STRING s1, DEST_STRING s2 with
  | None, _ => true
  | Some _, None => false
  | Some (c1, t1), Some (c2, t2) => bool_decide (c1 = c2) && isPREFIX t1 t2
  end.
Proof. intros [|c1 t1] [|c2 t2]; reflexivity. Qed.

(*! HOL "HOL/src/string/stringScript.sml" "isPREFIX_STRCAT" *)
Theorem isPREFIX_STRCAT : forall s1 s2 : string, isPREFIX s1 s2 <-> exists s3, s2 = STRCAT s1 s3.
Proof.
  induction s1 as [|c1 t1 IH]; intros s2; cbn.
  - split; [intros _; exists s2; reflexivity|intros _; reflexivity].
  - destruct s2 as [|c2 t2]; cbn.
    + split; [discriminate|intros [s3 H]; discriminate].
    + unfold is_true; rewrite andb_true_iff, bool_decide_spec; fold (is_true (isPREFIX t1 t2)).
      rewrite IH; split.
      * intros [-> [s3 ->]]; exists s3; reflexivity.
      * intros [s3 H]; injection H as -> ->; eauto.
Qed.

(** ** Orderings *)

(*! HOL "HOL/src/string/stringScript.sml" "string_lt_def" *)
Fixpoint string_lt (s1 s2 : string) : bool :=
  match s1, s2 with
  | _, [] => false
  | [], _ :: _ => true
  | c1 :: s1, c2 :: s2 => char_lt c1 c2 || bool_decide (c1 = c2) && string_lt s1 s2
  end.

(*! HOL "HOL/src/string/stringScript.sml" "string_le_def" *)
Definition string_le (s1 s2 : string) : bool := bool_decide (s1 = s2) || string_lt s1 s2.

(*! HOL "HOL/src/string/stringScript.sml" "string_gt_def" *)
Definition string_gt (s1 s2 : string) : bool := string_lt s2 s1.

(*! HOL "HOL/src/string/stringScript.sml" "string_ge_def" *)
Definition string_ge (s1 s2 : string) : bool := string_le s2 s1.

Lemma string_lt_cons c1 s1 c2 s2 :
  string_lt (STRING c1 s1) (STRING c2 s2) = true <->
  ORD c1 < ORD c2 \/ c1 = c2 /\ string_lt s1 s2 = true.
Proof.
  cbn [string_lt]; rewrite orb_true_iff, andb_true_iff, bool_decide_spec; unfold char_lt.
  rewrite <- N.ltb_lt; reflexivity.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "string_lt_nonrefl" *)
Theorem string_lt_nonrefl : forall s, ~ string_lt s s.
Proof.
  unfold is_true; induction s as [|c s IH]; [discriminate|].
  rewrite string_lt_cons; intros [H|[_ H]]; [lia|auto].
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "string_lt_antisym" *)
Theorem string_lt_antisym : forall s t, ~ (string_lt s t /\ string_lt t s).
Proof.
  unfold is_true; induction s as [|c s IH]; intros [|d t] [H1 H2];
    try (cbn in *; discriminate).
  rewrite string_lt_cons in H1, H2.
  destruct H1 as [H1|[e1 H1]], H2 as [H2|[e2 H2]]; subst; try lia.
  eapply IH; eauto.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "string_lt_cases" *)
Theorem string_lt_cases : forall s t, s = t \/ string_lt s t \/ string_lt t s.
Proof.
  unfold is_true; induction s as [|c s IH]; intros [|d t]; auto.
  rewrite !string_lt_cons.
  destruct (N.lt_trichotomy (ORD c) (ORD d)) as [H|[H|H]]; auto.
  apply ORD_11 in H; subst d.
  destruct (IH t) as [->|[H|H]]; auto.
Qed.

(*! HOL "HOL/src/string/stringScript.sml" "string_lt_trans" *)
Theorem string_lt_trans : forall s1 s2 s3, string_lt s1 s2 /\ string_lt s2 s3 -> string_lt s1 s3.
Proof.
  unfold is_true; induction s1 as [|c1 s1 IH]; intros [|c2 s2] [|c3 s3] [H1 H2];
    try (cbn in *; congruence).
  rewrite string_lt_cons in H1, H2 |- *.
  destruct H1 as [H1|[e1 H1]], H2 as [H2|[e2 H2]]; subst; try (left; lia).
  right; split; [reflexivity|eapply IH; eauto].
Qed.
