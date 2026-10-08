(** * HOL4 [ASCIInumbers]: maps between numbers and digit strings *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list numposrep.
From Galette.HOL.src.string Require Import string.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "s2n_def" *)
Definition s2n (b : N) (f : ascii -> N) (s : string) : N := l2n b (MAP f (REVERSE s)).

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "n2s_def" *)
Definition n2s (b : N) (f : N -> ascii) (n : N) : string := REVERSE (MAP f (n2l b n)).

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "HEX" *)
Definition HEX (n : N) : ascii :=
  if n <? 10 then CHR (ORD "0"%char + n) else
  if n <? 16 then CHR (ORD "A"%char + (n - 10)) else CHR 0.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "HEX_def" *)
Theorem HEX_def :
  HEX 0 = "0"%char /\ HEX 1 = "1"%char /\ HEX 2 = "2"%char /\ HEX 3 = "3"%char /\
  HEX 4 = "4"%char /\ HEX 5 = "5"%char /\ HEX 6 = "6"%char /\ HEX 7 = "7"%char /\
  HEX 8 = "8"%char /\ HEX 9 = "9"%char /\ HEX 10 = "A"%char /\ HEX 11 = "B"%char /\
  HEX 12 = "C"%char /\ HEX 13 = "D"%char /\ HEX 14 = "E"%char /\ HEX 15 = "F"%char.
Proof. repeat split. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "UNHEX" *)
Definition UNHEX (c : ascii) : N :=
  let n := ORD c in
  if (ORD "0"%char <=? n) && (n <=? ORD "9"%char) then n - ORD "0"%char else
  if (ORD "a"%char <=? n) && (n <=? ORD "f"%char) then 10 + n - ORD "a"%char else
  if (ORD "A"%char <=? n) && (n <=? ORD "F"%char) then 10 + n - ORD "A"%char else 0.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "UNHEX_def" *)
Theorem UNHEX_def :
  UNHEX "0"%char = 0 /\ UNHEX "1"%char = 1 /\
  UNHEX "2"%char = 2 /\ UNHEX "3"%char = 3 /\
  UNHEX "4"%char = 4 /\ UNHEX "5"%char = 5 /\
  UNHEX "6"%char = 6 /\ UNHEX "7"%char = 7 /\
  UNHEX "8"%char = 8 /\ UNHEX "9"%char = 9 /\
  UNHEX "a"%char = 10 /\ UNHEX "b"%char = 11 /\ UNHEX "c"%char = 12 /\
  UNHEX "d"%char = 13 /\ UNHEX "e"%char = 14 /\ UNHEX "f"%char = 15 /\
  UNHEX "A"%char = 10 /\ UNHEX "B"%char = 11 /\ UNHEX "C"%char = 12 /\
  UNHEX "D"%char = 13 /\ UNHEX "E"%char = 14 /\ UNHEX "F"%char = 15.
Proof. repeat split. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "UNHEX_HEX" *)
Theorem UNHEX_HEX : forall n, n < 16 -> UNHEX (HEX n) = n.
Proof.
  intros n Hn; assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15) by lia.
  repeat (destruct H as [->|H]; [reflexivity|]); subst; reflexivity.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "HEX_UNHEX" *)
Theorem HEX_UNHEX : forall c, isHexDigit c -> HEX (UNHEX c) = toUpper c.
Proof. intros [[] [] [] [] [] [] [] []]; vm_compute; congruence. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "DEC_UNDEC" *)
Theorem DEC_UNDEC : forall c, isDigit c -> HEX (UNHEX c) = c.
Proof. intros [[] [] [] [] [] [] [] []]; vm_compute; congruence. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "isDigit_HEX" *)
Theorem isDigit_HEX : forall n, n < 10 -> isDigit (HEX n).
Proof.
  intros n Hn; assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9) by lia.
  repeat (destruct H as [->|H]; [reflexivity|]); subst; reflexivity.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "isHexDigit_HEX" *)
Theorem isHexDigit_HEX : forall n, n < 16 ->
  isHexDigit (HEX n) /\ (isAlpha (HEX n) -> isUpper (HEX n)).
Proof.
  intros n Hn; assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15) by lia.
  repeat (destruct H as [->|H]; [split; [reflexivity|intros Ha; vm_compute in *; congruence]|]);
    subst; split; [reflexivity|intros Ha; vm_compute in *; congruence].
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_from_bin_string_def" *)
Definition num_from_bin_string : string -> N := s2n 2 UNHEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_from_oct_string_def" *)
Definition num_from_oct_string : string -> N := s2n 8 UNHEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_from_dec_string_def" *)
Definition num_from_dec_string : string -> N := s2n 10 UNHEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_from_hex_string_def" *)
Definition num_from_hex_string : string -> N := s2n 16 UNHEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_bin_string_def" *)
Definition num_to_bin_string : N -> string := n2s 2 HEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_oct_string_def" *)
Definition num_to_oct_string : N -> string := n2s 8 HEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_dec_string_def" *)
Definition num_to_dec_string : N -> string := n2s 10 HEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_hex_string_def" *)
Definition num_to_hex_string : N -> string := n2s 16 HEX.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_dec_string_compute" *)
Theorem num_to_dec_string_compute : num_to_dec_string = n2lA [] HEX 10.
Proof.
  apply functional_extensionality; intros n; unfold num_to_dec_string, n2s.
  rewrite n2lA_n2l, app_nil_r, map_rev; reflexivity.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "s2n_compute" *)
Theorem s2n_compute : forall b f s, s2n b f s = l2n b (MAP f (REVERSE (EXPLODE s))).
Proof. intros b f s; rewrite (proj1 (IMPLODE_EXPLODE_I s)); reflexivity. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "n2s_compute" *)
Theorem n2s_compute : forall b f n, n2s b f n = IMPLODE (REVERSE (MAP f (n2l b n))).
Proof. intros; rewrite (proj2 (IMPLODE_EXPLODE_I _)); reflexivity. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "fromBinString_def" *)
Definition fromBinString (s : string) : option N :=
  if negb (bool_decide (s = EMPTYSTRING)) &&
     EVERY (fun c => bool_decide (c = "0"%char) || bool_decide (c = "1"%char)) s
  then Some (num_from_bin_string s) else None.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "fromDecString_def" *)
Definition fromDecString (s : string) : option N :=
  if negb (bool_decide (s = EMPTYSTRING)) && EVERY isDigit s
  then Some (num_from_dec_string s) else None.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "fromHexString_def" *)
Definition fromHexString (s : string) : option N :=
  if negb (bool_decide (s = EMPTYSTRING)) && EVERY isHexDigit s
  then Some (num_from_hex_string s) else None.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "s2n_n2s" *)
Theorem s2n_n2s : forall c2n n2c b n,
  1 < b /\ (forall x, x < b -> c2n (n2c x) = x) -> s2n b c2n (n2s b n2c n) = n.
Proof.
  intros c2n n2c b n [Hb Hc]; unfold s2n, n2s.
  rewrite rev_involutive, map_map.
  rewrite map_ext_in with (g := fun x => x).
  - rewrite map_id; apply l2n_n2l, Hb.
  - intros x Hx; apply Hc.
    pose proof (n2l_BOUND b n ltac:(lia)) as HB.
    apply EVERY_Forall in HB; rewrite Forall_forall in HB.
    apply N.ltb_lt, HB, Hx.
Qed.

(** HOL overloads [toString] for [num_to_dec_string] and [toNum] for
    [num_from_dec_string]; the Rocq statements use the constants. *)

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "toNum_toString" *)
Theorem toNum_toString : forall n, num_from_dec_string (num_to_dec_string n) = n.
Proof.
  intros n; apply s2n_n2s; split; [lia|].
  intros x Hx; apply UNHEX_HEX; lia.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "toString_toNum_cancel" *)
Theorem toString_toNum_cancel : forall n, num_from_dec_string (num_to_dec_string n) = n.
Proof. exact toNum_toString. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "toString_inj" *)
Theorem toString_inj : forall n m, num_to_dec_string n = num_to_dec_string m <-> n = m.
Proof.
  intros n m; split; [|intros ->; reflexivity].
  intros H; rewrite <- (toNum_toString n), H; apply toNum_toString.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "toString_11" *)
Theorem toString_11 : forall n m, num_to_dec_string n = num_to_dec_string m <-> n = m.
Proof. exact toString_inj. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "STRCAT_toString_inj" *)
Theorem STRCAT_toString_inj : forall n m s,
  STRCAT s (num_to_dec_string n) = STRCAT s (num_to_dec_string m) <-> n = m.
Proof. intros n m s; rewrite (proj1 STRCAT_11); apply toString_inj. Qed.

Lemma n2l_nonempty b n : n2l b n <> [].
Proof. rewrite n2l_def; destruct (_ || _); discriminate. Qed.

Lemma n2s_nonempty b f n : n2s b f n <> EMPTYSTRING.
Proof.
  unfold n2s; intros H; apply (f_equal (@List.rev ascii)) in H.
  rewrite rev_involutive in H; cbn in H.
  apply map_eq_nil in H; apply (n2l_nonempty b n), H.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_bin_string_nil" *)
Theorem num_to_bin_string_nil : forall n, num_to_bin_string n <> [].
Proof. intros n; apply n2s_nonempty. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_oct_string_nil" *)
Theorem num_to_oct_string_nil : forall n, num_to_oct_string n <> [].
Proof. intros n; apply n2s_nonempty. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_dec_string_nil" *)
Theorem num_to_dec_string_nil : forall n, num_to_dec_string n <> [].
Proof. intros n; apply n2s_nonempty. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "num_to_hex_string_nil" *)
Theorem num_to_hex_string_nil : forall n, num_to_hex_string n <> [].
Proof. intros n; apply n2s_nonempty. Qed.

Lemma EVERY_n2s (P : ascii -> bool) b f n :
  (forall x, x < b -> P (f x) = true) -> 0 < b -> EVERY P (n2s b f n) = true.
Proof.
  intros HP Hb; unfold n2s; apply EVERY_Forall, Forall_rev, Forall_map.
  pose proof (n2l_BOUND b n Hb) as HB; apply EVERY_Forall in HB.
  eapply Forall_impl; [|exact HB]; intros x Hx; apply HP, N.ltb_lt, Hx.
Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "EVERY_isDigit_num_to_dec_string" *)
Theorem EVERY_isDigit_num_to_dec_string : forall n, EVERY isDigit (num_to_dec_string n).
Proof. intros n; apply EVERY_n2s; [apply isDigit_HEX|lia]. Qed.

(*! HOL "HOL/src/string/ASCIInumbersScript.sml" "EVERY_isHexDigit_num_to_hex_string" *)
Theorem EVERY_isHexDigit_num_to_hex_string : forall n,
  EVERY (fun c => isHexDigit c && implb (isAlpha c) (isUpper c)) (num_to_hex_string n).
Proof.
  intros n; apply EVERY_n2s; [|lia].
  intros x Hx; destruct (isHexDigit_HEX x Hx) as [H1 H2]; rewrite H1; cbn.
  destruct (isAlpha (HEX x)); cbn; [apply H2|]; reflexivity.
Qed.
