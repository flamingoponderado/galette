(** * CakeML [mlint]: pure functions of the basis [Int] module

    Port of [cakeml/basis/pure/mlintScript.sml], restricted to the printing
    functions used by the compiler ([toString] on [int] and its [num]
    overload [num_to_str]).

    [num_to_chars] is defined in HOL by well-founded recursion on a
    lexicographic measure (dividing by [10 ** exp_for_dec_enc] first).  Here
    it is defined by its characterisation [num_to_chars_thm] (decimal digits
    of [k + i * 10 ** j] prepended to [acc]), which is the tagged theorem;
    HOL's defining equations are not stated, so [num_to_chars_def] is not
    tagged.

    Not ported: [padLen_DEC], [maxSmall_DEC], the [fromString] family,
    [int_cmp], [num_gcd], [int_gcd] and their theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string ASCIInumbers.
From Galette.cakeml.basis.pure Require Import mlstring.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/basis/pure/mlintScript.sml" "toChar_def" *)
Definition toChar (digit : N) : ascii :=
  if digit <? 10 then CHR (ORD "0"%char + digit)
  else CHR (ORD "A"%char + digit - 10).

(*! HOL "cakeml/basis/pure/mlintScript.sml" "exp_for_dec_enc_def" *)
Definition exp_for_dec_enc : N := 8.

(** HOL [num_to_chars] (see the header): the decimal digits of
    [k + i * 10 ** j] followed by [acc]. *)
Definition num_to_chars (i j k : N) (acc : string) : string :=
  num_to_dec_string (k + i * 10 ^ j) ++ acc.

(*! HOL "cakeml/basis/pure/mlintScript.sml" "num_to_chars_thm" *)
Theorem num_to_chars_thm : forall i j k acc,
  num_to_chars i j k acc = num_to_dec_string (k + (i * (10 ^ j))) ++ acc.
Proof. reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlintScript.sml" "int_to_string_def" *)
Definition int_to_string (neg_char : ascii) (i : Z) : mlstring :=
  if (0 <=? i)%Z
  then implode (num_to_chars (Z.to_N i) 0 0 [])
  else implode (neg_char :: num_to_chars (Z.to_N (Z.abs i)) 0 0 []).

(** HOL [toString] on [int] (HOL's [toString_def1]). *)
(*! HOL "cakeml/basis/pure/mlintScript.sml" "toString_def1" *)
Definition toString (i : Z) : mlstring := int_to_string "~"%char i.

(*! HOL "cakeml/basis/pure/mlintScript.sml" "num_to_str_def" *)
Definition num_to_str (n : N) : mlstring := toString (Z.of_N n).

(*! HOL "cakeml/basis/pure/mlintScript.sml" "num_to_str_thm" *)
Theorem num_to_str_thm : forall n, num_to_str n = implode (num_to_dec_string n).
Proof.
  intros n; unfold num_to_str, toString, int_to_string.
  replace (0 <=? Z.of_N n)%Z with true by (symmetry; apply Z.leb_le; lia).
  unfold num_to_chars; rewrite N2Z.id, app_nil_r; f_equal; f_equal; lia.
Qed.
