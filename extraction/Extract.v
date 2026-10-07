(** Extraction of the Galette compiler to OCaml.

    HOL [num] is Rocq [nat]; it is extracted to Zarith's arbitrary-precision
    integers ([Z.t]) and its arithmetic to the corresponding Zarith
    operations.  This is the only trusted step between the Rocq definitions and
    the executable (besides the OCaml toolchain): each realisation below
    agrees with the Rocq definition on all natural numbers. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlString.
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.

Extract Inductive nat => "Z.t" ["Z.zero" "Z.succ"]
  "(fun fO fS n -> if Z.equal n Z.zero then fO () else fS (Z.pred n))".
Extract Inlined Constant Init.Nat.add => "Z.add".
Extract Inlined Constant PeanoNat.Nat.add => "Z.add".
Extract Inlined Constant Init.Nat.mul => "Z.mul".
Extract Inlined Constant PeanoNat.Nat.mul => "Z.mul".
Extract Inlined Constant Init.Nat.sub => "(fun n m -> Z.max Z.zero (Z.sub n m))".
Extract Inlined Constant PeanoNat.Nat.sub => "(fun n m -> Z.max Z.zero (Z.sub n m))".
Extract Inlined Constant Init.Nat.pred => "(fun n -> Z.max Z.zero (Z.pred n))".
Extract Inlined Constant PeanoNat.Nat.pred => "(fun n -> Z.max Z.zero (Z.pred n))".
Extract Inlined Constant Init.Nat.div => "(fun n m -> if Z.equal m Z.zero then Z.zero else Z.div n m)".
Extract Inlined Constant PeanoNat.Nat.div => "(fun n m -> if Z.equal m Z.zero then Z.zero else Z.div n m)".
Extract Inlined Constant Init.Nat.modulo => "(fun n m -> if Z.equal m Z.zero then n else Z.rem n m)".
Extract Inlined Constant PeanoNat.Nat.modulo => "(fun n m -> if Z.equal m Z.zero then n else Z.rem n m)".
Extract Inlined Constant Init.Nat.pow => "(fun n m -> Z.pow n (Z.to_int m))".
Extract Inlined Constant PeanoNat.Nat.pow => "(fun n m -> Z.pow n (Z.to_int m))".
Extract Inlined Constant Init.Nat.eqb => "Z.equal".
Extract Inlined Constant PeanoNat.Nat.eqb => "Z.equal".
Extract Inlined Constant Init.Nat.leb => "Z.leq".
Extract Inlined Constant PeanoNat.Nat.leb => "Z.leq".
Extract Inlined Constant Init.Nat.ltb => "Z.lt".
Extract Inlined Constant PeanoNat.Nat.ltb => "Z.lt".
Extract Inlined Constant Init.Nat.max => "Z.max".
Extract Inlined Constant PeanoNat.Nat.max => "Z.max".
Extract Inlined Constant Init.Nat.min => "Z.min".
Extract Inlined Constant PeanoNat.Nat.min => "Z.min".
Extract Inlined Constant Init.Nat.land => "Z.logand".
Extract Inlined Constant PeanoNat.Nat.land => "Z.logand".
Extract Inlined Constant Init.Nat.lor => "Z.logor".
Extract Inlined Constant PeanoNat.Nat.lor => "Z.logor".
Extract Inlined Constant Init.Nat.lxor => "Z.logxor".
Extract Inlined Constant PeanoNat.Nat.lxor => "Z.logxor".
Extract Inlined Constant Init.Nat.testbit => "(fun n i -> Z.testbit n (Z.to_int i))".
Extract Inlined Constant PeanoNat.Nat.testbit => "(fun n i -> Z.testbit n (Z.to_int i))".
Extract Inlined Constant Init.Nat.shiftl => "(fun n i -> Z.shift_left n (Z.to_int i))".
Extract Inlined Constant PeanoNat.Nat.shiftl => "(fun n i -> Z.shift_left n (Z.to_int i))".
Extract Inlined Constant Init.Nat.shiftr => "(fun n i -> Z.shift_right n (Z.to_int i))".
Extract Inlined Constant PeanoNat.Nat.shiftr => "(fun n i -> Z.shift_right n (Z.to_int i))".
Extract Inlined Constant Init.Nat.log2 => "(fun n -> if Z.leq n Z.zero then Z.zero else Z.of_int (Z.log2 n))".
Extract Inlined Constant PeanoNat.Nat.log2 => "(fun n -> if Z.leq n Z.zero then Z.zero else Z.of_int (Z.log2 n))".
Extract Inlined Constant PeanoNat.Nat.eq_dec => "Z.equal".

(** [ARB]/[select] are not computable; reaching them at run time is a bug. *)
Extract Constant select => "(fun _ _ -> failwith ""Galette: ARB/select evaluated"")".

Definition smoke : list nat :=
  let x := (n2w 300 : word8) in
  let y := (n2w 200 : word8) in
  [w2n (word_add x y); w2n (word_sub y x); w2n (word_lsl x 3);
   w2n (word_asr (n2w 200 : word8) 2); w2n (word_ror x 3);
   if word_lt x y then 1 else 0; if word_lo x y then 1 else 0;
   w2n (sw2sw (n2w 200 : word8) : word64); w2n (word_1comp (n2w 0 : word64))].

Set Extraction Output Directory ".".
Extraction "galette_smoke.ml" smoke.
