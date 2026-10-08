(** Extraction of the Galette compiler to OCaml.

    HOL [num] is Rocq [N] and HOL [int] is Rocq [Z]; both (and [positive],
    and [nat] where it still occurs) are extracted to Zarith's
    arbitrary-precision integers, accessed through the alias module
    [Galette_zarith] (= Zarith's [Z]) so that the [Z] module extracted from
    Rocq cannot shadow it.  Each realisation below agrees with the Rocq
    definition on all arguments (division and modulus by zero included).
    This file is part of the trusted base of the executable. *)

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlString.
From Stdlib Require Import NArith ZArith.
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.

Extract Inductive positive => "Galette_zarith.t"
  [ "(fun p -> Galette_zarith.add (Galette_zarith.shift_left p 1) Galette_zarith.one)" "(fun p -> Galette_zarith.shift_left p 1)" "Galette_zarith.one" ]
  "(fun f2p1 f2p f1 p -> if Galette_zarith.leq p Galette_zarith.one then f1 () else if Galette_zarith.is_even p then f2p (Galette_zarith.shift_right p 1) else f2p1 (Galette_zarith.shift_right p 1))".
Extract Inductive N => "Galette_zarith.t" [ "Galette_zarith.zero" "(fun p -> p)" ]
  "(fun f0 fp n -> if Galette_zarith.equal n Galette_zarith.zero then f0 () else fp n)".
Extract Inductive Z => "Galette_zarith.t" [ "Galette_zarith.zero" "(fun p -> p)" "Galette_zarith.neg" ]
  "(fun f0 fp fn z -> let s = Galette_zarith.sign z in if s = 0 then f0 () else if s > 0 then fp z else fn (Galette_zarith.neg z))".
Extract Inductive nat => "Galette_zarith.t" [ "Galette_zarith.zero" "Galette_zarith.succ" ]
  "(fun fO fS n -> if Galette_zarith.equal n Galette_zarith.zero then fO () else fS (Galette_zarith.pred n))".

Extract Inlined Constant Init.Nat.add => "Galette_zarith.add".
Extract Inlined Constant Init.Nat.mul => "Galette_zarith.mul".
Extract Inlined Constant Init.Nat.eqb => "Galette_zarith.equal".
Extract Inlined Constant Init.Nat.leb => "Galette_zarith.leq".
Extract Inlined Constant Init.Nat.ltb => "Galette_zarith.lt".
Extract Inlined Constant Init.Nat.max => "Galette_zarith.max".
Extract Inlined Constant Init.Nat.min => "Galette_zarith.min".
Extract Inlined Constant Init.Nat.land => "Galette_zarith.logand".
Extract Inlined Constant Init.Nat.lor => "Galette_zarith.logor".
Extract Inlined Constant Init.Nat.lxor => "Galette_zarith.logxor".
Extract Inlined Constant Init.Nat.testbit => "(fun n i -> Galette_zarith.testbit n (Galette_zarith.to_int i))".
Extract Inlined Constant Init.Nat.shiftl => "(fun n i -> Galette_zarith.shift_left n (Galette_zarith.to_int i))".
Extract Inlined Constant Init.Nat.shiftr => "(fun n i -> Galette_zarith.shift_right n (Galette_zarith.to_int i))".
Extract Inlined Constant Init.Nat.pow => "(fun n m -> Galette_zarith.pow n (Galette_zarith.to_int m))".
Extract Inlined Constant Init.Nat.even => "Galette_zarith.is_even".
Extract Inlined Constant Init.Nat.odd => "Galette_zarith.is_odd".
Extract Inlined Constant Init.Nat.succ => "Galette_zarith.succ".
Extract Inlined Constant Init.Nat.sub => "(fun n m -> Galette_zarith.max Galette_zarith.zero (Galette_zarith.sub n m))".
Extract Inlined Constant Init.Nat.pred => "(fun n -> Galette_zarith.max Galette_zarith.zero (Galette_zarith.pred n))".
Extract Inlined Constant Init.Nat.div => "(fun n m -> if Galette_zarith.equal m Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.div n m)".
Extract Inlined Constant Init.Nat.modulo => "(fun n m -> if Galette_zarith.equal m Galette_zarith.zero then n else Galette_zarith.rem n m)".
Extract Inlined Constant Init.Nat.log2 => "(fun n -> if Galette_zarith.leq n Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.of_int (Galette_zarith.log2 n))".
Extract Inlined Constant Init.Nat.div2 => "(fun n -> Galette_zarith.shift_right n 1)".
Extract Inlined Constant PeanoNat.Nat.add => "Galette_zarith.add".
Extract Inlined Constant PeanoNat.Nat.mul => "Galette_zarith.mul".
Extract Inlined Constant PeanoNat.Nat.eqb => "Galette_zarith.equal".
Extract Inlined Constant PeanoNat.Nat.leb => "Galette_zarith.leq".
Extract Inlined Constant PeanoNat.Nat.ltb => "Galette_zarith.lt".
Extract Inlined Constant PeanoNat.Nat.max => "Galette_zarith.max".
Extract Inlined Constant PeanoNat.Nat.min => "Galette_zarith.min".
Extract Inlined Constant PeanoNat.Nat.compare => "(fun a b -> let c = Galette_zarith.compare a b in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Inlined Constant PeanoNat.Nat.land => "Galette_zarith.logand".
Extract Inlined Constant PeanoNat.Nat.lor => "Galette_zarith.logor".
Extract Inlined Constant PeanoNat.Nat.lxor => "Galette_zarith.logxor".
Extract Inlined Constant PeanoNat.Nat.testbit => "(fun n i -> Galette_zarith.testbit n (Galette_zarith.to_int i))".
Extract Inlined Constant PeanoNat.Nat.shiftl => "(fun n i -> Galette_zarith.shift_left n (Galette_zarith.to_int i))".
Extract Inlined Constant PeanoNat.Nat.shiftr => "(fun n i -> Galette_zarith.shift_right n (Galette_zarith.to_int i))".
Extract Inlined Constant PeanoNat.Nat.pow => "(fun n m -> Galette_zarith.pow n (Galette_zarith.to_int m))".
Extract Inlined Constant PeanoNat.Nat.even => "Galette_zarith.is_even".
Extract Inlined Constant PeanoNat.Nat.odd => "Galette_zarith.is_odd".
Extract Inlined Constant PeanoNat.Nat.succ => "Galette_zarith.succ".
Extract Inlined Constant PeanoNat.Nat.eq_dec => "Galette_zarith.equal".
Extract Inlined Constant PeanoNat.Nat.sub => "(fun n m -> Galette_zarith.max Galette_zarith.zero (Galette_zarith.sub n m))".
Extract Inlined Constant PeanoNat.Nat.pred => "(fun n -> Galette_zarith.max Galette_zarith.zero (Galette_zarith.pred n))".
Extract Inlined Constant PeanoNat.Nat.div => "(fun n m -> if Galette_zarith.equal m Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.div n m)".
Extract Inlined Constant PeanoNat.Nat.modulo => "(fun n m -> if Galette_zarith.equal m Galette_zarith.zero then n else Galette_zarith.rem n m)".
Extract Inlined Constant PeanoNat.Nat.log2 => "(fun n -> if Galette_zarith.leq n Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.of_int (Galette_zarith.log2 n))".
Extract Inlined Constant PeanoNat.Nat.div2 => "(fun n -> Galette_zarith.shift_right n 1)".
Extract Inlined Constant PeanoNat.Nat.ldiff => "(fun a b -> Galette_zarith.logand a (Galette_zarith.lognot b))".
Extract Inlined Constant PeanoNat.Nat.sqrt => "Galette_zarith.sqrt".
Extract Inlined Constant N.add => "Galette_zarith.add".
Extract Inlined Constant N.mul => "Galette_zarith.mul".
Extract Inlined Constant N.eqb => "Galette_zarith.equal".
Extract Inlined Constant N.leb => "Galette_zarith.leq".
Extract Inlined Constant N.ltb => "Galette_zarith.lt".
Extract Inlined Constant N.max => "Galette_zarith.max".
Extract Inlined Constant N.min => "Galette_zarith.min".
Extract Inlined Constant N.compare => "(fun a b -> let c = Galette_zarith.compare a b in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Inlined Constant N.land => "Galette_zarith.logand".
Extract Inlined Constant N.lor => "Galette_zarith.logor".
Extract Inlined Constant N.lxor => "Galette_zarith.logxor".
Extract Inlined Constant N.testbit => "(fun n i -> Galette_zarith.testbit n (Galette_zarith.to_int i))".
Extract Inlined Constant N.shiftl => "(fun n i -> Galette_zarith.shift_left n (Galette_zarith.to_int i))".
Extract Inlined Constant N.shiftr => "(fun n i -> Galette_zarith.shift_right n (Galette_zarith.to_int i))".
Extract Inlined Constant N.pow => "(fun n m -> Galette_zarith.pow n (Galette_zarith.to_int m))".
Extract Inlined Constant N.even => "Galette_zarith.is_even".
Extract Inlined Constant N.odd => "Galette_zarith.is_odd".
Extract Inlined Constant N.succ => "Galette_zarith.succ".
Extract Inlined Constant N.eq_dec => "Galette_zarith.equal".
Extract Inlined Constant N.double => "(fun n -> Galette_zarith.shift_left n 1)".
Extract Inlined Constant N.sub => "(fun n m -> Galette_zarith.max Galette_zarith.zero (Galette_zarith.sub n m))".
Extract Inlined Constant N.pred => "(fun n -> Galette_zarith.max Galette_zarith.zero (Galette_zarith.pred n))".
Extract Inlined Constant N.div => "(fun n m -> if Galette_zarith.equal m Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.div n m)".
Extract Inlined Constant N.modulo => "(fun n m -> if Galette_zarith.equal m Galette_zarith.zero then n else Galette_zarith.rem n m)".
Extract Inlined Constant N.log2 => "(fun n -> if Galette_zarith.leq n Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.of_int (Galette_zarith.log2 n))".
Extract Inlined Constant N.div2 => "(fun n -> Galette_zarith.shift_right n 1)".
Extract Inlined Constant N.ldiff => "(fun a b -> Galette_zarith.logand a (Galette_zarith.lognot b))".
Extract Inlined Constant N.sqrt => "Galette_zarith.sqrt".
Extract Inlined Constant Z.add => "Galette_zarith.add".
Extract Inlined Constant Z.mul => "Galette_zarith.mul".
Extract Inlined Constant Z.eqb => "Galette_zarith.equal".
Extract Inlined Constant Z.leb => "Galette_zarith.leq".
Extract Inlined Constant Z.ltb => "Galette_zarith.lt".
Extract Inlined Constant Z.max => "Galette_zarith.max".
Extract Inlined Constant Z.min => "Galette_zarith.min".
Extract Inlined Constant Z.compare => "(fun a b -> let c = Galette_zarith.compare a b in if c = 0 then Eq else if c < 0 then Lt else Gt)".
Extract Inlined Constant Z.land => "Galette_zarith.logand".
Extract Inlined Constant Z.lor => "Galette_zarith.logor".
Extract Inlined Constant Z.lxor => "Galette_zarith.logxor".
Extract Inlined Constant Z.testbit => "(fun n i -> Galette_zarith.testbit n (Galette_zarith.to_int i))".
Extract Inlined Constant Z.shiftl => "(fun n i -> Galette_zarith.shift_left n (Galette_zarith.to_int i))".
Extract Inlined Constant Z.shiftr => "(fun n i -> Galette_zarith.shift_right n (Galette_zarith.to_int i))".
Extract Inlined Constant Z.pow => "(fun n m -> Galette_zarith.pow n (Galette_zarith.to_int m))".
Extract Inlined Constant Z.succ => "Galette_zarith.succ".
Extract Inlined Constant Z.eq_dec => "Galette_zarith.equal".
Extract Inlined Constant Z.sub => "Galette_zarith.sub".
Extract Inlined Constant Z.opp => "Galette_zarith.neg".
Extract Inlined Constant Z.pred => "Galette_zarith.pred".
Extract Inlined Constant Z.abs => "Galette_zarith.abs".
Extract Inlined Constant Z.sgn => "(fun z -> Galette_zarith.of_int (Galette_zarith.sign z))".
Extract Inlined Constant Z.div => "(fun a b -> if Galette_zarith.equal b Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.fdiv a b)".
Extract Inlined Constant Z.modulo => "(fun a b -> if Galette_zarith.equal b Galette_zarith.zero then a else Galette_zarith.sub a (Galette_zarith.mul b (Galette_zarith.fdiv a b)))".
Extract Inlined Constant Z.quot => "(fun a b -> if Galette_zarith.equal b Galette_zarith.zero then Galette_zarith.zero else Galette_zarith.div a b)".
Extract Inlined Constant Z.rem => "(fun a b -> if Galette_zarith.equal b Galette_zarith.zero then a else Galette_zarith.rem a b)".
Extract Inlined Constant Z.of_nat => "(fun n -> n)".
Extract Inlined Constant Z.to_nat => "(fun z -> Galette_zarith.max Galette_zarith.zero z)".
Extract Inlined Constant Z.of_N => "(fun n -> n)".
Extract Inlined Constant Z.to_N => "(fun z -> Galette_zarith.max Galette_zarith.zero z)".
Extract Inlined Constant Z.abs_nat => "Galette_zarith.abs".
Extract Inlined Constant Z.abs_N => "Galette_zarith.abs".
Extract Inlined Constant Z.even => "Galette_zarith.is_even".
Extract Inlined Constant Z.odd => "Galette_zarith.is_odd".
Extract Inlined Constant N.of_nat => "(fun n -> n)".
Extract Inlined Constant N.to_nat => "(fun n -> n)".
Extract Inlined Constant N.peano_rect =>
  "(fun _ f0 fs n -> let rec go i acc = if Galette_zarith.equal i n then acc else go (Galette_zarith.succ i) (fs i acc) in go Galette_zarith.zero f0)".
Extract Inlined Constant N.peano_rec =>
  "(fun f0 fs n -> let rec go i acc = if Galette_zarith.equal i n then acc else go (Galette_zarith.succ i) (fs i acc) in go Galette_zarith.zero f0)".

(** [ARB]/[select] are not computable; reaching them at run time is a bug. *)
Extract Constant select => "(fun _ _ -> failwith ""Galette: ARB/select evaluated"")".

Open Scope N_scope.
Definition smoke : list N :=
  let x := (n2w 300 : word8) in
  let y := (n2w 200 : word8) in
  [w2n (word_add x y); w2n (word_sub y x); w2n (word_lsl x 3);
   w2n (word_asr (n2w 200 : word8) 2); w2n (word_ror x 3);
   if word_lt x y then 1 else 0; if word_lo x y then 1 else 0;
   w2n (sw2sw (n2w 200 : word8) : word64); w2n (word_1comp (n2w 0 : word64));
   w2n (word_add (n2w 18446744073709551615 : word64) (n2w 5))].

Set Extraction Output Directory ".".
Extraction "galette_smoke.ml" smoke.
