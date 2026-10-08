(** * CakeML [bvl_to_bvi]: stub locations and configuration

    Partial port of [cakeml/compiler/backend/bvl_to_bviScript.sml]: only the
    stub location constants used by later passes (e.g. [stack_to_lab]'s
    [InitGlobals_location]), and the [config] record with its
    [default_config] (HOL's local overload [num_stubs] is
    [backend_common]'s [bvl_num_stubs]).  The BVL-to-BVI compiler itself is
    not part of the Pancake pipeline and is not ported. *)

From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import backend_common bvl bvi.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "AllocGlobal_location_def" *)
Definition AllocGlobal_location : N := data_num_stubs.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "CopyGlobals_location_def" *)
Definition CopyGlobals_location : N := AllocGlobal_location + 1.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "InitGlobals_location_def" *)
Definition InitGlobals_location : N := CopyGlobals_location + 1.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "ListLength_location_def" *)
Definition ListLength_location : N := InitGlobals_location + 1.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "FromListByte_location_def" *)
Definition FromListByte_location : N := ListLength_location + 1.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "ToListByte_location_def" *)
Definition ToListByte_location : N := FromListByte_location + 1.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "SumListLength_location_def" *)
Definition SumListLength_location : N := ToListByte_location + 1.
(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "ConcatByte_location_def" *)
Definition ConcatByte_location : N := SumListLength_location + 1.

(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "config" *)
Record config : Type := {
  inline_size_limit : N;
  exp_cut : N;
  split_main_at_seq : bool;
  next_name1 : N;
  next_name2 : N;
  next_name3 : N;
  do_tailrec : bool;
  do_tmc : bool;
  inlines : spt (N * bvl.exp);
  bvi_inlines : spt (N * bvi.exp)
}.

(*! HOL "cakeml/compiler/backend/bvl_to_bviScript.sml" "default_config_def" *)
Definition default_config : config :=
  {| inline_size_limit := 10;
     exp_cut := 1000;
     split_main_at_seq := true;
     next_name1 := bvl_num_stubs + 1;
     next_name2 := bvl_num_stubs + 2;
     next_name3 := bvl_num_stubs + 3;
     do_tailrec := true;
     do_tmc := true;
     inlines := LN;
     bvi_inlines := LN |}.

#[global] Instance config_inhabited : Inhabited config := default_config.
