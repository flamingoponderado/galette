(** * CakeML [word_cse]: common sub-expression elimination on wordLang

    Port of [cakeml/compiler/backend/word_cseScript.sml].

    - The instruction maps are HOL [balanced_map]s keyed by [num list] and
      compared by [listCmp]; [balanced_map] is required qualified
      ([balanced_map.lookup], [balanced_map.insert], [balanced_map.empty])
      as its names clash with sptree's.  [listCmp]'s results
      [Less]/[Equal]/[Greater] (comparisonTheory overloads) are
      [LESS]/[EQUAL]/[GREATER].
    - [lookup_any] ([miscScript]) is not yet in [misc.v]; [lookup_any] below
      is an untagged copy.
    - HOL's record updates are written as record constructions.
    - The HOL test theorems are ported at the end, with the test-only
      constant [Seqs] (which HOL deletes after the tests) as a local
      definition. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.HOL.src.finite_maps Require Import sptree alist.
From Galette.HOL.examples.data_structures.balanced_bst Require balanced_map.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang.
Open Scope N_scope.

(** [miscScript]'s [lookup_any] (untagged copy; see the file header). *)
Definition lookup_any {A} (x : N) (sp : spt A) (d : A) : A :=
  match lookup x sp with
  | None => d
  | Some m => m
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "knowledge" *)
Record knowledge : Type := {
  to_canonical : num_map N;
  to_latest : num_map N;
  gets_mem : list (store_name * N);
  instrs_mem : balanced_map.balanced_map (list N) N;
  loads_mem : balanced_map.balanced_map (list N) N
}.

(** ** List comparison *)

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "listCmp_def" *)
Fixpoint listCmp (l1 l2 : list N) : ordering :=
  match l1, l2 with
  | hd1 :: tl1, hd2 :: tl2 =>
      if hd1 =? hd2 then listCmp tl1 tl2
      else if hd2 <? hd1 then GREATER else LESS
  | [], [] => EQUAL
  | hd1 :: tl1, [] => GREATER
  | [], hd2 :: tl2 => LESS
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "empty_data_def" *)
Definition empty_data : knowledge :=
  {| to_canonical := LN; to_latest := LN; gets_mem := [];
     instrs_mem := balanced_map.empty; loads_mem := balanced_map.empty |}.

#[global] Instance knowledge_inhabited : Inhabited knowledge := empty_data.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "keep_data_def" *)
Definition keep_data (canon : num_map N) (write_to_reg : N) : bool :=
  IS_NONE (lookup write_to_reg canon).

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "invalidate_data_def" *)
Definition invalidate_data (data : knowledge) (write_to_reg : N) : knowledge :=
  if keep_data (to_canonical data) write_to_reg then data else empty_data.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "invalidate_regs_def" *)
Fixpoint invalidate_regs (data : knowledge) (l : list N) : knowledge :=
  match l with
  | [] => data
  | r :: rs => invalidate_regs (invalidate_data data r) rs
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "register_read_def" *)
Definition register_read (data : knowledge) (r : N) : knowledge :=
  if negb (EVEN r) && keep_data (to_canonical data) r then
    {| to_canonical := insert r r (to_canonical data); to_latest := to_latest data;
       gets_mem := gets_mem data; instrs_mem := instrs_mem data; loads_mem := loads_mem data |}
  else data.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "register_reads_def" *)
Fixpoint register_reads (data : knowledge) (l : list N) : knowledge :=
  match l with
  | [] => data
  | r :: rs => register_reads (register_read data r) rs
  end.

(** ** Register transformations *)

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalRegs_def" *)
Definition canonicalRegs (data : knowledge) (r : N) : N :=
  lookup_any r (to_canonical data) r.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalRegs'_def" *)
Definition canonicalRegs' (avoid : N) (data : knowledge) (r : N) : N :=
  let n := canonicalRegs data r in
  if n =? avoid then r else n.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalImmReg_def" *)
Definition canonicalImmReg {a} (data : knowledge) (ri : reg_imm a) : reg_imm a :=
  match ri with
  | Reg r => Reg (canonicalRegs data r)
  | Imm w => Imm w
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalImmReg'_def" *)
Definition canonicalImmReg' {a} (avoid : N) (data : knowledge) (ri : reg_imm a) : reg_imm a :=
  match ri with
  | Reg r => Reg (canonicalRegs' avoid data r)
  | Imm w => Imm w
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalMultRegs_def" *)
Definition canonicalMultRegs (data : knowledge) (regs : list N) : list N :=
  MAP (canonicalRegs data) regs.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "map_insert_def" *)
Fixpoint map_insert {A} (l : list (N * A)) (m : spt A) : spt A :=
  match l with
  | [] => m
  | (x, y) :: xs => insert x y (map_insert xs m)
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalMoveRegs_def" *)
Definition canonicalMoveRegs (data : knowledge) (moves : list (N * N)) : knowledge :=
  let data := register_reads data (MAP SND moves) in
  if EVERY (keep_data (to_canonical data)) (MAP FST moves) then
    let xs := FILTER (fun '(a, b) => negb (EVEN a) && negb (EVEN b)) moves in
    let ys := MAP (fun '(a, b) => (a, canonicalRegs data b)) xs in
    let to_c := map_insert ys (to_canonical data) in
    let zs := MAP (fun '(a, b) => (b, a)) ys in
    let to_l := map_insert zs (to_latest data) in
    {| to_canonical := to_c; to_latest := to_l; gets_mem := gets_mem data;
       instrs_mem := instrs_mem data; loads_mem := loads_mem data |}
  else empty_data.

Section Canon.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalArith_def" *)
Definition canonicalArith (data : knowledge) (x : arith a) : arith a :=
  match x with
  | Binop op r1 r2 r3 => Binop op r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data r3)
  | asm.Shift s r1 r2 ri => asm.Shift s r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data ri)
  | Div r1 r2 r3 => Div r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | LongMul r1 r2 r3 r4 => LongMul r1 r2 (canonicalRegs data r3) (canonicalRegs data r4)
  | LongDiv r1 r2 r3 r4 r5 =>
      LongDiv r1 r2 (canonicalRegs data r3) (canonicalRegs data r4) (canonicalRegs data r5)
  | AddCarry r1 r2 r3 r4 =>
      AddCarry r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4
  | AddOverflow r1 r2 r3 r4 =>
      AddOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4
  | SubOverflow r1 r2 r3 r4 =>
      SubOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4
  end.

End Canon.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "canonicalFp_def" *)
Definition canonicalFp (data : knowledge) (x : fp) : fp :=
  match x with
  | FPLess r1 r2 r3 => FPLess r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPLessEqual r1 r2 r3 => FPLessEqual r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPEqual r1 r2 r3 => FPEqual r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPAbs r1 r2 => FPAbs r1 (canonicalRegs data r2)
  | FPNeg r1 r2 => FPNeg r1 (canonicalRegs data r2)
  | FPSqrt r1 r2 => FPSqrt r1 (canonicalRegs data r2)
  | FPAdd r1 r2 r3 => FPAdd r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPSub r1 r2 r3 => FPSub r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPMul r1 r2 r3 => FPMul r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPDiv r1 r2 r3 => FPDiv r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPFma r1 r2 r3 => FPFma r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPMov r1 r2 => FPMov r1 (canonicalRegs data r2)
  | FPMovToReg r1 r2 r3 => FPMovToReg r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPMovFromReg r1 r2 r3 => FPMovFromReg r1 (canonicalRegs data r2) (canonicalRegs data r3)
  | FPToInt r1 r2 => FPToInt r1 (canonicalRegs data r2)
  | FPFromInt r1 r2 => FPFromInt r1 (canonicalRegs data r2)
  end.

(** ** Seen instructions memory *)

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "wordToNum_def" *)
Definition wordToNum {a} (w : word a) : N := w2n w.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "shiftToNum_def" *)
Definition shiftToNum (s : shift) : N :=
  match s with Lsl => 40 | Lsr => 41 | Asr => 42 | Ror => 43 end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "arithOpToNum_def" *)
Definition arithOpToNum (op : binop) : N :=
  match op with asm.Add => 35 | asm.Sub => 36 | And => 37 | Or => 38 | asm.Xor => 39 end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "regImmToNumList_def" *)
Definition regImmToNumList {a} (ri : reg_imm a) : list N :=
  match ri with
  | Reg r => [33; r + 100]
  | Imm w => [34; wordToNum w]
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "arithToNumList_def" *)
Definition arithToNumList {a} (x : arith a) : list N :=
  match x with
  | Binop op r1 r2 ri => [25; arithOpToNum op; r2 + 100] ++ regImmToNumList ri
  | LongMul r1 r2 r3 r4 => [26; r3 + 100; r4 + 100]
  | LongDiv r1 r2 r3 r4 r5 => [27; r3 + 100; r4 + 100; r5 + 100]
  | asm.Shift s r1 r2 ri => [28; shiftToNum s; r2 + 100] ++ regImmToNumList ri
  | Div r1 r2 r3 => [29; r2 + 100; r3 + 100]
  | AddCarry r1 r2 r3 r4 => [30; r2 + 100; r3 + 100]
  | AddOverflow r1 r2 r3 r4 => [31; r2 + 100; r3 + 100]
  | SubOverflow r1 r2 r3 r4 => [32; r2 + 100; r3 + 100]
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "memOpToNum_def" *)
Definition memOpToNum (m : memop) : N :=
  match m with
  | asm.Load => 21
  | Load8 => 22
  | Load16 => 46
  | Load32 => 44
  | asm.Store => 23
  | Store8 => 47
  | Store16 => 24
  | Store32 => 45
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "loadToNumList_def" *)
Definition loadToNumList {a} (op : memop) (a0 : N) (ofs : word a) : list N :=
  [memOpToNum op; a0 + 100; wordToNum ofs].

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "fpToNumList_def" *)
Definition fpToNumList (x : fp) : list N :=
  match x with
  | FPLess r1 r2 r3 => [5; r2 + 100; r3 + 100]
  | FPLessEqual r1 r2 r3 => [6; r2 + 100; r3 + 100]
  | FPEqual r1 r2 r3 => [7; r2 + 100; r3 + 100]
  | FPAbs r1 r2 => [8; r2 + 100]
  | FPNeg r1 r2 => [9; r2 + 100]
  | FPSqrt r1 r2 => [10; r2 + 100]
  | FPAdd r1 r2 r3 => [11; r2 + 100; r3 + 100]
  | FPSub r1 r2 r3 => [12; r2 + 100; r3 + 100]
  | FPMul r1 r2 r3 => [13; r2 + 100; r3 + 100]
  | FPDiv r1 r2 r3 => [14; r2 + 100; r3 + 100]
  | FPFma r1 r2 r3 => [15; r1 + 100; r2 + 100; r3 + 100]
  | FPMov r1 r2 => [16; r2 + 100]
  | FPMovToReg r1 r2 r3 => [17; r2 + 100; r3 + 100]
  | FPMovFromReg r1 r2 r3 => [18; r2 + 100; r3 + 100]
  | FPToInt r1 r2 => [19; r2 + 100]
  | FPFromInt r1 r2 => [20; r2 + 100]
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "instToNumList_def" *)
Definition instToNumList {a} (i : inst a) : list N :=
  match i with
  | asm.Const r w => [2; wordToNum w]
  | Arith x => 3 :: arithToNumList x
  | FP x => 4 :: fpToNumList x
  | _ => [1]
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "OpCurrHeapToNumList_def" *)
Definition OpCurrHeapToNumList (op : binop) (r2 : N) : list N :=
  [0; arithOpToNum op; r2 + 100].

(** ** Word CSE functions *)

Section Cse.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "firstRegOfArith_def" *)
Definition firstRegOfArith (x : arith a) : N :=
  match x with
  | Binop _ r _ _ => r
  | asm.Shift _ r _ _ => r
  | Div r _ _ => r
  | LongMul r _ _ _ => r
  | LongDiv r _ _ _ _ => r
  | AddCarry r _ _ _ => r
  | AddOverflow r _ _ _ => r
  | SubOverflow r _ _ _ => r
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "arithWrites_def" *)
Definition arithWrites (x : arith a) : list N :=
  match x with
  | Binop _ r _ _ => [r]
  | asm.Shift _ r _ _ => [r]
  | Div r _ _ => [r]
  | LongMul r1 r2 _ _ => [r1; r2]
  | LongDiv r1 r2 _ _ _ => [r1; r2]
  | AddCarry r1 _ _ r4 => [r1; r4]
  | AddOverflow r1 _ _ r4 => [r1; r4]
  | SubOverflow r1 _ _ r4 => [r1; r4]
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "arithReads_def" *)
Definition arithReads (x : arith a) : list N :=
  match x with
  | Binop _ _ r2 (Reg r3) => [r2; r3]
  | Binop _ _ r2 (Imm _) => [r2]
  | asm.Shift _ _ r2 (Reg r3) => [r2; r3]
  | asm.Shift _ _ r2 (Imm _) => [r2]
  | Div _ r2 r3 => [r2; r3]
  | LongMul _ _ r3 r4 => [r3; r4]
  | LongDiv _ _ r3 r4 r5 => [r3; r4; r5]
  | AddCarry _ r2 r3 r4 => [r2; r3; r4]
  | AddOverflow _ r2 r3 _ => [r2; r3]
  | SubOverflow _ r2 r3 _ => [r2; r3]
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "fpWrites_def" *)
Definition fpWrites (x : fp) : list N :=
  match x with
  | FPLess r _ _ => [r]
  | FPLessEqual r _ _ => [r]
  | FPEqual r _ _ => [r]
  | FPMovToReg r1 r2 _ => [r1; r2]
  | _ => []
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "add_to_data_aux_def" *)
Definition add_to_data_aux (data : knowledge) (r : N) (i : list N) (x : prog a)
    : knowledge * prog a :=
  match balanced_map.lookup listCmp i (instrs_mem data) with
  | Some r' =>
      let k := lookup_any r' (to_latest data) r' in
      if EVEN r then (data, Move 0 [(r, k)])
      else ({| to_canonical := insert r r' (to_canonical data);
               to_latest := insert r' r (to_latest data);
               gets_mem := gets_mem data; instrs_mem := instrs_mem data;
               loads_mem := loads_mem data |}, Move 0 [(r, k)])
  | None =>
      if EVEN r then (data, x)
      else ({| to_canonical := insert r r (to_canonical data);
               to_latest := insert r r (to_latest data);
               gets_mem := gets_mem data;
               instrs_mem := balanced_map.insert listCmp i r (instrs_mem data);
               loads_mem := loads_mem data |}, x)
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "add_to_data_def" *)
Definition add_to_data (data : knowledge) (r : N) (adjusted x : inst a) : knowledge * prog a :=
  let i := instToNumList adjusted in
  add_to_data_aux data r i (Inst x).

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "add_to_data_const_def" *)
Definition add_to_data_const (data : knowledge) (r : N) (w : word a) : knowledge * prog a :=
  let i := instToNumList (asm.Const r w : inst a) in
  match balanced_map.lookup listCmp i (instrs_mem data) with
  | Some r' =>
      ({| to_canonical := insert r r' (to_canonical data);
          to_latest := insert r' r (to_latest data);
          gets_mem := gets_mem data; instrs_mem := instrs_mem data;
          loads_mem := loads_mem data |}, Inst (asm.Const r w))
  | None =>
      ({| to_canonical := insert r r (to_canonical data);
          to_latest := insert r r (to_latest data);
          gets_mem := gets_mem data;
          instrs_mem := balanced_map.insert listCmp i r (instrs_mem data);
          loads_mem := loads_mem data |}, Inst (asm.Const r w))
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "add_to_load_aux_def" *)
Definition add_to_load_aux (data : knowledge) (r : N) (i : list N) (x : prog a)
    : knowledge * prog a :=
  match balanced_map.lookup listCmp i (loads_mem data) with
  | Some r' =>
      let k := lookup_any r' (to_latest data) r' in
      if EVEN r then (data, Move 0 [(r, k)])
      else ({| to_canonical := insert r r' (to_canonical data);
               to_latest := insert r' r (to_latest data);
               gets_mem := gets_mem data; instrs_mem := instrs_mem data;
               loads_mem := loads_mem data |}, Move 0 [(r, k)])
  | None =>
      if EVEN r then (data, x)
      else ({| to_canonical := insert r r (to_canonical data);
               to_latest := insert r r (to_latest data);
               gets_mem := gets_mem data; instrs_mem := instrs_mem data;
               loads_mem := balanced_map.insert listCmp i r (loads_mem data) |}, x)
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "can_mem_arith_def" *)
Definition can_mem_arith (x : arith a) : bool :=
  match x with
  | Binop _ _ r1 (Reg r2) => ODD r1 && ODD r2
  | Binop _ _ r1 (Imm _) => ODD r1
  | Div _ r1 r2 => ODD r1 && ODD r2
  | asm.Shift _ _ r (Imm _) => ODD r
  | _ => false
  end.

End Cse.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "is_store_def" *)
Definition is_store (m : memop) : bool :=
  match m with
  | asm.Load => false
  | Load8 => false
  | Load16 => false
  | Load32 => false
  | asm.Store => true
  | Store8 => true
  | Store16 => true
  | Store32 => true
  end.

(** [data with loads_mem := v]. *)
Definition set_loads_mem (data : knowledge) (v : balanced_map.balanced_map (list N) N)
    : knowledge :=
  {| to_canonical := to_canonical data; to_latest := to_latest data;
     gets_mem := gets_mem data; instrs_mem := instrs_mem data; loads_mem := v |}.

(** [data with gets_mem := v]. *)
Definition set_gets_mem (data : knowledge) (v : list (store_name * N)) : knowledge :=
  {| to_canonical := to_canonical data; to_latest := to_latest data;
     gets_mem := v; instrs_mem := instrs_mem data; loads_mem := loads_mem data |}.

Section Cse2.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "word_cseInst_def" *)
Definition word_cseInst (data : knowledge) (i : inst a) : knowledge * prog a :=
  match i with
  | asm.Skip => (data, Inst asm.Skip)
  | asm.Const r w =>
      let data := invalidate_data data r in
      if EVEN r then (data, Inst (asm.Const r w)) else add_to_data_const data r w
  | Arith x =>
      let r := firstRegOfArith x in
      let data := invalidate_regs data (arithWrites x) in
      let a' := canonicalArith data x in
      let rds := arithReads a' in
      if can_mem_arith a' && negb (MEM r rds) then
        add_to_data (register_reads data rds) r (Arith a') (Arith x)
      else (data, Inst (Arith x))
  | Mem op r (Addr a0 ofs) =>
      if is_store op then
        (set_loads_mem data balanced_map.empty, Inst (Mem op r (Addr a0 ofs)))
      else
        let data := invalidate_data data r in
        if EVEN r || EVEN a0 || (a0 =? r) then (data, Inst (Mem op r (Addr a0 ofs)))
        else
          let a' := canonicalRegs' r data a0 in
          add_to_load_aux (register_read data a') r (loadToNumList op a' ofs)
                          (Inst (Mem op r (Addr a0 ofs)))
  | FP x => (invalidate_regs data (fpWrites x), Inst (FP x))
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "dest_Var_def" *)
Definition dest_Var (e : exp a) : option N :=
  match e with Var v => Some v | _ => None end.

End Cse2.

(** ** If-join merge *)

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "bm_inter_eq_acc_def" *)
Fixpoint bm_inter_eq_acc (m2 m1 acc : balanced_map.balanced_map (list N) N)
    : balanced_map.balanced_map (list N) N :=
  match m1 with
  | balanced_map.Tip => acc
  | balanced_map.Bin n k v l r =>
      bm_inter_eq_acc m2 l
        (bm_inter_eq_acc m2 r
          (if bool_decide (balanced_map.lookup listCmp k m2 = Some v)
           then balanced_map.insert listCmp k v acc
           else acc))
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "bm_inter_eq_def" *)
Definition bm_inter_eq (m1 m2 : balanced_map.balanced_map (list N) N)
    : balanced_map.balanced_map (list N) N :=
  bm_inter_eq_acc m2 m1 balanced_map.empty.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "merge_data_def" *)
Definition merge_data (d1 d2 : knowledge) : knowledge :=
  {| to_canonical := inter_eq (to_canonical d1) (to_canonical d2);
     to_latest := LN;
     gets_mem := FILTER (fun '(x, v) => bool_decide (ALOOKUP (gets_mem d2) x = Some v))
                        (gets_mem d1);
     instrs_mem := bm_inter_eq (instrs_mem d1) (instrs_mem d2);
     loads_mem := bm_inter_eq (loads_mem d1) (loads_mem d2) |}.

Section Cse3.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "word_cse_def" *)
Fixpoint word_cse (data : knowledge) (p : prog a) : knowledge * prog a :=
  match p with
  | Move r rs =>
      let data' := canonicalMoveRegs data rs in
      (data', Move r rs)
  | Inst i =>
      let '(data', p) := word_cseInst data i in (data', p)
  | Get r x =>
      let data := invalidate_data data r in
      match ALOOKUP (gets_mem data) x with
      | None =>
          if EVEN r then (data, Get r x)
          else ({| to_canonical := insert r r (to_canonical data);
                   to_latest := insert r r (to_latest data);
                   gets_mem := (x, r) :: gets_mem data;
                   instrs_mem := instrs_mem data; loads_mem := loads_mem data |},
                Get r x)
      | Some k =>
          if EVEN r then (data, Move 1 [(r, lookup_any k (to_latest data) k)])
          else ({| to_canonical := insert r k (to_canonical data);
                   to_latest := insert k r (to_latest data);
                   gets_mem := gets_mem data;
                   instrs_mem := instrs_mem data; loads_mem := loads_mem data |},
                Move 1 [(r, lookup_any k (to_latest data) k)])
      end
  | Set_ x e =>
      if decide (x = CurrHeap) then (empty_data, Set_ x e)
      else
        let new_gets_mem := FILTER (fun '(m, n) => negb (bool_decide (m = x))) (gets_mem data) in
        match dest_Var e with
        | None => (set_gets_mem data new_gets_mem, Set_ x e)
        | Some v =>
            if EVEN v then (set_gets_mem data new_gets_mem, Set_ x e)
            else ({| to_canonical := insert v (lookup_any v (to_canonical data) v)
                                            (to_canonical data);
                     to_latest := to_latest data;
                     gets_mem := (x, canonicalRegs data v) :: new_gets_mem;
                     instrs_mem := instrs_mem data; loads_mem := loads_mem data |},
                  Set_ x e)
        end
  | MustTerminate p =>
      let '(data', p') := word_cse data p in (data', MustTerminate p')
  | Call ret dest args handler => (empty_data, Call ret dest args handler)
  | Seq p1 p2 =>
      let '(data1, p1') := word_cse data p1 in
      let '(data2, p2') := word_cse data1 p2 in
      (data2, Seq p1' p2')
  | If c r1 r2 p1 p2 =>
      let '(data1, p1') := word_cse data p1 in
      let '(data2, p2') := word_cse data p2 in
      (merge_data data1 data2, If c r1 r2 p1' p2')
  | OpCurrHeap b r1 r2 =>
      let data := invalidate_data data r1 in
      if EVEN r2 || (r2 =? r1) then (data, OpCurrHeap b r1 r2)
      else
        let r2' := canonicalRegs' r1 data r2 in
        let pL := OpCurrHeapToNumList b r2' in
        add_to_data_aux (register_read data r2') r1 pL (OpCurrHeap b r1 r2)
  | LocValue r l =>
      let data := invalidate_data data r in
      add_to_data_aux data r [48; l] (LocValue r l)
  | Skip => (data, Skip)
  | Store e r => (set_loads_mem data balanced_map.empty, Store e r)
  | Assign r e => (data, Assign r e)
  | Raise r => (data, Raise r)
  | Return r1 r2 => (data, Return r1 r2)
  | Tick => (data, Tick)
  | Alloc r m => (empty_data, Alloc r m)
  | Install p l dp dl m => (empty_data, Install p l dp dl m)
  | CodeBufferWrite r1 r2 => (data, CodeBufferWrite r1 r2)
  | DataBufferWrite r1 r2 => (data, DataBufferWrite r1 r2)
  | FFI s p1 l1 p2 l2 m => (empty_data, FFI s p1 l1 p2 l2 m)
  | StoreConsts r1 r2 r3 r4 payload =>
      let data := invalidate_regs data [r1; r2; r3; r4] in
      (set_loads_mem data balanced_map.empty, StoreConsts r1 r2 r3 r4 payload)
  | ShareInst op r exp =>
      let data := if is_store op then data else invalidate_data data r in
      (data, ShareInst op r exp)
  | Loop names c exit_names =>
      let '(_, c') := word_cse empty_data c in
      (empty_data, Loop names c' exit_names)
  | Break k => (data, Break k)
  | Continue k => (data, Continue k)
  end.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "word_common_subexp_elim_def" *)
Definition word_common_subexp_elim (prog : prog a) : wordLang.prog a :=
  let '(_, new_prog) := word_cse empty_data prog in new_prog.

End Cse3.

(** ** Tests (HOL's [local] test theorems, at width 64) *)

Section Tests.

(** HOL's test-only [Seqs] (deleted by HOL after the tests). *)
Local Fixpoint Seqs (l : list (prog 64)) : prog 64 :=
  match l with
  | [] => Skip
  | [x] => x
  | x :: ((_ :: _) as t) => Seq x (Seqs t)
  end.

Local Abbreviation w := (n2w : N -> word 64).

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_latest_name_used" *)
Theorem test_latest_name_used :
  word_common_subexp_elim
    (Seqs [Inst (asm.Const 1 (w 0));
           Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
           Inst (Arith (Binop asm.Add 9 1 (Reg 1)));
           Inst (Arith (Binop asm.Add 11 1 (Reg 1)));
           Inst (Arith (Binop asm.Add 13 1 (Reg 1)))])
  =
    Seqs [Inst (asm.Const 1 (w 0));
          Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
          Move 0 [(9, 7)];
          Move 0 [(11, 9)];
          Move 0 [(13, 11)]].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_get_set" *)
Theorem test_get_set :
  word_common_subexp_elim
    (Seqs [Get 1 NextFree;
           Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
           Set_ NextFree (Var 7);
           Get 9 NextFree;
           Inst (Arith (Binop asm.Add 11 1 (Reg 1)));
           Get 33 NextFree;
           Get 35 NextFree;
           Get 37 NextFree])
  =
    Seqs [Get 1 NextFree;
          Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
          Set_ NextFree (Var 7);
          Move 1 [(9, 7)];
          Move 0 [(11, 9)];
          Move 1 [(33, 11)];
          Move 1 [(35, 33)];
          Move 1 [(37, 35)]].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_pattern_match_and_cons" *)
Theorem test_pattern_match_and_cons :
  word_common_subexp_elim
    (Seqs [Inst (Arith (asm.Shift Lsr 301 297 (Imm (w 9))));
           OpCurrHeap asm.Add 305 301;
           Inst (Mem asm.Load 309 (Addr 305 (w 8)));
           Move 0 [(313, 297)];
           Inst (Arith (asm.Shift Lsr 317 313 (Imm (w 9))));
           OpCurrHeap asm.Add 321 317;
           Inst (Mem asm.Load 325 (Addr 321 (w 16)));
           Move 0 [(329, 313)];
           Inst (Arith (asm.Shift Lsr 333 329 (Imm (w 9))));
           OpCurrHeap asm.Add 337 333;
           Inst (Mem asm.Load 341 (Addr 337 (w 24)));
           Get 345 NextFree;
           Inst (asm.Const 349 (w 0x200000003));
           Move 0 [(353, 345)];
           Inst (Mem asm.Store 349 (Addr 353 (w 0)));
           Move 0 [(357, 353)];
           Inst (Mem asm.Store 325 (Addr 357 (w 8)));
           Move 0 [(361, 357)];
           Inst (Mem asm.Store 341 (Addr 361 (w 16)));
           Move 0 [(365, 361)];
           OpCurrHeap asm.Sub 369 365;
           Inst (Arith (asm.Shift Lsl 373 369 (Imm (w 9))));
           Inst (Arith (Binop Or 377 373 (Imm (w 5))));
           Move 0 [(381, 365)];
           Inst (Arith (Binop asm.Add 385 381 (Imm (w 24))));
           Set_ NextFree (Var 385);
           Get 389 NextFree;
           Inst (asm.Const 393 (w 0x200000003));
           Move 0 [(397, 389)];
           Inst (Mem asm.Store 393 (Addr 397 (w 0)));
           Move 0 [(401, 397)];
           Inst (Mem asm.Store 309 (Addr 401 (w 8)));
           Move 0 [(405, 401)];
           Inst (Mem asm.Store 377 (Addr 405 (w 16)));
           Move 0 [(409, 405)];
           OpCurrHeap asm.Sub 413 409;
           Inst (Arith (asm.Shift Lsl 417 413 (Imm (w 9))));
           Inst (Arith (Binop Or 421 417 (Imm (w 5))));
           Move 0 [(425, 409)];
           Inst (Arith (Binop asm.Add 429 425 (Imm (w 24))));
           Set_ NextFree (Var 429);
           Move 0 [(2, 421)]; Return 273 [2]])
  =
    Seqs [Inst (Arith (asm.Shift Lsr 301 297 (Imm (w 9))));
          OpCurrHeap asm.Add 305 301;
          Inst (Mem asm.Load 309 (Addr 305 (w 8)));
          Move 0 [(313, 297)];
          Move 0 [(317, 301)];
          Move 0 [(321, 305)];
          Inst (Mem asm.Load 325 (Addr 321 (w 16)));
          Move 0 [(329, 313)];
          Move 0 [(333, 317)];
          Move 0 [(337, 321)];
          Inst (Mem asm.Load 341 (Addr 337 (w 24)));
          Get 345 NextFree;
          Inst (asm.Const 349 (w 0x200000003));
          Move 0 [(353, 345)];
          Inst (Mem asm.Store 349 (Addr 353 (w 0)));
          Move 0 [(357, 353)];
          Inst (Mem asm.Store 325 (Addr 357 (w 8)));
          Move 0 [(361, 357)];
          Inst (Mem asm.Store 341 (Addr 361 (w 16)));
          Move 0 [(365, 361)];
          OpCurrHeap asm.Sub 369 365;
          Inst (Arith (asm.Shift Lsl 373 369 (Imm (w 9))));
          Inst (Arith (Binop Or 377 373 (Imm (w 5))));
          Move 0 [(381, 365)];
          Inst (Arith (Binop asm.Add 385 381 (Imm (w 24))));
          Set_ NextFree (Var 385);
          Move 1 [(389, 385)];
          Inst (asm.Const 393 (w 0x200000003));
          Move 0 [(397, 389)];
          Inst (Mem asm.Store 393 (Addr 397 (w 0)));
          Move 0 [(401, 397)];
          Inst (Mem asm.Store 309 (Addr 401 (w 8)));
          Move 0 [(405, 401)];
          Inst (Mem asm.Store 377 (Addr 405 (w 16)));
          Move 0 [(409, 405)];
          OpCurrHeap asm.Sub 413 409;
          Inst (Arith (asm.Shift Lsl 417 413 (Imm (w 9))));
          Inst (Arith (Binop Or 421 417 (Imm (w 5))));
          Move 0 [(425, 409)];
          Inst (Arith (Binop asm.Add 429 425 (Imm (w 24))));
          Set_ NextFree (Var 429);
          Move 0 [(2, 421)];
          Return 273 [2]].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_load_cse" *)
Theorem test_load_cse :
  word_common_subexp_elim
    (Seqs [Inst (Mem asm.Load 9 (Addr 7 (w 0)));
           Inst (Arith (asm.Shift Lsr 11 9 (Imm (w 29))));
           Inst (Mem asm.Load 13 (Addr 7 (w 0)));
           Inst (Arith (asm.Shift Lsr 15 13 (Imm (w 29))));
           Inst (Mem Load8 17 (Addr 7 (w 0)));
           Inst (Mem asm.Store 15 (Addr 7 (w 0)));
           Inst (Mem asm.Load 19 (Addr 7 (w 0)))])
  =
    Seqs [Inst (Mem asm.Load 9 (Addr 7 (w 0)));
          Inst (Arith (asm.Shift Lsr 11 9 (Imm (w 29))));
          Move 0 [(13, 9)];
          Move 0 [(15, 11)];
          Inst (Mem Load8 17 (Addr 7 (w 0)));
          Inst (Mem asm.Store 15 (Addr 7 (w 0)));
          Inst (Mem asm.Load 19 (Addr 7 (w 0)))].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_set_currheap" *)
Theorem test_set_currheap :
  word_common_subexp_elim
    (Seqs [Inst (asm.Const 1 (w 0));
           Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
           OpCurrHeap asm.Add 3 1;
           Set_ CurrHeap (Var 7);
           Inst (Arith (Binop asm.Add 9 1 (Reg 1)));
           OpCurrHeap asm.Add 5 1])
  =
    Seqs [Inst (asm.Const 1 (w 0));
          Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
          OpCurrHeap asm.Add 3 1;
          Set_ CurrHeap (Var 7);
          Inst (Arith (Binop asm.Add 9 1 (Reg 1)));
          OpCurrHeap asm.Add 5 1].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_locvalue" *)
Theorem test_locvalue :
  word_common_subexp_elim (Seqs [LocValue 7 100; LocValue 9 100])
  = Seqs [LocValue 7 100; Move 0 [(9, 7)]].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_multi_output_invalidation" *)
Theorem test_multi_output_invalidation :
  word_common_subexp_elim
    (Seqs [Inst (Arith (Binop asm.Add 9 1 (Reg 1)));
           Inst (Arith (LongMul 7 9 3 5));
           Inst (Arith (Binop asm.Add 11 1 (Reg 1)))])
  =
    Seqs [Inst (Arith (Binop asm.Add 9 1 (Reg 1)));
          Inst (Arith (LongMul 7 9 3 5));
          Inst (Arith (Binop asm.Add 11 1 (Reg 1)))].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_self_read_not_cse" *)
Theorem test_self_read_not_cse :
  word_common_subexp_elim
    (Seqs [Inst (Arith (Binop asm.Add 7 7 (Imm (w 1))));
           Inst (Arith (Binop asm.Add 9 7 (Imm (w 1))))])
  =
    Seqs [Inst (Arith (Binop asm.Add 7 7 (Imm (w 1))));
          Inst (Arith (Binop asm.Add 9 7 (Imm (w 1))))].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_if_merge" *)
Theorem test_if_merge :
  word_common_subexp_elim
    (Seqs [Inst (asm.Const 1 (w 0));
           Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
           If Equal 1 (Imm (w 0))
              (Inst (Arith (Binop asm.Add 9 1 (Reg 1))))
              (Move 0 [(11, 7)]);
           Inst (Arith (Binop asm.Add 13 1 (Reg 1)))])
  =
    Seqs [Inst (asm.Const 1 (w 0));
          Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
          If Equal 1 (Imm (w 0)) (Move 0 [(9, 7)]) (Move 0 [(11, 7)]);
          Move 0 [(13, 7)]].
Proof. vm_compute; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/word_cseScript.sml" "test_if_merge_clobber" *)
Theorem test_if_merge_clobber :
  word_common_subexp_elim
    (Seqs [Inst (asm.Const 1 (w 0));
           Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
           If Equal 1 (Imm (w 0)) (Move 0 [(7, 3)]) Skip;
           Inst (Arith (Binop asm.Add 9 1 (Reg 1)))])
  =
    Seqs [Inst (asm.Const 1 (w 0));
          Inst (Arith (Binop asm.Add 7 1 (Reg 1)));
          If Equal 1 (Imm (w 0)) (Move 0 [(7, 3)]) Skip;
          Inst (Arith (Binop asm.Add 9 1 (Reg 1)))].
Proof. vm_compute; reflexivity. Qed.

End Tests.
