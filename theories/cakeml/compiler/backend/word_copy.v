(** * CakeML [word_copy]: copy propagation on wordLang programs

    Port of [cakeml/compiler/backend/word_copyScript.sml].

    [copy_prop_inst]'s final HOL clause [copy_prop_inst _ cs = ARB] is
    unreachable (the earlier clauses cover every [inst]; Rocq rejects the
    redundant clause), so it is omitted.  HOL's record updates are written
    as record constructions. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.finite_maps Require Import sptree alist.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang.
From Galette.cakeml.compiler.backend.reg_alloc Require reg_alloc.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "copy_state" *)
Record copy_state : Type := {
  to_eq : num_map N;
  from_eq : num_map N;
  store_to_eq : list (store_name * N);
  next : N
}.

#[global] Instance copy_state_inhabited : Inhabited copy_state :=
  {| to_eq := LN; from_eq := LN; store_to_eq := []; next := 0 |}.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "empty_eq_def" *)
Definition empty_eq : copy_state :=
  {| to_eq := LN; from_eq := LN; store_to_eq := []; next := 0 |}.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "lookup_eq_def" *)
Definition lookup_eq (cs : copy_state) (v : N) : N :=
  match lookup v (to_eq cs) with
  | None => v
  | Some c =>
      match lookup c (from_eq cs) with
      | None => v
      | Some v' => v'
      end
  end.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "lookup_eq_imm_def" *)
Definition lookup_eq_imm {a} (cs : copy_state) (vi : reg_imm a) : reg_imm a :=
  match vi with
  | Reg v => Reg (lookup_eq cs v)
  | _ => vi
  end.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "remove_eq_def" *)
Definition remove_eq (cs : copy_state) (v : N) : copy_state :=
  match lookup v (to_eq cs) with
  | None => cs
  | Some c => empty_eq
  end.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "remove_eqs_def" *)
Fixpoint remove_eqs (cs : copy_state) (l : list N) : copy_state :=
  match l with
  | [] => cs
  | v :: vs => remove_eqs (remove_eq cs v) vs
  end.

Section Copy.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_inst_def" *)
Definition copy_prop_inst (i : inst a) (cs : copy_state) : prog a * copy_state :=
  match i with
  | asm.Skip => (Skip, cs)
  | asm.Const reg w => (Inst (asm.Const reg w), remove_eq cs reg)
  | Arith (Binop bop r1 r2 ri) =>
      let cs' := remove_eq cs r1 in
      let r2' := lookup_eq cs r2 in
      let ri' := lookup_eq_imm cs ri in
      let ri'' := if decide (ri' = Reg r1) then ri else ri' in
      (Inst (Arith (Binop bop r1 r2' ri'')), cs')
  | Arith (asm.Shift shift r1 r2 n) =>
      let cs' := remove_eq cs r1 in
      let r2' := lookup_eq cs r2 in
      let n' := lookup_eq_imm cs n in
      let n'' := if decide (n' = Reg r1) then n else n' in
      (Inst (Arith (asm.Shift shift r1 r2' n'')), cs')
  | Arith (Div r1 r2 r3) =>
      let r2' := lookup_eq cs r2 in
      let r3' := lookup_eq cs r3 in
      (Inst (Arith (Div r1 r2' r3')), remove_eq cs r1)
  | Arith (AddCarry r1 r2 r3 r4) =>
      let cs' := remove_eqs cs [r1; r4] in
      let r2' := lookup_eq cs r2 in
      let r3' := lookup_eq cs r3 in
      let r3'' := if decide (r3' = r1) then r3 else r3' in
      (Inst (Arith (AddCarry r1 r2' r3'' r4)), cs')
  | Arith (AddOverflow r1 r2 r3 r4) =>
      let cs' := remove_eqs cs [r1; r4] in
      let r2' := lookup_eq cs r2 in
      let r3' := lookup_eq cs r3 in
      let r3'' := if decide (r3' = r1) then r3 else r3' in
      (Inst (Arith (AddOverflow r1 r2' r3'' r4)), cs')
  | Arith (SubOverflow r1 r2 r3 r4) =>
      let cs' := remove_eqs cs [r1; r4] in
      let r2' := lookup_eq cs r2 in
      let r3' := lookup_eq cs r3 in
      let r3'' := if decide (r3' = r1) then r3 else r3' in
      (Inst (Arith (SubOverflow r1 r2' r3'' r4)), cs')
  | Arith (LongMul r1 r2 r3 r4) =>
      (Inst (Arith (LongMul r1 r2 r3 r4)), remove_eqs cs [r1; r2])
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      let r3' := lookup_eq cs r3 in
      let r4' := lookup_eq cs r4 in
      let r5' := lookup_eq cs r5 in
      (Inst (Arith (LongDiv r1 r2 r3' r4' r5')), remove_eqs cs [r2; r1])
  | Mem asm.Load r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      (Inst (Mem asm.Load r (Addr a' w)), remove_eq cs r)
  | Mem asm.Store r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      let r' := lookup_eq cs r in
      (Inst (Mem asm.Store r' (Addr a' w)), cs)
  | Mem Load8 r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      (Inst (Mem Load8 r (Addr a' w)), remove_eq cs r)
  | Mem Store8 r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      let r' := lookup_eq cs r in
      (Inst (Mem Store8 r' (Addr a' w)), cs)
  | Mem Load16 r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      (Inst (Mem Load16 r (Addr a' w)), remove_eq cs r)
  | Mem Store16 r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      let r' := lookup_eq cs r in
      (Inst (Mem Store16 r' (Addr a' w)), cs)
  | Mem Load32 r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      (Inst (Mem Load32 r (Addr a' w)), remove_eq cs r)
  | Mem Store32 r (Addr a0 w) =>
      let a' := lookup_eq cs a0 in
      let r' := lookup_eq cs r in
      (Inst (Mem Store32 r' (Addr a' w)), cs)
  | FP (FPLess r f1 f2) => (Inst (FP (FPLess r f1 f2)), remove_eq cs r)
  | FP (FPLessEqual r f1 f2) => (Inst (FP (FPLessEqual r f1 f2)), remove_eq cs r)
  | FP (FPEqual r f1 f2) => (Inst (FP (FPEqual r f1 f2)), remove_eq cs r)
  | FP (FPMovToReg r1 r2 d) => (Inst (FP (FPMovToReg r1 r2 d)), remove_eqs cs [r1; r2])
  | FP (FPMovFromReg d r1 r2) =>
      let r1' := lookup_eq cs r1 in
      let r2' := lookup_eq cs r2 in
      let '(r1'', r2'') := if decide (r1' = r2') then (r1, r2) else (r1', r2') in
      (Inst (FP (FPMovFromReg d r1'' r2'')), cs)
  | FP x => (Inst (FP x), cs)
  end.

End Copy.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "set_eq_def" *)
Definition set_eq (cs : copy_state) (x y : N) : copy_state :=
  if reg_alloc.is_alloc_var x && reg_alloc.is_alloc_var y then
    match match lookup y (to_eq cs) with
          | None => None
          | Some c => match lookup c (from_eq cs) with None => None | Some _ => Some c end
          end with
    | None =>
        {| to_eq := insert x (next cs) (insert y (next cs) (to_eq cs));
           from_eq := insert (next cs) x (from_eq cs);
           store_to_eq := store_to_eq cs;
           next := next cs + 1 |}
    | Some c =>
        {| to_eq := insert x c (to_eq cs);
           from_eq := insert c x (from_eq cs);
           store_to_eq := store_to_eq cs;
           next := next cs |}
    end
  else cs.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "set_store_eq_def" *)
Definition set_store_eq (cs : copy_state) (s : store_name) (y : N) : copy_state :=
  if reg_alloc.is_alloc_var y then
    match match lookup y (to_eq cs) with
          | None => None
          | Some c => match lookup c (from_eq cs) with None => None | Some _ => Some c end
          end with
    | None =>
        {| to_eq := insert y (next cs) (to_eq cs);
           from_eq := insert (next cs) y (from_eq cs);
           store_to_eq := (s, next cs) :: store_to_eq cs;
           next := next cs + 1 |}
    | Some c =>
        {| to_eq := to_eq cs;
           from_eq := from_eq cs;
           store_to_eq := (s, c) :: store_to_eq cs;
           next := next cs |}
    end
  else empty_eq.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "lookup_store_eq_def" *)
Definition lookup_store_eq (cs : copy_state) (s : store_name) : option N :=
  match ALOOKUP (store_to_eq cs) s with
  | None => None
  | Some c =>
      match lookup c (from_eq cs) with
      | None => None
      | Some v' => Some v'
      end
  end.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "merge_eqs_def" *)
Definition merge_eqs (cs ds : copy_state) : copy_state :=
  {| to_eq := inter_eq (to_eq cs) (to_eq ds);
     from_eq := inter_eq (from_eq cs) (from_eq ds);
     store_to_eq :=
       FILTER (fun '(s, c) => bool_decide (ALOOKUP (store_to_eq cs) s = Some c) &&
                              bool_decide (ALOOKUP (store_to_eq ds) s = Some c))
              (store_to_eq cs);
     next := MAX (next cs) (next ds) |}.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_move_def" *)
Fixpoint copy_prop_move (l : list (N * N)) (cs : copy_state) : list (N * N) * copy_state :=
  match l with
  | [] => ([], cs)
  | (x, y) :: xs =>
      let y' := lookup_eq cs y in
      let '(ms, cs') := copy_prop_move xs cs in
      let cs'' := set_eq (remove_eq cs' x) x y in
      ((x, y') :: ms, cs'')
  end.

Section CopyProg.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_share_def" *)
Definition copy_prop_share (e : exp a) (cs : copy_state) : exp a :=
  match e with
  | Var r => Var (lookup_eq cs r)
  | Op asm.Add [Var r; Const c] => Op asm.Add [Var (lookup_eq cs r); Const c]
  | _ => e
  end.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_prog_def" *)
Fixpoint copy_prop_prog (p : prog a) (cs : copy_state) : prog a * copy_state :=
  match p with
  | Skip => (Skip, cs)
  | Move pri xs =>
      let tt := MAP FST xs in
      let ss := MAP SND xs in
      if EVERY (fun t => negb (MEM t ss)) tt then
        let '(xs', cs') := copy_prop_move xs cs in
        (Move pri xs', cs')
      else (Move pri xs, empty_eq)
  | Inst i => copy_prop_inst i cs
  | Return v1 v2 =>
      let v1' := lookup_eq cs v1 in
      let v2' := MAP (lookup_eq cs) v2 in
      (Return v1' v2', cs)
  | Raise v => let v' := lookup_eq cs v in (Raise v', cs)
  | OpCurrHeap b dst src =>
      let src' := lookup_eq cs src in
      let src'' := if decide (src' = dst) then src else src' in
      (OpCurrHeap b dst src'', remove_eq cs dst)
  | Tick => (Tick, cs)
  | MustTerminate p1 =>
      let '(p1', cs') := copy_prop_prog p1 cs in (MustTerminate p1', cs')
  | Seq p1 p2 =>
      let '(q1, cs') := copy_prop_prog p1 cs in
      let '(q2, cs'') := copy_prop_prog p2 cs' in
      (Seq q1 q2, cs'')
  | If cmp r ri p1 p2 =>
      let r' := lookup_eq cs r in
      let ri' := lookup_eq_imm cs ri in
      let '(q1, cs') := copy_prop_prog p1 cs in
      let '(q2, cs'') := copy_prop_prog p2 cs in
      (If cmp r' ri' q1 q2, merge_eqs cs' cs'')
  | Set_ name exp =>
      match exp with
      | Var n =>
          let n' := lookup_eq cs n in
          (Set_ name (Var n'), set_store_eq cs name n)
      | _ => (Set_ name exp, empty_eq)
      end
  | Get n name =>
      match lookup_store_eq cs name with
      | None => (Get n name, set_store_eq (remove_eq cs n) name n)
      | Some v =>
          if negb (bool_decide (v = n)) then
            let '(xs', cs') := copy_prop_move [(n, v)] cs in
            (Move 0 xs', cs')
          else (Skip, cs)
      end
  | Call ret dest args handler => (Call ret dest args handler, empty_eq)
  | Alloc r live => (Alloc r live, empty_eq)
  | StoreConsts a0 b c d ws => (StoreConsts a0 b c d ws, remove_eqs cs [a0; b; c; d])
  | LocValue r l1 => (LocValue r l1, remove_eq cs r)
  | Install r1 r2 r3 r4 live => (Install r1 r2 r3 r4 live, empty_eq)
  | CodeBufferWrite r1 r2 =>
      let r1' := lookup_eq cs r1 in
      let r2' := lookup_eq cs r2 in
      (CodeBufferWrite r1' r2', cs)
  | DataBufferWrite r1 r2 =>
      let r1' := lookup_eq cs r1 in
      let r2' := lookup_eq cs r2 in
      (DataBufferWrite r1' r2', cs)
  | FFI i r1 r2 r3 r4 live => (FFI i r1 r2 r3 r4 live, empty_eq)
  | ShareInst op v exp =>
      let exp' := copy_prop_share exp cs in
      (ShareInst op v exp', remove_eq cs v)
  | Loop names c exit_names =>
      let '(c', _) := copy_prop_prog c empty_eq in
      (Loop names c' exit_names, empty_eq)
  | Break k => (Break k, cs)
  | Continue k => (Continue k, cs)
  | prog => (prog, empty_eq)
  end.

(*! HOL "cakeml/compiler/backend/word_copyScript.sml" "copy_prop_def" *)
Definition copy_prop (e : prog a) : prog a := FST (copy_prop_prog e empty_eq).

End CopyProg.
