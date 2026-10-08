(** * CakeML [word_alloc]: SSA renaming and register allocation for wordLang

    A port of the definitions of [compiler/backend/word_allocScript.sml].
    The theorems [get_writes_pmatch], [get_prefs_pmatch],
    [get_forced_pmatch] (the [pmatch] restatements) and [total_colour_alt]
    are not ported.

    Conventions:
    - HOL tuples nest to the right ([(prog, ssa, na)] is
      [(prog, (ssa, na))]); HOL's [Move0]/[Move1] overloads are
      [Move 0]/[Move 1].
    - Tests [p = Skip] on programs and [ls = []] on lists are written as
      [match]es (the same function: equality with a nullary constructor).
    - HOL's catch-all clauses are [_] branches after HOL's explicit ones
      (first-match semantics).
    - Constructors: wordLang's [Skip], [Seq], [Set_], [Inst], [Call], ...
      are unqualified; ASM's are [asm.Skip], [asm.Const], [asm.Shift],
      [asm.Load], [asm.Store]; the clash-tree constructors are [Delta],
      [reg_alloc.Set_], [reg_alloc.Seq], [reg_alloc.Branch].
    - [listTheory.oEL] is not in [list.v] yet; it is defined locally
      (untagged), as in [loop_live.v].
    - This script's [numset_list_insert] (non-tail-recursive) shadows
      [linear_scan$numset_list_insert]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc linear_scan.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang.
Open Scope N_scope.

(** HOL [oEL] ([listScript]; Galette-local until ported there). *)
#[local] Fixpoint oEL {A} (n : N) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if decide (n = 0) then Some x else oEL (n - 1) xs
  end.

Definition is_Skip {a} (p : prog a) : bool := match p with Skip => true | _ => false end.

(** ** SSA form *)

Section SSA.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "apply_nummap_key_def" *)
Definition apply_nummap_key {A} (f : N -> N) (names : num_map A) : num_map A :=
  fromAList (MAP (fun '(x, y) => (f x, y)) (toAList names)).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "apply_nummaps_key_def" *)
Definition apply_nummaps_key {A B} (f : N -> N) (names : num_map A * num_map B)
    : num_map A * num_map B :=
  (fromAList (MAP (fun '(x, y) => (f x, y)) (toAList (FST names))),
   fromAList (MAP (fun '(x, y) => (f x, y)) (toAList (SND names)))).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "option_lookup_def" *)
Definition option_lookup (t : num_map N) (v : N) : N :=
  match lookup v t with None => 0 | Some x => x end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "even_list_def" *)
Definition even_list : N -> list N := GENLIST (fun x => 2 * x).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "next_var_rename_def" *)
Definition next_var_rename (v : N) (ssa : num_map N) (na : N) : N * (num_map N * N) :=
  (na, (insert v na ssa, na + 4)).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "list_next_var_rename_def" *)
Fixpoint list_next_var_rename (l : list N) (ssa : num_map N) (na : N)
    : list N * (num_map N * N) :=
  match l with
  | [] => ([], (ssa, na))
  | x :: xs =>
      let '(y, (ssa', na')) := next_var_rename x ssa na in
      let '(ys, (ssa'', na'')) := list_next_var_rename xs ssa' na' in
      (y :: ys, (ssa'', na''))
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "fake_move_def" *)
Definition fake_move (v : N) : prog a := Inst (asm.Const v (n2w 0)).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "merge_moves_def" *)
Fixpoint merge_moves (l : list N) (ssa_L ssa_R : num_map N) (na : N)
    : list (N * N) * (list (N * N) * (N * (num_map N * num_map N))) :=
  match l with
  | [] => ([], ([], (na, (ssa_L, ssa_R))))
  | x :: xs =>
      let '(seqL, (seqR, (na', (ssa_L', ssa_R')))) := merge_moves xs ssa_L ssa_R na in
      let optLx := lookup x ssa_L' in
      let optLy := lookup x ssa_R' in
      match optLx, optLy with
      | Some Lx, Some Ly =>
          if Lx =? Ly then (seqL, (seqR, (na', (ssa_L', ssa_R'))))
          else
            let Lmove := (na', Lx) in
            let Rmove := (na', Ly) in
            (Lmove :: seqL, (Rmove :: seqR, (na' + 4, (insert x na' ssa_L', insert x na' ssa_R'))))
      | _, _ => (seqL, (seqR, (na', (ssa_L', ssa_R'))))
      end
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "priority_def" *)
Definition priority (o_ : option (unit + unit)) (b : bool) : N :=
  match o_ with
  | None => 1
  | Some (inl tt) => if b then 2 else 1
  | Some (inr tt) => if b then 1 else 2
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "fake_moves_def" *)
Fixpoint fake_moves (prio : option (unit + unit)) (l : list N) (ssa_L ssa_R : num_map N) (na : N)
    : prog a * (prog a * (N * (num_map N * num_map N))) :=
  match l with
  | [] => (Skip, (Skip, (na, (ssa_L, ssa_R))))
  | x :: xs =>
      let '(seqL, (seqR, (na', (ssa_L', ssa_R')))) := fake_moves prio xs ssa_L ssa_R na in
      let optLx := lookup x ssa_L' in
      let optLy := lookup x ssa_R' in
      match optLx, optLy with
      | None, Some Ly =>
          let Lmove := Seq seqL (fake_move na') in
          let Rmove := Seq seqR (Move (priority prio false) [(na', Ly)]) in
          (Lmove, (Rmove, (na' + 4, (insert x na' ssa_L', insert x na' ssa_R'))))
      | Some Lx, None =>
          let Lmove := Seq seqL (Move (priority prio true) [(na', Lx)]) in
          let Rmove := Seq seqR (fake_move na') in
          (Lmove, (Rmove, (na' + 4, (insert x na' ssa_L', insert x na' ssa_R'))))
      | _, _ => (seqL, (seqR, (na', (ssa_L', ssa_R'))))
      end
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "fix_inconsistencies_def" *)
Definition fix_inconsistencies (prio : option (unit + unit)) (ssa_L ssa_R : num_map N) (na : N)
    : prog a * (prog a * (N * num_map N)) :=
  let var_union := MAP FST (toAList (union ssa_L ssa_R)) in
  let '(Lmov, (Rmov, (na', (ssa_L', ssa_R')))) := merge_moves var_union ssa_L ssa_R na in
  let '(Lseq, (Rseq, (na'', (ssa_L'', ssa_R'')))) := fake_moves prio var_union ssa_L' ssa_R' na' in
  (Seq (Move (priority prio true) Lmov) Lseq,
   (Seq (Move (priority prio false) Rmov) Rseq, (na'', ssa_L''))).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "ssa_cc_trans_inst_def" *)
Definition ssa_cc_trans_inst (i : inst a) (ssa : num_map N) (na : N)
    : prog a * (num_map N * N) :=
  match i with
  | asm.Skip => (Skip, (ssa, na))
  | asm.Const reg w =>
      let '(reg', (ssa', na')) := next_var_rename reg ssa na in
      (Inst (asm.Const reg' w), (ssa', na'))
  | Arith (Binop bop r1 r2 ri) =>
      match ri with
      | Reg r3 =>
          let r3' := option_lookup ssa r3 in
          let r2' := option_lookup ssa r2 in
          let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
          (Inst (Arith (Binop bop r1' r2' (Reg r3'))), (ssa', na'))
      | _ =>
          let r2' := option_lookup ssa r2 in
          let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
          (Inst (Arith (Binop bop r1' r2' ri)), (ssa', na'))
      end
  | Arith (asm.Shift shift r1 r2 ri) =>
      match ri with
      | Reg r3 =>
          let r3' := option_lookup ssa r3 in
          let r2' := option_lookup ssa r2 in
          let mov_in := Move 1 [(8, r3')] in
          let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
          (Seq mov_in (Inst (Arith (asm.Shift shift r1' r2' (Reg 8)))), (ssa', na'))
      | _ =>
          let r2' := option_lookup ssa r2 in
          let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
          (Inst (Arith (asm.Shift shift r1' r2' ri)), (ssa', na'))
      end
  | Arith (Div r1 r2 r3) =>
      let r2' := option_lookup ssa r2 in
      let r3' := option_lookup ssa r3 in
      let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
      (Inst (Arith (Div r1' r2' r3')), (ssa', na'))
  | Arith (AddCarry r1 r2 r3 r4) =>
      let r2' := option_lookup ssa r2 in
      let r3' := option_lookup ssa r3 in
      let r4' := option_lookup ssa r4 in
      let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
      let mov_in := Move 1 [(0, r4')] in
      let '(r4'', (ssa'', na'')) := next_var_rename r4 ssa' na' in
      let mov_out := Move 1 [(r4'', 0)] in
      (Seq mov_in (Seq (Inst (Arith (AddCarry r1' r2' r3' 0))) mov_out), (ssa'', na''))
  | Arith (AddOverflow r1 r2 r3 r4) =>
      let r2' := option_lookup ssa r2 in
      let r3' := option_lookup ssa r3 in
      let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
      let '(r4'', (ssa'', na'')) := next_var_rename r4 ssa' na' in
      let mov_out := Move 1 [(r4'', 0)] in
      (Seq (Inst (Arith (AddOverflow r1' r2' r3' 0))) mov_out, (ssa'', na''))
  | Arith (SubOverflow r1 r2 r3 r4) =>
      let r2' := option_lookup ssa r2 in
      let r3' := option_lookup ssa r3 in
      let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
      let '(r4'', (ssa'', na'')) := next_var_rename r4 ssa' na' in
      let mov_out := Move 1 [(r4'', 0)] in
      (Seq (Inst (Arith (SubOverflow r1' r2' r3' 0))) mov_out, (ssa'', na''))
  | Arith (LongMul r1 r2 r3 r4) =>
      let r3' := option_lookup ssa r3 in
      let r4' := option_lookup ssa r4 in
      let mov_in := Move 1 [(0, r3'); (4, r4')] in
      let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
      let '(r2', (ssa'', na'')) := next_var_rename r2 ssa' na' in
      let mov_out := Move 1 [(r2', 0); (r1', 6)] in
      (Seq mov_in (Seq (Inst (Arith (LongMul 6 0 0 4))) mov_out), (ssa'', na''))
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      let r3' := option_lookup ssa r3 in
      let r4' := option_lookup ssa r4 in
      let r5' := option_lookup ssa r5 in
      let mov_in := Move 1 [(6, r3'); (0, r4')] in
      let '(r2', (ssa', na')) := next_var_rename r2 ssa na in
      let '(r1', (ssa'', na'')) := next_var_rename r1 ssa' na' in
      let mov_out := Move 1 [(r2', 6); (r1', 0)] in
      (Seq mov_in (Seq (Inst (Arith (LongDiv 0 6 6 0 r5'))) mov_out), (ssa'', na''))
  | Mem asm.Load r (Addr a0 w) =>
      let a' := option_lookup ssa a0 in
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (Inst (Mem asm.Load r' (Addr a' w)), (ssa', na'))
  | Mem asm.Store r (Addr a0 w) =>
      let a' := option_lookup ssa a0 in
      let r' := option_lookup ssa r in
      (Inst (Mem asm.Store r' (Addr a' w)), (ssa, na))
  | Mem Load32 r (Addr a0 w) =>
      let a' := option_lookup ssa a0 in
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (Inst (Mem Load32 r' (Addr a' w)), (ssa', na'))
  | Mem Store32 r (Addr a0 w) =>
      let a' := option_lookup ssa a0 in
      let r' := option_lookup ssa r in
      (Inst (Mem Store32 r' (Addr a' w)), (ssa, na))
  | Mem Load8 r (Addr a0 w) =>
      let a' := option_lookup ssa a0 in
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (Inst (Mem Load8 r' (Addr a' w)), (ssa', na'))
  | Mem Store8 r (Addr a0 w) =>
      let a' := option_lookup ssa a0 in
      let r' := option_lookup ssa r in
      (Inst (Mem Store8 r' (Addr a' w)), (ssa, na))
  | FP (FPLess r f1 f2) =>
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (Inst (FP (FPLess r' f1 f2)), (ssa', na'))
  | FP (FPLessEqual r f1 f2) =>
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (Inst (FP (FPLessEqual r' f1 f2)), (ssa', na'))
  | FP (FPEqual r f1 f2) =>
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (Inst (FP (FPEqual r' f1 f2)), (ssa', na'))
  | FP (FPMovToReg r1 r2 d) =>
      if dimindex a =? 64 then
        let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
        (Inst (FP (FPMovToReg r1' r2 d)), (ssa', na'))
      else
        let '(r1', (ssa', na')) := next_var_rename r1 ssa na in
        let '(r2', (ssa'', na'')) := next_var_rename r2 ssa' na' in
        (Inst (FP (FPMovToReg r1' r2' d)), (ssa'', na''))
  | FP (FPMovFromReg d r1 r2) =>
      if dimindex a =? 64 then
        let r1' := option_lookup ssa r1 in
        (Inst (FP (FPMovFromReg d r1' 0)), (ssa, na))
      else
        let r1' := option_lookup ssa r1 in
        let r2' := option_lookup ssa r2 in
        if r1' =? r2' then
          let '(r2'', (ssa', na')) := next_var_rename r2 ssa na in
          let mov_in := Move 0 [(r2'', r2')] in
          (Seq mov_in (Inst (FP (FPMovFromReg d r1' r2''))), (ssa', na'))
        else (Inst (FP (FPMovFromReg d r1' r2')), (ssa, na))
  | x => (Inst x, (ssa, na))
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "ssa_cc_trans_exp_def" *)
Fixpoint ssa_cc_trans_exp (t : num_map N) (e : exp a) : exp a :=
  match e with
  | Var num => Var (option_lookup t num)
  | Load exp => Load (ssa_cc_trans_exp t exp)
  | Op wop ls => Op wop (MAP (ssa_cc_trans_exp t) ls)
  | Shift sh exp nexp => Shift sh (ssa_cc_trans_exp t exp) (ssa_cc_trans_exp t nexp)
  | expr => expr
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "list_next_var_rename_move_def" *)
Definition list_next_var_rename_move (ssa : num_map N) (n : N) (ls : list N)
    : prog a * (num_map N * N) :=
  let cur_ls := MAP (option_lookup ssa) ls in
  let '(new_ls, (ssa', n')) := list_next_var_rename ls ssa n in
  (Move 0 (ZIP (new_ls, cur_ls)), (ssa', n')).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "force_rename_def" *)
Fixpoint force_rename (l : list (N * N)) (ssa : num_map N) : num_map N :=
  match l with
  | [] => ssa
  | (x, y) :: xs => force_rename xs (insert x y ssa)
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "mk_prio_def" *)
Definition mk_prio (el er : prog a) : option (unit + unit) :=
  if is_Skip el then Some (inl tt)
  else if is_Skip er then Some (inr tt)
  else None.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "ssa_reconcile_def" *)
Definition ssa_reconcile (cur_ssa tgt_ssa : num_map N) (ns : num_set) : prog a :=
  let vars := MAP FST (toAList ns) in
  let moves := FILTER (fun '(a0, b) => negb (a0 =? b))
    (FLAT (MAP (fun v =>
       match lookup v cur_ssa with
       | None => []
       | Some cur_v => [(option_lookup tgt_ssa v, cur_v)]
       end) vars)) in
  match moves with [] => Skip | _ => Move 1 moves end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "loop_setup_def" *)
Definition loop_setup (names exit_names : num_set) (ssa : num_map N) (na : N)
    : prog a * (num_map N * N) :=
  let all_vars_ls := MAP FST (toAList (union names exit_names)) in
  let extend_ls := FILTER (fun v => bool_decide (lookup v ssa = None)) all_vars_ls in
  let refresh_ls := FILTER (fun v => IS_SOME (lookup v ssa)) all_vars_ls in
  let '(fresh_pos_ls, (ssa_ext, na_ext)) := list_next_var_rename extend_ls ssa na in
  let fake_prog := FOLDR Seq Skip (MAP (fun r => fake_move r) fresh_pos_ls) in
  let '(refresh_mov, (ssa_refreshed, na_refreshed)) :=
    list_next_var_rename_move ssa_ext na_ext refresh_ls in
  (Seq fake_prog refresh_mov, (ssa_refreshed, na_refreshed)).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "ssa_cc_trans_def" *)
Fixpoint ssa_cc_trans (p : prog a) (ssa : num_map N) (na : N)
    (lt : list (num_map N * (num_set * num_set))) {struct p} : prog a * (num_map N * N) :=
  match p with
  | Skip => (Skip, (ssa, na))
  | Move pri ls =>
      let ls_1 := MAP FST ls in
      let ls_2 := MAP SND ls in
      let ren_ls2 := MAP (option_lookup ssa) ls_2 in
      let '(ren_ls1, (ssa', na')) := list_next_var_rename ls_1 ssa na in
      let force := FILTER (fun '(x, y) => negb (MEM x ls_1)) (ZIP (ls_2, ren_ls1)) in
      (Move pri (ZIP (ren_ls1, ren_ls2)), (force_rename force ssa', na'))
  | StoreConsts a0 b c d ws =>
      let c1 := option_lookup ssa c in
      let d1 := option_lookup ssa d in
      let '(d2, (ssa', na')) := next_var_rename d ssa na in
      let '(c2, (ssa'', na'')) := next_var_rename c ssa' na' in
      let prog := Seq (Move 1 [(4, c1); (6, d1)])
                    (Seq (StoreConsts 0 2 4 6 ws) (Move 1 [(c2, 4); (d2, 6)])) in
      (prog, (ssa'', na''))
  | Inst i =>
      let '(i', (ssa', na')) := ssa_cc_trans_inst i ssa na in
      (i', (ssa', na'))
  | Assign num exp =>
      let exp' := ssa_cc_trans_exp ssa exp in
      let '(num', (ssa', na')) := next_var_rename num ssa na in
      (Assign num' exp', (ssa', na'))
  | Get num store =>
      let '(num', (ssa', na')) := next_var_rename num ssa na in
      (Get num' store, (ssa', na'))
  | Store exp num =>
      let exp' := ssa_cc_trans_exp ssa exp in
      let num' := option_lookup ssa num in
      (Store exp' num', (ssa, na))
  | Seq s1 s2 =>
      let '(s1', (ssa', na')) := ssa_cc_trans s1 ssa na lt in
      let '(s2', (ssa'', na'')) := ssa_cc_trans s2 ssa' na' lt in
      (Seq s1' s2', (ssa'', na''))
  | MustTerminate s1 =>
      let '(s1', (ssa', na')) := ssa_cc_trans s1 ssa na lt in
      (MustTerminate s1', (ssa', na'))
  | If cmp r1 ri e2 e3 =>
      let r1' := option_lookup ssa r1 in
      let ri' := match ri with Reg r => Reg (option_lookup ssa r) | Imm v => Imm v end in
      let '(e2', (ssa2, na2)) := ssa_cc_trans e2 ssa na lt in
      let '(e3', (ssa3, na3)) := ssa_cc_trans e3 ssa na2 lt in
      let prio := mk_prio e2' e3' in
      let '(e2_cons, (e3_cons, (na_fin, ssa_fin))) := fix_inconsistencies prio ssa2 ssa3 na3 in
      (If cmp r1' ri' (Seq e2' e2_cons) (Seq e3' e3_cons), (ssa_fin, na_fin))
  | Alloc num numset =>
      let all_names := union (FST numset) (SND numset) in
      let ls := MAP FST (toAList all_names) in
      let '(stack_mov, (ssa', na')) := list_next_var_rename_move ssa (na + 2) ls in
      let num' := option_lookup ssa' num in
      let stack_set := apply_nummaps_key (option_lookup ssa') numset in
      let ssa_cut := inter ssa' all_names in
      let '(ret_mov, (ssa'', na'')) := list_next_var_rename_move ssa_cut (na' + 2) ls in
      let prog := Seq stack_mov (Seq (Move 1 [(2, num')]) (Seq (Alloc 2 stack_set) ret_mov)) in
      (prog, (ssa'', na''))
  | Raise num =>
      let num' := option_lookup ssa num in
      let mov := Move 1 [(2, num')] in
      (Seq mov (Raise 2), (ssa, na))
  | OpCurrHeap b dst src =>
      let src' := option_lookup ssa src in
      let '(dst', (ssa', na')) := next_var_rename dst ssa na in
      (OpCurrHeap b dst' src', (ssa', na'))
  | Return num nums =>
      let num' := option_lookup ssa num in
      let nums' := MAP (option_lookup ssa) nums in
      let rets := GENLIST (fun x => 2 * (x + 1)) (LENGTH nums') in
      let mov := Move 0 (ZIP (rets, nums')) in
      (Seq mov (Return num' rets), (ssa, na))
  | Tick => (Tick, (ssa, na))
  | Set_ n exp =>
      let exp' := ssa_cc_trans_exp ssa exp in
      (Set_ n exp', (ssa, na))
  | LocValue r l1 =>
      let '(r', (ssa', na')) := next_var_rename r ssa na in
      (LocValue r' l1, (ssa', na'))
  | Install ptr len dptr dlen numset =>
      let all_names := union (FST numset) (SND numset) in
      let ls := MAP FST (toAList all_names) in
      let '(stack_mov, (ssa', na')) := list_next_var_rename_move ssa (na + 2) ls in
      let stack_set := apply_nummaps_key (option_lookup ssa') numset in
      let ptr' := option_lookup ssa' ptr in
      let len' := option_lookup ssa' len in
      let dptr' := option_lookup ssa' dptr in
      let dlen' := option_lookup ssa' dlen in
      let ssa_cut := inter ssa' all_names in
      let '(ptr'', (ssa'', na'')) := next_var_rename ptr ssa_cut (na' + 2) in
      let '(ret_mov, (ssa''', na''')) := list_next_var_rename_move ssa'' na'' ls in
      let prog := Seq stack_mov
                    (Seq (Move 1 [(2, ptr'); (4, len')])
                    (Seq (Install 2 4 dptr' dlen' stack_set)
                    (Seq (Move 1 [(ptr'', 2)]) ret_mov))) in
      (prog, (ssa''', na'''))
  | CodeBufferWrite r1 r2 =>
      let r1' := option_lookup ssa r1 in
      let r2' := option_lookup ssa r2 in
      (CodeBufferWrite r1' r2', (ssa, na))
  | DataBufferWrite r1 r2 =>
      let r1' := option_lookup ssa r1 in
      let r2' := option_lookup ssa r2 in
      (DataBufferWrite r1' r2', (ssa, na))
  | FFI ffi_index ptr1 len1 ptr2 len2 numset =>
      let all_names := union (FST numset) (SND numset) in
      let ls := MAP FST (toAList all_names) in
      let '(stack_mov, (ssa', na')) := list_next_var_rename_move ssa (na + 2) ls in
      let stack_set := apply_nummaps_key (option_lookup ssa') numset in
      let cptr1 := option_lookup ssa' ptr1 in
      let clen1 := option_lookup ssa' len1 in
      let cptr2 := option_lookup ssa' ptr2 in
      let clen2 := option_lookup ssa' len2 in
      let ssa_cut := inter ssa' all_names in
      let '(ret_mov, (ssa'', na'')) := list_next_var_rename_move ssa_cut (na' + 2) ls in
      let prog := Seq stack_mov
                    (Seq (Move 1 [(2, cptr1); (4, clen1); (6, cptr2); (8, clen2)])
                    (Seq (FFI ffi_index 2 4 6 8 stack_set) ret_mov)) in
      (prog, (ssa'', na''))
  | Call None dest args h =>
      let names := MAP (option_lookup ssa) args in
      let conv_args := GENLIST (fun x => 2 * x) (LENGTH names) in
      let move_args := Move 1 (ZIP (conv_args, names)) in
      let prog := Seq move_args (Call None dest conv_args h) in
      (prog, (ssa, na))
  | Call (Some (ret, (numset, (ret_handler, (l1, l2))))) dest args h =>
      let all_names := union (FST numset) (SND numset) in
      let ls := MAP FST (toAList all_names) in
      let '(stack_mov, (ssa', na')) := list_next_var_rename_move ssa (na + 2) ls in
      let stack_set := apply_nummaps_key (option_lookup ssa') numset in
      let names := MAP (option_lookup ssa) args in
      let conv_args := GENLIST (fun x => 2 * (x + 1)) (LENGTH names) in
      let move_args := Move 1 (ZIP (conv_args, names)) in
      let ssa_cut := inter ssa' all_names in
      let '(ret_mov, (ssa'', na'')) := list_next_var_rename_move ssa_cut (na' + 2) ls in
      let '(ret', (ssa_2_p, na_2_p)) := list_next_var_rename ret ssa'' na'' in
      let '(ren_ret_handler, (ssa_2, na_2)) := ssa_cc_trans ret_handler ssa_2_p na_2_p lt in
      let regs := GENLIST (fun x => 2 * (x + 1)) (LENGTH ret) in
      let mov_ret_handler := Seq ret_mov (Seq (Move 1 (ZIP (ret', regs))) ren_ret_handler) in
      match h with
      | None =>
          let prog := Seq stack_mov (Seq move_args
                        (Call (Some (regs, (stack_set, (mov_ret_handler, (l1, l2)))))
                           dest conv_args None)) in
          (prog, (ssa_2, na_2))
      | Some (n, (h, (l1', l2'))) =>
          let '(n', (ssa_3_p, na_3_p)) := next_var_rename n ssa'' na_2 in
          let '(ren_exc_handler, (ssa_3, na_3)) := ssa_cc_trans h ssa_3_p na_3_p lt in
          let mov_exc_handler := Seq ret_mov (Seq (Move 1 [(n', 2)]) ren_exc_handler) in
          let prio := mk_prio mov_ret_handler mov_exc_handler in
          let '(ret_cons, (exc_cons, (na_fin, ssa_fin))) :=
            fix_inconsistencies prio ssa_2 ssa_3 na_3 in
          let cons_ret_handler := Seq mov_ret_handler ret_cons in
          let cons_exc_handler := Seq mov_exc_handler exc_cons in
          let prog := Seq stack_mov (Seq move_args
                        (Call (Some (regs, (stack_set, (cons_ret_handler, (l1, l2)))))
                           dest conv_args (Some (2, (cons_exc_handler, (l1', l2')))))) in
          (prog, (ssa_fin, na_fin))
      end
  | ShareInst op v exp =>
      let exp' := ssa_cc_trans_exp ssa exp in
      if bool_decide (op = asm.Store \/ op = Store8 \/ op = Store16 \/ op = Store32) then
        (ShareInst op (option_lookup ssa v) exp', (ssa, na))
      else
        let '(v', (ssa', na')) := next_var_rename v ssa na in
        (ShareInst op v' exp', (ssa', na'))
  | Loop names body exit_names =>
      let '(setup_prog, (ssa_refreshed, na_refreshed)) := loop_setup names exit_names ssa na in
      let ssa_names := apply_nummap_key (option_lookup ssa_refreshed) names in
      let ssa_exit := apply_nummap_key (option_lookup ssa_refreshed) exit_names in
      let ssa_body := inter ssa_refreshed names in
      let '(body', (ssa', na')) :=
        ssa_cc_trans body ssa_body na_refreshed ((ssa_refreshed, (names, exit_names)) :: lt) in
      let back_moves := ssa_reconcile ssa' ssa_refreshed names in
      let body_final := if is_Skip back_moves then body' else Seq body' back_moves in
      (Seq setup_prog (Loop ssa_names body_final ssa_exit),
       (inter ssa_refreshed exit_names, na'))
  | Break n =>
      match oEL n lt with
      | None => (Break n, (ssa, na))
      | Some (tgt_ssa, (names, exit_names)) =>
          let moves := ssa_reconcile ssa tgt_ssa exit_names in
          (if is_Skip moves then Break n else Seq moves (Break n), (ssa, na))
      end
  | Continue n =>
      match oEL n lt with
      | None => (Continue n, (ssa, na))
      | Some (tgt_ssa, (names, exit_names)) =>
          let moves := ssa_reconcile ssa tgt_ssa names in
          (if is_Skip moves then Continue n else Seq moves (Continue n), (ssa, na))
      end
  end.

(** ** Applying a colouring *)

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_exp_def" *)
Fixpoint apply_colour_exp (f : N -> N) (e : exp a) : exp a :=
  match e with
  | Var num => Var (f num)
  | Load exp => Load (apply_colour_exp f exp)
  | Op wop ls => Op wop (MAP (apply_colour_exp f) ls)
  | Shift sh exp nexp => Shift sh (apply_colour_exp f exp) (apply_colour_exp f nexp)
  | expr => expr
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_imm_def" *)
Definition apply_colour_imm (f : N -> N) (ri : reg_imm a) : reg_imm a :=
  match ri with Reg n => Reg (f n) | x => x end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_inst_def" *)
Definition apply_colour_inst (f : N -> N) (i : inst a) : inst a :=
  match i with
  | asm.Skip => asm.Skip
  | asm.Const reg w => asm.Const (f reg) w
  | Arith (Binop bop r1 r2 ri) => Arith (Binop bop (f r1) (f r2) (apply_colour_imm f ri))
  | Arith (asm.Shift shift r1 r2 ri) => Arith (asm.Shift shift (f r1) (f r2) (apply_colour_imm f ri))
  | Arith (Div r1 r2 r3) => Arith (Div (f r1) (f r2) (f r3))
  | Arith (AddCarry r1 r2 r3 r4) => Arith (AddCarry (f r1) (f r2) (f r3) (f r4))
  | Arith (AddOverflow r1 r2 r3 r4) => Arith (AddOverflow (f r1) (f r2) (f r3) (f r4))
  | Arith (SubOverflow r1 r2 r3 r4) => Arith (SubOverflow (f r1) (f r2) (f r3) (f r4))
  | Arith (LongMul r1 r2 r3 r4) => Arith (LongMul (f r1) (f r2) (f r3) (f r4))
  | Arith (LongDiv r1 r2 r3 r4 r5) => Arith (LongDiv (f r1) (f r2) (f r3) (f r4) (f r5))
  | Mem asm.Load r (Addr a0 w) => Mem asm.Load (f r) (Addr (f a0) w)
  | Mem asm.Store r (Addr a0 w) => Mem asm.Store (f r) (Addr (f a0) w)
  | Mem Load32 r (Addr a0 w) => Mem Load32 (f r) (Addr (f a0) w)
  | Mem Store32 r (Addr a0 w) => Mem Store32 (f r) (Addr (f a0) w)
  | Mem Load8 r (Addr a0 w) => Mem Load8 (f r) (Addr (f a0) w)
  | Mem Store8 r (Addr a0 w) => Mem Store8 (f r) (Addr (f a0) w)
  | FP (FPLess r f1 f2) => FP (FPLess (f r) f1 f2)
  | FP (FPLessEqual r f1 f2) => FP (FPLessEqual (f r) f1 f2)
  | FP (FPEqual r f1 f2) => FP (FPEqual (f r) f1 f2)
  | FP (FPMovToReg r1 r2 d) => FP (FPMovToReg (f r1) (f r2) d)
  | FP (FPMovFromReg d r1 r2) => FP (FPMovFromReg d (f r1) (f r2))
  | x => x
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_def" *)
Fixpoint apply_colour (f : N -> N) (p : prog a) : prog a :=
  match p with
  | Skip => Skip
  | Move pri ls => Move pri (ZIP (MAP (fun x => f (FST x)) ls, MAP (fun x => f (SND x)) ls))
  | Inst i => Inst (apply_colour_inst f i)
  | Assign num exp => Assign (f num) (apply_colour_exp f exp)
  | Get num store => Get (f num) store
  | Store exp num => Store (apply_colour_exp f exp) (f num)
  | Call ret dest args h =>
      let ret := match ret with
                 | None => None
                 | Some (vs, (cutset, (ret_handler, (l1, l2)))) =>
                     Some (MAP f vs, (apply_nummaps_key f cutset,
                                      (apply_colour f ret_handler, (l1, l2))))
                 end in
      let args := MAP f args in
      let h := match h with
               | None => None
               | Some (v, (prog, (l1, l2))) => Some (f v, (apply_colour f prog, (l1, l2)))
               end in
      Call ret dest args h
  | Seq s1 s2 => Seq (apply_colour f s1) (apply_colour f s2)
  | MustTerminate s1 => MustTerminate (apply_colour f s1)
  | If cmp r1 ri e2 e3 => If cmp (f r1) (apply_colour_imm f ri) (apply_colour f e2) (apply_colour f e3)
  | Install r1 r2 r3 r4 numset => Install (f r1) (f r2) (f r3) (f r4) (apply_nummaps_key f numset)
  | CodeBufferWrite r1 r2 => CodeBufferWrite (f r1) (f r2)
  | DataBufferWrite r1 r2 => DataBufferWrite (f r1) (f r2)
  | FFI ffi_index ptr1 len1 ptr2 len2 numset =>
      FFI ffi_index (f ptr1) (f len1) (f ptr2) (f len2) (apply_nummaps_key f numset)
  | LocValue r l1 => LocValue (f r) l1
  | Alloc num numset => Alloc (f num) (apply_nummaps_key f numset)
  | StoreConsts a0 b c d ws => StoreConsts (f a0) (f b) (f c) (f d) ws
  | Raise num => Raise (f num)
  | Return num1 nums => Return (f num1) (MAP f nums)
  | Tick => Tick
  | Set_ n exp => Set_ n (apply_colour_exp f exp)
  | OpCurrHeap b n1 n2 => OpCurrHeap b (f n1) (f n2)
  | ShareInst op v exp => ShareInst op (f v) (apply_colour_exp f exp)
  | Loop names body exit_names =>
      Loop (apply_nummap_key f names) (apply_colour f body) (apply_nummap_key f exit_names)
  | p => p
  end.

(** ** Liveness analysis *)

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_writes_inst_def" *)
Definition get_writes_inst (i : inst a) : num_set :=
  match i with
  | asm.Const reg w => insert reg tt LN
  | Arith (Binop bop r1 r2 ri) => insert r1 tt LN
  | Arith (asm.Shift shift r1 r2 ri) => insert r1 tt LN
  | Arith (Div r1 r2 r3) => insert r1 tt LN
  | Arith (AddCarry r1 r2 r3 r4) => insert r4 tt (insert r1 tt LN)
  | Arith (AddOverflow r1 r2 r3 r4) => insert r4 tt (insert r1 tt LN)
  | Arith (SubOverflow r1 r2 r3 r4) => insert r4 tt (insert r1 tt LN)
  | Arith (LongMul r1 r2 r3 r4) => insert r2 tt (insert r1 tt LN)
  | Arith (LongDiv r1 r2 r3 r4 r5) => insert r2 tt (insert r1 tt LN)
  | Mem asm.Load r (Addr a0 w) => insert r tt LN
  | Mem Load32 r (Addr a0 w) => insert r tt LN
  | Mem Load8 r (Addr a0 w) => insert r tt LN
  | FP (FPLess r f1 f2) => insert r tt LN
  | FP (FPLessEqual r f1 f2) => insert r tt LN
  | FP (FPEqual r f1 f2) => insert r tt LN
  | FP (FPMovToReg r1 r2 d) =>
      if dimindex a =? 64 then insert r1 tt LN else insert r2 tt (insert r1 tt LN)
  | _ => LN
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_live_inst_def" *)
Definition get_live_inst (i : inst a) (live : num_set) : num_set :=
  match i with
  | asm.Skip => live
  | asm.Const reg w => delete reg live
  | Arith (Binop bop r1 r2 ri) =>
      match ri with
      | Reg r3 => insert r2 tt (insert r3 tt (delete r1 live))
      | _ => insert r2 tt (delete r1 live)
      end
  | Arith (asm.Shift shift r1 r2 ri) =>
      match ri with
      | Reg r3 => insert r2 tt (insert r3 tt (delete r1 live))
      | _ => insert r2 tt (delete r1 live)
      end
  | Arith (Div r1 r2 r3) => insert r3 tt (insert r2 tt (delete r1 live))
  | Arith (AddCarry r1 r2 r3 r4) => insert r4 tt (insert r3 tt (insert r2 tt (delete r1 live)))
  | Arith (AddOverflow r1 r2 r3 r4) => insert r3 tt (insert r2 tt (delete r4 (delete r1 live)))
  | Arith (SubOverflow r1 r2 r3 r4) => insert r3 tt (insert r2 tt (delete r4 (delete r1 live)))
  | Arith (LongMul r1 r2 r3 r4) => insert r4 tt (insert r3 tt (delete r2 (delete r1 live)))
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      insert r5 tt (insert r4 tt (insert r3 tt (delete r2 (delete r1 live))))
  | Mem asm.Load r (Addr a0 w) => insert a0 tt (delete r live)
  | Mem asm.Store r (Addr a0 w) => insert a0 tt (insert r tt live)
  | Mem Load32 r (Addr a0 w) => insert a0 tt (delete r live)
  | Mem Store32 r (Addr a0 w) => insert a0 tt (insert r tt live)
  | Mem Load8 r (Addr a0 w) => insert a0 tt (delete r live)
  | Mem Store8 r (Addr a0 w) => insert a0 tt (insert r tt live)
  | FP (FPLess r f1 f2) => delete r live
  | FP (FPLessEqual r f1 f2) => delete r live
  | FP (FPEqual r f1 f2) => delete r live
  | FP (FPMovToReg r1 r2 d) =>
      if dimindex a =? 64 then delete r1 live else delete r1 (delete r2 live)
  | FP (FPMovFromReg d r1 r2) =>
      if dimindex a =? 64 then insert r1 tt live else insert r2 tt (insert r1 tt live)
  | _ => live
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "big_union_def" *)
Definition big_union (ls : list num_set) : num_set := FOLDR (fun x y => union x y) LN ls.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_live_exp_def" *)
Fixpoint get_live_exp (e : exp a) : num_set :=
  match e with
  | Var num => insert num tt LN
  | Load exp => get_live_exp exp
  | Op wop ls => big_union (MAP get_live_exp ls)
  | Shift sh exp nexp => union (get_live_exp exp) (get_live_exp nexp)
  | _ => LN
  end.

End SSA.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "numset_list_insert_def" *)
Fixpoint numset_list_insert (l : list N) (t : num_set) : num_set :=
  match l with
  | [] => t
  | x :: xs => insert x tt (numset_list_insert xs t)
  end.

Section Live.
Context {a : N}.

Definition is_store_op (op : memop) : bool :=
  bool_decide (op = asm.Store \/ op = Store8 \/ op = Store16 \/ op = Store32).

(** HOL's [get_live_def] has a second, unreachable [StoreConsts] clause;
    the first one is used. *)
(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_live_def" *)
Fixpoint get_live (p : prog a) (live : num_set) (lt : list (num_set * num_set)) : num_set :=
  match p with
  | Skip => live
  | Move pri ls =>
      let killed := FOLDR delete live (MAP FST ls) in
      numset_list_insert (MAP SND ls) killed
  | Inst i => get_live_inst i live
  | Assign num exp =>
      let sub := get_live_exp exp in
      union sub (delete num live)
  | Get num store => delete num live
  | Store exp num => insert num tt (union (get_live_exp exp) live)
  | Seq s1 s2 => get_live s1 (get_live s2 live lt) lt
  | MustTerminate s1 => get_live s1 live lt
  | If cmp r1 ri e2 e3 =>
      let e2_live := get_live e2 live lt in
      let e3_live := get_live e3 live lt in
      let union_live := union e2_live e3_live in
      match ri with
      | Reg r2 => insert r2 tt (insert r1 tt union_live)
      | _ => insert r1 tt union_live
      end
  | Alloc num numset => insert num tt (union (FST numset) (SND numset))
  | StoreConsts a0 b c d ws => insert c tt (insert d tt (delete a0 (delete b live)))
  | Install r1 r2 r3 r4 numset => list_insert [r1; r2; r3; r4] (union (FST numset) (SND numset))
  | CodeBufferWrite r1 r2 => list_insert [r1; r2] live
  | DataBufferWrite r1 r2 => list_insert [r1; r2] live
  | FFI ffi_index ptr1 len1 ptr2 len2 numset =>
      insert ptr1 tt (insert len1 tt (insert ptr2 tt (insert len2 tt
        (union (FST numset) (SND numset)))))
  | Raise num => insert num tt live
  | Return num1 nums => insert num1 tt (numset_list_insert nums live)
  | Tick => live
  | LocValue r l1 => delete r live
  | Set_ n exp => union (get_live_exp exp) live
  | OpCurrHeap b n1 n2 => insert n2 tt (delete n1 live)
  | ShareInst mop v exp =>
      let sub := get_live_exp exp in
      if is_store_op mop then union sub (insert v tt live)
      else union sub (delete v live)
  | Loop names body exit_names => names
  | Break n => match oEL n lt with None => LN | Some (names, exit_names) => exit_names end
  | Continue n => match oEL n lt with None => LN | Some (names, exit_names) => names end
  | Call None dest args h => numset_list_insert args LN
  | Call (Some (_, (cutset, _))) dest args h =>
      union (union (FST cutset) (SND cutset)) (numset_list_insert args LN)
  end.

(** ** Dead instruction removal *)

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "remove_dead_inst_def" *)
Definition remove_dead_inst (i : inst a) (live : num_set) : bool :=
  let dead r := bool_decide (lookup r live = None) in
  match i with
  | asm.Skip => true
  | asm.Const reg w => dead reg
  | Arith (Binop bop r1 r2 ri) => dead r1
  | Arith (asm.Shift shift r1 r2 n) => dead r1
  | Arith (Div r1 r2 r3) => dead r1
  | Arith (AddCarry r1 r2 r3 r4) => dead r1 && dead r4
  | Arith (AddOverflow r1 r2 r3 r4) => dead r1 && dead r4
  | Arith (SubOverflow r1 r2 r3 r4) => dead r1 && dead r4
  | Arith (LongMul r1 r2 r3 r4) => dead r1 && dead r2
  | Arith (LongDiv r1 r2 r3 r4 r5) => dead r1 && dead r2
  | Mem asm.Load r (Addr a0 w) => dead r
  | Mem Load32 r (Addr a0 w) => dead r
  | Mem Load8 r (Addr a0 w) => dead r
  | FP (FPLess r f1 f2) => dead r
  | FP (FPLessEqual r f1 f2) => dead r
  | FP (FPEqual r f1 f2) => dead r
  | FP (FPMovToReg r1 r2 d) => if dimindex a =? 64 then dead r1 else dead r1 && dead r2
  | _ => false
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "remove_dead_def" *)
Fixpoint remove_dead (p : prog a) (live : num_set) (nlive : list store_name)
    (lt : list (num_set * num_set)) : prog a * (num_set * list store_name) :=
  match p with
  | Move pri ls =>
      let ls := FILTER (fun '(x, y) => bool_decide (lookup x live = Some tt)) ls in
      match ls with
      | [] => (Skip, (live, nlive))
      | _ =>
          let killed := FOLDR delete live (MAP FST ls) in
          (Move pri ls, (numset_list_insert (MAP SND ls) killed, nlive))
      end
  | Inst i =>
      if remove_dead_inst i live then (Skip, (live, nlive))
      else (Inst i, (get_live_inst i live, nlive))
  | Get num store =>
      if bool_decide (lookup num live = None) then (Skip, (live, nlive))
      else (Get num store, (delete num live, FILTER (fun s => negb (bool_decide (store = s))) nlive))
  | OpCurrHeap b num src =>
      if bool_decide (lookup num live = None) then (Skip, (live, nlive))
      else (OpCurrHeap b num src,
            (insert src tt (delete num live), FILTER (fun s => negb (bool_decide (CurrHeap = s))) nlive))
  | LocValue r l1 =>
      if bool_decide (lookup r live = None) then (Skip, (live, nlive))
      else (LocValue r l1, (delete r live, nlive))
  | Set_ store_name exp =>
      match exp with
      | Var r =>
          if MEM store_name nlive then (Skip, (live, nlive))
          else (Set_ store_name (Var r), (insert r tt live, store_name :: nlive))
      | _ =>
          let prog := Set_ store_name exp in
          (prog, (get_live prog live lt, []))
      end
  | Seq s1 s2 =>
      let '(s2, (s2live, s2nlive)) := remove_dead s2 live nlive lt in
      let '(s1, (s1live, s1nlive)) := remove_dead s1 s2live s2nlive lt in
      let prog := if is_Skip s1 then s2 else if is_Skip s2 then s1 else Seq s1 s2 in
      (prog, (s1live, s1nlive))
  | MustTerminate s1 =>
      let '(s1, (s1live, s1nlive)) := remove_dead s1 live nlive lt in
      (MustTerminate s1, (s1live, s1nlive))
  | If cmp r1 ri e2 e3 =>
      let '(e2, (e2_live, e2_nlive)) := remove_dead e2 live nlive lt in
      let '(e3, (e3_live, e3_nlive)) := remove_dead e3 live nlive lt in
      let union_live := union e2_live e3_live in
      let liveset := match ri with
                     | Reg r2 => insert r2 tt (insert r1 tt union_live)
                     | _ => insert r1 tt union_live
                     end in
      let nliveset := FILTER (fun s => MEM s e3_nlive) e2_nlive in
      let prog := if is_Skip e2 && is_Skip e3 then Skip else If cmp r1 ri e2 e3 in
      (prog, (liveset, nliveset))
  | Call (Some (v, (cutsets, (ret_handler, (l1, l2))))) dest args h =>
      let args_set := numset_list_insert args LN in
      let cutset := union (FST cutsets) (SND cutsets) in
      let live_set := union cutset args_set in
      let '(ret_handler, _) := remove_dead ret_handler live nlive lt in
      let h := match h with
               | None => None
               | Some (v', (prog, (l1, l2))) => Some (v', (FST (remove_dead prog live nlive lt), (l1, l2)))
               end in
      (Call (Some (v, (cutsets, (ret_handler, (l1, l2))))) dest args h, (live_set, []))
  | Call None a0 b c =>
      let prog := Call None a0 b c in (prog, (get_live prog live lt, []))
  | Alloc a0 b =>
      let prog := Alloc a0 b in (prog, (get_live prog live lt, []))
  | Raise a0 =>
      let prog := Raise a0 in (prog, (get_live prog live lt, []))
  | Return a0 b =>
      let prog := Return a0 b in (prog, (get_live prog live lt, []))
  | Loop names body exit_names =>
      let lt' := (names, exit_names) :: lt in
      let '(body', (_, _)) := remove_dead body names [] lt' in
      (Loop names body' exit_names, (names, []))
  | Break n =>
      let prog := Break n in (prog, (get_live prog live lt, []))
  | Continue n =>
      let prog := Continue n in (prog, (get_live prog live lt, []))
  | prog => (prog, (get_live prog live lt, nlive))
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "remove_dead_prog_def" *)
Definition remove_dead_prog (prog : prog a) : wordLang.prog a := FST (remove_dead prog LN [] []).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_writes_def" *)
Definition get_writes (p : prog a) : num_set :=
  match p with
  | Move pri ls => numset_list_insert (MAP FST ls) LN
  | Inst i => get_writes_inst i
  | Assign num exp => insert num tt LN
  | Get num store => insert num tt LN
  | LocValue r l1 => insert r tt LN
  | Install r1 _ _ _ _ => insert r1 tt LN
  | OpCurrHeap b r1 _ => insert r1 tt LN
  | StoreConsts a0 b c d _ => insert a0 tt (insert b tt (insert c tt (insert d tt LN)))
  | ShareInst asm.Load v _ => insert v tt LN
  | ShareInst Load8 v _ => insert v tt LN
  | ShareInst Load16 v _ => insert v tt LN
  | ShareInst Load32 v _ => insert v tt LN
  | _ => LN
  end.

(** ** Clash trees *)

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_delta_inst_def" *)
Definition get_delta_inst (i : inst a) : clash_tree :=
  match i with
  | asm.Skip => Delta [] []
  | asm.Const reg w => Delta [reg] []
  | Arith (Binop bop r1 r2 ri) =>
      match ri with Reg r3 => Delta [r1] [r2; r3] | _ => Delta [r1] [r2] end
  | Arith (asm.Shift shift r1 r2 ri) =>
      match ri with Reg r3 => Delta [r1] [r2; r3] | _ => Delta [r1] [r2] end
  | Arith (Div r1 r2 r3) => Delta [r1] [r3; r2]
  | Arith (AddCarry r1 r2 r3 r4) => Delta [r1; r4] [r4; r3; r2]
  | Arith (AddOverflow r1 r2 r3 r4) => Delta [r1; r4] [r3; r2]
  | Arith (SubOverflow r1 r2 r3 r4) => Delta [r1; r4] [r3; r2]
  | Arith (LongMul r1 r2 r3 r4) => Delta [r1; r2] [r4; r3]
  | Arith (LongDiv r1 r2 r3 r4 r5) => Delta [r1; r2] [r5; r4; r3]
  | Mem asm.Load r (Addr a0 w) => Delta [r] [a0]
  | Mem asm.Store r (Addr a0 w) => Delta [] [r; a0]
  | Mem Load32 r (Addr a0 w) => Delta [r] [a0]
  | Mem Store32 r (Addr a0 w) => Delta [] [r; a0]
  | Mem Load8 r (Addr a0 w) => Delta [r] [a0]
  | Mem Store8 r (Addr a0 w) => Delta [] [r; a0]
  | FP (FPLess r f1 f2) => Delta [r] []
  | FP (FPLessEqual r f1 f2) => Delta [r] []
  | FP (FPEqual r f1 f2) => Delta [r] []
  | FP (FPMovToReg r1 r2 d) => if dimindex a =? 64 then Delta [r1] [] else Delta [r1; r2] []
  | FP (FPMovFromReg d r1 r2) => if dimindex a =? 64 then Delta [] [r1] else Delta [] [r1; r2]
  | _ => Delta [] []
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_reads_exp_def" *)
Fixpoint get_reads_exp (e : exp a) : list N :=
  match e with
  | Var num => [num]
  | Load exp => get_reads_exp exp
  | Op wop ls => FLAT (MAP get_reads_exp ls)
  | Shift sh exp nexp => get_reads_exp exp ++ get_reads_exp nexp
  | _ => []
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_clash_tree_def" *)
Fixpoint get_clash_tree (p : prog a) (lt : list (num_set * num_set)) : clash_tree :=
  match p with
  | Skip => Delta [] []
  | Move pri ls => Delta (MAP FST ls) (MAP SND ls)
  | Inst i => get_delta_inst i
  | Assign num exp => Delta [num] (get_reads_exp exp)
  | Get num store => Delta [num] []
  | Store exp num => Delta [] (num :: get_reads_exp exp)
  | Seq s1 s2 => reg_alloc.Seq (get_clash_tree s1 lt) (get_clash_tree s2 lt)
  | If cmp r1 ri e2 e3 =>
      let e2t := get_clash_tree e2 lt in
      let e3t := get_clash_tree e3 lt in
      match ri with
      | Reg r2 => reg_alloc.Seq (Delta [] [r1; r2]) (reg_alloc.Branch None e2t e3t)
      | _ => reg_alloc.Seq (Delta [] [r1]) (reg_alloc.Branch None e2t e3t)
      end
  | MustTerminate s => get_clash_tree s lt
  | Alloc num numset =>
      reg_alloc.Seq (Delta [] [num]) (reg_alloc.Set_ (union (FST numset) (SND numset)))
  | Install r1 r2 r3 r4 numset =>
      reg_alloc.Seq (Delta [] [r4; r3; r2; r1])
        (reg_alloc.Seq (reg_alloc.Set_ (union (FST numset) (SND numset))) (Delta [r1] []))
  | CodeBufferWrite r1 r2 => Delta [] [r2; r1]
  | DataBufferWrite r1 r2 => Delta [] [r2; r1]
  | FFI ffi_index ptr1 len1 ptr2 len2 numset =>
      reg_alloc.Seq (Delta [] [ptr1; len1; ptr2; len2])
        (reg_alloc.Set_ (union (FST numset) (SND numset)))
  | Raise num => Delta [] [num]
  | Return num1 nums => Delta [] (num1 :: nums)
  | Tick => Delta [] []
  | LocValue r l1 => Delta [r] []
  | Set_ n exp => Delta [] (get_reads_exp exp)
  | OpCurrHeap b dst src => Delta [dst] [src]
  | StoreConsts a0 b c d ws => Delta [a0; b; c; d] [c; d]
  | ShareInst op v exp =>
      if is_store_op op then Delta [] (v :: get_reads_exp exp)
      else Delta [v] (get_reads_exp exp)
  | Loop names body exit_names =>
      reg_alloc.Seq (reg_alloc.Set_ names)
        (reg_alloc.Seq (reg_alloc.Set_ exit_names)
          (reg_alloc.Seq (get_clash_tree body ((names, exit_names) :: lt)) (reg_alloc.Set_ names)))
  | Break n =>
      match oEL n lt with
      | None => reg_alloc.Set_ LN
      | Some (names, exit_names) => reg_alloc.Set_ exit_names
      end
  | Continue n =>
      match oEL n lt with
      | None => reg_alloc.Set_ LN
      | Some (names, exit_names) => reg_alloc.Set_ names
      end
  | Call ret dest args h =>
      let args_set := numset_list_insert args LN in
      match ret with
      | None => reg_alloc.Set_ args_set
      | Some (vs, (cutsets, (ret_handler, _))) =>
          let cutset := union (FST cutsets) (SND cutsets) in
          let live_set := union cutset args_set in
          let ret_tree := reg_alloc.Seq (reg_alloc.Set_ (numset_list_insert vs cutset))
                            (get_clash_tree ret_handler lt) in
          match h with
          | None => reg_alloc.Seq (reg_alloc.Set_ live_set) ret_tree
          | Some (v', (prog, _)) =>
              let handler_tree := reg_alloc.Seq (reg_alloc.Set_ (insert v' tt cutset))
                                    (get_clash_tree prog lt) in
              reg_alloc.Branch (Some live_set) ret_tree handler_tree
          end
      end
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_prefs_def" *)
Fixpoint get_prefs (p : prog a) (acc : list (N * (N * N))) : list (N * (N * N)) :=
  match p with
  | Move pri ls => MAP (fun '(x, y) => (pri, (x, y))) ls ++ acc
  | MustTerminate s1 => get_prefs s1 acc
  | Seq s1 s2 => get_prefs s1 (get_prefs s2 acc)
  | If cmp num rimm e2 e3 => get_prefs e2 (get_prefs e3 acc)
  | Call (Some (v, (cutset, (ret_handler, (l1, l2))))) dest args h =>
      match h with
      | None => get_prefs ret_handler acc
      | Some (v, (prog, (l1, l2))) => get_prefs prog (get_prefs ret_handler acc)
      end
  | Loop names body exit_names => get_prefs body acc
  | _ => acc
  end.

End Live.

(** ** Heuristics *)

(** [(const, reg, mem, rreg, rmem)], right-nested. *)
(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "heu_data" *)
Abbreviation heu_data := (N * (N * (N * (N * N))))%type.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "add1_lhs_const_def" *)
Definition add1_lhs_const (x : N) (t : num_map heu_data) : num_map heu_data :=
  match lookup x t with
  | None => insert x (1, (0, (0, (0, 0)))) t
  | Some (const, (reg, (mem, (rreg, rmem)))) => insert x (const + 1, (reg, (mem, (rreg, rmem)))) t
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "add1_lhs_reg_def" *)
Definition add1_lhs_reg (x : N) (t : num_map heu_data) : num_map heu_data :=
  match lookup x t with
  | None => insert x (0, (1, (0, (0, 0)))) t
  | Some (const, (reg, (mem, (rreg, rmem)))) => insert x (const, (reg + 1, (mem, (rreg, rmem)))) t
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "add1_lhs_mem_def" *)
Definition add1_lhs_mem (x : N) (t : num_map heu_data) : num_map heu_data :=
  match lookup x t with
  | None => insert x (0, (0, (1, (0, 0)))) t
  | Some (const, (reg, (mem, (rreg, rmem)))) => insert x (const, (reg, (mem + 1, (rreg, rmem)))) t
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "add1_rhs_reg_def" *)
Definition add1_rhs_reg (x : N) (t : num_map heu_data) : num_map heu_data :=
  match lookup x t with
  | None => insert x (0, (0, (0, (1, 0)))) t
  | Some (const, (reg, (mem, (rreg, rmem)))) => insert x (const, (reg, (mem, (rreg + 1, rmem)))) t
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "add1_rhs_mem_def" *)
Definition add1_rhs_mem (x : N) (t : num_map heu_data) : num_map heu_data :=
  match lookup x t with
  | None => insert x (0, (0, (0, (0, 1)))) t
  | Some (const, (reg, (mem, (rreg, rmem)))) => insert x (const, (reg, (mem, (rreg, rmem + 1)))) t
  end.

Section Heu.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_heu_inst_def" *)
Definition get_heu_inst (i : inst a) (lr : num_map heu_data) : num_map heu_data :=
  match i with
  | asm.Skip => lr
  | asm.Const reg w => add1_lhs_const reg lr
  | Arith (Binop bop r1 r2 ri) =>
      match ri with
      | Reg r3 => add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))
      | _ => add1_lhs_reg r1 (add1_rhs_reg r2 lr)
      end
  | Arith (asm.Shift shift r1 r2 ri) =>
      match ri with
      | Reg r3 => add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))
      | _ => add1_lhs_reg r1 (add1_rhs_reg r2 lr)
      end
  | Arith (Div r1 r2 r3) => add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))
  | Arith (AddCarry r1 r2 r3 r4) =>
      add1_lhs_reg r4 (add1_lhs_reg r1 (add1_rhs_reg r4 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))))
  | Arith (AddOverflow r1 r2 r3 r4) =>
      add1_lhs_reg r4 (add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))
  | Arith (SubOverflow r1 r2 r3 r4) =>
      add1_lhs_reg r4 (add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))
  | Arith (LongMul r1 r2 r3 r4) =>
      add1_lhs_reg r2 (add1_lhs_reg r1 (add1_rhs_reg r4 (add1_rhs_reg r3 lr)))
  | Arith (LongDiv r1 r2 r3 r4 r5) =>
      add1_lhs_reg r2 (add1_lhs_reg r1 (add1_rhs_reg r5 (add1_rhs_reg r4 (add1_rhs_reg r3 lr))))
  | Mem asm.Load r (Addr a0 w) => add1_lhs_mem r lr
  | Mem asm.Store r (Addr a0 w) => add1_rhs_mem r lr
  | Mem Load32 r (Addr a0 w) => add1_lhs_mem r lr
  | Mem Load8 r (Addr a0 w) => add1_lhs_mem r lr
  | Mem Store32 r (Addr a0 w) => add1_rhs_mem r lr
  | Mem Store8 r (Addr a0 w) => add1_rhs_mem r lr
  | FP (FPLess r f1 f2) => add1_lhs_reg r lr
  | FP (FPLessEqual r f1 f2) => add1_lhs_reg r lr
  | FP (FPEqual r f1 f2) => add1_lhs_reg r lr
  | FP (FPMovToReg r1 r2 d) => add1_lhs_reg r2 (add1_lhs_reg r1 lr)
  | FP (FPMovFromReg d r1 r2) => add1_rhs_reg r2 (add1_rhs_reg r1 lr)
  | _ => lr
  end.

End Heu.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "heu_max_def" *)
Definition heu_max (x y : heu_data) : heu_data :=
  let '(c1, (r1, (m1, (rr1, rm1)))) := x in
  let '(c2, (r2, (m2, (rr2, rm2)))) := y in
  (MAX c1 c2, (MAX r1 r2, (MAX m1 m2, (MAX rr1 rr2, MAX rm1 rm2)))).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "heu_max_all_def" *)
Definition heu_max_all (t1 t2 : num_map heu_data) : num_map heu_data :=
  let t1r := difference t1 t2 in
  union t1r
    (mapi (fun k v => match lookup k t1 with None => v | Some v' => heu_max v v' end) t2).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "heu_merge_call_def" *)
Definition heu_merge_call (t1 t2 : num_set) : num_set := union t1 t2.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "add_call_def" *)
Definition add_call {A} (lr : num_map A) (calls : num_set) : num_set :=
  union (sptree.map (fun v => tt) lr) calls.

Section Heu2.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_heu_def" *)
Fixpoint get_heu (fc : N) (p : prog a) (lrc : num_map heu_data * num_set)
    : num_map heu_data * num_set :=
  let '(lr, calls) := lrc in
  match p with
  | Move pri ls => (FOLDR add1_lhs_reg (FOLDR add1_rhs_reg lr (MAP SND ls)) (MAP FST ls), calls)
  | Inst i => (get_heu_inst i lr, calls)
  | Get num store => (add1_lhs_mem num lr, calls)
  | Set_ _ exp =>
      match exp with
      | Var r => (add1_rhs_mem r lr, calls)
      | _ => (lr, calls)
      end
  | OpCurrHeap b dst src => (add1_lhs_reg dst (add1_rhs_reg src lr), calls)
  | LocValue r l1 => (add1_lhs_reg r lr, calls)
  | Seq s1 s2 => get_heu fc s2 (get_heu fc s1 lrc)
  | MustTerminate s1 => get_heu fc s1 lrc
  | If cmp r1 ri e2 e3 =>
      let '(lr2, calls2) := get_heu fc e2 lrc in
      let '(lr3, calls3) := get_heu fc e3 lrc in
      let lr := heu_max_all lr2 lr3 in
      let calls := heu_merge_call calls2 calls3 in
      (match ri with
       | Reg r2 => add1_rhs_reg r1 (add1_rhs_reg r2 lr)
       | _ => add1_rhs_reg r1 lr
       end, calls)
  | Call None dest args h =>
      match dest with
      | None => (lr, calls)
      | Some p => if p =? fc then (lr, add_call lr calls) else (lr, calls)
      end
  | Call (Some (_, (_, (e2, _)))) dest args h =>
      let calls := match dest with
                   | None => calls
                   | Some p => if p =? fc then add_call lr calls else calls
                   end in
      let '(lr2, calls2) := get_heu fc e2 (lr, calls) in
      match h with
      | None => (lr2, calls)
      | Some (_, (e3, _)) =>
          let '(lr3, calls3) := get_heu fc e3 (lr, calls) in
          (heu_max_all lr2 lr3, heu_merge_call calls2 calls3)
      end
  | ShareInst asm.Load r _ => (add1_lhs_mem r lr, calls)
  | ShareInst Load8 r _ => (add1_lhs_mem r lr, calls)
  | ShareInst Load16 r _ => (add1_lhs_mem r lr, calls)
  | ShareInst Load32 r _ => (add1_lhs_mem r lr, calls)
  | ShareInst asm.Store r _ => (add1_rhs_mem r lr, calls)
  | ShareInst Store8 r _ => (add1_rhs_mem r lr, calls)
  | ShareInst Store16 r _ => (add1_rhs_mem r lr, calls)
  | ShareInst Store32 r _ => (add1_rhs_mem r lr, calls)
  | Loop names body exit_names => get_heu fc body lrc
  | _ => lrc
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_forced_def" *)
Fixpoint get_forced (c : asm_config a) (p : prog a) (acc : list (N * N)) : list (N * N) :=
  match p with
  | Inst i =>
      match i with
      | Arith (AddCarry r1 r2 r3 r4) =>
          if bool_decide (ISA c = MIPS \/ ISA c = RISC_V) then
            (if r1 =? r3 then [] else [(r1, r3)]) ++
            (if r1 =? r4 then [] else [(r1, r4)]) ++ acc
          else acc
      | Arith (AddOverflow r1 r2 r3 r4) =>
          if bool_decide (ISA c = MIPS \/ ISA c = RISC_V) then
            (if r1 =? r3 then [] else [(r1, r3)]) ++ acc
          else acc
      | Arith (SubOverflow r1 r2 r3 r4) =>
          if bool_decide (ISA c = MIPS \/ ISA c = RISC_V) then
            (if r1 =? r3 then [] else [(r1, r3)]) ++ acc
          else acc
      | Arith (LongMul r1 r2 r3 r4) =>
          if bool_decide (ISA c = ARMv7) then
            (if r1 =? r2 then [] else [(r1, r2)]) ++ acc
          else if bool_decide (ISA c = ARMv8 \/ ISA c = RISC_V \/ ISA c = Ag32) then
            (if r1 =? r3 then [] else [(r1, r3)]) ++
            (if r1 =? r4 then [] else [(r1, r4)]) ++ acc
          else acc
      | FP (FPMovToReg r1 r2 d) =>
          (if (dimindex a =? 32) && negb (r1 =? r2) then [(r1, r2)] else []) ++ acc
      | FP (FPMovFromReg d r1 r2) =>
          (if (dimindex a =? 32) && negb (r1 =? r2) then [(r1, r2)] else []) ++ acc
      | _ => acc
      end
  | MustTerminate s1 => get_forced c s1 acc
  | Seq s1 s2 => get_forced c s1 (get_forced c s2 acc)
  | If cmp num rimm e2 e3 => get_forced c e2 (get_forced c e3 acc)
  | Call (Some (v, (cutset, (ret_handler, (l1, l2))))) dest args h =>
      match h with
      | None => get_forced c ret_handler acc
      | Some (v, (prog, (l1, l2))) => get_forced c prog (get_forced c ret_handler acc)
      end
  | Loop names body exit_names => get_forced c body acc
  | _ => acc
  end.

End Heu2.

(** ** Checking oracle colourings *)

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "check_colouring_ok_alt_def" *)
Fixpoint check_colouring_ok_alt {A} (col : N -> N) (l : list (num_map A)) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      let names := MAP (fun y => col (FST y)) (toAList x) in
      ALL_DISTINCT names && check_colouring_ok_alt col xs
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "every_even_colour_def" *)
Definition every_even_colour (col : num_map N) : bool :=
  EVERY (fun '(x, y) => if is_phy_var x then y =? x DIV 2 else true) (toAList col).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "total_colour_def" *)
Definition total_colour (col : num_map N) (x : N) : N :=
  match lookup x col with
  | None => if is_phy_var x then x else 0
  | Some x => 2 * x
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "oracle_colour_ok_def" *)
Definition oracle_colour_ok {a} (k : N) (col_opt : option (num_map N)) (tree : clash_tree)
    (prog : prog a) (ls : list (N * N)) : option (wordLang.prog a) :=
  match col_opt with
  | None => None
  | Some col =>
      let tcol := total_colour col in
      if every_even_colour col &&
         match check_clash_tree tcol tree LN LN with None => false | Some _ => true end
      then
        let prog := apply_colour tcol prog in
        if every_stack_var (fun x => 2 * k <=? x) prog &&
           EVERY (fun '(x, y) => negb (tcol x =? tcol y)) ls
        then Some prog
        else None
      else None
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "canonize_moves_aux_def" *)
Fixpoint canonize_moves_aux (curp : N) (curm : N * N) (ctr : N) (l : list (N * (N * N)))
    (acc : list (N * (N * (N * N)))) : list (N * (N * (N * N))) :=
  match l with
  | [] => (ctr, (curp, curm)) :: acc
  | (p, m) :: xs =>
      if bool_decide (curm = m) then canonize_moves_aux (MAX curp p) m (ctr + 1) xs acc
      else canonize_moves_aux p m 1 xs ((ctr, (curp, curm)) :: acc)
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "canonize_moves_def" *)
Definition canonize_moves (ls : list (N * (N * N))) : list (N * (N * (N * N))) :=
  let can1 := MAP (fun '(p, (x, y)) => if x <=? y then (p, (x, y)) else (p, (y, x))) ls in
  let can2 := sort (fun '(p1, (x1, y1)) '(p2, (x2, y2)) =>
                      if x1 =? x2 then if y1 =? y2 then p1 <? p2 else y1 <? y2
                      else x1 <? x2) can1 in
  match can2 with
  | [] => []
  | (p, m) :: xs => canonize_moves_aux p m 1 xs []
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_spillcost_def" *)
Definition get_spillcost (h : heu_data) (istail : bool) : N :=
  let '(c, (lr, (lm, (rr, rm)))) := h in
  (c + 2 * lr + 4 * lm + 2 * rr + 4 * rm) * (if istail then 5 else 1).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_coalescecost_def" *)
Definition get_coalescecost (spillcost : num_map N) (m : N * (N * (N * N))) : N * (N * N) :=
  let '(n, (p, (x, y))) := m in
  let xcost := if bool_decide (lookup x spillcost = None) then 0 else 1 in
  let ycost := if bool_decide (lookup y spillcost = None) then 0 else 1 in
  (n * (10 * (p + 1) + xcost + ycost), (x, y)).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_heuristics_def" *)
Definition get_heuristics {a} (alg fc : N) (prog : prog a)
    : list (N * (N * N)) * option (num_map N) :=
  if alg MOD 2 =? 1 then
    let '(lr, calls) := get_heu fc prog (LN, LN) in
    let moves := get_prefs prog [] in
    let spillcosts := mapi (fun k v => get_spillcost v (bool_decide (lookup k calls = None))) lr in
    let canon_moves := canonize_moves moves in
    let heu_moves := MAP (get_coalescecost spillcosts) canon_moves in
    (heu_moves, Some spillcosts)
  else
    let moves := get_prefs prog [] in
    (moves, None).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "select_reg_alloc_def" *)
Definition select_reg_alloc (alg : N) (spillcosts : option (num_map N)) (k : N)
    (heu_moves : list (N * (N * N))) (tree : clash_tree) (forced : list (N * N)) (fs : num_set)
    : exc (num_map N) state_exn :=
  if 4 <=? alg then linear_scan_reg_alloc k heu_moves tree forced
  else reg_alloc (if alg <=? 1 then Simple else IRC) spillcosts k heu_moves tree forced fs.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "merge_stack_only_def" *)
Definition merge_stack_only (m : N * N) (tfs : num_set * num_set) : num_set * num_set :=
  let '(x, y) := m in
  let '(ts, fs) := tfs in
  if bool_decide (lookup x ts = Some tt) then
    let ts := if is_alloc_var y then insert y tt ts else ts in
    let fs := if is_phy_var y then fs else insert x tt fs in
    (ts, fs)
  else if is_stack_var x then
    let ts := if is_alloc_var y then insert y tt ts else ts in
    (ts, fs)
  else (delete y ts, fs).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "merge_stack_sets_def" *)
Definition merge_stack_sets (tfs tfsL tfsR : num_set * num_set) : num_set * num_set :=
  let '(ts, fs) := tfs in
  let '(tsL, fsL) := tfsL in
  let '(tsR, fsR) := tfsR in
  let keep1 := inter tsR (inter tsL ts) in
  let keep2 := union (difference tsL ts) (difference tsR ts) in
  (union keep1 keep2, union fsL fsR).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "remove_temp_stack_def" *)
Definition remove_temp_stack (ls : list N) (tfs : num_set * num_set) : num_set * num_set :=
  let '(ts, fs) := tfs in (FOLDR delete ts ls, fs).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_stack_only_aux_def" *)
Fixpoint get_stack_only_aux {a} (tfs : num_set * num_set) (p : prog a) : num_set * num_set :=
  match p with
  | Move pri ls => FOLDR merge_stack_only tfs ls
  | Seq s1 s2 => get_stack_only_aux (get_stack_only_aux tfs s2) s1
  | If cmp r1 ri e2 e3 =>
      let tfsL := get_stack_only_aux tfs e2 in
      let tfsR := get_stack_only_aux tfs e3 in
      let tfsM := merge_stack_sets tfs tfsL tfsR in
      match ri with
      | Reg r2 => remove_temp_stack [r1; r2] tfsM
      | _ => remove_temp_stack [r1] tfsM
      end
  | MustTerminate s => get_stack_only_aux tfs s
  | Call ret dest args h =>
      match ret with
      | None => tfs
      | Some (v, (cutset, (ret_handler, _))) =>
          let rettfs := get_stack_only_aux tfs ret_handler in
          match h with
          | None => rettfs
          | Some (v', (handler, _)) =>
              let handlertfs := get_stack_only_aux tfs handler in
              merge_stack_sets tfs rettfs handlertfs
          end
      end
  | Loop names body exit_names => get_stack_only_aux tfs body
  | prog =>
      match get_clash_tree prog [] with
      | Delta ws rs => remove_temp_stack (ws ++ rs) tfs
      | _ => tfs
      end
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "get_stack_only_def" *)
Definition get_stack_only {a} (prog : prog a) : num_set := SND (get_stack_only_aux (LN, LN) prog).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "word_alloc_def" *)
Definition word_alloc {a} (fc : N) (c : asm_config a) (alg k : N) (prog : prog a)
    (col_opt : option (num_map N)) : wordLang.prog a :=
  let tree := get_clash_tree prog [] in
  let fs := get_stack_only prog in
  let forced := get_forced c prog [] in
  match oracle_colour_ok k col_opt tree prog forced with
  | None =>
      let '(heu_moves, spillcosts) := get_heuristics alg fc prog in
      match select_reg_alloc alg spillcosts k heu_moves tree forced fs with
      | M_success col => apply_colour (total_colour col) prog
      | M_failure _ => prog
      end
  | Some col_prog => col_prog
  end.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "setup_ssa_def" *)
Definition setup_ssa {a} (n lim : N) (prog : prog a) : wordLang.prog a * (num_map N * N) :=
  let args := even_list n in
  let '(new_ls, (ssa', n')) := list_next_var_rename args LN lim in
  (Move 1 (ZIP (new_ls, args)), (ssa', n')).

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "limit_var_def" *)
Definition limit_var {a} (prog : prog a) : N :=
  let x := max_var prog in
  x + (4 - x MOD 4) + 1.

(*! HOL "cakeml/compiler/backend/word_allocScript.sml" "full_ssa_cc_trans_def" *)
Definition full_ssa_cc_trans {a} (n : N) (prog : prog a) : wordLang.prog a :=
  let lim := limit_var prog in
  let '(mov, (ssa, na)) := setup_ssa n lim prog in
  let '(prog', (ssa', na')) := ssa_cc_trans prog ssa na [] in
  Seq mov prog'.
