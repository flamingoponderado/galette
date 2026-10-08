(** * CakeML [word_simp]: lightweight optimisations on wordLang programs

    Port of [cakeml/compiler/backend/word_simpScript.sml].  The [_pmatch]
    theorems (alternative [pmatch] presentations of the same functions,
    used by HOL's translator) are not ported.  [dest_Raise_num] and
    [is_simple] are defined in HOL with [pmatch] ([..._pmatch_def],
    [nocompute]) and evaluated through the compiled-out [_def] theorems;
    the Rocq definitions are the ordinary [match]es, tagged with the
    [_def] names.  [SmartSeq]'s and [const_fp_loop]'s HOL tests
    [p1 = Skip] / [handler = NONE] are written as pattern matches (same
    value). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang.
Open Scope N_scope.

Section Simp.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "SmartSeq_def" *)
Definition SmartSeq (p1 p2 : prog a) : prog a :=
  match p1 with Skip => p2 | _ => Seq p1 p2 end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "Seq_assoc_def" *)
Fixpoint Seq_assoc (p1 : prog a) (p : prog a) {struct p} : prog a :=
  match p with
  | Skip => p1
  | Seq q1 q2 => Seq_assoc (Seq_assoc p1 q1) q2
  | If v n r q1 q2 => SmartSeq p1 (If v n r (Seq_assoc Skip q1) (Seq_assoc Skip q2))
  | MustTerminate q => SmartSeq p1 (MustTerminate (Seq_assoc Skip q))
  | Call ret_prog dest args handler =>
      SmartSeq p1 (Call (match ret_prog with
                         | None => None
                         | Some (x1, (x2, (q1, (x3, x4)))) =>
                             Some (x1, (x2, (Seq_assoc Skip q1, (x3, x4))))
                         end)
                        dest args
                        (match handler with
                         | None => None
                         | Some (y1, (q2, (y2, y3))) => Some (y1, (Seq_assoc Skip q2, (y2, y3)))
                         end))
  | Loop names body exit_names => SmartSeq p1 (Loop names (Seq_assoc Skip body) exit_names)
  | other => SmartSeq p1 other
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "dest_Seq_def" *)
Definition dest_Seq (p : prog a) : prog a * prog a :=
  match p with
  | Seq p1 p2 => (p1, p2)
  | p => (Skip, p)
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "dest_If_def" *)
Definition dest_If (p : prog a)
    : option (cmp * (N * (reg_imm a * (prog a * prog a)))) :=
  match p with
  | If x1 x2 x3 p1 p2 => Some (x1, (x2, (x3, (p1, p2))))
  | _ => None
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "dest_If_Eq_Imm_def" *)
Definition dest_If_Eq_Imm (p : prog a) : option (N * (word a * (prog a * prog a))) :=
  match dest_If p with
  | Some (Equal, (n, (Imm w, (p1, p2)))) => Some (n, (w, (p1, p2)))
  | _ => None
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "dest_Seq_Assign_Const_def" *)
Definition dest_Seq_Assign_Const (n : N) (p : prog a) : option (prog a * word a) :=
  let '(p1, p2) := dest_Seq p in
  match p2 with
  | Assign m (Const w) => if decide (m = n) then Some (p1, w) else None
  | _ => None
  end.

(** ** Constant folding and propagation *)

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "strip_const_def" *)
Fixpoint strip_const (l : list (exp a)) : option (list (word a)) :=
  match l with
  | [] => Some []
  | Const w :: cs =>
      match strip_const cs with
      | Some ws => Some (w :: ws)
      | _ => None
      end
  | _ => None
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "const_fp_exp_def" *)
Fixpoint const_fp_exp (e : exp a) (cs : num_map (word a)) : exp a :=
  match e with
  | Var v =>
      match lookup v cs with
      | Some x => Const x
      | None => Var v
      end
  | Op op args =>
      let const_fp_args := MAP (fun a0 => const_fp_exp a0 cs) args in
      match strip_const const_fp_args with
      | Some ws =>
          match word_op op ws with
          | Some w => Const w
          | _ => Op op (MAP Const ws)
          end
      | _ => Op op const_fp_args
      end
  | Shift sh e e1 =>
      let const_fp_exp_e := const_fp_exp e cs in
      let const_fp_exp_e1 := const_fp_exp e1 cs in
      match const_fp_exp_e, const_fp_exp_e1 with
      | Const c, Const c1 =>
          match word_sh sh c (w2n c1) with
          | Some w => Const w
          | _ => Shift sh (Const c) (Const c1)
          end
      | _, _ => Shift sh const_fp_exp_e const_fp_exp_e1
      end
  | e => e
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "const_fp_move_cs_def" *)
Fixpoint const_fp_move_cs (l : list (N * N)) (ocs ncs : num_map (word a)) : num_map (word a) :=
  match l with
  | [] => ncs
  | m :: ms =>
      let v := FST m in
      let nncs :=
        match lookup (SND m) ocs with
        | Some c => insert v c ncs
        | _ => delete v ncs
        end in
      const_fp_move_cs ms ocs nncs
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "const_fp_inst_cs_def" *)
Definition const_fp_inst_cs (i : inst a) (cs : num_map (word a)) : num_map (word a) :=
  match i with
  | asm.Const r _ => delete r cs
  | Arith (Binop _ r _ _) => delete r cs
  | Arith (asm.Shift _ r _ _) => delete r cs
  | Arith (AddCarry r1 _ _ r2) => delete r2 (delete r1 cs)
  | Arith (AddOverflow r1 _ _ r2) => delete r2 (delete r1 cs)
  | Arith (SubOverflow r1 _ _ r2) => delete r2 (delete r1 cs)
  | Arith (LongMul r1 r2 _ _) => delete r1 (delete r2 cs)
  | Arith (LongDiv r1 r2 _ _ _) => delete r1 (delete r2 cs)
  | Arith (Div r1 _ _) => delete r1 cs
  | Mem asm.Load r _ => delete r cs
  | Mem Load32 r _ => delete r cs
  | Mem Load8 r _ => delete r cs
  | FP (FPLess r f1 f2) => delete r cs
  | FP (FPLessEqual r f1 f2) => delete r cs
  | FP (FPEqual r f1 f2) => delete r cs
  | FP (FPMovToReg r1 r2 d) =>
      if dimindex a =? 64 then delete r1 cs else delete r2 (delete r1 cs)
  | _ => cs
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "get_var_imm_cs_def" *)
Definition get_var_imm_cs (ri : reg_imm a) (cs : num_map (word a)) : option (word a) :=
  match ri with
  | Reg r => lookup r cs
  | Imm i => Some i
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "is_gc_const_def" *)
Definition is_gc_const (c : word a) : bool := bool_decide (word_and c (n2w 1) = n2w 0).

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "all_names_def" *)
Definition all_names {B} (p : spt B * spt B) : spt B :=
  let '(n, m) := p in union n m.

(** HOL's local overload [delete_all n l = FOLDR delete l n]. *)
(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "delete_all" *)
Definition delete_all {B} (n : list N) (l : spt B) : spt B := FOLDR delete l n.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "drop_consts_def" *)
Fixpoint drop_consts (cs : num_map (word a)) (l : list N) : prog a :=
  match l with
  | [] => Skip
  | n :: ns =>
      match lookup n cs with
      | None => drop_consts cs ns
      | Some w => SmartSeq (drop_consts cs ns) (Assign n (Const w))
      end
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "const_fp_loop_def" *)
Fixpoint const_fp_loop (p : prog a) (cs : num_map (word a)) : prog a * num_map (word a) :=
  match p with
  | Move pri moves => (Move pri moves, const_fp_move_cs moves cs cs)
  | Inst i => (Inst i, const_fp_inst_cs i cs)
  | Assign v e =>
      let const_fp_e := const_fp_exp e cs in
      match const_fp_e with
      | Const c => (Assign v const_fp_e, insert v c cs)
      | _ => (Assign v const_fp_e, delete v cs)
      end
  | Get v name => (Get v name, delete v cs)
  | OpCurrHeap b v w => (OpCurrHeap b v w, delete v cs)
  | MustTerminate p =>
      let '(p', cs') := const_fp_loop p cs in (MustTerminate p', cs')
  | Seq p1 p2 =>
      let '(p1', cs') := const_fp_loop p1 cs in
      let '(p2', cs'') := const_fp_loop p2 cs' in
      (Seq p1' p2', cs'')
  | If cmp lhs rhs p1 p2 =>
      match lookup lhs cs, get_var_imm_cs rhs cs with
      | Some clhs, Some crhs =>
          if word_cmp cmp clhs crhs then const_fp_loop p1 cs else const_fp_loop p2 cs
      | _, _ =>
          let '(p1', p1cs) := const_fp_loop p1 cs in
          let '(p2', p2cs) := const_fp_loop p2 cs in
          (If cmp lhs rhs p1' p2', inter_eq p1cs p2cs)
      end
  | Call ret dest args handler =>
      match ret with
      | None => (SmartSeq (drop_consts cs args) (Call ret dest args handler),
                 filter_v is_gc_const cs)
      | Some (n, (names, (ret_handler, (l1, l2)))) =>
          match handler with
          | None =>
              let cs' := delete_all n (filter_v is_gc_const (inter cs (all_names names))) in
              let '(ret_handler', cs'') := const_fp_loop ret_handler cs' in
              (SmartSeq (drop_consts cs args)
                 (Call (Some (n, (names, (ret_handler', (l1, l2))))) dest args handler), cs'')
          | Some _ =>
              (SmartSeq (drop_consts cs args) (Call ret dest args handler), LN)
          end
      end
  | FFI x0 x1 x2 x3 x4 names =>
      (SmartSeq (drop_consts cs [x1; x2; x3; x4]) (FFI x0 x1 x2 x3 x4 names),
       inter cs (all_names names))
  | LocValue v x3 => (LocValue v x3, delete v cs)
  | Alloc n names =>
      (SmartSeq (drop_consts cs [n]) (Alloc n names),
       filter_v is_gc_const (inter cs (all_names names)))
  | StoreConsts a0 b c d ws =>
      (StoreConsts a0 b c d ws, delete a0 (delete b (delete c (delete d cs))))
  | Install r1 r2 r3 r4 names =>
      (SmartSeq (drop_consts cs [r1; r2; r3; r4]) (Install r1 r2 r3 r4 names),
       delete r1 (filter_v is_gc_const (inter cs (all_names names))))
  | Store e v => (Store (const_fp_exp e cs) v, cs)
  | ShareInst asm.Load v e => (ShareInst asm.Load v (const_fp_exp e cs), delete v cs)
  | ShareInst Load8 v e => (ShareInst Load8 v (const_fp_exp e cs), delete v cs)
  | ShareInst Load16 v e => (ShareInst Load16 v (const_fp_exp e cs), delete v cs)
  | ShareInst Load32 v e => (ShareInst Load32 v (const_fp_exp e cs), delete v cs)
  | ShareInst asm.Store v e => (ShareInst asm.Store v (const_fp_exp e cs), cs)
  | ShareInst Store8 v e => (ShareInst Store8 v (const_fp_exp e cs), cs)
  | ShareInst Store16 v e => (ShareInst Store16 v (const_fp_exp e cs), cs)
  | ShareInst Store32 v e => (ShareInst Store32 v (const_fp_exp e cs), cs)
  | Loop names body exit_names =>
      (Loop names (FST (const_fp_loop body LN)) exit_names, LN)
  | p => (p, cs)
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "const_fp_def" *)
Definition const_fp (p : prog a) : prog a := FST (const_fp_loop p LN).

(** ** Merging near-consecutive [If]s *)

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "rewrite_duplicate_if_max_reassoc_def" *)
Definition rewrite_duplicate_if_max_reassoc : N := 8.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "dest_Raise_num_def" *)
Definition dest_Raise_num (p : prog a) : N :=
  match p with Raise n => n | _ => 0 end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "is_simple_def" *)
Definition is_simple (p : prog a) : bool :=
  match p with
  | Tick => true
  | Skip => true
  | Move _ _ => true
  | Assign _ _ => true
  | _ => false
  end.

(** HOL's [try_if_hoist2] recurses on [p1] (and decrements [N]); it is
    structural in [p1] here.  The [N = 0] test comes first, as in HOL. *)
(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "try_if_hoist2_def" *)
Fixpoint try_if_hoist2 (N0 : N) (p1 interm dummy p2 : prog a) {struct p1} : option (prog a) :=
  if N0 =? 0 then None
  else match p1 with
  | If cmp lhs rhs br1 br2 =>
      let res1 := dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq br1 interm) dummy)))) in
      if res1 =? 0 then None
      else
      let res2 := dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq br2 interm) dummy)))) in
      if negb (res1 + res2 =? 3) then None
      else Some (const_fp (If cmp lhs rhs (Seq (Seq br1 interm) p2) (Seq (Seq br2 interm) p2)))
  | Seq p3 p4 =>
      match dest_If p4 with
      | Some (cmp, (lhs, (rhs, (br1, br2)))) =>
          let res1 := dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq br1 interm) dummy)))) in
          if res1 =? 0 then None
          else
          let res2 := dest_Raise_num (SND (dest_Seq (const_fp (Seq (Seq br2 interm) dummy)))) in
          if negb (res1 + res2 =? 3) then None
          else Some (Seq p3 (const_fp (If cmp lhs rhs (Seq (Seq br1 interm) p2)
                                          (Seq (Seq br2 interm) p2))))
      | None =>
          if is_simple p4
          then try_if_hoist2 (N0 - 1) p3 (Seq p4 interm) dummy p2
          else None
      end
  | _ => None
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "try_if_hoist1_def" *)
Definition try_if_hoist1 (p1 p2 : prog a) : option (prog a) :=
  match dest_If p2 with
  | None => None
  | Some (cmp, (lhs, (rhs, (_, _)))) =>
      let dummy := If cmp lhs rhs (Raise 1) (Raise 2) in
      try_if_hoist2 rewrite_duplicate_if_max_reassoc p1 Skip dummy p2
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "simp_duplicate_if_def" *)
Fixpoint simp_duplicate_if (p : prog a) : prog a :=
  match p with
  | MustTerminate q => MustTerminate (simp_duplicate_if q)
  | Call ret_prog dest args handler =>
      Call (match ret_prog with
            | None => None
            | Some (x1, (x2, (q1, (x3, x4)))) => Some (x1, (x2, (simp_duplicate_if q1, (x3, x4))))
            end)
           dest args
           (match handler with
            | None => None
            | Some (y1, (q2, (y2, y3))) => Some (y1, (simp_duplicate_if q2, (y2, y3)))
            end)
  | If cmp lhs rhs br1 br2 => If cmp lhs rhs (simp_duplicate_if br1) (simp_duplicate_if br2)
  | Seq p1 p2 =>
      let p1x := simp_duplicate_if p1 in
      let p2x := simp_duplicate_if p2 in
      match try_if_hoist1 p1x p2x with
      | None => Seq p1x p2x
      | Some p3 => Seq_assoc Skip p3
      end
  | Loop names body exit_names => Loop names (simp_duplicate_if body) exit_names
  | _ => p
  end.

(** ** Pushing code out of [If]s whose other branch halts *)

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "push_out_if_aux_def" *)
Fixpoint push_out_if_aux (p : prog a) : prog a * bool :=
  match p with
  | MustTerminate q =>
      let '(c, b) := push_out_if_aux q in (MustTerminate c, b)
  | Return _ _ => (p, true)
  | Raise _ => (p, true)
  | Call None _ _ _ => (p, true)
  | If cmp r1 ri c1 c2 =>
      match push_out_if_aux c1, push_out_if_aux c2 with
      | (c1', true), (c2', true) => (If cmp r1 ri c1' c2', true)
      | (c1', false), (c2', true) => (Seq (If cmp r1 ri Skip c2') c1', false)
      | (c1', true), (c2', false) => (Seq (If cmp r1 ri c1' Skip) c2', false)
      | (c1', false), (c2', false) => (If cmp r1 ri c1' c2', false)
      end
  | Seq c1 c2 =>
      match push_out_if_aux c1 with
      | (c1', true) => (Seq c1' c2, true)
      | (c1', false) =>
          let '(c2', b) := push_out_if_aux c2 in (Seq c1' c2', b)
      end
  | Loop names body exit_names => (Loop names (FST (push_out_if_aux body)) exit_names, false)
  | _ => (p, false)
  end.

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "push_out_if_def" *)
Definition push_out_if (p : prog a) : prog a := FST (push_out_if_aux p).

(*! HOL "cakeml/compiler/backend/word_simpScript.sml" "compile_exp_def" *)
Definition compile_exp (e : prog a) : prog a :=
  let e := Seq_assoc Skip e in
  let e := const_fp e in
  let e := simp_duplicate_if e in
  let e := push_out_if e in
  e.

End Simp.
