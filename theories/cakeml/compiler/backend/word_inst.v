(** * CakeML [word_inst]: instruction selection (maximal munch)

    Port of [cakeml/compiler/backend/word_instScript.sml].  The [_pmatch]
    theorems (alternative presentations for HOL's translator) are not
    ported.

    HOL defines [pull_exp], [flatten_exp] and [inst_select_exp] by
    well-founded recursion on [exp_size].  [pull_exp] and
    [inst_select_exp] only recurse on subterms, so they are structural
    [Fixpoint]s with HOL's clauses.  [flatten_exp]'s clause
    [flatten_exp (Op op (x::xs)) = Op op [flatten_exp (Op op xs); ...]]
    recurses on [Op op xs], which is not a subterm; the [Fixpoint] computes
    it through an inner recursion on the argument list, and
    [flatten_exp_eqns] proves HOL's clauses (with HOL's first-match side
    conditions made explicit).  It is therefore not tagged. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.sort Require Import sorting.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang wordLang.
Open Scope N_scope.

Section Inst.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "pull_ops_def" *)
Fixpoint pull_ops (op : binop) (l : list (exp a)) (acc : list (exp a)) : list (exp a) :=
  match l with
  | [] => acc
  | x :: xs =>
      match x with
      | Op op' ls => if decide (op = op') then pull_ops op xs (ls ++ acc)
                     else pull_ops op xs (x :: acc)
      | _ => pull_ops op xs (x :: acc)
      end
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "is_const_def" *)
Definition is_const (e : exp a) : bool :=
  match e with Const w => true | _ => false end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "rm_const_def" *)
Definition rm_const (e : exp a) : word a :=
  match e with Const w => w | _ => n2w 0 end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "convert_sub_def" *)
Definition convert_sub (l : list (exp a)) : exp a :=
  match l with
  | [Const w1; Const w2] => Const (word_sub w1 w2)
  | [x; Const w] => Op asm.Add [Const (word_2comp w); x]
  | ls => Op asm.Sub ls
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "op_consts_def" *)
Definition op_consts (op : binop) : exp a :=
  match op with
  | And => Const (word_1comp (n2w 0))
  | _ => Const (n2w 0)
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "reduce_const_def" *)
Definition reduce_const (op : binop) (w : word a) (rest : list (exp a)) : exp a :=
  if decide (w = n2w 0) then
    if decide (op = asm.Add \/ op = Or \/ op = asm.Xor) then
      match rest with
      | [] => Const w
      | [x] => x
      | _ => Op op rest
      end
    else if decide (op = And) then Const (n2w 0)
    else Op op (Const w :: rest)
  else Op op (Const w :: rest).

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "optimize_consts_def" *)
Definition optimize_consts (op : binop) (ls : list (exp a)) : exp a :=
  let '(const_ls, nconst_ls) := PARTITION is_const ls in
  match const_ls with
  | [] => Op op nconst_ls
  | _ =>
      let w := THE (word_op op (MAP rm_const const_ls)) in
      reduce_const op w nconst_ls
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "pull_exp_def" *)
Fixpoint pull_exp (e : exp a) : exp a :=
  match e with
  | Op asm.Sub ls =>
      let new_ls := MAP pull_exp ls in
      convert_sub new_ls
  | Op op [] => op_consts op
  | Op _ [x] => pull_exp x
  | Op op ls =>
      let new_ls := MAP pull_exp ls in
      let pull_ls := pull_ops op new_ls [] in
      optimize_consts op pull_ls
  | Load exp => Load (pull_exp exp)
  | Shift shift exp nexp => Shift shift (pull_exp exp) (pull_exp nexp)
  | exp => exp
  end.

(** HOL [flatten_exp]; see the file header. *)
Fixpoint flatten_exp (e : exp a) : exp a :=
  match e with
  | Op asm.Sub exps => Op asm.Sub (MAP flatten_exp exps)
  | Op op exps =>
      (fix flatten_args (l : list (exp a)) : exp a :=
         match l with
         | [] => op_consts op
         | [x] => flatten_exp x
         | x :: xs => Op op [flatten_args xs; flatten_exp x]
         end) exps
  | Load exp => Load (flatten_exp exp)
  | Shift shift exp nexp => Shift shift (flatten_exp exp) (flatten_exp nexp)
  | exp => exp
  end.

(** HOL's clauses of [flatten_exp_def] (in HOL's order; a clause applies when
    the earlier ones do not). *)
Lemma flatten_exp_eqns :
  (forall exps, flatten_exp (Op asm.Sub exps) = Op asm.Sub (MAP flatten_exp exps)) /\
  (forall op, op <> asm.Sub -> flatten_exp (Op op []) = op_consts op) /\
  (forall op x, op <> asm.Sub -> flatten_exp (Op op [x]) = flatten_exp x) /\
  (forall op x xs, op <> asm.Sub -> xs <> [] ->
     flatten_exp (Op op (x :: xs)) = Op op [flatten_exp (Op op xs); flatten_exp x]) /\
  (forall exp, flatten_exp (Load exp) = Load (flatten_exp exp)) /\
  (forall shift exp nexp,
     flatten_exp (Shift shift exp nexp) = Shift shift (flatten_exp exp) (flatten_exp nexp)) /\
  (forall w, flatten_exp (Const w) = Const w) /\
  (forall v, flatten_exp (Var v) = Var v) /\
  (forall s, flatten_exp (Lookup s) = Lookup s).
Proof.
  repeat split; try reflexivity.
  - intros [] ?; try reflexivity; congruence.
  - intros [] ? ?; try reflexivity; congruence.
  - intros [] x [|y ys] ? ?; try reflexivity; congruence.
Qed.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "is_Lookup_CurrHeap_def" *)
Definition is_Lookup_CurrHeap (e : exp a) : bool :=
  match e with Lookup CurrHeap => true | _ => false end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "inst_select_exp_def" *)
Fixpoint inst_select_exp (c : asm_config a) (tar temp : N) (e : exp a) {struct e} : prog a :=
  match e with
  | Load exp =>
      match exp with
      | Op asm.Add [exp'; Const w] =>
          if addr_offset_ok c w then
            let prog := inst_select_exp c temp temp exp' in
            Seq prog (Inst (Mem asm.Load tar (Addr temp w)))
          else
            let prog := inst_select_exp c temp temp exp in
            Seq prog (Inst (Mem asm.Load tar (Addr temp (n2w 0))))
      | _ =>
          let prog := inst_select_exp c temp temp exp in
          Seq prog (Inst (Mem asm.Load tar (Addr temp (n2w 0))))
      end
  | Const w => Inst (asm.Const tar w)
  | Var v => Move 0 [(tar, v)]
  | Lookup store_name => Get tar store_name
  | Op op [e1; e2] =>
      if is_Lookup_CurrHeap e2 then
        let p1 := inst_select_exp c temp temp e1 in
        Seq p1 (OpCurrHeap op tar temp)
      else if is_Lookup_CurrHeap e1 && negb (bool_decide (op = asm.Sub)) then
        let p2 := inst_select_exp c temp temp e2 in
        Seq p2 (OpCurrHeap op tar temp)
      else
      let p1 := inst_select_exp c temp temp e1 in
      match e2 with
      | Const w =>
          if valid_imm c (inl op) w then
            Seq p1 (Inst (Arith (Binop op tar temp (Imm w))))
          else if bool_decide (op = asm.Add) && valid_imm c (inl asm.Sub) (word_2comp w) then
            Seq p1 (Inst (Arith (Binop asm.Sub tar temp (Imm (word_2comp w)))))
          else
            let p2 := Inst (asm.Const (temp + 1) w) in
            Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp + 1))))))
      | _ =>
          let p2 := inst_select_exp c (temp + 1) (temp + 1) e2 in
          Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp + 1))))))
      end
  | Shift sh exp e1 =>
      match e1 with
      | Const shift_len =>
          let n := w2n shift_len in
          if n <? dimindex a then
            let prog := inst_select_exp c temp temp exp in
            if n =? 0 then Seq prog (Move 0 [(tar, temp)])
            else Seq prog (Inst (Arith (asm.Shift sh tar temp (Imm (n2w n)))))
          else Inst (asm.Const tar (n2w 0))
      | _ =>
          let p := inst_select_exp c temp temp exp in
          let p1 := inst_select_exp c (temp + 1) (temp + 1) e1 in
          Seq p (Seq p1 (Inst (Arith (asm.Shift sh tar temp (Reg (temp + 1))))))
      end
  | _ => Skip
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "inst_select_def" *)
Fixpoint inst_select (c : asm_config a) (temp : N) (p : prog a) : prog a :=
  match p with
  | Assign v exp => inst_select_exp c v temp (flatten_exp (pull_exp exp))
  | Set_ store exp =>
      let prog := inst_select_exp c temp temp (flatten_exp (pull_exp exp)) in
      Seq prog (Set_ store (Var temp))
  | Store exp var =>
      let exp := flatten_exp (pull_exp exp) in
      match exp with
      | Op asm.Add [exp'; Const w] =>
          if addr_offset_ok c w then
            let prog := inst_select_exp c temp temp exp' in
            Seq prog (Inst (Mem asm.Store var (Addr temp w)))
          else
            let prog := inst_select_exp c temp temp exp in
            Seq prog (Inst (Mem asm.Store var (Addr temp (n2w 0))))
      | _ =>
          let prog := inst_select_exp c temp temp exp in
          Seq prog (Inst (Mem asm.Store var (Addr temp (n2w 0))))
      end
  | Seq p1 p2 => Seq (inst_select c temp p1) (inst_select c temp p2)
  | MustTerminate p1 => MustTerminate (inst_select c temp p1)
  | ShareInst op v exp =>
      let exp := flatten_exp (pull_exp exp) in
      match exp with
      | Op asm.Add [exp'; Const w] =>
          if (bool_decide (op = asm.Load \/ op = asm.Store) && addr_offset_ok c w) ||
             (bool_decide (op = Load32 \/ op = Store32) && addr_offset_ok c w) ||
             (bool_decide (op = Load16 \/ op = Store16) && hw_offset_ok c w) ||
             (bool_decide (op = Load8 \/ op = Store8) && byte_offset_ok c w) then
            let prog := inst_select_exp c temp temp exp' in
            Seq prog (ShareInst op v (Op asm.Add [Var temp; Const w]))
          else
            let prog := inst_select_exp c temp temp exp in
            Seq prog (ShareInst op v (Var temp))
      | _ =>
          let prog := inst_select_exp c temp temp exp in
          Seq prog (ShareInst op v (Var temp))
      end
  | If cmp r1 ri c1 c2 => If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2)
  | Call ret dest args handler =>
      let retsel :=
        match ret with
        | None => None
        | Some (n, (names, (ret_handler, (l1, l2)))) =>
            Some (n, (names, (inst_select c temp ret_handler, (l1, l2))))
        end in
      let handlersel :=
        match handler with
        | None => None
        | Some (n, (h, (l1, l2))) => Some (n, (inst_select c temp h, (l1, l2)))
        end in
      Call retsel dest args handlersel
  | Loop names body exit_names => Loop names (inst_select c temp body) exit_names
  | prog => prog
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "three_to_two_reg_def" *)
Fixpoint three_to_two_reg (p : prog a) : prog a :=
  match p with
  | Inst (Arith (Binop bop r1 r2 ri)) =>
      Seq (Move 0 [(r1, r2)]) (Inst (Arith (Binop bop r1 r1 ri)))
  | Inst (Arith (asm.Shift l r1 r2 n)) =>
      Seq (Move 0 [(r1, r2)]) (Inst (Arith (asm.Shift l r1 r1 n)))
  | Inst (Arith (AddCarry r1 r2 r3 r4)) =>
      Seq (Move 0 [(r1, r2)]) (Inst (Arith (AddCarry r1 r1 r3 r4)))
  | Inst (Arith (AddOverflow r1 r2 r3 r4)) =>
      Seq (Move 0 [(r1, r2)]) (Inst (Arith (AddOverflow r1 r1 r3 r4)))
  | Inst (Arith (SubOverflow r1 r2 r3 r4)) =>
      Seq (Move 0 [(r1, r2)]) (Inst (Arith (SubOverflow r1 r1 r3 r4)))
  | OpCurrHeap bop r1 r2 => Seq (Move 0 [(r1, r2)]) (OpCurrHeap bop r1 r1)
  | Seq p1 p2 => Seq (three_to_two_reg p1) (three_to_two_reg p2)
  | MustTerminate p1 => MustTerminate (three_to_two_reg p1)
  | If cmp r1 ri c1 c2 => If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2)
  | Call ret dest args handler =>
      let retsel :=
        match ret with
        | None => None
        | Some (n, (names, (ret_handler, (l1, l2)))) =>
            Some (n, (names, (three_to_two_reg ret_handler, (l1, l2))))
        end in
      let handlersel :=
        match handler with
        | None => None
        | Some (n, (h, (l1, l2))) => Some (n, (three_to_two_reg h, (l1, l2)))
        end in
      Call retsel dest args handlersel
  | Loop names body exit_names => Loop names (three_to_two_reg body) exit_names
  | prog => prog
  end.

(*! HOL "cakeml/compiler/backend/word_instScript.sml" "three_to_two_reg_prog_def" *)
Definition three_to_two_reg_prog (b : bool) (p : prog a) : prog a :=
  if b then three_to_two_reg p else p.

End Inst.
