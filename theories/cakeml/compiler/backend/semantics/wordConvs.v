(** * CakeML [wordConvs]: syntactic conventions on wordLang programs

    The predicates are [bool]-valued like [wordLang]'s [every_var] (they are
    computable); in theorem statements they are read as propositions.  HOL's
    set-membership tests on literal sets ([m IN {Load; Store; ...}]) are
    [MEM] on the corresponding lists. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Galette.cakeml.compiler.backend Require Import wordLang.
From Stdlib Require Import Permutation.
Open Scope N_scope.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_def" *)
Definition labels_rel (old_labs new_labs : list (N * N)) : Prop :=
  (is_true (ALL_DISTINCT old_labs) -> is_true (ALL_DISTINCT new_labs)) /\
  set new_labs SUBSET set old_labs.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "flat_exp_conventions_def" *)
Fixpoint flat_exp_conventions (p : prog a) : bool :=
  match p with
  | Assign v exp => false
  | Store exp num => false
  | Set_ store_name (Var r) => true
  | Set_ store_name _ => false
  | ShareInst op v (Var r) => true
  | ShareInst op v (Op asm.Add [Var r; Const c]) => true
  | ShareInst op v _ => false
  | Seq p1 p2 => flat_exp_conventions p1 && flat_exp_conventions p2
  | Loop names c exit_names => flat_exp_conventions c
  | If cmp r1 ri e2 e3 => flat_exp_conventions e2 && flat_exp_conventions e3
  | MustTerminate p => flat_exp_conventions p
  | Call ret dest args h =>
      match ret with
      | NONE => true
      | SOME (v, (cutset, (ret_handler, (l1, l2)))) => flat_exp_conventions ret_handler
      end &&
      match h with
      | NONE => true
      | SOME (v, (prog0, (l1, l2))) => flat_exp_conventions prog0
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "inst_ok_less_def" *)
Definition inst_ok_less (c : asm_config a) (i : inst a) : bool :=
  match i with
  | Arith (Binop b r1 r2 (Imm w)) => valid_imm c (inl b) w
  | Arith (asm.Shift l r1 r2 (Imm i)) =>
      implb (bool_decide (i = n2w 0)) (bool_decide (l = Lsl)) && (w2n i <? dimindex a)
  | Arith (Div r1 r2 r3) => MEM (ISA c) [ARMv8; MIPS; RISC_V]
  | Arith (LongMul r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = ARMv7)) (negb (r1 =? r2)) &&
      implb (bool_decide (ISA c = ARMv8) || bool_decide (ISA c = RISC_V) || bool_decide (ISA c = Ag32))
            (negb (r1 =? r3) && negb (r1 =? r4))
  | Arith (LongDiv r1 r2 r3 r4 r5) => bool_decide (ISA c = x86_64)
  | Arith (AddCarry r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V))
            (negb (r1 =? r3) && negb (r1 =? r4))
  | Arith (AddOverflow r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V)) (negb (r1 =? r3))
  | Arith (SubOverflow r1 r2 r3 r4) =>
      implb (bool_decide (ISA c = MIPS) || bool_decide (ISA c = RISC_V)) (negb (r1 =? r3))
  | Mem m r (Addr r' w) =>
      if MEM m [asm.Load; asm.Store; Load16; Store16; Load32; Store32]
      then addr_offset_ok c w
      else if MEM m [Load16; Store16]
      then hw_offset_ok c w
      else byte_offset_ok c w
  | FP (FPLess r d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPLessEqual r d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPEqual r d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPAbs d1 d2) => implb (two_reg_arith c) (negb (d1 =? d2)) && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPNeg d1 d2) => implb (two_reg_arith c) (negb (d1 =? d2)) && fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPSqrt d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPAdd d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPSub d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPMul d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPDiv d1 d2 d3) =>
      implb (two_reg_arith c) (d1 =? d2) && fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPFma d1 d2 d3) =>
      bool_decide (ISA c = ARMv7) && (2 <? fp_reg_count c) &&
      fp_reg_ok d1 c && fp_reg_ok d2 c && fp_reg_ok d3 c
  | FP (FPMov d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPMovToReg r1 r2 d) => implb (dimindex a =? 32) (negb (r1 =? r2)) && fp_reg_ok d c
  | FP (FPMovFromReg d r1 r2) => implb (dimindex a =? 32) (negb (r1 =? r2)) && fp_reg_ok d c
  | FP (FPToInt d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | FP (FPFromInt d1 d2) => fp_reg_ok d1 c && fp_reg_ok d2 c
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "distinct_tar_reg_def" *)
Definition distinct_tar_reg (i : inst a) : bool :=
  match i with
  | Arith (Binop bop r1 r2 ri) => negb (bool_decide (ri = Reg r1))
  | Arith (asm.Shift l r1 r2 ri) => negb (bool_decide (ri = Reg r1))
  | Arith (AddCarry r1 r2 r3 r4) => negb (r1 =? r3) && negb (r1 =? r4)
  | Arith (AddOverflow r1 r2 r3 r4) => negb (r1 =? r3)
  | Arith (SubOverflow r1 r2 r3 r4) => negb (r1 =? r3)
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "two_reg_inst_def" *)
Definition two_reg_inst (i : inst a) : bool :=
  match i with
  | Arith (Binop bop r1 r2 ri) => r1 =? r2
  | Arith (asm.Shift l r1 r2 ri) => r1 =? r2
  | Arith (AddCarry r1 r2 r3 r4) => r1 =? r2
  | Arith (AddOverflow r1 r2 r3 r4) => r1 =? r2
  | Arith (SubOverflow r1 r2 r3 r4) => r1 =? r2
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_inst_def" *)
Fixpoint every_inst (P : inst a -> bool) (p : prog a) : bool :=
  match p with
  | Inst i => P i
  | Seq p1 p2 => every_inst P p1 && every_inst P p2
  | Loop names c exit_names => every_inst P c
  | If cmp r1 ri c1 c2 => every_inst P c1 && every_inst P c2
  | OpCurrHeap bop r1 r2 => P (Arith (Binop bop r1 r2 (Reg r2)))
  | MustTerminate p => every_inst P p
  | Call ret dest args handler =>
      match ret with
      | NONE => true
      | SOME (n, (names, (ret_handler, (l1, l2)))) =>
          every_inst P ret_handler &&
          match handler with
          | NONE => true
          | SOME (n, (h, (l1, l2))) => every_inst P h
          end
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "full_inst_ok_less_def" *)
Fixpoint full_inst_ok_less (c : asm_config a) (p : prog a) : bool :=
  match p with
  | Inst i => inst_ok_less c i
  | Seq p1 p2 => full_inst_ok_less c p1 && full_inst_ok_less c p2
  | Loop names p exit_names => full_inst_ok_less c p
  | If cmp r1 ri c1 c2 => full_inst_ok_less c c1 && full_inst_ok_less c c2
  | MustTerminate p => full_inst_ok_less c p
  | Call ret dest args handler =>
      match ret with
      | NONE => true
      | SOME (n, (names, (ret_handler, (l1, l2)))) =>
          full_inst_ok_less c ret_handler &&
          match handler with
          | NONE => true
          | SOME (n, (h, (l1, l2))) => full_inst_ok_less c h
          end
      end
  | ShareInst op r ad =>
      match exp_to_addr ad with
      | SOME (Addr _ w) =>
          if MEM op [asm.Load; asm.Store; Load32; Store32]
          then addr_offset_ok c w
          else if MEM op [Load16; Store16]
          then hw_offset_ok c w
          else byte_offset_ok c w
      | NONE => false
      end
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "wf_names_def" *)
Definition wf_names {A B} (t : spt A * spt B) : bool := wf (FST t) && wf (SND t).

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "wf_cutsets_def" *)
Fixpoint wf_cutsets (p : prog a) : bool :=
  match p with
  | Alloc n s => wf_names s
  | Install _ _ _ _ s => wf_names s
  | Call ret dest args h =>
      match ret with
      | NONE => true
      | SOME (v, (cutset, (ret_handler, (l1, l2)))) =>
          wf_names cutset && wf_cutsets ret_handler &&
          match h with
          | NONE => true
          | SOME (v, (prog0, (l1, l2))) => wf_cutsets prog0
          end
      end
  | FFI x1 y1 x2 y2 z args => wf_names args
  | MustTerminate s => wf_cutsets s
  | Seq s1 s2 => wf_cutsets s1 && wf_cutsets s2
  | Loop names p exit_names => wf names && wf exit_names && wf_cutsets p
  | If cmp r1 ri e2 e3 => wf_cutsets e2 && wf_cutsets e3
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "inst_arg_convention_def" *)
Definition inst_arg_convention (i : inst a) : bool :=
  match i with
  | Arith (AddCarry r1 r2 r3 r4) => r4 =? 0
  | Arith (asm.Shift _ _ _ (Reg r)) => r =? 8
  | Arith (AddOverflow r1 r2 r3 r4) => r4 =? 0
  | Arith (SubOverflow r1 r2 r3 r4) => r4 =? 0
  | Arith (LongMul r1 r2 r3 r4) => (r1 =? 6) && (r2 =? 0) && (r3 =? 0) && (r4 =? 4)
  | Arith (LongDiv r1 r2 r3 r4 r5) => (r1 =? 0) && (r2 =? 6) && (r3 =? 6) && (r4 =? 0)
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "call_arg_convention_def" *)
Fixpoint call_arg_convention (p : prog a) : bool :=
  match p with
  | Inst i => inst_arg_convention i
  | Return x ys => bool_decide (ys = GENLIST (fun x => 2 * (x + 1)) (LENGTH ys))
  | Raise y => y =? 2
  | Install ptr len _ _ _ => (ptr =? 2) && (len =? 4)
  | FFI x ptr len ptr2 len2 args => (ptr =? 2) && (len =? 4) && (ptr2 =? 6) && (len2 =? 8)
  | Alloc n s => n =? 2
  | StoreConsts a0 b c d ws => (a0 =? 0) && (b =? 2) && (c =? 4) && (d =? 6)
  | Call ret dest args h =>
      match ret with
      | NONE => bool_decide (args = GENLIST (fun x => 2 * x) (LENGTH args))
      | SOME (vs, (cutset, (ret_handler, (l1, l2)))) =>
          bool_decide (args = GENLIST (fun x => 2 * (x + 1)) (LENGTH args)) &&
          bool_decide (vs = GENLIST (fun x => 2 * (x + 1)) (LENGTH vs)) &&
          call_arg_convention ret_handler &&
          match h with
          | NONE => true
          | SOME (v, (prog0, (l1, l2))) => (v =? 2) && call_arg_convention prog0
          end
      end
  | MustTerminate s1 => call_arg_convention s1
  | Seq s1 s2 => call_arg_convention s1 && call_arg_convention s2
  | Loop names p exit_names => call_arg_convention p
  | If cmp r1 ri e2 e3 => call_arg_convention e2 && call_arg_convention e3
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "pre_alloc_conventions_def" *)
Definition pre_alloc_conventions (p : prog a) : bool :=
  every_stack_var is_stack_var p && call_arg_convention p.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "post_alloc_conventions_def" *)
Definition post_alloc_conventions (k : N) (prog0 : prog a) : bool :=
  every_var is_phy_var prog0 && every_stack_var (fun x => 2 * k <=? x) prog0 &&
  call_arg_convention prog0.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "extract_labels_def" *)
Fixpoint extract_labels (p : prog a) : list (N * N) :=
  match p with
  | Call ret dest args h =>
      match ret with
      | NONE => []
      | SOME (v, (cutset, (ret_handler, (l1, l2)))) =>
          let ret_rest := extract_labels ret_handler in
          match h with
          | NONE => [(l1, l2)] ++ ret_rest
          | SOME (v, (prog0, (l1', l2'))) =>
              let h_rest := extract_labels prog0 in
              [(l1, l2); (l1', l2')] ++ ret_rest ++ h_rest
          end
      end
  | MustTerminate s1 => extract_labels s1
  | Seq s1 s2 => extract_labels s1 ++ extract_labels s2
  | Loop names p exit_names => extract_labels p
  | If cmp r1 ri e2 e3 => extract_labels e2 ++ extract_labels e3
  | _ => []
  end.

End Defs.

(** ** Galette-only infrastructure: nested induction principles *)

Section Ind.
Context {a : N}.

(** Induction on [prog] with induction hypotheses for the programs nested
    in the arguments of [Call]. *)
Lemma prog_nested_ind (P : prog a -> Prop)
    (Hskip : P Skip)
    (Hmove : forall pri moves, P (Move pri moves))
    (Hinst : forall i, P (Inst i))
    (Hassign : forall v e, P (Assign v e))
    (Hget : forall v n, P (Get v n))
    (Hset : forall v e, P (Set_ v e))
    (Hstore : forall e v, P (Store e v))
    (Hmt : forall p, P p -> P (MustTerminate p))
    (Hcall : forall ret dest args h,
        match ret with Some (_, (_, (p, _))) => P p | None => True end ->
        match h with Some (_, (p, _)) => P p | None => True end ->
        P (Call ret dest args h))
    (Hseq : forall p1 p2, P p1 -> P p2 -> P (Seq p1 p2))
    (Hif : forall c r ri p1 p2, P p1 -> P p2 -> P (If c r ri p1 p2))
    (Hloop : forall n1 p n2, P p -> P (Loop n1 p n2))
    (Halloc : forall n names, P (Alloc n names))
    (Hsc : forall a0 b c d ws, P (StoreConsts a0 b c d ws))
    (Hraise : forall n, P (Raise n))
    (Hret : forall n ns, P (Return n ns))
    (Hbrk : forall n, P (Break n))
    (Hcont : forall n, P (Continue n))
    (Htick : P Tick)
    (Hoch : forall b n1 n2, P (OpCurrHeap b n1 n2))
    (Hlocv : forall r l, P (LocValue r l))
    (Hinstall : forall r1 r2 r3 r4 names, P (Install r1 r2 r3 r4 names))
    (Hcbw : forall r1 r2, P (CodeBufferWrite r1 r2))
    (Hdbw : forall r1 r2, P (DataBufferWrite r1 r2))
    (Hffi : forall s r1 r2 r3 r4 names, P (FFI s r1 r2 r3 r4 names))
    (Hshare : forall op v e, P (ShareInst op v e))
    : forall p : prog a, P p.
Proof.
  fix rec 1; intros p; destruct p.
  - apply Hskip.
  - apply Hmove.
  - apply Hinst.
  - apply Hassign.
  - apply Hget.
  - apply Hset.
  - apply Hstore.
  - apply Hmt, rec.
  - apply Hcall.
    + destruct o as [[? [? [p ?]]]|]; [apply rec|exact Logic.I].
    + destruct o1 as [[? [p ?]]|]; [apply rec|exact Logic.I].
  - apply Hseq; apply rec.
  - apply Hif; apply rec.
  - apply Hloop, rec.
  - apply Halloc.
  - apply Hsc.
  - apply Hraise.
  - apply Hret.
  - apply Hbrk.
  - apply Hcont.
  - apply Htick.
  - apply Hoch.
  - apply Hlocv.
  - apply Hinstall.
  - apply Hcbw.
  - apply Hdbw.
  - apply Hffi.
  - apply Hshare.
Qed.

(** Induction on [exp] with induction hypotheses for the arguments of
    [Op]. *)
Fixpoint exp_nested_ind (P : exp a -> Prop)
    (Hc : forall w, P (Const w)) (Hv : forall n, P (Var n)) (Hl : forall n, P (Lookup n))
    (Hld : forall e, P e -> P (Load e))
    (Hop : forall op es, Forall P es -> P (Op op es))
    (Hsh : forall s e1 e2, P e1 -> P e2 -> P (Shift s e1 e2)) (e : exp a) : P e :=
  let rec := exp_nested_ind P Hc Hv Hl Hld Hop Hsh in
  let fix go (l : list (exp a)) : Forall P l :=
    match l with [] => Forall_nil _ | x :: xs => Forall_cons _ (rec x) (go xs) end in
  match e with
  | Const w => Hc w
  | Var n => Hv n
  | Lookup n => Hl n
  | Load e => Hld e (rec e)
  | Op op es => Hop op es (go es)
  | Shift s e1 e2 => Hsh s e1 e2 (rec e1) (rec e2)
  end.

End Ind.

(** Boolean reasoning: split conjunctions of booleans in the context and
    the goal. *)
Ltac bool_simpl :=
  unfold is_true in *;
  repeat match goal with
         | H : is_true (_ && _) |- _ => apply andb_true_iff in H; destruct H
         | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
         | |- is_true (_ && _) => apply andb_true_iff; split
         | |- (_ && _) = true => apply andb_true_iff; split
         end.

(** Case split the instruction structure (asm [inst], [arith], [fp],
    [addr], [reg_imm]). *)
Ltac destruct_inst i :=
  destruct i as [|? ?|[? ? ? []|? ? ? []|? ? ?|? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?]
                |[] ? [? ?]|[]].

(** ** Monotonicity and conjunction lemmas *)

Section Mono.
Context {a : N}.

Local Lemma EVERY_mono {A} (P Q : A -> bool) l :
  (forall x, P x -> Q x) -> EVERY P l -> EVERY Q l.
Proof.
  intros HPQ; induction l as [|x l IH]; cbn; [auto|].
  intros H; bool_simpl; auto.
Qed.

Local Lemma EVERY_conj {A} (P Q : A -> bool) l :
  EVERY P l && EVERY Q l = EVERY (fun x => P x && Q x) l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite <- IH; destruct (P x), (Q x), (EVERY P l), (EVERY Q l); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_inst_mono" *)
Theorem every_var_inst_mono : forall (P : N -> bool) (inst : asm.inst a) (Q : N -> bool),
  (forall x, P x -> Q x) /\ every_var_inst P inst -> every_var_inst Q inst.
Proof.
  intros P i Q [HPQ H]; destruct_inst i; unfold every_var_inst, every_var_imm in *;
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    bool_simpl; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_exp_mono" *)
Theorem every_var_exp_mono : forall (P : N -> bool) (exp : exp a) (Q : N -> bool),
  (forall x, P x -> Q x) /\ every_var_exp P exp -> every_var_exp Q exp.
Proof.
  intros P e Q [HPQ H]; revert H.
  induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [every_var_exp]; intros H; bool_simpl; auto.
  unfold is_true in *; rewrite EVERY_Forall in *.
  rewrite Forall_forall in *; intros x Hx; apply IH; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_name_mono" *)
Theorem every_name_mono : forall (P : N -> bool) (names : cutsets) (Q : N -> bool),
  (forall x, P x -> Q x) /\ every_name P names -> every_name Q names.
Proof.
  intros P names Q [HPQ H]; unfold every_name in *; bool_simpl; eapply EVERY_mono; eauto.
Qed.

Local Ltac mono_tac :=
  solve [ eauto
        | eapply EVERY_mono; eauto
        | eapply every_var_inst_mono; split; eauto
        | eapply every_var_exp_mono; split; eauto
        | eapply every_name_mono; split; eauto ].

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_mono" *)
Theorem every_var_mono : forall (P : N -> bool) (prog : prog a) (Q : N -> bool),
  (forall x, P x -> Q x) /\ every_var P prog -> every_var Q prog.
Proof.
  intros P p Q [HPQ H]; revert H.
  induction p as [| | | | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|c r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [every_var]; intros Hv0;
    try (destruct ri); unfold every_var_imm in *; bool_simpl;
    try mono_tac.
  destruct ret as [[v [cs [rh [l1 l2]]]]|]; [|reflexivity].
  destruct h as [[hv [hp [hl1 hl2]]]|]; bool_simpl; mono_tac.
Qed.


Local Lemma every_var_inst_conj_eq (P Q : N -> bool) (i : asm.inst a) :
  every_var_inst P i && every_var_inst Q i = every_var_inst (fun x => P x && Q x) i.
Proof.
  destruct_inst i; unfold every_var_inst, every_var_imm;
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    repeat match goal with |- context [P ?x] => destruct (P x) end;
    repeat match goal with |- context [Q ?x] => destruct (Q x) end; reflexivity.
Qed.

Local Lemma every_var_exp_conj_eq (P Q : N -> bool) (e : exp a) :
  every_var_exp P e && every_var_exp Q e = every_var_exp (fun x => P x && Q x) e.
Proof.
  induction e as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [every_var_exp]; try reflexivity; try assumption.
  - induction IH as [|x l Hx Hl IHl]; cbn [EVERY]; [reflexivity|].
    rewrite <- Hx, <- IHl.
    destruct (every_var_exp P x), (every_var_exp Q x),
      (EVERY (every_var_exp P) l), (EVERY (every_var_exp Q) l); reflexivity.
  - rewrite <- IH1, <- IH2; destruct (every_var_exp P e1), (every_var_exp Q e1),
      (every_var_exp P e2), (every_var_exp Q e2); reflexivity.
Qed.

Local Lemma every_name_conj_eq (P Q : N -> bool) (names : cutsets) :
  every_name P names && every_name Q names = every_name (fun x => P x && Q x) names.
Proof.
  unfold every_name; rewrite <- !EVERY_conj.
  destruct (EVERY P _), (EVERY Q _), (EVERY P _), (EVERY Q _); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_inst_conj" *)
Theorem every_var_inst_conj : forall (P : N -> bool) (inst : asm.inst a) (Q : N -> bool),
  every_var_inst P inst /\ every_var_inst Q inst <->
  every_var_inst (fun x => P x && Q x) inst.
Proof. intros; unfold is_true; rewrite <- every_var_inst_conj_eq, andb_true_iff; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_exp_conj" *)
Theorem every_var_exp_conj : forall (P : N -> bool) (exp : exp a) (Q : N -> bool),
  every_var_exp P exp /\ every_var_exp Q exp <->
  every_var_exp (fun x => P x && Q x) exp.
Proof. intros; unfold is_true; rewrite <- every_var_exp_conj_eq, andb_true_iff; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_name_conj" *)
Theorem every_name_conj : forall (P : N -> bool) (names : cutsets) (Q : N -> bool),
  every_name P names /\ every_name Q names <->
  every_name (fun x => P x && Q x) names.
Proof. intros; unfold is_true; rewrite <- every_name_conj_eq, andb_true_iff; reflexivity. Qed.

Local Ltac andb_eq := apply Bool.eq_iff_eq_true; rewrite ?andb_true_iff; tauto.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_conj" *)
Theorem every_var_conj : forall (P : N -> bool) (prog : prog a) (Q : N -> bool),
  every_var P prog /\ every_var Q prog <->
  every_var (fun x => P x && Q x) prog.
Proof.
  intros P p Q; unfold is_true; rewrite <- andb_true_iff.
  apply Bool.eq_iff_eq_true.
  induction p as [| | | | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|c r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [every_var];
    rewrite <- ?every_var_inst_conj_eq, <- ?every_var_exp_conj_eq, <- ?every_name_conj_eq,
      <- ?EVERY_conj;
    try (destruct ri; unfold every_var_imm);
    try (rewrite <- IHp); try (rewrite <- IHp1, <- IHp2); try andb_eq.
  destruct ret as [[v [cs [rh [l1 l2]]]]|]; [|andb_eq].
  rewrite <- every_name_conj_eq, <- EVERY_conj, <- Hr.
  destruct h as [[hv [hp [hl1 hl2]]]|]; [rewrite <- Hh|]; andb_eq.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_var_imp_every_stack_var" *)
Theorem every_var_imp_every_stack_var : forall (P : N -> bool) (prog : prog a),
  every_var P prog -> every_stack_var P prog.
Proof.
  intros P p; induction p using prog_nested_ind; cbn [every_var every_stack_var];
    intros Hv; bool_simpl; auto.
  destruct ret as [[v [cs [rh [l1 l2]]]]|]; [|reflexivity].
  destruct h as [[hv [hp [hl1 hl2]]]|]; bool_simpl; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_stack_var_mono" *)
Theorem every_stack_var_mono : forall (P : N -> bool) (prog : prog a) (Q : N -> bool),
  (forall x, P x -> Q x) /\ every_stack_var P prog -> every_stack_var Q prog.
Proof.
  intros P p Q [HPQ H]; revert H.
  induction p as [| | | | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|c r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [every_stack_var]; intros Hv0; bool_simpl; try mono_tac.
  destruct ret as [[v [cs [rh [l1 l2]]]]|]; [|reflexivity].
  destruct h as [[hv [hp [hl1 hl2]]]|]; bool_simpl; mono_tac.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "every_stack_var_conj" *)
Theorem every_stack_var_conj : forall (P : N -> bool) (prog : prog a) (Q : N -> bool),
  every_stack_var P prog /\ every_stack_var Q prog <->
  every_stack_var (fun x => P x && Q x) prog.
Proof.
  intros P p Q; unfold is_true; rewrite <- andb_true_iff.
  apply Bool.eq_iff_eq_true.
  pose proof (every_name_conj_eq P Q) as Hn.
  induction p as [| | | | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|c r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [every_stack_var]; rewrite <- ?Hn;
    try (rewrite <- IHp); try (rewrite <- IHp1, <- IHp2);
    try andb_eq.
  destruct ret as [[v [cs [rh [l1 l2]]]]|]; [|reflexivity].
  rewrite <- Hn, <- Hr.
  destruct h as [[hv [hp [hl1 hl2]]]|]; [rewrite <- Hh|]; andb_eq.
Qed.

End Mono.

(** ** [labels_rel] *)

Section LabelsRel.

Local Lemma ALL_DISTINCT_app (l1 l2 : list (N * N)) :
  is_true (ALL_DISTINCT (l1 ++ l2)) <->
  is_true (ALL_DISTINCT l1) /\ is_true (ALL_DISTINCT l2) /\
  (forall x, In x l1 -> ~ In x l2).
Proof.
  unfold is_true; rewrite !ALL_DISTINCT_NoDup; split.
  - intros H; split; [eapply NoDup_app_remove_r; eauto|split; [eapply NoDup_app_remove_l; eauto|]].
    clear -H; induction l1 as [|y l1 IH]; intros x Hx; [destruct Hx|].
    inversion H as [|? ? Hy Hd]; subst. destruct Hx as [<-|Hx]; [|apply IH; auto].
    intros Hin; apply Hy, in_or_app; right; exact Hin.
  - intros [H1 [H2 H3]]; apply NoDup_app; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_refl" *)
Theorem labels_rel_refl : forall xs, labels_rel xs xs.
Proof. intros xs; split; [auto|intros x Hx; exact Hx]. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_APPEND" *)
Theorem labels_rel_APPEND : forall xs xs1 ys ys1,
  labels_rel xs xs1 /\ labels_rel ys ys1 -> labels_rel (xs ++ ys) (xs1 ++ ys1).
Proof.
  intros xs xs1 ys ys1 [[Hd1 Hs1] [Hd2 Hs2]]; unfold pred_set.SUBSET in *; split.
  - rewrite !ALL_DISTINCT_app. intros [A1 [A2 A3]]; split; [auto|split; [auto|]].
    intros x Hx Hy. apply (A3 x); [apply IN_set, Hs1, IN_set, Hx|apply IN_set, Hs2, IN_set, Hy].
  - intros x Hx. rewrite IN_set in *. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app;
      [left; apply IN_set, Hs1, IN_set, Hx|right; apply IN_set, Hs2, IN_set, Hx].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_CONS" *)
Theorem labels_rel_CONS : forall x x1 ys ys1,
  labels_rel [x] [x1] /\ labels_rel ys ys1 -> labels_rel (x :: ys) (x1 :: ys1).
Proof. intros x x1 ys ys1 H; exact (labels_rel_APPEND [x] [x1] ys ys1 H). Qed.

(** HOL's [PERM_IMP_labels_rel], with Rocq's [Permutation] for HOL's
    [sorting$PERM] (not ported). *)
Theorem PERM_IMP_labels_rel : forall xs ys,
  Permutation xs ys -> labels_rel ys xs.
Proof.
  intros xs ys HP; split.
  - unfold is_true; rewrite !ALL_DISTINCT_NoDup; intros H.
    eapply Permutation_NoDup; [symmetry; exact HP|exact H].
  - intros x Hx; rewrite IN_set in *; eapply Permutation_in; eauto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_TRANS" *)
Theorem labels_rel_TRANS : forall xs ys zs,
  labels_rel xs ys /\ labels_rel ys zs -> labels_rel xs zs.
Proof.
  intros xs ys zs [[H1 H2] [H3 H4]]; split; [auto|].
  intros x Hx; apply H2, H4, Hx.
Qed.

End LabelsRel.

(** ** [max_var] *)

Section MaxVar.
Context {a : N}.

Local Lemma MAX_cases m n : MAX m n = m \/ MAX m n = n.
Proof. unfold MAX; destruct (m <? n); auto. Qed.

Local Lemma max3_cases x y z : max3 x y z = x \/ max3 x y z = y \/ max3 x y z = z.
Proof. unfold max3; destruct (y <? x), (x <? z), (y <? z); auto. Qed.

Local Lemma MAX_LIST_P (P : N -> bool) l : P 0 -> EVERY P l -> P (MAX_LIST l).
Proof.
  intros H0; induction l as [|x l IH]; cbn [MAX_LIST EVERY]; [auto|].
  intros H; apply andb_true_iff in H as [H1 H2].
  destruct (MAX_cases x (MAX_LIST l)) as [->| ->]; [exact H1|apply IH, H2].
Qed.

Local Lemma max_var_exp_IMP (P : N -> bool) (exp : exp a) :
  P 0 /\ every_var_exp P exp -> P (max_var_exp exp).
Proof.
  intros [H0 H]; revert H.
  induction exp as [w|n|n|e IH|op es IH|sh e1 e2 IH1 IH2] using exp_nested_ind;
    cbn [max_var_exp every_var_exp]; intros H; auto.
  - apply MAX_LIST_P; [exact H0|].
    unfold is_true in *; apply EVERY_Forall in H; apply EVERY_Forall; rewrite Forall_map.
    rewrite Forall_forall in *; intros x Hx; apply IH; [exact Hx|apply H, Hx].
  - apply andb_true_iff in H as [Ha Hb].
    destruct (MAX_cases (max_var_exp e1) (max_var_exp e2)) as [->| ->]; auto.
Qed.

Local Ltac maxes :=
  repeat match goal with
         | |- context [MAX ?x ?y] =>
             let E := fresh "M" in destruct (MAX_cases x y) as [E|E]; rewrite E; clear E
         | |- context [max3 ?x ?y ?z] =>
             let E := fresh "M" in destruct (max3_cases x y z) as [E|[E|E]]; rewrite E; clear E
         end.

Local Lemma EVERY_app_true {A} (P : A -> bool) l1 l2 :
  EVERY P l1 = true /\ EVERY P l2 = true -> EVERY P (l1 ++ l2) = true.
Proof.
  intros [H1 H2]; induction l1 as [|x l1 IH]; cbn; [exact H2|].
  cbn in H1; apply andb_true_iff in H1 as [Hx Hl]; rewrite Hx, IH; auto.
Qed.

Local Ltac fin :=
  repeat first
    [ assumption
    | reflexivity
    | apply max_var_exp_IMP; split; assumption
    | apply MAX_LIST_P; [assumption|]
    | progress cbn [EVERY]
    | apply andb_true_iff; split
    | apply EVERY_app_true; split ].

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "max_var_intro" *)
Theorem max_var_intro : forall (P : N -> bool) (prog : prog a),
  P 0 /\ every_var P prog -> P (max_var prog).
Proof.
  intros P p [H0 H]; revert H.
  induction p as [| | i| | | | |p IHp|ret dest args h Hr Hh|p1 p2 IHp1 IHp2|c r ri p1 p2 IHp1 IHp2
                 |n1 p n2 IHp| | | | | | | | | | | | | |] using prog_nested_ind;
    cbn [max_var every_var]; intros Hv; bool_simpl; cbn zeta.
  all: try (destruct ri; cbn zeta).
  all: unfold every_name, cutsets_max, every_var_imm in *; bool_simpl.
  all: try solve [maxes; auto; fin].
  - (* Inst *)
    destruct_inst i; unfold every_var_inst, max_var_inst, every_var_imm in *;
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
      repeat match goal with H : context [if ?c then _ else _] |- _ => destruct c end;
      bool_simpl; maxes; auto.
  - (* Call *)
    destruct ret as [[v [cs [rh [l1 l2]]]]|]; [|fin].
    unfold every_name in *.
    destruct h as [[hv [hp [hl1 hl2]]]|]; bool_simpl; maxes; auto; fin.
Qed.

End MaxVar.

(** ** Code labels *)

Section CodeLabels.
Context {a : N}.

(** HOL's set of code labels ([num set]); a [Prop]-valued predicate. *)
(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "get_code_labels_def" *)
Fixpoint get_code_labels (p : prog a) : N -> Prop :=
  match p with
  | Call r d a0 h =>
      match d with SOME x => x INSERT {} | _ => {} end
      UNION match r with SOME (_, (_, (x, _))) => get_code_labels x | _ => {} end
      UNION match h with SOME (_, (x, (l1, l2))) => get_code_labels x | _ => {} end
  | Seq p1 p2 => get_code_labels p1 UNION get_code_labels p2
  | Loop names p exit_names => get_code_labels p
  | If _ _ _ p1 p2 => get_code_labels p1 UNION get_code_labels p2
  | MustTerminate p => get_code_labels p
  | LocValue _ l1 => l1 INSERT {}
  | _ => {}
  end.

End CodeLabels.

Section CodeLabels2.
Context {a : N}.

(** Handler labels point only within the current table entry. *)
(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "good_handlers_def" *)
Fixpoint good_handlers (n : N) (p : prog a) : bool :=
  match p with
  | Call r d a0 h =>
      match r with
      | NONE => true
      | SOME (_, (_, (x, _))) =>
          good_handlers n x &&
          match h with SOME (_, (x, (l1, _))) => (l1 =? n) && good_handlers n x | _ => true end
      end
  | Seq p1 p2 => good_handlers n p1 && good_handlers n p2
  | Loop names p exit_names => good_handlers n p
  | If _ _ _ p1 p2 => good_handlers n p1 && good_handlers n p2
  | MustTerminate p => good_handlers n p
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "good_code_labels_def" *)
Definition good_code_labels (p : list (N * (N * prog a))) (elabs : N -> Prop) : Prop :=
  is_true (EVERY (fun '(n, (m, pp)) => good_handlers n pp) p) /\
  BIGUNION (set (MAP (fun '(n, (m, pp)) => get_code_labels pp) p)) SUBSET
  (set (MAP FST p) UNION elabs).

(** Syntactic elements that some phases may remove but not create.  HOL's
    [P] is a boolean predicate on programs and the result a [bool]; both are
    [Prop]-valued here (HOL's [P]s are disequalities of programs). *)
(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "not_created_subprogs_def" *)
Fixpoint not_created_subprogs (P : prog a -> Prop) (p : prog a) : Prop :=
  match p with
  | MustTerminate p => P (MustTerminate Skip) /\ not_created_subprogs P p
  | Seq p1 p2 => not_created_subprogs P p1 /\ not_created_subprogs P p2
  | Loop names c exit_names => not_created_subprogs P c
  | If _ _ _ p1 p2 => not_created_subprogs P p1 /\ not_created_subprogs P p2
  | Call r dest args h =>
      P (Call NONE dest [] NONE) /\
      match r with NONE => True | SOME (_, (_, (p, _))) => not_created_subprogs P p end /\
      match h with
      | NONE => True
      | SOME (_, (p, (h1, _))) =>
          P (Call NONE NONE [] (SOME (0, (Skip, (h1, 0))))) /\ not_created_subprogs P p
      end
  | Alloc _ _ => P (Alloc 0 (LN, LN))
  | LocValue _ l => P (LocValue 0 l)
  | ShareInst _ _ _ => P (ShareInst ARB 0 (Var 0))
  | Install _ _ _ _ _ => P (Install 0 0 0 0 (LN, LN))
  | _ => True
  end.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "not_created_subprogs_P_def" *)
Theorem not_created_subprogs_P_def : forall (P : prog a -> Prop),
  (forall p, not_created_subprogs P (MustTerminate p) = (P (MustTerminate Skip) /\ not_created_subprogs P p)) /\
  (forall p1 p2, not_created_subprogs P (Seq p1 p2) = (not_created_subprogs P p1 /\ not_created_subprogs P p2)) /\
  (forall names c exit_names, not_created_subprogs P (Loop names c exit_names) = not_created_subprogs P c) /\
  (forall v0 v1 v2 p1 p2, not_created_subprogs P (If v0 v1 v2 p1 p2) = (not_created_subprogs P p1 /\ not_created_subprogs P p2)) /\
  (forall r dest args h, not_created_subprogs P (Call r dest args h) =
      (P (Call NONE dest [] NONE) /\
       match r with NONE => True | SOME (_, (_, (p, _))) => not_created_subprogs P p end /\
       match h with
       | NONE => True
       | SOME (_, (p, (h1, _))) =>
           P (Call NONE NONE [] (SOME (0, (Skip, (h1, 0))))) /\ not_created_subprogs P p
       end)) /\
  (forall v0 v1, not_created_subprogs P (Alloc v0 v1) = P (Alloc 0 (LN, LN))) /\
  (forall v0 l, not_created_subprogs P (LocValue v0 l) = P (LocValue 0 l)) /\
  (forall v0 v1 v2, not_created_subprogs P (ShareInst v0 v1 v2) = P (ShareInst ARB 0 (Var 0))) /\
  (forall v0 v1 v2 v3 v4, not_created_subprogs P (Install v0 v1 v2 v3 v4) = P (Install 0 0 0 0 (LN, LN))) /\
  (not_created_subprogs P (Skip) = True) /\
  (forall v0 v1, not_created_subprogs P (Move v0 v1) = True) /\
  (forall v0, not_created_subprogs P (Inst v0) = True) /\
  (forall v0 v1, not_created_subprogs P (Assign v0 v1) = True) /\
  (forall v0 v1, not_created_subprogs P (Get v0 v1) = True) /\
  (forall v0 v1, not_created_subprogs P (Set_ v0 v1) = True) /\
  (forall v0 v1, not_created_subprogs P (Store v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4, not_created_subprogs P (StoreConsts v0 v1 v2 v3 v4) = True) /\
  (forall v0, not_created_subprogs P (Raise v0) = True) /\
  (forall v0 v1, not_created_subprogs P (Return v0 v1) = True) /\
  (forall v0, not_created_subprogs P (Break v0) = True) /\
  (forall v0, not_created_subprogs P (Continue v0) = True) /\
  (not_created_subprogs P (Tick) = True) /\
  (forall v0 v1 v2, not_created_subprogs P (OpCurrHeap v0 v1 v2) = True) /\
  (forall v0 v1, not_created_subprogs P (CodeBufferWrite v0 v1) = True) /\
  (forall v0 v1, not_created_subprogs P (DataBufferWrite v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4 v5, not_created_subprogs P (FFI v0 v1 v2 v3 v4 v5) = True).
Proof. intros P; repeat split; intros; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_alloc_subprogs_def" *)
Definition no_alloc (p : prog a) : Prop := not_created_subprogs (fun q => Alloc 0 (LN, LN) <> q) p.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_alloc_def" *)
Theorem no_alloc_def :
  (forall p, no_alloc (MustTerminate p) = (@Alloc a 0 (LN, LN) <> (MustTerminate Skip) /\ no_alloc p)) /\
  (forall p1 p2, no_alloc (Seq p1 p2) = (no_alloc p1 /\ no_alloc p2)) /\
  (forall names c exit_names, no_alloc (Loop names c exit_names) = no_alloc c) /\
  (forall v0 v1 v2 p1 p2, no_alloc (If v0 v1 v2 p1 p2) = (no_alloc p1 /\ no_alloc p2)) /\
  (forall r dest args h, no_alloc (Call r dest args h) =
      (@Alloc a 0 (LN, LN) <> (Call NONE dest [] NONE) /\
       match r with NONE => True | SOME (_, (_, (p, _))) => no_alloc p end /\
       match h with
       | NONE => True
       | SOME (_, (p, (h1, _))) =>
           @Alloc a 0 (LN, LN) <> (Call NONE NONE [] (SOME (0, (Skip, (h1, 0))))) /\ no_alloc p
       end)) /\
  (forall v0 v1, no_alloc (Alloc v0 v1) = (@Alloc a 0 (LN, LN) <> (Alloc 0 (LN, LN)))) /\
  (forall v0 l, no_alloc (LocValue v0 l) = (@Alloc a 0 (LN, LN) <> (LocValue 0 l))) /\
  (forall v0 v1 v2, no_alloc (ShareInst v0 v1 v2) = (@Alloc a 0 (LN, LN) <> (ShareInst ARB 0 (Var 0)))) /\
  (forall v0 v1 v2 v3 v4, no_alloc (Install v0 v1 v2 v3 v4) = (@Alloc a 0 (LN, LN) <> (Install 0 0 0 0 (LN, LN)))) /\
  (no_alloc (Skip) = True) /\
  (forall v0 v1, no_alloc (Move v0 v1) = True) /\
  (forall v0, no_alloc (Inst v0) = True) /\
  (forall v0 v1, no_alloc (Assign v0 v1) = True) /\
  (forall v0 v1, no_alloc (Get v0 v1) = True) /\
  (forall v0 v1, no_alloc (Set_ v0 v1) = True) /\
  (forall v0 v1, no_alloc (Store v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4, no_alloc (StoreConsts v0 v1 v2 v3 v4) = True) /\
  (forall v0, no_alloc (Raise v0) = True) /\
  (forall v0 v1, no_alloc (Return v0 v1) = True) /\
  (forall v0, no_alloc (Break v0) = True) /\
  (forall v0, no_alloc (Continue v0) = True) /\
  (no_alloc (Tick) = True) /\
  (forall v0 v1 v2, no_alloc (OpCurrHeap v0 v1 v2) = True) /\
  (forall v0 v1, no_alloc (CodeBufferWrite v0 v1) = True) /\
  (forall v0 v1, no_alloc (DataBufferWrite v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4 v5, no_alloc (FFI v0 v1 v2 v3 v4 v5) = True).
Proof. repeat split; intros; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_install_subprogs_def" *)
Definition no_install (p : prog a) : Prop := not_created_subprogs (fun q => Install 0 0 0 0 (LN, LN) <> q) p.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_install_def" *)
Theorem no_install_def :
  (forall p, no_install (MustTerminate p) = (@Install a 0 0 0 0 (LN, LN) <> (MustTerminate Skip) /\ no_install p)) /\
  (forall p1 p2, no_install (Seq p1 p2) = (no_install p1 /\ no_install p2)) /\
  (forall names c exit_names, no_install (Loop names c exit_names) = no_install c) /\
  (forall v0 v1 v2 p1 p2, no_install (If v0 v1 v2 p1 p2) = (no_install p1 /\ no_install p2)) /\
  (forall r dest args h, no_install (Call r dest args h) =
      (@Install a 0 0 0 0 (LN, LN) <> (Call NONE dest [] NONE) /\
       match r with NONE => True | SOME (_, (_, (p, _))) => no_install p end /\
       match h with
       | NONE => True
       | SOME (_, (p, (h1, _))) =>
           @Install a 0 0 0 0 (LN, LN) <> (Call NONE NONE [] (SOME (0, (Skip, (h1, 0))))) /\ no_install p
       end)) /\
  (forall v0 v1, no_install (Alloc v0 v1) = (@Install a 0 0 0 0 (LN, LN) <> (Alloc 0 (LN, LN)))) /\
  (forall v0 l, no_install (LocValue v0 l) = (@Install a 0 0 0 0 (LN, LN) <> (LocValue 0 l))) /\
  (forall v0 v1 v2, no_install (ShareInst v0 v1 v2) = (@Install a 0 0 0 0 (LN, LN) <> (ShareInst ARB 0 (Var 0)))) /\
  (forall v0 v1 v2 v3 v4, no_install (Install v0 v1 v2 v3 v4) = (@Install a 0 0 0 0 (LN, LN) <> (Install 0 0 0 0 (LN, LN)))) /\
  (no_install (Skip) = True) /\
  (forall v0 v1, no_install (Move v0 v1) = True) /\
  (forall v0, no_install (Inst v0) = True) /\
  (forall v0 v1, no_install (Assign v0 v1) = True) /\
  (forall v0 v1, no_install (Get v0 v1) = True) /\
  (forall v0 v1, no_install (Set_ v0 v1) = True) /\
  (forall v0 v1, no_install (Store v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4, no_install (StoreConsts v0 v1 v2 v3 v4) = True) /\
  (forall v0, no_install (Raise v0) = True) /\
  (forall v0 v1, no_install (Return v0 v1) = True) /\
  (forall v0, no_install (Break v0) = True) /\
  (forall v0, no_install (Continue v0) = True) /\
  (no_install (Tick) = True) /\
  (forall v0 v1 v2, no_install (OpCurrHeap v0 v1 v2) = True) /\
  (forall v0 v1, no_install (CodeBufferWrite v0 v1) = True) /\
  (forall v0 v1, no_install (DataBufferWrite v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4 v5, no_install (FFI v0 v1 v2 v3 v4 v5) = True).
Proof. repeat split; intros; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_mt_subprogs_def" *)
Definition no_mt (p : prog a) : Prop := not_created_subprogs (fun q => MustTerminate Skip <> q) p.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_mt_def" *)
Theorem no_mt_def :
  (forall p, no_mt (MustTerminate p) = (@MustTerminate a Skip <> (MustTerminate Skip) /\ no_mt p)) /\
  (forall p1 p2, no_mt (Seq p1 p2) = (no_mt p1 /\ no_mt p2)) /\
  (forall names c exit_names, no_mt (Loop names c exit_names) = no_mt c) /\
  (forall v0 v1 v2 p1 p2, no_mt (If v0 v1 v2 p1 p2) = (no_mt p1 /\ no_mt p2)) /\
  (forall r dest args h, no_mt (Call r dest args h) =
      (@MustTerminate a Skip <> (Call NONE dest [] NONE) /\
       match r with NONE => True | SOME (_, (_, (p, _))) => no_mt p end /\
       match h with
       | NONE => True
       | SOME (_, (p, (h1, _))) =>
           @MustTerminate a Skip <> (Call NONE NONE [] (SOME (0, (Skip, (h1, 0))))) /\ no_mt p
       end)) /\
  (forall v0 v1, no_mt (Alloc v0 v1) = (@MustTerminate a Skip <> (Alloc 0 (LN, LN)))) /\
  (forall v0 l, no_mt (LocValue v0 l) = (@MustTerminate a Skip <> (LocValue 0 l))) /\
  (forall v0 v1 v2, no_mt (ShareInst v0 v1 v2) = (@MustTerminate a Skip <> (ShareInst ARB 0 (Var 0)))) /\
  (forall v0 v1 v2 v3 v4, no_mt (Install v0 v1 v2 v3 v4) = (@MustTerminate a Skip <> (Install 0 0 0 0 (LN, LN)))) /\
  (no_mt (Skip) = True) /\
  (forall v0 v1, no_mt (Move v0 v1) = True) /\
  (forall v0, no_mt (Inst v0) = True) /\
  (forall v0 v1, no_mt (Assign v0 v1) = True) /\
  (forall v0 v1, no_mt (Get v0 v1) = True) /\
  (forall v0 v1, no_mt (Set_ v0 v1) = True) /\
  (forall v0 v1, no_mt (Store v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4, no_mt (StoreConsts v0 v1 v2 v3 v4) = True) /\
  (forall v0, no_mt (Raise v0) = True) /\
  (forall v0 v1, no_mt (Return v0 v1) = True) /\
  (forall v0, no_mt (Break v0) = True) /\
  (forall v0, no_mt (Continue v0) = True) /\
  (no_mt (Tick) = True) /\
  (forall v0 v1 v2, no_mt (OpCurrHeap v0 v1 v2) = True) /\
  (forall v0 v1, no_mt (CodeBufferWrite v0 v1) = True) /\
  (forall v0 v1, no_mt (DataBufferWrite v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4 v5, no_mt (FFI v0 v1 v2 v3 v4 v5) = True).
Proof. repeat split; intros; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_share_inst_subprogs_def" *)
Definition no_share_inst (p : prog a) : Prop := not_created_subprogs (fun q => ShareInst ARB 0 (Var 0) <> q) p.

(*! HOL "cakeml/compiler/backend/semantics/wordConvsScript.sml" "no_share_inst_def" *)
Theorem no_share_inst_def :
  (forall p, no_share_inst (MustTerminate p) = (@ShareInst a ARB 0 (Var 0) <> (MustTerminate Skip) /\ no_share_inst p)) /\
  (forall p1 p2, no_share_inst (Seq p1 p2) = (no_share_inst p1 /\ no_share_inst p2)) /\
  (forall names c exit_names, no_share_inst (Loop names c exit_names) = no_share_inst c) /\
  (forall v0 v1 v2 p1 p2, no_share_inst (If v0 v1 v2 p1 p2) = (no_share_inst p1 /\ no_share_inst p2)) /\
  (forall r dest args h, no_share_inst (Call r dest args h) =
      (@ShareInst a ARB 0 (Var 0) <> (Call NONE dest [] NONE) /\
       match r with NONE => True | SOME (_, (_, (p, _))) => no_share_inst p end /\
       match h with
       | NONE => True
       | SOME (_, (p, (h1, _))) =>
           @ShareInst a ARB 0 (Var 0) <> (Call NONE NONE [] (SOME (0, (Skip, (h1, 0))))) /\ no_share_inst p
       end)) /\
  (forall v0 v1, no_share_inst (Alloc v0 v1) = (@ShareInst a ARB 0 (Var 0) <> (Alloc 0 (LN, LN)))) /\
  (forall v0 l, no_share_inst (LocValue v0 l) = (@ShareInst a ARB 0 (Var 0) <> (LocValue 0 l))) /\
  (forall v0 v1 v2, no_share_inst (ShareInst v0 v1 v2) = (@ShareInst a ARB 0 (Var 0) <> (ShareInst ARB 0 (Var 0)))) /\
  (forall v0 v1 v2 v3 v4, no_share_inst (Install v0 v1 v2 v3 v4) = (@ShareInst a ARB 0 (Var 0) <> (Install 0 0 0 0 (LN, LN)))) /\
  (no_share_inst (Skip) = True) /\
  (forall v0 v1, no_share_inst (Move v0 v1) = True) /\
  (forall v0, no_share_inst (Inst v0) = True) /\
  (forall v0 v1, no_share_inst (Assign v0 v1) = True) /\
  (forall v0 v1, no_share_inst (Get v0 v1) = True) /\
  (forall v0 v1, no_share_inst (Set_ v0 v1) = True) /\
  (forall v0 v1, no_share_inst (Store v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4, no_share_inst (StoreConsts v0 v1 v2 v3 v4) = True) /\
  (forall v0, no_share_inst (Raise v0) = True) /\
  (forall v0 v1, no_share_inst (Return v0 v1) = True) /\
  (forall v0, no_share_inst (Break v0) = True) /\
  (forall v0, no_share_inst (Continue v0) = True) /\
  (no_share_inst (Tick) = True) /\
  (forall v0 v1 v2, no_share_inst (OpCurrHeap v0 v1 v2) = True) /\
  (forall v0 v1, no_share_inst (CodeBufferWrite v0 v1) = True) /\
  (forall v0 v1, no_share_inst (DataBufferWrite v0 v1) = True) /\
  (forall v0 v1 v2 v3 v4 v5, no_share_inst (FFI v0 v1 v2 v3 v4 v5) = True).
Proof. repeat split; intros; reflexivity. Qed.

End CodeLabels2.
