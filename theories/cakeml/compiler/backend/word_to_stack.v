(** * CakeML [word_to_stack]: from wordLang to stackLang

    Port of [cakeml/compiler/backend/word_to_stackScript.sml].

    - The input language's constructors are written [wordLang.X]; unqualified
      [Skip], [Inst], [Seq], ... are stackLang's (imported last).  ASM's
      [Const], [Shift], [Load], [Store], [Skip] are written [asm.X].
    - HOL's [kf = (k,f,f')] is the right-nested triple [(k, (f, f'))].
    - HOL [store_consts_stub_location] is wordLang's (the stackLang constant
      of the same name is a different stub); it is written qualified.
    - HOL's [f ## g] (pair map) and [DIV2] are written out as
      [fun '(x, y) => (f x, g y)] and [n DIV 2].
    - [word_list] (HOL: measure [LENGTH xs]) and [const_words_to_bitmap]
      (terminating on [ws_len]) are computed with a fuel; [stack_move] and
      [copy_ret_aux] (recursion on [SUC n] / [n-1]) use [num_rec].  HOL's
      equations are the tagged [_def] theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair option.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend.reg_alloc Require Import parmove.
From Galette.cakeml.compiler.backend Require Import wordLang.
From Galette.cakeml.compiler.backend Require Import stackLang.
Open Scope N_scope.
Open Scope hol_string_scope.

(** [bitmaps_length] stores the current length of the bitmaps. *)
(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "config" *)
Record config : Type := {
  bitmaps_length : N;
  stack_frame_size : spt N
}.

Abbreviation kf_ty := (N * (N * N))%type.

Section WordToStack.
Context {a : N}.

Abbreviation sprog := (stackLang.prog a).
Abbreviation wprog := (wordLang.prog a).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wReg1_def" *)
Definition wReg1 (r : N) (kf : kf_ty) : list (N * N) * N :=
  let '(k, (f, f')) := kf in
  let r := r DIV 2 in
  if r <? k then ([], r) else ([(k, f - 1 - (r - k))], k).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wReg2_def" *)
Definition wReg2 (r : N) (kf : kf_ty) : list (N * N) * N :=
  let '(k, (f, f')) := kf in
  let r := r DIV 2 in
  if r <? k then ([], r) else ([(k + 1, f - 1 - (r - k))], k + 1).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite1_def" *)
Definition wRegWrite1 (g : N -> sprog) (r : N) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  let r := r DIV 2 in
  if r <? k then g r else Seq (g k) (StackStore k (f - 1 - (r - k))).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite2_def" *)
Definition wRegWrite2 (g : N -> sprog) (r : N) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  let r := r DIV 2 in
  if r <? k then g r else Seq (g (k + 1)) (StackStore (k + 1) (f - 1 - (r - k))).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wStackLoad_def" *)
Fixpoint wStackLoad (l : list (N * N)) (x : sprog) : sprog :=
  match l with
  | [] => x
  | (r, i) :: ps => Seq (StackLoad r i) (wStackLoad ps x)
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wStackStore_def" *)
Fixpoint wStackStore (l : list (N * N)) (x : sprog) : sprog :=
  match l with
  | [] => x
  | (r, i) :: ps => Seq (wStackStore ps x) (StackStore r i)
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wMoveSingle_def" *)
Definition wMoveSingle (xy : (N + N) * (N + N)) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  match xy with
  | (inl r1, inl r2) => Inst (Arith (Binop Or r1 r2 (Reg r2)))
  | (inl r1, inr r2) => StackLoad r1 (f - 1 - (r2 - k))
  | (inr r1, inl r2) => StackStore r2 (f - 1 - (r1 - k))
  | (inr r1, inr r2) => Seq (StackLoad k (f - 1 - (r2 - k)))
                            (StackStore k (f - 1 - (r1 - k)))
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wMoveAux_def" *)
Fixpoint wMoveAux (l : list ((N + N) * (N + N))) (kf : kf_ty) : sprog :=
  match l with
  | [] => Skip
  | [xy] => wMoveSingle xy kf
  | xy :: xys => Seq (wMoveSingle xy kf) (wMoveAux xys kf)
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "format_var_def" *)
Definition format_var (k : N) (o_ : option N) : N + N :=
  match o_ with
  | None => inl (k + 1)
  | Some x => if x <? k then inl x else inr x
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wMove_def" *)
Definition wMove (xs : list (N * N)) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  wMoveAux (MAP (fun '(x, y) => (format_var k x, format_var k y))
                (parmove (MAP (fun '(x, y) => (x DIV 2, y DIV 2)) xs))) (k, (f, f')).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wInst_def" *)
Definition wInst (i : inst a) (kf : kf_ty) : sprog :=
  match i with
  | asm.Const n c => wRegWrite1 (fun n => Inst (asm.Const n c)) n kf
  | Arith (Binop bop n1 n2 (Imm imm)) =>
      let '(l, n2) := wReg1 n2 kf in
      wStackLoad l (wRegWrite1 (fun n1 => Inst (Arith (Binop bop n1 n2 (Imm imm)))) n1 kf)
  | Arith (Binop bop n1 n2 (Reg n3)) =>
      let '(l, n2) := wReg1 n2 kf in
      let '(l', n3) := wReg2 n3 kf in
      wStackLoad (l ++ l') (wRegWrite1 (fun n1 => Inst (Arith (Binop bop n1 n2 (Reg n3)))) n1 kf)
  | Arith (asm.Shift sh n1 n2 (Imm imm)) =>
      let '(l, n2) := wReg1 n2 kf in
      wStackLoad l (wRegWrite1 (fun n1 => Inst (Arith (asm.Shift sh n1 n2 (Imm imm)))) n1 kf)
  | Arith (asm.Shift sh n1 n2 (Reg n3)) =>
      let '(l, n2) := wReg1 n2 kf in
      let '(l', n3) := wReg2 n3 kf in
      wStackLoad (l ++ l') (wRegWrite1 (fun n1 => Inst (Arith (asm.Shift sh n1 n2 (Reg n3)))) n1 kf)
  | Arith (Div n1 n2 n3) =>
      let '(l, n2) := wReg1 n2 kf in
      let '(l', n3) := wReg2 n3 kf in
      wStackLoad (l ++ l') (wRegWrite1 (fun n1 => Inst (Arith (Div n1 n2 n3))) n1 kf)
  | Arith (AddCarry n1 n2 n3 n4) =>
      let '(l, n2) := wReg1 n2 kf in
      let '(l', n3) := wReg2 n3 kf in
      wStackLoad (l ++ l') (wRegWrite1 (fun n1 => Inst (Arith (AddCarry n1 n2 n3 n4))) n1 kf)
  | Arith (AddOverflow n1 n2 n3 n4) =>
      let '(l, n2) := wReg1 n2 kf in
      let '(l', n3) := wReg2 n3 kf in
      wStackLoad (l ++ l') (wRegWrite1 (fun n1 => Inst (Arith (AddOverflow n1 n2 n3 n4))) n1 kf)
  | Arith (SubOverflow n1 n2 n3 n4) =>
      let '(l, n2) := wReg1 n2 kf in
      let '(l', n3) := wReg2 n3 kf in
      wStackLoad (l ++ l') (wRegWrite1 (fun n1 => Inst (Arith (SubOverflow n1 n2 n3 n4))) n1 kf)
  | Arith (LongMul n1 n2 n3 n4) =>
      Inst (Arith (LongMul 3 0 0 2))
  | Arith (LongDiv n1 n2 n3 n4 n5) =>
      let '(l, n5) := wReg1 n5 kf in
      wStackLoad l (Inst (Arith (LongDiv 0 3 3 0 n5)))
  | Mem asm.Load n1 (Addr n2 offset) =>
      let '(l, n2) := wReg1 n2 kf in
      wStackLoad l (wRegWrite1 (fun n1 => Inst (Mem asm.Load n1 (Addr n2 offset))) n1 kf)
  | Mem asm.Store n1 (Addr n2 offset) =>
      let '(l1, n2) := wReg1 n2 kf in
      let '(l2, n1) := wReg2 n1 kf in
      wStackLoad (l1 ++ l2) (Inst (Mem asm.Store n1 (Addr n2 offset)))
  | Mem Load8 n1 (Addr n2 offset) =>
      let '(l, n2) := wReg1 n2 kf in
      wStackLoad l (wRegWrite1 (fun n1 => Inst (Mem Load8 n1 (Addr n2 offset))) n1 kf)
  | Mem Store8 n1 (Addr n2 offset) =>
      let '(l1, n2) := wReg1 n2 kf in
      let '(l2, n1) := wReg2 n1 kf in
      wStackLoad (l1 ++ l2) (Inst (Mem Store8 n1 (Addr n2 offset)))
  | Mem Load32 n1 (Addr n2 offset) =>
      let '(l, n2) := wReg1 n2 kf in
      wStackLoad l (wRegWrite1 (fun n1 => Inst (Mem Load32 n1 (Addr n2 offset))) n1 kf)
  | Mem Store32 n1 (Addr n2 offset) =>
      let '(l1, n2) := wReg1 n2 kf in
      let '(l2, n1) := wReg2 n1 kf in
      wStackLoad (l1 ++ l2) (Inst (Mem Store32 n1 (Addr n2 offset)))
  | FP (FPLess r f1 f2) => wRegWrite1 (fun r => Inst (FP (FPLess r f1 f2))) r kf
  | FP (FPLessEqual r f1 f2) => wRegWrite1 (fun r => Inst (FP (FPLessEqual r f1 f2))) r kf
  | FP (FPEqual r f1 f2) => wRegWrite1 (fun r => Inst (FP (FPEqual r f1 f2))) r kf
  | FP (FPMovToReg r1 r2 d) =>
      if dimindex a =? 64 then
        wRegWrite1 (fun r1 => Inst (FP (FPMovToReg r1 0 d))) r1 kf
      else
        wRegWrite2 (fun r2 => wRegWrite1 (fun r1 => Inst (FP (FPMovToReg r1 r2 d))) r1 kf) r2 kf
  | FP (FPMovFromReg d r1 r2) =>
      let '(l, n1) := wReg1 r1 kf in
      let '(l', n2) := if dimindex a =? 64 then ([], 0) else wReg2 r2 kf in
      wStackLoad (l ++ l') (Inst (FP (FPMovFromReg d n1 n2)))
  | FP f => Inst (FP f)
  | _ => Inst asm.Skip
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wShareInst_def" *)
Definition wShareInst (op : memop) (v : N) (ad : addr a) (kf : kf_ty) : sprog :=
  match op, ad with
  | asm.Load, Addr ad offset =>
      let '(l, n2) := wReg1 ad kf in
      wStackLoad l (wRegWrite1 (fun r => ShMemOp asm.Load r (Addr n2 offset)) v kf)
  | Load8, Addr ad offset =>
      let '(l, n2) := wReg1 ad kf in
      wStackLoad l (wRegWrite1 (fun r => ShMemOp Load8 r (Addr n2 offset)) v kf)
  | Load16, Addr ad offset =>
      let '(l, n2) := wReg1 ad kf in
      wStackLoad l (wRegWrite1 (fun r => ShMemOp Load16 r (Addr n2 offset)) v kf)
  | Load32, Addr ad offset =>
      let '(l, n2) := wReg1 ad kf in
      wStackLoad l (wRegWrite1 (fun r => ShMemOp Load32 r (Addr n2 offset)) v kf)
  | asm.Store, Addr ad offset =>
      let '(l1, n2) := wReg1 ad kf in
      let '(l2, n1) := wReg2 v kf in
      wStackLoad (l1 ++ l2) (ShMemOp asm.Store n1 (Addr n2 offset))
  | Store8, Addr ad offset =>
      let '(l1, n2) := wReg1 ad kf in
      let '(l2, n1) := wReg2 v kf in
      wStackLoad (l1 ++ l2) (ShMemOp Store8 n1 (Addr n2 offset))
  | Store16, Addr ad offset =>
      let '(l1, n2) := wReg1 ad kf in
      let '(l2, n1) := wReg2 v kf in
      wStackLoad (l1 ++ l2) (ShMemOp Store16 n1 (Addr n2 offset))
  | Store32, Addr ad offset =>
      let '(l1, n2) := wReg1 ad kf in
      let '(l2, n1) := wReg2 v kf in
      wStackLoad (l1 ++ l2) (ShMemOp Store32 n1 (Addr n2 offset))
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "bits_to_word_def" *)
Fixpoint bits_to_word (l : list bool) : word a :=
  match l with
  | [] => n2w 0
  | true :: xs => word_or (word_lsl (bits_to_word xs) 1) (n2w 1)
  | false :: xs => word_lsl (bits_to_word xs) 1
  end.

Fixpoint word_list_f (fuel : nat) (xs : list bool) (d : N) : list (word a) :=
  match fuel with
  | O => []
  | S fuel =>
      if (LENGTH xs <=? d) || (d =? 0) then [bits_to_word xs]
      else bits_to_word (TAKE d xs ++ [true]) :: word_list_f fuel (DROP d xs) d
  end.

(** HOL [word_list] (measure [LENGTH xs]). *)
Definition word_list (xs : list bool) (d : N) : list (word a) :=
  word_list_f (S (length xs)) xs d.

Lemma word_list_f_fuel : forall f1 f2 xs d,
  (length xs < f1)%nat -> (length xs < f2)%nat -> word_list_f f1 xs d = word_list_f f2 xs d.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] xs d H1 H2; try lia; cbn [word_list_f].
  destruct ((LENGTH xs <=? d) || (d =? 0)) eqn:E; [reflexivity|].
  f_equal; apply IH;
    (rewrite DROP_skipn, length_skipn; apply Bool.orb_false_iff in E as [E1 E2];
     apply N.leb_gt in E1; apply N.eqb_neq in E2; rewrite LENGTH_length in E1; lia).
Qed.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "word_list_def" *)
Theorem word_list_def : forall xs d,
  word_list xs d =
    if (LENGTH xs <=? d) || (d =? 0) then [bits_to_word xs]
    else bits_to_word (TAKE d xs ++ [true]) :: word_list (DROP d xs) d.
Proof.
  intros xs d; unfold word_list at 1; cbn [word_list_f].
  destruct ((LENGTH xs <=? d) || (d =? 0)) eqn:E; [reflexivity|].
  f_equal; unfold word_list; apply word_list_f_fuel;
    (rewrite DROP_skipn, length_skipn; apply Bool.orb_false_iff in E as [E1 E2];
     apply N.leb_gt in E1; apply N.eqb_neq in E2; rewrite LENGTH_length in E1; lia).
Qed.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "write_bitmap_def" *)
Definition write_bitmap (live : num_set) (k f' : N) : list (word a) :=
  let names := MAP (fun '(r, y) => (f' - 1) - (r DIV 2 - k)) (toAList live) in
  word_list (GENLIST (fun x => MEM x names) f' ++ [true]) (dimindex a - 1).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "insert_bitmap_def" *)
Definition insert_bitmap (ws : list (word a)) (bm : app_list (word a) * N)
    : (app_list (word a) * N) * N :=
  let '(data, data_len) := bm in
  let l := LENGTH ws in
  ((Append data (List ws), data_len + l), data_len).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "wLive_def" *)
Definition wLive (live : cutsets) (bitmaps : app_list (word a) * N) (kf : kf_ty)
    : sprog * (app_list (word a) * N) :=
  let '(k, (f, f')) := kf in
  if f =? 0 then (Skip, bitmaps)
  else
    let '(new_bitmaps, i) := insert_bitmap (write_bitmap (snd live) k f') bitmaps in
    (Seq (Inst (asm.Const k (n2w (i + 1)))) (StackStore k 0), new_bitmaps).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "SeqStackFree_def" *)
Definition SeqStackFree (n : N) (p : sprog) : sprog :=
  if n =? 0 then p else Seq (StackFree n) p.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "call_dest_def" *)
Definition call_dest (dest : option N) (args : list N) (kf : kf_ty) : sprog * (N + N) :=
  match dest with
  | Some pos => (Skip, inl pos)
  | None =>
      if LENGTH args =? 0 then (Skip, inl raise_stub_location)
      else let '(x1, r) := wReg2 (LAST args) kf in (wStackLoad x1 Skip, inr r)
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "stack_arg_count_def" *)
Definition stack_arg_count (dest : N + N) (arg_count k : N) : N :=
  match dest with
  | inl _ => arg_count - k
  | inr _ => (arg_count - 1) - k
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "stack_free_def" *)
Definition stack_free (dest : N + N) (arg_count : N) (kf : kf_ty) : N :=
  let '(k, (f, f')) := kf in f - stack_arg_count dest arg_count k.

(** HOL [stack_move] (recursion on [SUC n]). *)
Definition stack_move (n start offset i : N) (p : sprog) : sprog :=
  num_rec (fun _ => p)
    (fun n r start => Seq (r (start + 1))
                          (Seq (StackLoad i (start + offset)) (StackStore i start)))
    n start.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "stack_move_def" *)
Theorem stack_move_def : forall n start offset i p,
  stack_move 0 start offset i p = p /\
  stack_move (SUC n) start offset i p =
    Seq (stack_move n (start + 1) offset i p)
        (Seq (StackLoad i (start + offset)) (StackStore i start)).
Proof. intros; split; [reflexivity|unfold stack_move; rewrite num_rec_SUC; reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "StackArgs_def" *)
Definition StackArgs (dest : N + N) (arg_count : N) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  let n := stack_arg_count dest arg_count k in
  stack_move n 0 f k (StackAlloc n).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "perf_rsp_def" *)
Definition perf_rsp : N := 14.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "perf_rbp_def" *)
Definition perf_rbp : N := 15.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "perf_call_prefix_def" *)
Definition perf_call_prefix (l1 l2 k : N) : sprog :=
  list_Seq [
    LocValue k l1 l2;
    Inst (Mem asm.Store k (Addr perf_rsp (word_2comp (n2w 8))));
    Inst (Mem asm.Store perf_rbp (Addr perf_rsp (word_2comp (n2w 16))));
    Inst (Arith (Binop Sub perf_rsp perf_rsp (Imm (n2w 16))));
    Inst (Arith (Binop Or perf_rbp perf_rsp (Reg perf_rsp)))
  ].

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "perf_call_suffix_def" *)
Definition perf_call_suffix : sprog :=
  list_Seq [
    Inst (Mem asm.Load perf_rbp (Addr perf_rsp (n2w 0)));
    Inst (Arith (Binop asm.Add perf_rsp perf_rsp (Imm (n2w 16))))
  ].

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "handler_slots_def" *)
Definition handler_slots (perf : bool) : N := if perf then 5 else 3.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "StackHandlerArgs_def" *)
Definition StackHandlerArgs (perf : bool) (dest : N + N) (arg_count : N) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  StackArgs dest arg_count (k, (f + handler_slots perf, f' + handler_slots perf)).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "PushHandler_def" *)
Definition PushHandler (perf : bool) (l1 l2 : N) (kf : kf_ty) : sprog :=
  let '(k, (f, f')) := kf in
  Seq (StackAlloc (handler_slots perf))
 (Seq (Inst (asm.Const k (n2w 1)))
 (Seq (StackStore k 0)
 (Seq (LocValue k l1 l2)
 (Seq (StackStore k 1)
 (Seq (Get k Handler)
 (Seq (StackStore k 2)
 (Seq (if perf then
         list_Seq [
           Inst (Arith (Binop Or k perf_rsp (Reg perf_rsp)));
           StackStore k 3;
           Inst (Arith (Binop Or k perf_rbp (Reg perf_rbp)));
           StackStore k 4
         ]
       else Skip)
 (Seq (StackGetSize k)
      (Set_ Handler k))))))))).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "PopHandler_def" *)
Definition PopHandler (perf : bool) (kf : kf_ty) (prog : sprog) : sprog :=
  let '(k, (f, f')) := kf in
  Seq (StackLoad k 2)
 (Seq (Set_ Handler k)
 (Seq (StackFree (handler_slots perf))
  prog)).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "chunk_to_bits_def" *)
Fixpoint chunk_to_bits (l : list (bool * word a)) : word a :=
  match l with
  | [] => n2w 1
  | (b, w) :: ws =>
      let res := word_lsl (chunk_to_bits ws) 1 in
      if b then word_add res (n2w 1) else res
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "chunk_to_bitmap_def" *)
Definition chunk_to_bitmap (ws : list (bool * word a)) : list (word a) :=
  chunk_to_bits ws :: MAP snd ws.

Fixpoint const_words_to_bitmap_f (fuel : nat) (ws : list (bool * word a)) (ws_len : N)
    : list (word a) :=
  match fuel with
  | O => []
  | S fuel =>
      if (ws_len <? dimindex a - 1) || (dimindex a - 1 =? 0)
      then chunk_to_bitmap ws
      else
        let h := TAKE (dimindex a - 1) ws in
        let t := DROP (dimindex a - 1) ws in
        chunk_to_bitmap h ++ const_words_to_bitmap_f fuel t (ws_len - (dimindex a - 1))
  end.

(** HOL [const_words_to_bitmap] (terminating on [ws_len]). *)
Definition const_words_to_bitmap (ws : list (bool * word a)) (ws_len : N) : list (word a) :=
  const_words_to_bitmap_f (S (N.to_nat ws_len)) ws ws_len.

Lemma const_words_to_bitmap_f_fuel : forall f1 f2 ws ws_len,
  (N.to_nat ws_len < f1)%nat -> (N.to_nat ws_len < f2)%nat ->
  const_words_to_bitmap_f f1 ws ws_len = const_words_to_bitmap_f f2 ws ws_len.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] ws ws_len H1 H2; try lia; cbn [const_words_to_bitmap_f].
  destruct ((ws_len <? dimindex a - 1) || (dimindex a - 1 =? 0)) eqn:E; [reflexivity|].
  apply Bool.orb_false_iff in E as [E1 E2]; apply N.ltb_ge in E1; apply N.eqb_neq in E2.
  f_equal; apply IH; lia.
Qed.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "const_words_to_bitmap_def" *)
Theorem const_words_to_bitmap_def : forall ws ws_len,
  const_words_to_bitmap ws ws_len =
    if (ws_len <? dimindex a - 1) || (dimindex a - 1 =? 0)
    then chunk_to_bitmap ws
    else
      let h := TAKE (dimindex a - 1) ws in
      let t := DROP (dimindex a - 1) ws in
      chunk_to_bitmap h ++ const_words_to_bitmap t (ws_len - (dimindex a - 1)).
Proof.
  intros ws ws_len; unfold const_words_to_bitmap at 1; cbn [const_words_to_bitmap_f].
  destruct ((ws_len <? dimindex a - 1) || (dimindex a - 1 =? 0)) eqn:E; [reflexivity|].
  apply Bool.orb_false_iff in E as [E1 E2]; apply N.ltb_ge in E1; apply N.eqb_neq in E2.
  cbv zeta; f_equal; unfold const_words_to_bitmap; apply const_words_to_bitmap_f_fuel; lia.
Qed.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "num_stack_ret_def" *)
Definition num_stack_ret (k : N) (vs : list N) : N := LENGTH vs + 1 - k.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "skip_free_def" *)
Definition skip_free (kf : kf_ty) (vs : list N) : N :=
  let '(k, (f, f')) := kf in f - num_stack_ret k vs.

(** HOL [copy_ret_aux] (recursion on [n-1]). *)
Definition copy_ret_aux (k f n : N) : sprog :=
  num_rec Skip (fun n' r => list_Seq [StackLoad k n'; StackStore k (n' + f); r]) n.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "copy_ret_aux_def" *)
Theorem copy_ret_aux_def : forall k f n,
  copy_ret_aux k f n =
    if n =? 0 then Skip
    else let n' := n - 1 in
         list_Seq [StackLoad k n'; StackStore k (n' + f); copy_ret_aux k f n'].
Proof.
  intros k f n; destruct (N.eqb_spec n 0) as [->|Hn]; [reflexivity|].
  unfold copy_ret_aux at 1; replace n with (SUC (n - 1)) at 1 by lia.
  rewrite num_rec_SUC; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "copy_ret_def" *)
Definition copy_ret (perf is_handle : bool) (kf : kf_ty) (vs : list N) (kont : sprog) : sprog :=
  let '(k, (f, f')) := kf in
  let n := num_stack_ret k vs in
  if n =? 0 then kont
  else Seq (copy_ret_aux k (if is_handle then f + handler_slots perf else f) n)
           (SeqStackFree n kont).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "comp_def" *)
Fixpoint comp (conf : asm_config a) (perf : bool) (p : wprog) (bs : app_list (word a) * N)
    (kf : kf_ty) {struct p} : sprog * (app_list (word a) * N) :=
  match p with
  | wordLang.Skip => (Skip, bs)
  | wordLang.Move _ xs => (wMove xs kf, bs)
  | wordLang.Inst i => (wInst i kf, bs)
  | wordLang.Return v1 vs =>
      let '(xs, x) := wReg1 v1 kf in
      (wStackLoad xs (SeqStackFree (skip_free kf vs) (Return x)), bs)
  | wordLang.Raise v => (Call None (inl raise_stub_location) None, bs)
  | wordLang.OpCurrHeap b dst src =>
      let '(xs, src_r) := wReg1 src kf in
      (wStackLoad xs (wRegWrite1 (fun dst_r => OpCurrHeap b dst_r src_r) dst kf), bs)
  | wordLang.Tick => (Tick, bs)
  | wordLang.Break k => (Break k, bs)
  | wordLang.Continue k => (Continue k, bs)
  | wordLang.MustTerminate p1 => comp conf perf p1 bs kf
  | wordLang.Seq p1 p2 =>
      let '(q1, bs) := comp conf perf p1 bs kf in
      let '(q2, bs) := comp conf perf p2 bs kf in
      (Seq q1 q2, bs)
  | wordLang.If cmp r ri p1 p2 =>
      let '(x1, r') := wReg1 r kf in
      let '(q1, bs) := comp conf perf p1 bs kf in
      let '(q2, bs) := comp conf perf p2 bs kf in
      match ri with
      | Reg r =>
          let '(x2, n) := wReg2 r kf in
          (wStackLoad (x1 ++ x2) (If cmp r' (Reg n) q1 q2), bs)
      | Imm i =>
          if valid_imm conf (inr cmp) i then
            (wStackLoad x1 (If cmp r' (Imm i) q1 q2), bs)
          else
            let r := fst kf + 1 in
            (Seq (const_inst r i) (wStackLoad x1 (If cmp r' (Reg r) q1 q2)), bs)
      end
  | wordLang.Loop _ p1 _ =>
      let '(q1, bs) := comp conf perf p1 bs kf in
      (Loop q1, bs)
  | wordLang.Set_ name exp =>
      if decide (name = BitmapBase) then (Skip, bs)
      else
        match exp with
        | Var n => let '(x1, r') := wReg1 n kf in (wStackLoad x1 (Set_ name r'), bs)
        | _ => (Skip, bs)
        end
  | wordLang.Get n name => (wRegWrite1 (fun r => Get r name) n kf, bs)
  | wordLang.Call ret dest args handler =>
      let '(q0, dest) := call_dest dest args kf in
      match ret with
      | None => (Seq q0 (SeqStackFree (stack_free dest (LENGTH args) kf)
                         (Call None dest None)), bs)
      | Some (vs, (live, (ret_code, (l1, l2)))) =>
          let '(q1, bs) := wLive live bs kf in
          let '(q2, bs) := comp conf perf ret_code bs kf in
          let pre := if perf then perf_call_prefix l1 l2 (fst kf) else Skip in
          let suf := if perf then perf_call_suffix else Skip in
          match handler with
          | None =>
              let q3 := Seq suf (copy_ret perf false kf vs q2) in
              (Seq q0
                 (Seq q1
                    (Seq (StackArgs dest (LENGTH args + 1) kf)
                       (Seq pre
                          (Call (Some (q3, (0, (l1, l2)))) dest None)))),
               bs)
          | Some (handle_var, (handle_code, (h1, h2))) =>
              let q3 := Seq suf (copy_ret perf true kf vs (PopHandler perf kf q2)) in
              let '(q4, bs) := comp conf perf handle_code bs kf in
              (Seq q0
                 (Seq q1
                    (Seq (PushHandler perf h1 h2 kf)
                       (Seq (StackHandlerArgs perf dest (LENGTH args + 1) kf)
                          (Seq pre
                             (Call (Some (q3, (0, (l1, l2)))) dest (Some (q4, (h1, h2)))))))),
               bs)
          end
      end
  | wordLang.Alloc r live =>
      let '(q1, bs) := wLive live bs kf in
      (Seq q1 (Alloc 1), bs)
  | wordLang.StoreConsts a0 b c d ws =>
      let '(new_bs, i) := insert_bitmap (const_words_to_bitmap ws (LENGTH ws)) bs in
      (Seq (Inst (asm.Const 1 (n2w i)))
           (StoreConsts (fst kf) (fst kf + 1) (Some wordLang.store_consts_stub_location)),
       new_bs)
  | wordLang.LocValue r l1 => (wRegWrite1 (fun r => LocValue r l1 0) r kf, bs)
  | wordLang.Install r1 r2 r3 r4 live =>
      let '(l3, r3) := wReg1 r3 kf in
      let '(l4, r4) := wReg2 r4 kf in
      (wStackLoad (l3 ++ l4) (Install (r1 DIV 2) (r2 DIV 2) r3 r4 0), bs)
  | wordLang.CodeBufferWrite r1 r2 =>
      let '(l1, r1) := wReg1 r1 kf in
      let '(l2, r2) := wReg2 r2 kf in
      (wStackLoad (l1 ++ l2) (CodeBufferWrite r1 r2), bs)
  | wordLang.DataBufferWrite r1 r2 =>
      let '(l1, r1) := wReg1 r1 kf in
      let '(l2, r2) := wReg2 r2 kf in
      (wStackLoad (l1 ++ l2) (DataBufferWrite r1 r2), bs)
  | wordLang.FFI i r1 r2 r3 r4 live =>
      (FFI i (r1 DIV 2) (r2 DIV 2) (r3 DIV 2) (r4 DIV 2) 0, bs)
  | wordLang.ShareInst op v exp =>
      match exp_to_addr exp with
      | None => (Skip, bs)
      | Some addr => (wShareInst op v addr kf, bs)
      end
  | _ => (Skip, bs)
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "raise_stub_def" *)
Definition raise_stub (perf : bool) (k : N) : sprog :=
  Seq (Get k Handler)
 (Seq (StackSetSize k)
 (Seq (if perf then
         list_Seq [
           StackLoad k 3;
           Inst (Arith (Binop Or perf_rsp k (Reg k)));
           StackLoad k 4;
           Inst (Arith (Binop Or perf_rbp k (Reg k)))
         ]
       else Skip)
 (Seq (StackLoad k 2)
 (Seq (Set_ Handler k)
 (Seq (StackLoad k 1)
 (Seq (StackFree (handler_slots perf))
      (Raise k))))))).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "store_consts_stub_def" *)
Definition store_consts_stub (k : N) : sprog :=
  Seq (StoreConsts k (k + 1) None) (Return 0).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "compile_prog_def" *)
Definition compile_prog (asm_conf : asm_config a) (perf : bool) (prog : wprog)
    (arg_count reg_count : N) (bitmaps : app_list (word a) * N)
    : sprog * (N * (app_list (word a) * N)) :=
  let stack_arg_count := arg_count - reg_count in
  let stack_var_count := MAX ((max_var prog DIV 2 + 1) - reg_count) stack_arg_count in
  let f := if stack_var_count =? 0 then 0 else stack_var_count + 1 in
  let '(q1, bitmaps) := comp asm_conf perf prog bitmaps (reg_count, (f, stack_var_count)) in
  (Seq (StackAlloc (f - stack_arg_count)) q1, (f, bitmaps)).

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "compile_word_to_stack_def" *)
Fixpoint compile_word_to_stack (asm_conf : asm_config a) (perf : bool) (k : N)
    (progs : list (N * (N * wprog))) (bitmaps : app_list (word a) * N)
    : list (N * sprog) * (list N * (app_list (word a) * N)) :=
  match progs with
  | [] => ([], ([], bitmaps))
  | (i, (n, p)) :: progs =>
      let '(prog, (f, bitmaps)) := compile_prog asm_conf perf p n k bitmaps in
      let '(progs, (fs, bitmaps)) := compile_word_to_stack asm_conf perf k progs bitmaps in
      ((i, prog) :: progs, (f :: fs, bitmaps))
  end.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "compile_def" *)
Definition compile (asm_conf : asm_config a) (perf : bool) (progs : list (N * (N * wprog)))
    : list (word a) * (config * (list N * list (N * sprog))) :=
  let k := reg_count asm_conf - (5 + LENGTH (avoid_regs asm_conf)) in
  let init_bitmaps : app_list (word a) * N :=
    if perf then (List [n2w 16], 1) else (List [n2w 4], 1) in
  let '(progs, (fs, bitmaps)) := compile_word_to_stack asm_conf perf k progs init_bitmaps in
  let sfs := fromAList (MAP (fun '((i, _), n) => (i, n)) (ZIP (progs, fs))) in
  (append (fst bitmaps),
   ({| bitmaps_length := snd bitmaps; stack_frame_size := sfs |},
    (0 :: fs,
     (raise_stub_location, raise_stub perf k) ::
     (wordLang.store_consts_stub_location, store_consts_stub k) :: progs))).

End WordToStack.

(*! HOL "cakeml/compiler/backend/word_to_stackScript.sml" "stub_names_def" *)
Definition stub_names (u : unit) : list (N * mlstring) :=
  [(raise_stub_location, implode "_Raise");
   (wordLang.store_consts_stub_location, implode "_StoreConsts")].
