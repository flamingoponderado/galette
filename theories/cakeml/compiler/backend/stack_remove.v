(** * CakeML [stack_remove]: stack operations as memory accesses

    Port of [cakeml/compiler/backend/stack_removeScript.sml].

    [stack_alloc], [stack_free], [upshift], [downshift] (HOL: measure on
    [n], decreasing by [max_stack_alloc]) are computed with a fuel; HOL's
    equations are the tagged [_def] theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.combin Require combin.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.compiler.backend Require Import backend_common.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "max_stack_alloc_def" *)
Definition max_stack_alloc : N := 255.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "store_list_def" *)
Definition store_list : list store_name :=
  [NextFree; EndOfHeap; HeapLength; OtherHeap; TriggerGC;
   AllocSize; Handler; Globals; GlobReal; ProgStart; BitmapBase;
   GenStart; CodeBuffer; CodeBufferEnd; BitmapBuffer; BitmapBufferEnd;
   Temp (n2w 00); Temp (n2w 01); Temp (n2w 02); Temp (n2w 03); Temp (n2w 04);
   Temp (n2w 05); Temp (n2w 06); Temp (n2w 07); Temp (n2w 08); Temp (n2w 09);
   Temp (n2w 10); Temp (n2w 11); Temp (n2w 12); Temp (n2w 13); Temp (n2w 14);
   Temp (n2w 15); Temp (n2w 16); Temp (n2w 17); Temp (n2w 18); Temp (n2w 19);
   Temp (n2w 20); Temp (n2w 21); Temp (n2w 22); Temp (n2w 23); Temp (n2w 24);
   Temp (n2w 25); Temp (n2w 26); Temp (n2w 27); Temp (n2w 28); Temp (n2w 29);
   Temp (n2w 30); Temp (n2w 31)].

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "store_pos_def" *)
Definition store_pos (name : store_name) : N :=
  match INDEX_FIND 0 (fun n => bool_decide (n = name)) store_list with
  | None => 0
  | Some (i, _) => i + 1
  end.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "store_length_def" *)
Definition store_length : N :=
  if EVEN (LENGTH store_list) then LENGTH store_list else LENGTH store_list + 1.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "stack_err_lab_def" *)
Definition stack_err_lab : N := 2.

Section StackRemove.
Context {a : N}.

Abbreviation sprog := (stackLang.prog a).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "word_offset_def" *)
Definition word_offset (n : N) : word a := n2w (dimindex a DIV 8 * n).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "store_offset_def" *)
Definition store_offset (name : store_name) : word a :=
  word_sub (n2w 0) (word_offset (store_pos name)).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "halt_inst_def" *)
Definition halt_inst (w : word a) : sprog := Seq (const_inst 1 w) (Halt 1).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "single_stack_alloc_def" *)
Definition single_stack_alloc (jump : bool) (k n : N) : sprog :=
  if jump
  then Seq (Inst (Arith (Binop Sub k k (Imm (word_offset n)))))
           (JumpLower k (k + 1) stack_err_lab)
  else Seq (Inst (Arith (Binop Sub k k (Imm (word_offset n)))))
           (If Lower k (Reg (k + 1)) (halt_inst (n2w 2)) Skip).

Fixpoint stack_alloc_f (fuel : nat) (jump : bool) (k n : N) : sprog :=
  match fuel with
  | O => Skip
  | S fuel =>
      if n =? 0 then Skip else
      if n <=? max_stack_alloc then single_stack_alloc jump k n else
        Seq (single_stack_alloc jump k max_stack_alloc)
            (stack_alloc_f fuel jump k (n - max_stack_alloc))
  end.

(** HOL [stack_alloc] (measure [n]). *)
Definition stack_alloc (jump : bool) (k n : N) : sprog :=
  stack_alloc_f (S (N.to_nat n)) jump k n.

Lemma stack_alloc_f_fuel : forall f1 f2 jump k n,
  (N.to_nat n < f1)%nat -> (N.to_nat n < f2)%nat ->
  stack_alloc_f f1 jump k n = stack_alloc_f f2 jump k n.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] jump k n H1 H2; try lia; cbn [stack_alloc_f].
  destruct (N.eqb_spec n 0); [reflexivity|].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply IH; unfold max_stack_alloc in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "stack_alloc_def" *)
Theorem stack_alloc_def : forall jump k n,
  stack_alloc jump k n =
    if n =? 0 then Skip else
    if n <=? max_stack_alloc then single_stack_alloc jump k n else
      Seq (single_stack_alloc jump k max_stack_alloc)
          (stack_alloc jump k (n - max_stack_alloc)).
Proof.
  intros jump k n; unfold stack_alloc at 1; cbn [stack_alloc_f].
  destruct (N.eqb_spec n 0); [reflexivity|].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply stack_alloc_f_fuel; unfold max_stack_alloc in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "single_stack_free_def" *)
Definition single_stack_free (k n : N) : sprog :=
  Inst (Arith (Binop asm.Add k k (Imm (word_offset n)))).

Fixpoint stack_free_f (fuel : nat) (k n : N) : sprog :=
  match fuel with
  | O => Skip
  | S fuel =>
      if n =? 0 then Skip else
      if n <=? max_stack_alloc then single_stack_free k n else
        Seq (single_stack_free k max_stack_alloc)
            (stack_free_f fuel k (n - max_stack_alloc))
  end.

(** HOL [stack_free] (measure [n]). *)
Definition stack_free (k n : N) : sprog := stack_free_f (S (N.to_nat n)) k n.

Lemma stack_free_f_fuel : forall f1 f2 k n,
  (N.to_nat n < f1)%nat -> (N.to_nat n < f2)%nat ->
  stack_free_f f1 k n = stack_free_f f2 k n.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] k n H1 H2; try lia; cbn [stack_free_f].
  destruct (N.eqb_spec n 0); [reflexivity|].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply IH; unfold max_stack_alloc in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "stack_free_def" *)
Theorem stack_free_def : forall k n,
  stack_free k n =
    if n =? 0 then Skip else
    if n <=? max_stack_alloc then single_stack_free k n else
      Seq (single_stack_free k max_stack_alloc)
          (stack_free k (n - max_stack_alloc)).
Proof.
  intros k n; unfold stack_free at 1; cbn [stack_free_f].
  destruct (N.eqb_spec n 0); [reflexivity|].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply stack_free_f_fuel; unfold max_stack_alloc in *; lia.
Qed.

Fixpoint upshift_f (fuel : nat) (r n : N) : sprog :=
  match fuel with
  | O => Skip
  | S fuel =>
      if n <=? max_stack_alloc then
        Inst (Arith (Binop asm.Add r r (Imm (word_offset n))))
      else
        Seq (Inst (Arith (Binop asm.Add r r (Imm (word_offset max_stack_alloc)))))
            (upshift_f fuel r (n - max_stack_alloc))
  end.

(** HOL [upshift] (measure [n]). *)
Definition upshift (r n : N) : sprog := upshift_f (S (N.to_nat n)) r n.

Lemma upshift_f_fuel : forall f1 f2 r n,
  (N.to_nat n < f1)%nat -> (N.to_nat n < f2)%nat -> upshift_f f1 r n = upshift_f f2 r n.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] r n H1 H2; try lia; cbn [upshift_f].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply IH; unfold max_stack_alloc in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "upshift_def" *)
Theorem upshift_def : forall r n,
  upshift r n =
    if n <=? max_stack_alloc then
      Inst (Arith (Binop asm.Add r r (Imm (word_offset n))))
    else
      Seq (Inst (Arith (Binop asm.Add r r (Imm (word_offset max_stack_alloc)))))
          (upshift r (n - max_stack_alloc)).
Proof.
  intros r n; unfold upshift at 1; cbn [upshift_f].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply upshift_f_fuel; unfold max_stack_alloc in *; lia.
Qed.

Fixpoint downshift_f (fuel : nat) (r n : N) : sprog :=
  match fuel with
  | O => Skip
  | S fuel =>
      if n <=? max_stack_alloc then
        Inst (Arith (Binop Sub r r (Imm (word_offset n))))
      else
        Seq (Inst (Arith (Binop Sub r r (Imm (word_offset max_stack_alloc)))))
            (downshift_f fuel r (n - max_stack_alloc))
  end.

(** HOL [downshift] (measure [n]). *)
Definition downshift (r n : N) : sprog := downshift_f (S (N.to_nat n)) r n.

Lemma downshift_f_fuel : forall f1 f2 r n,
  (N.to_nat n < f1)%nat -> (N.to_nat n < f2)%nat -> downshift_f f1 r n = downshift_f f2 r n.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] r n H1 H2; try lia; cbn [downshift_f].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply IH; unfold max_stack_alloc in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "downshift_def" *)
Theorem downshift_def : forall r n,
  downshift r n =
    if n <=? max_stack_alloc then
      Inst (Arith (Binop Sub r r (Imm (word_offset n))))
    else
      Seq (Inst (Arith (Binop Sub r r (Imm (word_offset max_stack_alloc)))))
          (downshift r (n - max_stack_alloc)).
Proof.
  intros r n; unfold downshift at 1; cbn [downshift_f].
  destruct (N.leb_spec n max_stack_alloc); [reflexivity|].
  f_equal; apply downshift_f_fuel; unfold max_stack_alloc in *; lia.
Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "stack_store_def" *)
Definition stack_store (k r n : N) : sprog :=
  Seq (upshift k n)
 (Seq (Inst (Mem asm.Store r (Addr k (n2w 0)))) (downshift k n)).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "stack_load_def" *)
Definition stack_load (r n : N) : sprog :=
  Seq (upshift r n) (Inst (Mem asm.Load r (Addr r (n2w 0)))).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "copy_each_def" *)
Definition copy_each (t1 t2 : N) : sprog :=
  While NotEqual 1 (Imm (n2w 1))
    (list_Seq [load_inst t1 t2;
               add_bytes_in_word_inst t2;
               If Test 1 (Imm (n2w 1)) Skip (add_inst t1 3);
               right_shift_inst 1 1;
               store_inst t1 2;
               add_bytes_in_word_inst 2]).

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "copy_loop_def" *)
Definition copy_loop (t1 t2 : N) : sprog :=
  list_Seq [load_inst 1 t2;
            add_bytes_in_word_inst t2;
            While Less 1 (Imm (n2w 0))
              (list_Seq [copy_each t1 t2;
                         load_inst 1 t2;
                         add_bytes_in_word_inst t2]);
            copy_each t1 t2].

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "comp_def" *)
Fixpoint comp (jump : bool) (off : word a * word a) (k : N) (p : sprog) : sprog :=
  match p with
  | Get r name =>
      if decide (name = CurrHeap) then move r (k + 2)
      else Inst (Mem asm.Load r (Addr (k + 1) (store_offset name)))
  | Set_ name r =>
      if decide (name = CurrHeap) then move (k + 2) r
      else Inst (Mem asm.Store r (Addr (k + 1) (store_offset name)))
  | OpCurrHeap op r n =>
      Inst (Arith (Binop op r n (Reg (k + 2))))
  | StackFree n => stack_free k n
  | StackAlloc n => stack_alloc jump k n
  | StackStore r n =>
      let w := word_offset n in
      if offset_ok 0 off w then Inst (Mem asm.Store r (Addr k w))
      else stack_store k r n
  | StackLoad r n =>
      let w := word_offset n in
      if offset_ok 0 off w then Inst (Mem asm.Load r (Addr k w))
      else Seq (move r k) (stack_load r n)
  | DataBufferWrite r1 r2 => Inst (Mem asm.Store r2 (Addr r1 (n2w 0)))
  | StackLoadAny r i => Seq (Seq (move r i) (add_inst r k))
                            (Inst (Mem asm.Load r (Addr r (n2w 0))))
  | StackStoreAny r i => Seq (Inst (Arith (Binop asm.Add k k (Reg i))))
                        (Seq (Inst (Mem asm.Store r (Addr k (n2w 0))))
                             (Inst (Arith (Binop Sub k k (Reg i)))))
  | StackGetSize r => Seq (Seq (move r k) (sub_inst r (k + 1)))
                          (right_shift_inst r (word_shift a))
  | StackSetSize r => Seq (left_shift_inst r (word_shift a))
                          (Seq (move k (k + 1)) (add_inst k r))
  | BitmapLoad r v =>
      list_Seq [Inst (Mem asm.Load r (Addr (k + 1) (store_offset BitmapBase)));
                add_inst r v;
                left_shift_inst r (word_shift a);
                Inst (Mem asm.Load r (Addr r (n2w 0)))]
  | StoreConsts t1 t2 _ =>
      list_Seq [Inst (Mem asm.Load t2 (Addr (k + 1) (store_offset BitmapBase)));
                add_inst t2 1;
                left_shift_inst t2 (word_shift a);
                copy_loop t1 t2;
                move t1 1;
                move t2 1]
  | Seq p1 p2 => Seq (comp jump off k p1) (comp jump off k p2)
  | If c r ri p1 p2 => If c r ri (comp jump off k p1) (comp jump off k p2)
  | Loop p1 => Loop (comp jump off k p1)
  | Call ret dest exc =>
      Call (match ret with
            | None => None
            | Some (p1, (lr, (l1, l2))) => Some (comp jump off k p1, (lr, (l1, l2)))
            end)
        dest (match exc with
              | None => None
              | Some (p2, (l1, l2)) => Some (comp jump off k p2, (l1, l2))
              end)
  | p => p
  end.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "prog_comp_def" *)
Definition prog_comp (jump : bool) (off : word a * word a) (k : N) (np : N * sprog) : N * sprog :=
  let '(n, p) := np in (n, comp jump off k p).

(** ** Init code *)

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "store_list_code_def" *)
Fixpoint store_list_code (a0 t : N) (l : list (word a + N)) : sprog :=
  match l with
  | [] => Skip
  | inl w :: xs =>
      Seq (list_Seq [const_inst t w; store_inst t a0; add_bytes_in_word_inst a0])
          (store_list_code a0 t xs)
  | inr i :: xs =>
      Seq (list_Seq [store_inst i a0; add_bytes_in_word_inst a0])
          (store_list_code a0 t xs)
  end.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "init_memory_def" *)
Definition init_memory (k : N) (xs : list (word a + N)) : sprog :=
  list_Seq [const_inst 0 bytes_in_word;
            sub_inst k 0;
            const_inst 0 (n2w 0);
            store_inst 0 k;
            store_list_code (k + 1) 0 xs].

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "store_init_def" *)
Definition store_init (gen_gc : bool) (k : N) : store_name -> word a + N :=
  UPDATE_LIST (combin.K (inl (n2w 0)))
    [(CurrHeap, inr (k + 2));
     (GlobReal, inr (k + 2));
     (NextFree, inr (k + 2));
     (TriggerGC, inr (if gen_gc then k + 2 else 2));
     (EndOfHeap, inr 2);
     (HeapLength, inr 5);
     (OtherHeap, inr 2);
     (BitmapBase, inr 3);
     (BitmapBuffer, inr 4);
     (BitmapBufferEnd, inr 6);
     (CodeBuffer, inr 7);
     (CodeBufferEnd, inr 1)].

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "init_code_def" *)
Definition init_code (gen_gc : bool) (max_heap k : N) : sprog :=
  let max_heap : word a :=
    if max_heap * w2n (bytes_in_word : word a) <? dimword a
    then word_mul (n2w max_heap) bytes_in_word
    else word_sub (n2w 0) (n2w 1) in
  list_Seq [move 0 4;
            sub_inst 0 2;
            right_shift_inst 0 (1 + word_shift a);
            left_shift_inst 0 (word_shift a);
            add_inst 0 2;
            const_inst 5 (word_mul (n2w max_stack_alloc) bytes_in_word : word a);
            add_inst 2 5;
            sub_inst 4 5;
            If Lower 3 (Reg 2) (move 3 0)
              (If Lower 4 (Reg 3) (move 3 0) Skip);
            const_inst 0 (word_mul (n2w max_stack_alloc) bytes_in_word : word a);
            sub_inst 2 0;
            add_inst 4 0;
            move 0 3;
            sub_inst 0 2;
            const_inst 5 max_heap;
            If Lower 5 (Reg 0) (Seq (move 3 2) (add_inst 3 5)) Skip;
            sub_inst 3 2;
            right_shift_inst 3 (word_shift a + 1);
            left_shift_inst 3 (word_shift a + 1);
            add_inst 3 2;
            move 5 3;
            sub_inst 5 2;
            right_shift_inst 5 1;
            move (k + 2) 2;
            add_inst 2 5;
            move k 4;
            move (k + 1) 3;
            load_inst 3 (k + 2);
            right_shift_inst 3 (word_shift a);
            move 0 (k + 2);
            add_bytes_in_word_inst 0;
            load_inst 4 0;
            add_bytes_in_word_inst 0;
            load_inst 6 0;
            add_bytes_in_word_inst 0;
            load_inst 7 0;
            add_bytes_in_word_inst 0;
            load_inst 1 0;
            init_memory k (MAP (store_init gen_gc k) (REVERSE store_list));
            LocValue 0 1 0].

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "init_stubs_def" *)
Definition init_stubs (gen_gc : bool) (max_heap k start : N) : list (N * sprog) :=
  [(0, Seq (init_code gen_gc max_heap k) (Call None (inl start) None));
   (1, halt_inst (n2w 0));
   (2, halt_inst (n2w 2))].

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "check_init_stubs_length" *)
Theorem check_init_stubs_length : forall gen_gc max_heap k start,
  LENGTH (init_stubs gen_gc max_heap k start) + 2 = stack_num_stubs.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "compile_def" *)
Definition compile (jump : bool) (off : word a * word a) (gen_gc : bool) (max_heap k start : N)
    (prog : list (N * sprog)) : list (N * sprog) :=
  init_stubs gen_gc max_heap k start ++ MAP (prog_comp jump off k) prog.

End StackRemove.

(*! HOL "cakeml/compiler/backend/stack_removeScript.sml" "stub_names_def" *)
Definition stub_names (u : unit) : list (N * mlstring) :=
  [(0, implode "_Init");
   (1, implode "_Halt0");
   (2, implode "_Halt2")].
