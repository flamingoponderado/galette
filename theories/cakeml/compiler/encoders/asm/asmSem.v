(** * CakeML [asmSem]: the semantics of ASM instructions

    Port of [cakeml/compiler/encoders/asm/asmSemScript.sml].

    - HOL's ['a asm_state] is [asm_state a] (width index [a]); its fields
      carry HOL's names, [s with f := v] is [set_<f> v s].  The address
      set [mem_domain : 'a word set] is [word a -> Prop].
    - HOL's functions [reg_imm], [addr], [inst] and [asm] share their names
      with the types of [asm.v].  Rocq has one namespace, so after this file
      the short names denote the functions; the types remain available as
      [asm.reg_imm], [asm.addr], [asm.inst], [asm.asm].
    - [assert b] takes a HOL boolean ([bool]); the memory-domain tests
      [a IN s.mem_domain] are decided classically ([classical_dec]), as
      [mem_domain] is an arbitrary set.
    - [fp_upd] mentions the IEEE operations [fp64_*]/[int_to_fp64] of
      [machine_ieee], which Galette has not ported: they are the untagged
      [ARB] stand-ins of [HOL/src/floating_point/machine_ieee.v], so
      [fp_upd] (and through it [inst]/[asm]/[asm_step]) is HOL's text but
      its floating-point results are unspecified there. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.n_bit Require Import words alignment.
From Galette.HOL.src.integer Require Import integer_word.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.floating_point Require Import binary_ieee machine_ieee.
From Galette.cakeml.semantics Require Import ast.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
Open Scope N_scope.

(** ** The state *)

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "asm_state" *)
Record asm_state (a : N) : Type := mk_asm_state {
  regs : N -> word a;
  fp_regs : N -> word64;
  mem : word a -> word8;
  mem_domain : word a -> Prop;
  pc : word a;
  lr : reg;
  align : N;
  be : bool;
  failed : bool
}.
Arguments mk_asm_state {a} _ _ _ _ _ _ _ _ _.
Arguments regs {a} _.
Arguments fp_regs {a} _.
Arguments mem {a} _.
Arguments mem_domain {a} _.
Arguments pc {a} _.
Arguments lr {a} _.
Arguments align {a} _.
Arguments be {a} _.
Arguments failed {a} _.

#[global] Instance asm_state_inhabited {a} : Inhabited (asm_state a) :=
  mk_asm_state (fun _ => n2w 0) (fun _ => n2w 0) (fun _ => n2w 0)
    (fun _ => False) (n2w 0) 0 0 false false.

Section AsmSem.
Context {a : N}.
Implicit Types (s : asm_state a).

(** Record updates [s with f := v]. *)
Definition set_regs x s := mk_asm_state x s.(fp_regs) s.(mem) s.(mem_domain) s.(pc) s.(lr) s.(align) s.(be) s.(failed).
Definition set_fp_regs x s := mk_asm_state s.(regs) x s.(mem) s.(mem_domain) s.(pc) s.(lr) s.(align) s.(be) s.(failed).
Definition set_mem x s := mk_asm_state s.(regs) s.(fp_regs) x s.(mem_domain) s.(pc) s.(lr) s.(align) s.(be) s.(failed).
Definition set_mem_domain x s := mk_asm_state s.(regs) s.(fp_regs) s.(mem) x s.(pc) s.(lr) s.(align) s.(be) s.(failed).
Definition set_pc x s := mk_asm_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) x s.(lr) s.(align) s.(be) s.(failed).
Definition set_lr x s := mk_asm_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(pc) x s.(align) s.(be) s.(failed).
Definition set_align x s := mk_asm_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(pc) s.(lr) x s.(be) s.(failed).
Definition set_be x s := mk_asm_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(pc) s.(lr) s.(align) x s.(failed).
Definition set_failed x s := mk_asm_state s.(regs) s.(fp_regs) s.(mem) s.(mem_domain) s.(pc) s.(lr) s.(align) s.(be) x.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "upd_pc_def" *)
Definition upd_pc (pc0 : word a) s : asm_state a := set_pc pc0 s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "upd_reg_def" *)
Definition upd_reg (r : N) (v : word a) s : asm_state a :=
  set_regs ((r =+ v) s.(regs)) s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "upd_fp_reg_def" *)
Definition upd_fp_reg (r : N) (v : word64) s : asm_state a :=
  set_fp_regs ((r =+ v) s.(fp_regs)) s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "upd_mem_def" *)
Definition upd_mem (ad : word a) (b : word8) s : asm_state a :=
  set_mem ((ad =+ b) s.(mem)) s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "read_reg_def" *)
Definition read_reg (r : N) s : word a := s.(regs) r.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "read_fp_reg_def" *)
Definition read_fp_reg (r : N) s : word64 := s.(fp_regs) r.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "read_mem_def" *)
Definition read_mem (ad : word a) s : word8 := s.(mem) ad.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "assert_def" *)
Definition assert (b : bool) s : asm_state a :=
  set_failed (negb b || s.(failed)) s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "reg_imm_def" *)
Definition reg_imm (ri : asm.reg_imm a) s : word a :=
  match ri with
  | Reg r => read_reg r s
  | Imm w => w
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "binop_upd_def" *)
Definition binop_upd (r : N) (b : binop) (w1 w2 : word a) : asm_state a -> asm_state a :=
  match b with
  | Add => upd_reg r (w1 + w2)%w
  | Sub => upd_reg r (w1 - w2)%w
  | And => upd_reg r (word_and w1 w2)
  | Or => upd_reg r (word_or w1 w2)
  | Xor => upd_reg r (word_xor w1 w2)
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "word_shift_def" *)
Definition word_shift (l : shift) (w : word a) (n : N) : word a :=
  match l with
  | Lsl => (w << n)%w
  | Lsr => (w >>> n)%w
  | Asr => (w >> n)%w
  | Ror => word_ror w n
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "arith_upd_def" *)
Definition arith_upd (x : arith a) s : asm_state a :=
  match x with
  | Binop b r1 r2 ri =>
      binop_upd r1 b (read_reg r2 s) (reg_imm ri s) s
  | Shift l r1 r2 ri =>
      assert (match ri with Reg r => w2n (read_reg r s) <? dimindex a | _ => true end)
        (upd_reg r1 (word_shift l (read_reg r2 s) (w2n (reg_imm ri s))) s)
  | Div r1 r2 r3 =>
      let q := read_reg r3 s in
      assert (negb (bool_decide (q = n2w 0))) (upd_reg r1 (word_quot (read_reg r2 s) q) s)
  | LongMul r1 r2 r3 r4 =>
      let r := w2n (read_reg r3 s) * w2n (read_reg r4 s) in
      upd_reg r2 (n2w r) (upd_reg r1 (n2w (r DIV dimword a)) s)
  | LongDiv r1 r2 r3 r4 r5 =>
      let n := w2n (read_reg r3 s) * dimword a + w2n (read_reg r4 s) in
      let d := w2n (read_reg r5 s) in
      let q := n DIV d in
      assert (negb (d =? 0) && (q <? dimword a))
        (upd_reg r1 (n2w q) (upd_reg r2 (n2w (n MOD d)) s))
  | AddCarry r1 r2 r3 r4 =>
      let r := w2n (read_reg r2 s) + w2n (read_reg r3 s) +
               (if bool_decide (read_reg r4 s = n2w 0) then 0 else 1) in
      upd_reg r4 (if dimword a <=? r then n2w 1 else n2w 0)
        (upd_reg r1 (n2w r) s)
  | AddOverflow r1 r2 r3 r4 =>
      let w2 := read_reg r2 s in
      let w3 := read_reg r3 s in
      upd_reg r4 (if negb (Z.eqb (w2i (w2 + w3)%w) (w2i w2 + w2i w3)%Z) then n2w 1 else n2w 0)
        (upd_reg r1 (w2 + w3)%w s)
  | SubOverflow r1 r2 r3 r4 =>
      let w2 := read_reg r2 s in
      let w3 := read_reg r3 s in
      upd_reg r4 (if negb (Z.eqb (w2i (w2 - w3)%w) (w2i w2 - w2i w3)%Z) then n2w 1 else n2w 0)
        (upd_reg r1 (w2 - w3)%w s)
  end.

(** The [fp64_*] and [int_to_fp64] operations are the untagged [ARB]
    stand-ins of [machine_ieee.v] (see the file header). *)
(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "fp_upd_def" *)
Definition fp_upd (x : fp) s : asm_state a :=
  match x with
  | FPLess r d1 d2 =>
      upd_reg r (if fp64_lessThan (read_fp_reg d1 s) (read_fp_reg d2 s)
                 then n2w 1 else n2w 0) s
  | FPLessEqual r d1 d2 =>
      upd_reg r (if fp64_lessEqual (read_fp_reg d1 s) (read_fp_reg d2 s)
                 then n2w 1 else n2w 0) s
  | FPEqual r d1 d2 =>
      upd_reg r (if fp64_equal (read_fp_reg d1 s) (read_fp_reg d2 s)
                 then n2w 1 else n2w 0) s
  | FPMov d1 d2 => upd_fp_reg d1 (read_fp_reg d2 s) s
  | FPAbs d1 d2 => upd_fp_reg d1 (fp64_abs (read_fp_reg d2 s)) s
  | FPNeg d1 d2 => upd_fp_reg d1 (fp64_negate (read_fp_reg d2 s)) s
  | FPSqrt d1 d2 =>
      upd_fp_reg d1 (fp64_sqrt roundTiesToEven (read_fp_reg d2 s)) s
  | FPAdd d1 d2 d3 =>
      upd_fp_reg d1
        (fp64_add roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPSub d1 d2 d3 =>
      upd_fp_reg d1
        (fp64_sub roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPMul d1 d2 d3 =>
      upd_fp_reg d1
        (fp64_mul roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPDiv d1 d2 d3 =>
      upd_fp_reg d1
        (fp64_div roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s
  | FPFma d1 d2 d3 =>
      upd_fp_reg d1
        (fp64_mul_add roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)
           (read_fp_reg d1 s)) s
  | FPMovToReg r1 r2 d =>
      if dimindex a =? 64 then
        upd_reg r1 (w2w (read_fp_reg d s)) s
      else let v := read_fp_reg d s in
        upd_reg r2 ((63 >< 32) v)%w (upd_reg r1 ((31 >< 0) v)%w s)
  | FPMovFromReg d r1 r2 =>
      upd_fp_reg d
        (if dimindex a =? 64 then
           w2w (read_reg r1 s)
         else
           (read_reg r2 s @@ read_reg r1 s)%w) s
  | FPToInt d1 d2 =>
      match fp64_to_int roundTiesToEven (read_fp_reg d2 s) with
      | Some i =>
          let w := (i2w i : word32) in
          (if dimindex a =? 64 then
             upd_fp_reg d1 (w2w w)
           else let '(h, l) := if ODD d1 then (63, 32) else (31, 0) in
             upd_fp_reg (d1 DIV 2)
               (bit_field_insert h l w (read_fp_reg (d1 DIV 2) s)))
            (assert (Z.eqb (w2i w) i) s)
      | _ => assert false s
      end
  | FPFromInt d1 d2 =>
      let i := if dimindex a =? 64 then
                 w2i ((31 >< 0) (read_fp_reg d2 s) : word32)%w
               else let v := read_fp_reg (d2 DIV 2) s in
                 w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : word a)%w
      in
      upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "addr_def" *)
Definition addr (x : asm.addr a) s : word a :=
  match x with Addr r offset => (read_reg r s + offset)%w end.

(** [read_mem_word], by primitive recursion on the byte count; HOL's
    equations are [read_mem_word_def] below. *)
Definition read_mem_word (ad : word a) (n : N) s : word a * asm_state a :=
  num_rec (fun (_ : word a) s => (n2w 0, s))
    (fun _ rec ad s =>
       let '(w, s1) := rec (if s.(be) then (ad - n2w 1)%w else (ad + n2w 1)%w) s in
       (word_or (w << 8)%w (w2w (read_mem ad s1)),
        assert (if classical_dec (ad IN s1.(mem_domain)) then true else false) s1))
    n ad s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "read_mem_word_def" *)
Theorem read_mem_word_def : forall ad n s,
  read_mem_word ad 0 s = (n2w 0, s) /\
  read_mem_word ad (SUC n) s =
    let '(w, s1) := read_mem_word (if s.(be) then (ad - n2w 1)%w else (ad + n2w 1)%w) n s in
    (word_or (w << 8)%w (w2w (read_mem ad s1)),
     assert (if classical_dec (ad IN s1.(mem_domain)) then true else false) s1).
Proof.
  intros ad n s; split; [reflexivity|].
  unfold read_mem_word; rewrite num_rec_SUC; reflexivity.
Qed.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "mem_load_def" *)
Definition mem_load (n : N) (r : N) (x : asm.addr a) s : asm_state a :=
  let ad := addr x s in
  let '(w, s) := read_mem_word (if s.(be) then (ad + n2w (n - 1))%w else ad) n s in
  let s := upd_reg r w s in
  assert (aligned (LOG2 n) ad) s.

(** [write_mem_word], by primitive recursion; HOL's equations are
    [write_mem_word_def] below. *)
Definition write_mem_word (ad : word a) (n : N) (w : word a) s : asm_state a :=
  num_rec (fun (_ : word a) (_ : word a) s => s)
    (fun _ rec ad w s =>
       let s1 := rec (if s.(be) then (ad - n2w 1)%w else (ad + n2w 1)%w) (w >>> 8)%w s in
       assert (if classical_dec (ad IN s1.(mem_domain)) then true else false)
         (upd_mem ad (w2w w) s1))
    n ad w s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "write_mem_word_def" *)
Theorem write_mem_word_def : forall ad n w s,
  write_mem_word ad 0 w s = s /\
  write_mem_word ad (SUC n) w s =
    let s1 := write_mem_word (if s.(be) then (ad - n2w 1)%w else (ad + n2w 1)%w) n (w >>> 8)%w s in
    assert (if classical_dec (ad IN s1.(mem_domain)) then true else false)
      (upd_mem ad (w2w w) s1).
Proof.
  intros ad n w s; split; [reflexivity|].
  unfold write_mem_word; rewrite num_rec_SUC; reflexivity.
Qed.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "mem_store_def" *)
Definition mem_store (n : N) (r : N) (x : asm.addr a) s : asm_state a :=
  let ad := addr x s in
  let w := read_reg r s in
  let s := write_mem_word (if s.(be) then (ad + n2w (n - 1))%w else ad) n w s in
  assert (aligned (LOG2 n) ad) s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "mem_op_def" *)
Definition mem_op (m : memop) (r : N) (x : asm.addr a) : asm_state a -> asm_state a :=
  match m with
  | Load => mem_load (dimindex a DIV 8) r x
  | Store => mem_store (dimindex a DIV 8) r x
  | Load8 => mem_load 1 r x
  | Store8 => mem_store 1 r x
  | Load16 => mem_load 2 r x
  | Store16 => mem_store 2 r x
  | Load32 => mem_load 4 r x
  | Store32 => mem_store 4 r x
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "inst_def" *)
Definition inst (i : asm.inst a) s : asm_state a :=
  match i with
  | Skip => s
  | Const r imm => upd_reg r imm s
  | Arith x => arith_upd x s
  | Mem m r x => mem_op m r x s
  | FP fp => fp_upd fp s
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "jump_to_offset_def" *)
Definition jump_to_offset (w : word a) s : asm_state a :=
  upd_pc (s.(pc) + w)%w s.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "asm_def" *)
Definition asm (i : asm.asm a) (pc0 : word a) s : asm_state a :=
  match i with
  | Inst i => upd_pc pc0 (inst i s)
  | Jump l => jump_to_offset l s
  | JumpCmp c r ri l =>
      if word_cmp c (read_reg r s) (reg_imm ri s)
      then jump_to_offset l s
      else upd_pc pc0 s
  | Call l => jump_to_offset l (upd_reg s.(lr) pc0 s)
  | JumpReg r =>
      let ad := read_reg r s in upd_pc ad (assert (aligned s.(align) ad) s)
  | Loc r l => upd_pc pc0 (upd_reg r (s.(pc) + l)%w s)
  end.

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "is_test_def" *)
Definition is_test (c : cmp) : bool :=
  bool_decide (c = Test) || bool_decide (c = NotTest).

(*! HOL "cakeml/compiler/encoders/asm/asmSemScript.sml" "asm_step_def" *)
Definition asm_step (c : asm_config a) (s1 : asm_state a) (i : asm.asm a)
    (s2 : asm_state a) : Prop :=
  bytes_in_memory s1.(pc) (encode c i) s1.(mem) s1.(mem_domain) /\
  (match link_reg c with Some r => s1.(lr) = r | None => True end) /\
  (s1.(be) = big_endian c) /\
  (s1.(align) = code_alignment c) /\
  (asm i (s1.(pc) + n2w (LENGTH (encode c i)))%w s1 = s2) /\
  ~ s2.(failed) /\ asm_ok i c.

End AsmSem.
