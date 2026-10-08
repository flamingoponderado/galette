(** * CakeML Pancake [crepSem]: semantics of crepLang

    Port of [cakeml/pancake/semantics/crepSemScript.sml], following the
    recipe of [panSem.v].  Carrier notes:
    - [state] is a Rocq record with HOL's field names; HOL's
      [s with f := v] is [set_<f> v s] (helpers below).  There is no field
      helper for [globals]: HOL's own [set_globals] (a different function,
      [set_globals gv w s]) is ported under its name.
    - [word_lab], [Word], [isWord], [theWord] and the memory helpers
      ([mem_load_32], [mem_load_byte], [mem_store], [mem_store_32],
      [mem_store_byte], [write_bytearray]) are panSem's (HOL: [panSem] is an
      ancestor); they are imported by name since the other panSem names
      ([state], [eval], [evaluate], [result], ...) clash with this file's.
    - The constructors [Break], [Continue], [Return] of [result] shadow the
      crepLang program constructors, written [crepLang.Break] etc.; the
      [asm] memops [Load], [Store], [Load32] are written [asm.Load] etc.
    - Sets ([memaddrs], [sh_memaddrs]) are [_ -> Prop], tested with
      [classical_dec] (the semantics is not executable).
    - [evaluate] (HOL: well-founded recursion on (clock, program size)) is
      [evaluate_c] with a clock fuel, as in [panSem.v]; [evaluate_eqn] is its
      unfolding and HOL's final [evaluate_def] is proved from it.

    Not ported: the generated induction theorems
    [eval_ind]/[evaluate_ind] (and the rebound [evaluate_ind]) are not
    ported: their statements are produced by HOL's definition package and
    do not appear in the script. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte bitstring.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
From Galette.cakeml.pancake Require panLang.
From Galette.cakeml.pancake Require Import crepLang.
From Galette.cakeml.pancake.semantics Require panSem.
Import panSem(word_lab(..), isWord, theWord, mem_load_32, mem_load_byte, mem_store,
              mem_store_32, mem_store_byte, write_bytearray).
Open Scope N_scope.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "varname" *)
Abbreviation varname := N.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "funname" *)
Abbreviation funname := mlstring.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "state" *)
Record state (a : N) (ffi : Type) : Type := mk_state {
  locals : fmap varname (word_lab a);
  globals : fmap (word 5) (word_lab a);
  code : fmap funname (list varname * prog a);
  memory : word a -> word_lab a;
  memaddrs : word a -> Prop;
  sh_memaddrs : word a -> Prop;
  clock : N;
  be : bool;
  ffi : ffi_state ffi;
  base_addr : word a;
  top_addr : word a
}.
Arguments mk_state {a ffi}.
Arguments locals {a ffi}. Arguments globals {a ffi}. Arguments code {a ffi}.
Arguments memory {a ffi}. Arguments memaddrs {a ffi}. Arguments sh_memaddrs {a ffi}.
Arguments clock {a ffi}. Arguments be {a ffi}. Arguments ffi {a ffi}.
Arguments base_addr {a ffi}. Arguments top_addr {a ffi}.

(** HOL [s with f := x] for each field used. *)
Section Updates.
Context {a : N} {ffi_t : Type}.
Definition set_locals x (s : state a ffi_t) := mk_state x s.(globals) s.(code) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_code x (s : state a ffi_t) := mk_state s.(locals) s.(globals) x s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_memory x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(code) x s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_clock x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(code) s.(memory) s.(memaddrs) s.(sh_memaddrs) x s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_ffi (x : ffi_state ffi_t) (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(code) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) x s.(base_addr) s.(top_addr).
End Updates.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "result" *)
Inductive result (a : N) : Type :=
| Error : result a
| TimeOut : result a
| Break : N -> result a
| Continue : N -> result a
| Return : list (word_lab a) -> result a
| Exception : word a -> result a
| FinalFFI : final_event -> result a.
Arguments Error {a}. Arguments TimeOut {a}. Arguments Break {a} _. Arguments Continue {a} _.
Arguments Return {a} _. Arguments Exception {a} _. Arguments FinalFFI {a} _.

Section Defs.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "mem_load_def" *)
Definition mem_load (addr : word a) (s : state a ffi_t) : option (word_lab a) :=
  if classical_dec (addr IN memaddrs s) then SOME (memory s addr) else NONE.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "set_var_def" *)
Definition set_var (v : varname) (w : word_lab a) (s : state a ffi_t) : state a ffi_t :=
  set_locals (locals s |+ (v, w)) s.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "set_globals_def" *)
Definition set_globals (gv : word 5) (w : word_lab a) (s : state a ffi_t) : state a ffi_t :=
  mk_state s.(locals) (globals s |+ (gv, w)) s.(code) s.(memory) s.(memaddrs) s.(sh_memaddrs)
    s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "upd_locals_def" *)
Definition upd_locals (varargs : list (varname * word_lab a)) (s : state a ffi_t) : state a ffi_t :=
  set_locals (FEMPTY |++ varargs) s.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "empty_locals_def" *)
Definition empty_locals (s : state a ffi_t) : state a ffi_t := set_locals FEMPTY s.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "lookup_code_def" *)
Definition lookup_code {K Nm P C} `{EqDecision Nm} (code0 : fmap K (list Nm * P)) (fname : K)
    (args : list (word_lab a)) (len : C) : option (P * fmap Nm (word_lab a)) :=
  match FLOOKUP code0 fname with
  | SOME (ns, prog0) =>
      if andb (LENGTH ns =? LENGTH args) (ALL_DISTINCT ns)
      then SOME (prog0, FEMPTY |++ ZIP (ns, args)) else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "crep_op_def" *)
Definition crep_op (op : crepop) (ws : list (word a)) : option (word a) :=
  match op, ws with
  | Mul, [w1; w2] => SOME (w1 * w2)
  | _, _ => NONE
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "eval_def" *)
Fixpoint eval (s : state a ffi_t) (e : exp a) {struct e} : option (word_lab a) :=
  match e with
  | Const w => SOME (Word w)
  | Var v => FLOOKUP (locals s) v
  | Load addr =>
      match eval s addr with
      | SOME (Word w) => mem_load w s
      | _ => NONE
      end
  | Load32 addr =>
      match eval s addr with
      | SOME (Word w) =>
          match mem_load_32 (memory s) (memaddrs s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (Word (w2w w))
          end
      | _ => NONE
      end
  | LoadByte addr =>
      match eval s addr with
      | SOME (Word w) =>
          match mem_load_byte (memory s) (memaddrs s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (Word (w2w w))
          end
      | _ => NONE
      end
  | LoadGlob gadr => FLOOKUP (globals s) gadr
  | Op op es =>
      match OPT_MMAP (eval s) es with
      | SOME ws =>
          if EVERY (fun w => match w with Word _ => true end) ws
          then OPTION_MAP Word (wordLang.word_op op (MAP (fun w => match w with Word n => n end) ws))
          else NONE
      | _ => NONE
      end
  | Crepop op es =>
      match OPT_MMAP (eval s) es with
      | SOME ws =>
          if EVERY (fun w => match w with Word _ => true end) ws
          then OPTION_MAP Word (crep_op op (MAP (fun w => match w with Word n => n end) ws))
          else NONE
      | _ => NONE
      end
  | Cmp cmp e1 e2 =>
      match eval s e1, eval s e2 with
      | SOME (Word w1), SOME (Word w2) =>
          SOME (Word (v2w [word_cmp cmp w1 w2]))
      | _, _ => NONE
      end
  | Shift sh e1 e2 =>
      match eval s e1, eval s e2 with
      | SOME (Word w1), SOME (Word w2) => OPTION_MAP Word (wordLang.word_sh sh w1 (w2n w2))
      | _, _ => NONE
      end
  | BaseAddr => SOME (Word (base_addr s))
  | TopAddr => SOME (Word (top_addr s))
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "dec_clock_def" *)
Definition dec_clock (s : state a ffi_t) : state a ffi_t := set_clock (clock s - 1) s.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "fix_clock_def" *)
Definition fix_clock {R} (old_s : state a ffi_t) (p : R * state a ffi_t) : R * state a ffi_t :=
  let '(res, new_s) := p in
  (res, set_clock (if clock old_s <? clock new_s then clock old_s else clock new_s) new_s).

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "fix_clock_IMP_LESS_EQ" *)
Theorem fix_clock_IMP_LESS_EQ : forall {R} (s : state a ffi_t) (x : R * state a ffi_t) res s1,
  fix_clock s x = (res, s1) -> (clock s1 <= clock s)%N.
Proof.
  intros R s [r s'] res s1 H; cbn in H; inversion H; subst; cbn.
  destruct (N.ltb_spec (clock s) (clock s')); lia.
Qed.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "res_var_def" *)
Definition res_var {K V} `{EqDecision K} (lc : fmap K V) (p : K * option V)
    : fmap K V :=
  match p with
  | (n, NONE) => lc \\ n
  | (n, SOME v) => lc |+ (n, v)
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_load_def" *)
Definition sh_mem_load (v : varname) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  if (nb =? 0)%N then
    (if classical_dec (addr IN sh_memaddrs s) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_var v (Word (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s))
  else
    (if classical_dec (byte_align addr IN sh_memaddrs s) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_var v (Word (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s)).

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_store_def" *)
Definition sh_mem_store (v : varname) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  match FLOOKUP (locals s) v with
  | SOME (Word w) =>
      if (nb =? 0)%N then
        (if classical_dec (addr IN sh_memaddrs s) then
           match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
                   (word_to_bytes w false ++ word_to_bytes addr false) with
           | FFI_final outcome => (SOME (FinalFFI outcome), s)
           | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
           end
         else (SOME Error, s))
      else
        (if classical_dec (byte_align addr IN sh_memaddrs s) then
           match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
                   (TAKE nb (word_to_bytes w false) ++ word_to_bytes addr false) with
           | FFI_final outcome => (SOME (FinalFFI outcome), s)
           | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
           end
         else (SOME Error, s))
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_op_def" *)
Definition sh_mem_op (op : memop) (r : varname) (ad : word a) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  match op with
  | asm.Load => sh_mem_load r ad 0 s
  | asm.Store => sh_mem_store r ad 0 s
  | Load8 => sh_mem_load r ad 1 s
  | Store8 => sh_mem_store r ad 1 s
  | Load16 => sh_mem_load r ad 2 s
  | Store16 => sh_mem_store r ad 2 s
  | asm.Load32 => sh_mem_load r ad 4 s
  | asm.Store32 => sh_mem_store r ad 4 s
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "crep_primop_def" *)
Definition crep_primop (pop : panLang.primop) (args : list (word_lab a)) : option (list (word_lab a)) :=
  match pop with
  | panLang.AddCarry =>
      if andb (LENGTH args =? 3)%N (EVERY isWord args) then
        let l := theWord (EL 0 args) in
        let r := theWord (EL 1 args) in
        let ci := theWord (EL 2 args) in
        let '(res, co) := backend_common.word_add_carry l r ci in
        SOME [Word res; Word co]
      else NONE
  end.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "exit_loop_def" *)
Definition exit_loop (res : option (result a)) : option (result a) :=
  match res with
  | SOME (Break n) => SOME (Break (n - 1))
  | SOME (Continue n) => SOME (Continue (n - 1))
  | res => res
  end.

End Defs.

Section Evaluate.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(** [fix_clock old (f p old)], the shape in which HOL's [evaluate] uses
    [fix_clock]; a name for it lets [fix_clock_evaluate] be rewritten under
    binders (see [evaluate_def]). *)
Definition fcl (f : prog a -> state a ffi_t -> option (result a) * state a ffi_t)
    (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
  fix_clock s (f p s).

(** One step of HOL's [evaluate]: [go] evaluates at the same clock bound
    (structurally smaller programs), [lower] at a smaller clock. *)
Definition evaluate_body
    (go lower : prog a -> state a ffi_t -> option (result a) * state a ffi_t)
    (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
  match p with
  | Skip => (NONE, s)
  | Dec v e prog0 =>
      match eval s e with
      | SOME value =>
          let '(res, st) := go prog0 (set_locals (locals s |+ (v, value)) s) in
          (res, set_locals (res_var (locals st) (v, FLOOKUP (locals s) v)) st)
      | NONE => (SOME Error, s)
      end
  | Primitive lhss pop rhss =>
      match OPT_MMAP (FLOOKUP (locals s)) rhss with
      | SOME ws =>
          match crep_primop pop ws with
          | SOME res_ws =>
              if andb (LENGTH lhss =? LENGTH res_ws)
                      (andb (EVERY (fun v => IS_SOME (FLOOKUP (locals s) v)) lhss)
                            (ALL_DISTINCT lhss))
              then (NONE, set_locals (locals s |++ ZIP (lhss, res_ws)) s)
              else (SOME Error, s)
          | NONE => (SOME Error, s)
          end
      | NONE => (SOME Error, s)
      end
  | Assign v src =>
      match eval s src with
      | NONE => (SOME Error, s)
      | SOME w =>
          match FLOOKUP (locals s) v with
          | SOME _ => (NONE, set_locals (locals s |+ (v, w)) s)
          | _ => (SOME Error, s)
          end
      end
  | Store dst src =>
      match eval s dst, eval s src with
      | SOME (Word adr), SOME w =>
          match mem_store adr w (memaddrs s) (memory s) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | Store32 dst src =>
      match eval s dst, eval s src with
      | SOME (Word adr), SOME (Word w) =>
          match mem_store_32 (memory s) (memaddrs s) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | StoreByte dst src =>
      match eval s dst, eval s src with
      | SOME (Word adr), SOME (Word w) =>
          match mem_store_byte (memory s) (memaddrs s) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | StoreGlob dst src =>
      match eval s src with
      | SOME w => (NONE, set_globals dst w s)
      | _ => (SOME Error, s)
      end
  | ShMem op v ad =>
      match eval s ad with
      | SOME (Word addr) =>
          if is_load op then
            match FLOOKUP (locals s) v with
            | SOME _ => sh_mem_op op v addr s
            | _ => (SOME Error, s)
            end
          else
            match FLOOKUP (locals s) v with
            | SOME (Word _) => sh_mem_op op v addr s
            | _ => (SOME Error, s)
            end
      | _ => (SOME Error, s)
      end
  | Seq c1 c2 =>
      let '(res, s1) := fcl go c1 s in
      match res with NONE => go c2 s1 | _ => (res, s1) end
  | If e c1 c2 =>
      match eval s e with
      | SOME (Word w) => go (if negb (bool_decide (w = n2w 0)) then c1 else c2) s
      | _ => (SOME Error, s)
      end
  | crepLang.Break n => (SOME (Break n), s)
  | crepLang.Continue n => (SOME (Continue n), s)
  | While e c =>
      match eval s e with
      | SOME (Word w) =>
          if negb (bool_decide (w = n2w 0)) then
            if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
            else
              let '(res, s1) := fcl go c (dec_clock s) in
              match res with
              | SOME (Continue 0) => lower (While e c) s1
              | NONE => lower (While e c) s1
              | SOME (Break 0) => (NONE, s1)
              | res => (exit_loop res, s1)
              end
          else (NONE, s)
      | _ => (SOME Error, s)
      end
  | crepLang.Return es =>
      match OPT_MMAP (eval s) es with
      | SOME ws => (SOME (Return ws), empty_locals s)
      | _ => (SOME Error, s)
      end
  | Raise eid => (SOME (Exception eid), empty_locals s)
  | Tick =>
      if (clock s =? 0)%N then (SOME TimeOut, empty_locals s) else (NONE, dec_clock s)
  | Call caltyp fname argexps =>
      match OPT_MMAP (eval s) argexps with
      | SOME args =>
          match lookup_code (code s) fname args (LENGTH args) with
          | SOME (prog0, newlocals) =>
              if match caltyp with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end
              then (SOME Error, s)
              else
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
              else
                let eval_prog := fcl lower prog0 (set_locals newlocals (dec_clock s)) in
                match eval_prog with
                | (NONE, st) => (SOME Error, st)
                | (SOME (Break n), st) => (SOME Error, st)
                | (SOME (Continue n), st) => (SOME Error, st)
                | (SOME (Return retvs), st) =>
                    match caltyp with
                    | NONE => (SOME (Return retvs), empty_locals st)
                    | SOME (rts, _) =>
                        if negb (LENGTH retvs =? LENGTH rts) then (SOME Error, st)
                        else
                          match OPT_MMAP (FLOOKUP (locals s)) rts with
                          | SOME _ => (NONE, set_locals (locals s |++ ZIP (rts, retvs)) st)
                          | _ => (SOME Error, st)
                          end
                    end
                | (SOME (Exception eid), st) =>
                    match caltyp with
                    | NONE => (SOME (Exception eid), empty_locals st)
                    | SOME (_, NONE) => (SOME (Exception eid), empty_locals st)
                    | SOME (_, SOME (eid', p)) =>
                        if bool_decide (eid = eid') then lower p (set_locals (locals s) st)
                        else (SOME (Exception eid), empty_locals st)
                    end
                | (res, st) => (res, empty_locals st)
                end
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | ExtCall ffi_index ptr1 len1 ptr2 len2 =>
      match FLOOKUP (locals s) len1, FLOOKUP (locals s) ptr1,
            FLOOKUP (locals s) len2, FLOOKUP (locals s) ptr2 with
      | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
          match read_bytearray w2 (w2n w) (mem_load_byte (memory s) (memaddrs s) (be s)),
                read_bytearray w4 (w2n w3) (mem_load_byte (memory s) (memaddrs s) (be s)) with
          | SOME bytes, SOME bytes2 =>
              match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (SOME (FinalFFI outcome), s)
              | FFI_return new_ffi new_bytes =>
                  let nmem := write_bytearray w4 new_bytes (memory s) (memaddrs s) (be s) in
                  (NONE, set_ffi new_ffi (set_memory nmem s))
              end
          | _, _ => (SOME Error, s)
          end
      | _, _, _, _ => (SOME Error, s)
      end
  end.

Fixpoint evaluate_c (cf : nat) (p0 : prog a) (s0 : state a ffi_t) {struct cf}
    : option (result a) * state a ffi_t :=
  let lower (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
    match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c cf' p s end in
  let fix go (p : prog a) (s : state a ffi_t) {struct p} : option (result a) * state a ffi_t :=
    evaluate_body go lower p s in
  go p0 s0.

(** HOL [evaluate]: run with a clock fuel above the state's clock. *)
Definition evaluate (x : prog a * state a ffi_t) : option (result a) * state a ffi_t :=
  let '(p, s) := x in evaluate_c (Datatypes.S (N.to_nat (clock s))) p s.

End Evaluate.

(** ** Clock lemmas, fuel independence and HOL's [evaluate_def] *)
Section EvaluateEqns.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "clock_eq_simp" *)
Theorem clock_eq_simp : forall v w (s : state a ffi_t) gv,
  clock (set_var v w s) = clock s /\
  clock (empty_locals s) = clock s /\
  clock (set_globals gv w s) = clock s.
Proof. intros; repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_load_clock" *)
Theorem sh_mem_load_clock : forall v (addr : word a) nb (s : state a ffi_t) r s',
  sh_mem_load v addr nb s = (r, s') -> clock s' = clock s.
Proof.
  intros v addr nb s r s' H; unfold sh_mem_load in H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end; injection H as <- <-; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_store_clock" *)
Theorem sh_mem_store_clock : forall v (addr : word a) nb (s : state a ffi_t) r s',
  sh_mem_store v addr nb s = (r, s') -> clock s' = clock s.
Proof.
  intros v addr nb s r s' H; unfold sh_mem_store in H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in H
         end; injection H as <- <-; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "sh_mem_op_clock" *)
Theorem sh_mem_op_clock : forall op v (addr : word a) (s : state a ffi_t) r s',
  sh_mem_op op v addr s = (r, s') -> clock s' = clock s.
Proof.
  intros op v addr s r s' H; destruct op; cbn [sh_mem_op] in H;
    first [eapply sh_mem_load_clock; exact H | eapply sh_mem_store_clock; exact H].
Qed.

Fixpoint psize (p : prog a) : nat :=
  match p with
  | Dec _ _ p => Datatypes.S (psize p)
  | Seq c1 c2 => Datatypes.S (psize c1 + psize c2)
  | If _ c1 c2 => Datatypes.S (psize c1 + psize c2)
  | While _ c => Datatypes.S (psize c)
  | _ => 1
  end.

Definition eval_lt (x y : prog a * state a ffi_t) : Prop :=
  (clock (snd x) < clock (snd y))%N \/
  (clock (snd x) = clock (snd y) /\ (psize (fst x) < psize (fst y))%nat).

Lemma eval_lt_wf : well_founded eval_lt.
Proof.
  intros [p s].
  remember (N.to_nat (clock s)) as c eqn:Hc. revert p s Hc.
  induction c as [c IHc] using (well_founded_induction lt_wf).
  intros p s Hc.
  remember (psize p) as n eqn:Hn. revert p s Hc Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros p s Hc Hn; constructor; intros [p' s'] [Hlt|[Heq Hlt]]; cbn in *.
  - eapply IHc; [|reflexivity]. lia.
  - eapply IHn; [| |reflexivity]; [lia|]. lia.
Qed.

Definition lowerF (cf : nat) (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
  match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c cf' p s end.

Lemma evaluate_c_unfold cf p s :
  evaluate_c cf p s = evaluate_body (evaluate_c cf) (lowerF cf) p s.
Proof. destruct cf, p; reflexivity. Qed.

Ltac clock_facts :=
  repeat match goal with
         | H : fix_clock _ _ = (_, _) |- _ =>
             let Hle := fresh "Hle" in
             pose proof (fix_clock_IMP_LESS_EQ _ _ _ _ H) as Hle; clear H
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         end;
  cbn [clock set_locals set_code set_memory set_ffi set_clock set_var set_globals
       dec_clock empty_locals psize] in *.

Ltac prove_eval_lt := unfold eval_lt; cbn [fst snd]; clock_facts; lia.
Ltac prove_clock_lt := clock_facts; lia.

Lemma evaluate_body_ext
    (go1 go2 lo1 lo2 : prog a -> state a ffi_t -> option (result a) * state a ffi_t) p s :
  (forall p' s', eval_lt (p', s') (p, s) -> go1 p' s' = go2 p' s') ->
  (forall p' s', (clock s' < clock s)%N -> lo1 p' s' = lo2 p' s') ->
  evaluate_body go1 lo1 p s = evaluate_body go2 lo2 p s.
Proof.
  intros Hgo Hlo.
  destruct p; cbn [evaluate_body]; unfold fcl;
  repeat first
    [ reflexivity
    | match goal with
      | |- context [go1 ?p' ?s'] => rewrite (Hgo p' s') by prove_eval_lt
      | |- context [lo1 ?p' ?s'] => rewrite (Hlo p' s') by prove_clock_lt
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta
      end ].
Qed.

Lemma evaluate_c_fuel : forall (x : prog a * state a ffi_t) cf1 cf2,
  (N.to_nat (clock (snd x)) < cf1)%nat -> (N.to_nat (clock (snd x)) < cf2)%nat ->
  evaluate_c cf1 (fst x) (snd x) = evaluate_c cf2 (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros cf1 cf2 H1 H2; cbn [fst snd] in *.
  rewrite !evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Hlt. apply (IH (p', s') Hlt); cbn;
      destruct Hlt as [Hlt|[Heq _]]; cbn in *; lia.
  - intros p' s' Hlt. destruct cf1 as [|cf1]; [lia|]. destruct cf2 as [|cf2]; [lia|].
    cbn [lowerF]. apply (IH (p', s')); [left; exact Hlt| |]; cbn; lia.
Qed.

Lemma evaluate_eq_c cf (p : prog a) (s : state a ffi_t) :
  (N.to_nat (clock s) < cf)%nat -> evaluate (p, s) = evaluate_c cf p s.
Proof.
  intros H; unfold evaluate.
  apply (evaluate_c_fuel (p, s)); cbn; lia.
Qed.

(** [evaluate] is a fixed point of its one-step body. *)
Lemma evaluate_eqn (p : prog a) (s : state a ffi_t) :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s')) p s.
Proof.
  rewrite (evaluate_eq_c (Datatypes.S (N.to_nat (clock s)))) by lia.
  rewrite evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Hlt. symmetry; apply evaluate_eq_c.
    destruct Hlt as [Hlt|[Heq _]]; cbn in *; lia.
  - intros p' s' Hlt. cbn [lowerF]. symmetry; apply evaluate_eq_c. lia.
Qed.

Ltac clock_step IH H :=
  repeat first
    [ match type of H with
      | evaluate (?p', ?s'') = (?r', ?t) =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t H));
          clear H; clock_facts; lia
      | sh_mem_op _ _ _ _ = (_, _) =>
          apply sh_mem_op_clock in H; clock_facts; lia
      | (_, _) = (_, _) => injection H as <- <-; clock_facts; lia
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t E));
          clear E
      | E : fix_clock _ _ = (_, _) |- _ =>
          let Hle := fresh "Hle" in
          pose proof (fix_clock_IMP_LESS_EQ _ _ _ _ E) as Hle; clear E
      | E : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in E
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_clock" *)
Theorem evaluate_clock : forall (prog0 : prog a) (s : state a ffi_t) r s',
  evaluate (prog0, s) = (r, s') -> (clock s' <= clock s)%N.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s',
            evaluate x = (r, s') -> (clock s' <= clock (snd x))%N)
    by (intros p s r s' H; exact (G (p, s) r s' H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' H; cbn [snd].
  rewrite evaluate_eqn in H.
  destruct p; cbn [evaluate_body] in H; unfold fcl in H;
    clock_step IH H.
Qed.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "fix_clock_evaluate" *)
Theorem fix_clock_evaluate : forall (prog0 : prog a) (s : state a ffi_t),
  fix_clock s (evaluate (prog0, s)) = evaluate (prog0, s).
Proof.
  intros p s; destruct (evaluate (p, s)) as [r s'] eqn:E.
  pose proof (evaluate_clock p s r s' E) as Hc.
  unfold fix_clock; f_equal.
  destruct (N.ltb_spec (clock s) (clock s')); [lia|].
  destruct s'; reflexivity.
Qed.

Lemma fcl_evaluate :
  fcl (fun p s => evaluate (p, s)) = (fun p s => @evaluate a ffi_t (p, s)).
Proof.
  apply functional_extensionality; intros p.
  apply functional_extensionality; intros s.
  apply fix_clock_evaluate.
Qed.

(** HOL's final [evaluate_def] (the definition's equations with
    [fix_clock_evaluate] rewritten away). *)
(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "evaluate_def" 443 *)
Theorem evaluate_def :
  (forall (s : state a ffi_t),
     evaluate (Skip, s) =
     (NONE, s)) /\
  (forall v e prog0 (s : state a ffi_t),
     evaluate (Dec v e prog0, s) =
     match eval s e with
     | SOME value =>
         let '(res, st) := evaluate (prog0, set_locals (locals s |+ (v, value)) s) in
         (res, set_locals (res_var (locals st) (v, FLOOKUP (locals s) v)) st)
     | NONE => (SOME Error, s)
     end) /\
  (forall lhss pop rhss (s : state a ffi_t),
     evaluate (Primitive lhss pop rhss, s) =
     match OPT_MMAP (FLOOKUP (locals s)) rhss with
     | SOME ws =>
         match crep_primop pop ws with
         | SOME res_ws =>
             if andb (LENGTH lhss =? LENGTH res_ws)
                     (andb (EVERY (fun v => IS_SOME (FLOOKUP (locals s) v)) lhss)
                           (ALL_DISTINCT lhss))
             then (NONE, set_locals (locals s |++ ZIP (lhss, res_ws)) s)
             else (SOME Error, s)
         | NONE => (SOME Error, s)
         end
     | NONE => (SOME Error, s)
     end) /\
  (forall v src (s : state a ffi_t),
     evaluate (Assign v src, s) =
     match eval s src with
     | NONE => (SOME Error, s)
     | SOME w =>
         match FLOOKUP (locals s) v with
         | SOME _ => (NONE, set_locals (locals s |+ (v, w)) s)
         | _ => (SOME Error, s)
         end
     end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (Store dst src, s) =
     match eval s dst, eval s src with
     | SOME (Word adr), SOME w =>
         match mem_store adr w (memaddrs s) (memory s) with
         | SOME m => (NONE, set_memory m s)
         | NONE => (SOME Error, s)
         end
     | _, _ => (SOME Error, s)
     end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (Store32 dst src, s) =
     match eval s dst, eval s src with
     | SOME (Word adr), SOME (Word w) =>
         match mem_store_32 (memory s) (memaddrs s) (be s) adr (w2w w) with
         | SOME m => (NONE, set_memory m s)
         | NONE => (SOME Error, s)
         end
     | _, _ => (SOME Error, s)
     end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (StoreByte dst src, s) =
     match eval s dst, eval s src with
     | SOME (Word adr), SOME (Word w) =>
         match mem_store_byte (memory s) (memaddrs s) (be s) adr (w2w w) with
         | SOME m => (NONE, set_memory m s)
         | NONE => (SOME Error, s)
         end
     | _, _ => (SOME Error, s)
     end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (StoreGlob dst src, s) =
     match eval s src with
     | SOME w => (NONE, set_globals dst w s)
     | _ => (SOME Error, s)
     end) /\
  (forall op v ad (s : state a ffi_t),
     evaluate (ShMem op v ad, s) =
     match eval s ad with
     | SOME (Word addr) =>
         if is_load op then
           match FLOOKUP (locals s) v with
           | SOME _ => sh_mem_op op v addr s
           | _ => (SOME Error, s)
           end
         else
           match FLOOKUP (locals s) v with
           | SOME (Word _) => sh_mem_op op v addr s
           | _ => (SOME Error, s)
           end
     | _ => (SOME Error, s)
     end) /\
  (forall c1 c2 (s : state a ffi_t),
     evaluate (Seq c1 c2, s) =
     let '(res, s1) := evaluate (c1, s) in
     match res with NONE => evaluate (c2, s1) | _ => (res, s1) end) /\
  (forall e c1 c2 (s : state a ffi_t),
     evaluate (If e c1 c2, s) =
     match eval s e with
     | SOME (Word w) => evaluate (if negb (bool_decide (w = n2w 0)) then c1 else c2, s)
     | _ => (SOME Error, s)
     end) /\
  (forall n (s : state a ffi_t),
     evaluate (crepLang.Break n, s) =
     (SOME (Break n), s)) /\
  (forall n (s : state a ffi_t),
     evaluate (crepLang.Continue n, s) =
     (SOME (Continue n), s)) /\
  (forall e c (s : state a ffi_t),
     evaluate (While e c, s) =
     match eval s e with
     | SOME (Word w) =>
         if negb (bool_decide (w = n2w 0)) then
           if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
           else
             let '(res, s1) := evaluate (c, dec_clock s) in
             match res with
             | SOME (Continue 0) => evaluate (While e c, s1)
             | NONE => evaluate (While e c, s1)
             | SOME (Break 0) => (NONE, s1)
             | res => (exit_loop res, s1)
             end
         else (NONE, s)
     | _ => (SOME Error, s)
     end) /\
  (forall es (s : state a ffi_t),
     evaluate (crepLang.Return es, s) =
     match OPT_MMAP (eval s) es with
     | SOME ws => (SOME (Return ws), empty_locals s)
     | _ => (SOME Error, s)
     end) /\
  (forall eid (s : state a ffi_t),
     evaluate (Raise eid, s) =
     (SOME (Exception eid), empty_locals s)) /\
  (forall (s : state a ffi_t),
     evaluate (Tick, s) =
     if (clock s =? 0)%N then (SOME TimeOut, empty_locals s) else (NONE, dec_clock s)) /\
  (forall caltyp fname argexps (s : state a ffi_t),
     evaluate (Call caltyp fname argexps, s) =
     match OPT_MMAP (eval s) argexps with
     | SOME args =>
         match lookup_code (code s) fname args (LENGTH args) with
         | SOME (prog0, newlocals) =>
             if match caltyp with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end
             then (SOME Error, s)
             else
             if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
             else
               let eval_prog := evaluate (prog0, set_locals newlocals (dec_clock s)) in
               match eval_prog with
               | (NONE, st) => (SOME Error, st)
               | (SOME (Break n), st) => (SOME Error, st)
               | (SOME (Continue n), st) => (SOME Error, st)
               | (SOME (Return retvs), st) =>
                   match caltyp with
                   | NONE => (SOME (Return retvs), empty_locals st)
                   | SOME (rts, _) =>
                       if negb (LENGTH retvs =? LENGTH rts) then (SOME Error, st)
                       else
                         match OPT_MMAP (FLOOKUP (locals s)) rts with
                         | SOME _ => (NONE, set_locals (locals s |++ ZIP (rts, retvs)) st)
                         | _ => (SOME Error, st)
                         end
                   end
               | (SOME (Exception eid), st) =>
                   match caltyp with
                   | NONE => (SOME (Exception eid), empty_locals st)
                   | SOME (_, NONE) => (SOME (Exception eid), empty_locals st)
                   | SOME (_, SOME (eid', p)) =>
                       if bool_decide (eid = eid') then evaluate (p, set_locals (locals s) st)
                       else (SOME (Exception eid), empty_locals st)
                   end
               | (res, st) => (res, empty_locals st)
               end
         | _ => (SOME Error, s)
         end
     | _ => (SOME Error, s)
     end) /\
  (forall ffi_index ptr1 len1 ptr2 len2 (s : state a ffi_t),
     evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s) =
     match FLOOKUP (locals s) len1, FLOOKUP (locals s) ptr1,
           FLOOKUP (locals s) len2, FLOOKUP (locals s) ptr2 with
     | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
         match read_bytearray w2 (w2n w) (mem_load_byte (memory s) (memaddrs s) (be s)),
               read_bytearray w4 (w2n w3) (mem_load_byte (memory s) (memaddrs s) (be s)) with
         | SOME bytes, SOME bytes2 =>
             match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
             | FFI_final outcome => (SOME (FinalFFI outcome), s)
             | FFI_return new_ffi new_bytes =>
                 let nmem := write_bytearray w4 new_bytes (memory s) (memaddrs s) (be s) in
                 (NONE, set_ffi new_ffi (set_memory nmem s))
             end
         | _, _ => (SOME Error, s)
         end
     | _, _, _, _ => (SOME Error, s)
     end).

Proof.
  repeat split; intros; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite ?fcl_evaluate; reflexivity.
Qed.

End EvaluateEqns.

(** ** Observable semantics *)
Section Semantics.
Context {a : N} {ffi_t : Type}.

#[local] Instance behaviour_inhabited : Inhabited behaviour := Fail.

(*! HOL "cakeml/pancake/semantics/crepSemScript.sml" "semantics_def" *)
Definition semantics (s : state a ffi_t) (start : funname) : behaviour :=
  let prog0 := @crepLang.Call a NONE start [] in
  if classical_dec (exists k,
       match fst (evaluate (prog0, set_clock k s)) with
       | SOME TimeOut => False
       | SOME (FinalFFI _) => False
       | SOME (Return _) => False
       | _ => True
       end)
  then Fail
  else
    match some (fun res => exists k t r outcome,
             evaluate (prog0, set_clock k s) = (r, t) /\
             match r with
             | SOME (FinalFFI e) => outcome = FFI_outcome e
             | SOME (Return _) => outcome = Success
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (snd (evaluate (prog0, set_clock k s))))))
                          UNIV))
    end.

End Semantics.
