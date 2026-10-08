(** * CakeML Pancake [loopSem]: semantics of loopLang

    Port of [cakeml/pancake/semantics/loopSemScript.sml], following the
    recipe of [panSem.v].  Carrier notes:
    - [state] is a Rocq record with HOL's field names; HOL's
      [s with f := v] is [set_<f> v s] (helpers below).  There is no field
      helper for [globals]: HOL's own [set_globals] ([set_globals gv w s]) is
      ported under its name.
    - [word_loc] is wordLang's.  The HOL script uses a few definitions of
      [wordSem] ([isWord], [theWord], [mem_load_32], [mem_store_32],
      [mem_load_byte_aux], [mem_store_byte_aux], [write_bytearray],
      [the_words]); [wordSem] is not ported yet, so they are defined below,
      untagged, as HOL defines them (to be replaced by the [wordSem.v]
      translations).
    - The [result] constructors [Break], [Continue] shadow the loopLang
      program constructors, written [loopLang.Break] etc.; the [asm] memops
      [Load], [Store], [Load32], [Store32] are written [asm.Load] etc.;
      behaviour's [Fail] is [ffi.Fail] (loopLang's [Fail] is a program).
    - HOL's [l1 ∈ domain s.code] and [domain live ⊆ domain s.locals] are
      decided with [classical_dec] (the semantics is not executable).
    - HOL tests [res ≠ NONE] / [handler <> NONE] as [IS_SOME _], and
      [res = NONE] (in [Seq]) by matching; HOL's redundant catch-all
      [| _ => (SOME Error, s)] in the second branch of [sh_mem_load] is
      dropped (Rocq rejects redundant clauses; it is unreachable).
    - [evaluate] (HOL: well-founded recursion on (clock, program size)) is
      [evaluate_c] with a clock fuel, as in [panSem.v]; [evaluate_eqn] is its
      unfolding and HOL's final [evaluate_def] is proved from it.

    Not ported: the generated induction theorems [eval_ind]/[evaluate_ind]
    (and the rebound [evaluate_ind]): their statements are produced by HOL's
    definition package and do not appear in the script. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map sptree.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
Import wordLang(word_loc(..)).
From Galette.cakeml.pancake Require panLang.
From Galette.cakeml.pancake Require Import loopLang.
Open Scope N_scope.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "state" *)
Record state (a : N) (ffi : Type) : Type := mk_state {
  locals : spt (word_loc a);
  globals : fmap (word 5) (word_loc a);
  memory : word a -> word_loc a;
  mdomain : word a -> Prop;
  sh_mdomain : word a -> Prop;
  clock : N;
  code : spt (list N * prog a);
  be : bool;
  ffi : ffi_state ffi;
  base_addr : word a;
  top_addr : word a
}.
Arguments mk_state {a ffi}.
Arguments locals {a ffi}. Arguments globals {a ffi}. Arguments memory {a ffi}.
Arguments mdomain {a ffi}. Arguments sh_mdomain {a ffi}. Arguments clock {a ffi}.
Arguments code {a ffi}. Arguments be {a ffi}. Arguments ffi {a ffi}.
Arguments base_addr {a ffi}. Arguments top_addr {a ffi}.

(** HOL [s with f := x] for each field used. *)
Section Updates.
Context {a : N} {ffi_t : Type}.
Definition set_locals x (s : state a ffi_t) := mk_state x s.(globals) s.(memory) s.(mdomain) s.(sh_mdomain) s.(clock) s.(code) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_memory x (s : state a ffi_t) := mk_state s.(locals) s.(globals) x s.(mdomain) s.(sh_mdomain) s.(clock) s.(code) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_clock x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(memory) s.(mdomain) s.(sh_mdomain) x s.(code) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_ffi (x : ffi_state ffi_t) (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(memory) s.(mdomain) s.(sh_mdomain) s.(clock) s.(code) s.(be) x s.(base_addr) s.(top_addr).
End Updates.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "result" *)
Inductive result (w : N) : Type :=
| Result : list (word_loc w) -> result w
| Exception : word_loc w -> result w
| Break : N -> result w
| Continue : N -> result w
| TimeOut : result w
| FinalFFI : final_event -> result w
| Error : result w.
Arguments Result {w} _. Arguments Exception {w} _. Arguments Break {w} _.
Arguments Continue {w} _. Arguments TimeOut {w}. Arguments FinalFFI {w} _.
Arguments Error {w}.

(** ** wordSem prerequisites (HOL [wordSem], not yet ported; untagged) *)
Section WordSem.
Context {a : N}.
Local Open Scope word_scope.

(** HOL [wordSem$theWord] (unspecified on [Loc]). *)
Definition theWord (x : word_loc a) : word a := match x with Word w => w | _ => ARB end.

(** HOL [wordSem$isWord]. *)
Definition isWord (x : word_loc a) : bool := match x with Word _ => true | _ => false end.

(** HOL [wordSem$mem_load_32]. *)
Definition mem_load_32 (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) : option word32 :=
  if aligned 2 w then
    match m (byte_align w) with
    | Loc _ _ => NONE
    | Word v =>
        if classical_dec (byte_align w IN dm)
        then SOME (word_of_bytes be (n2w 0 : word32)
                     [get_byte w v be; get_byte (w + n2w 1) v be;
                      get_byte (w + n2w 2) v be; get_byte (w + n2w 3) v be])
        else NONE
    end
  else NONE.

(** HOL [wordSem$mem_store_32]. *)
Definition mem_store_32 (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) (hw : word32) : option (word a -> word_loc a) :=
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm) then
          let v0 := set_byte w (get_byte (n2w 0 : word32) hw be) v be in
          let v1 := set_byte (w + n2w 1) (get_byte (n2w 1) hw be) v0 be in
          let v2 := set_byte (w + n2w 2) (get_byte (n2w 2) hw be) v1 be in
          let v3 := set_byte (w + n2w 3) (get_byte (n2w 3) hw be) v2 be in
          SOME ((byte_align w =+ Word v3) m)
        else NONE
    | _ => NONE
    end
  else NONE.

(** HOL [wordSem$mem_load_byte_aux]. *)
Definition mem_load_byte_aux (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) : option word8 :=
  match m (byte_align w) with
  | Loc _ _ => NONE
  | Word v => if classical_dec (byte_align w IN dm) then SOME (get_byte w v be) else NONE
  end.

(** HOL [wordSem$mem_store_byte_aux]. *)
Definition mem_store_byte_aux (m : word a -> word_loc a) (dm : word a -> Prop) (be : bool)
    (w : word a) (b : word8) : option (word a -> word_loc a) :=
  match m (byte_align w) with
  | Word v =>
      if classical_dec (byte_align w IN dm)
      then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
      else NONE
  | _ => NONE
  end.

(** HOL [wordSem$write_bytearray]. *)
Fixpoint write_bytearray (a0 : word a) (bs : list word8) (m : word a -> word_loc a)
    (dm : word a -> Prop) (be : bool) : word a -> word_loc a :=
  match bs with
  | [] => m
  | b :: bs =>
      match mem_store_byte_aux (write_bytearray (a0 + n2w 1) bs m dm be) dm be a0 b with
      | SOME m => m
      | NONE => m
      end
  end.

(** HOL [wordSem$the_words]. *)
Fixpoint the_words (ws : list (option (word_loc a))) : option (list (word a)) :=
  match ws with
  | [] => SOME []
  | w :: ws =>
      match w, the_words ws with
      | SOME (Word x), SOME xs => SOME (x :: xs)
      | _, _ => NONE
      end
  end.

End WordSem.

Section Defs.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "dec_clock_def" *)
Definition dec_clock (s : state a ffi_t) : state a ffi_t := set_clock (clock s - 1) s.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "fix_clock_def" *)
Definition fix_clock {R} (old_s : state a ffi_t) (p : R * state a ffi_t) : R * state a ffi_t :=
  let '(res, new_s) := p in
  (res, set_clock (if clock old_s <? clock new_s then clock old_s else clock new_s) new_s).

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "set_globals_def" *)
Definition set_globals (gv : word 5) (w : word_loc a) (s : state a ffi_t) : state a ffi_t :=
  mk_state s.(locals) (globals s |+ (gv, w)) s.(memory) s.(mdomain) s.(sh_mdomain)
    s.(clock) s.(code) s.(be) s.(ffi) s.(base_addr) s.(top_addr).

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "mem_store_def" *)
Definition mem_store (addr : word a) (w : word_loc a) (s : state a ffi_t) : option (state a ffi_t) :=
  if classical_dec (addr IN mdomain s) then SOME (set_memory ((addr =+ w) (memory s)) s)
  else NONE.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "mem_load_def" *)
Definition mem_load (addr : word a) (s : state a ffi_t) : option (word_loc a) :=
  if classical_dec (addr IN mdomain s) then SOME (memory s addr) else NONE.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "eval_def" *)
Fixpoint eval (s : state a ffi_t) (e : exp a) {struct e} : option (word_loc a) :=
  match e with
  | Const w => SOME (Word w)
  | Var v => lookup v (locals s)
  | Lookup name => FLOOKUP (globals s) name
  | Load addr =>
      match eval s addr with
      | SOME (Word w) => mem_load w s
      | _ => NONE
      end
  | Op op wexps =>
      match the_words (MAP (eval s) wexps) with
      | SOME ws => OPTION_MAP Word (wordLang.word_op op ws)
      | _ => NONE
      end
  | Shift sh wexp1 wexp2 =>
      match eval s wexp1, eval s wexp2 with
      | SOME (Word w1), SOME (Word w2) => OPTION_MAP Word (wordLang.word_sh sh w1 (w2n w2))
      | _, _ => NONE
      end
  | BaseAddr => SOME (Word (base_addr s))
  | TopAddr => SOME (Word (top_addr s))
  end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "get_vars_def" *)
Fixpoint get_vars (vs : list N) (s : state a ffi_t) : option (list (word_loc a)) :=
  match vs with
  | [] => SOME []
  | v :: vs =>
      match lookup v (locals s) with
      | NONE => NONE
      | SOME x =>
          match get_vars vs s with
          | NONE => NONE
          | SOME xs => SOME (x :: xs)
          end
      end
  end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "set_var_def" *)
Definition set_var (v : N) (x : word_loc a) (s : state a ffi_t) : state a ffi_t :=
  set_locals (insert v x (locals s)) s.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "set_vars_def" *)
Definition set_vars (vs : list N) (xs : list (word_loc a)) (s : state a ffi_t) : state a ffi_t :=
  set_locals (alist_insert vs xs (locals s)) s.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "loop_arith_def" *)
Definition loop_arith (s : state a ffi_t) (arith : loopLang.loop_arith) : option (state a ffi_t) :=
  match arith with
  | LDiv r1 r2 r3 =>
      match lookup r3 (locals s), lookup r2 (locals s) with
      | SOME (Word q), SOME (Word w2) =>
          if negb (bool_decide (q = n2w 0)) then SOME (set_var r1 (Word (word_quot w2 q)) s)
          else NONE
      | _, _ => NONE
      end
  | LLongMul r1 r2 r3 r4 =>
      match lookup r3 (locals s), lookup r4 (locals s) with
      | SOME (Word w3), SOME (Word w4) =>
          let r := (w2n w3 * w2n w4)%N in
          SOME (set_var r2 (Word (n2w r)) (set_var r1 (Word (n2w (r DIV dimword a)%N)) s))
      | _, _ => NONE
      end
  | LLongDiv r1 r2 r3 r4 r5 =>
      match lookup r3 (locals s), lookup r4 (locals s), lookup r5 (locals s) with
      | SOME (Word w3), SOME (Word w4), SOME (Word w5) =>
          let n := (w2n w3 * dimword a + w2n w4)%N in
          let d := w2n w5 in
          let q := (n DIV d)%N in
          if andb (negb (d =? 0)%N) (q <? dimword a)%N then
            SOME (set_var r1 (Word (n2w q)) (set_var r2 (Word (n2w (n MOD d)%N)) s))
          else NONE
      | _, _, _ => NONE
      end
  end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "find_code_def" *)
Definition find_code (dest : option N) (args : list (word_loc a))
    (code0 : spt (list N * prog a)) : option (spt (word_loc a) * prog a) :=
  match dest with
  | SOME p =>
      match lookup p code0 with
      | NONE => NONE
      | SOME (params, exp) =>
          if LENGTH args =? LENGTH params
          then SOME (fromAList (ZIP (params, args)), exp) else NONE
      end
  | NONE =>
      if bool_decide (args = []) then NONE else
        match LAST args with
        | Loc loc 0 =>
            match lookup loc code0 with
            | NONE => NONE
            | SOME (params, exp) =>
                if LENGTH args =? LENGTH params + 1
                then SOME (fromAList (ZIP (params, FRONT args)), exp)
                else NONE
            end
        | _ => NONE
        end
  end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "get_var_imm_def" *)
Definition get_var_imm (ri : reg_imm a) (s : state a ffi_t) : option (word_loc a) :=
  match ri with
  | Reg n => lookup n (locals s)
  | Imm w => SOME (Word w)
  end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "fix_clock_IMP_LESS_EQ" *)
Theorem fix_clock_IMP_LESS_EQ : forall {R} (s : state a ffi_t) (x : R * state a ffi_t) res s1,
  fix_clock s x = (res, s1) -> (clock s1 <= clock s)%N.
Proof.
  intros R s [r s'] res s1 H; cbn in H; inversion H; subst; cbn.
  destruct (N.ltb_spec (clock s) (clock s')); lia.
Qed.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "call_env_def" *)
Definition call_env (args : list (word_loc a)) (s : state a ffi_t) : state a ffi_t :=
  set_locals (sptree.fromList args) s.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "cut_state_def" *)
Definition cut_state (live : num_set) (s : state a ffi_t) : option (state a ffi_t) :=
  if classical_dec (domain live SUBSET domain (locals s))
  then SOME (set_locals (inter (locals s) live) s)
  else NONE.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "cut_res_def" *)
Definition cut_res (live : num_set) (p : option (result a) * state a ffi_t)
    : option (result a) * state a ffi_t :=
  let '(res, s) := p in
  if IS_SOME res then (res, s) else
    match cut_state live s with
    | NONE => (SOME Error, s)
    | SOME s =>
        if (clock s =? 0)%N then (SOME TimeOut, set_locals LN s)
        else (res, dec_clock s)
    end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_load_def" *)
Definition sh_mem_load (v : N) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  if (nb =? 0)%N then
    (if classical_dec (addr IN sh_mdomain s) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), call_env [] s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_var v (Word (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s))
  else
    (if classical_dec (byte_align addr IN sh_mdomain s) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), call_env [] s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_var v (Word (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s)).

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_store_def" *)
Definition sh_mem_store (v : N) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  match lookup v (locals s) with
  | SOME (Word w) =>
      if (nb =? 0)%N then
        (if classical_dec (addr IN sh_mdomain s) then
           match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
                   (word_to_bytes w false ++ word_to_bytes addr false) with
           | FFI_final outcome => (SOME (FinalFFI outcome), call_env [] s)
           | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
           end
         else (SOME Error, s))
      else
        (if classical_dec (byte_align addr IN sh_mdomain s) then
           match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
                   (TAKE nb (word_to_bytes w false) ++ word_to_bytes addr false) with
           | FFI_final outcome => (SOME (FinalFFI outcome), call_env [] s)
           | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
           end
         else (SOME Error, s))
  | _ => (SOME Error, s)
  end.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "loop_primop_def" *)
Definition loop_primop (pop : panLang.primop) (args : list (word_loc a)) : option (list (word_loc a)) :=
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

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_op_def" *)
Definition sh_mem_op (op : memop) (r : N) (ad : word a) (s : state a ffi_t)
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

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "set_vars_clock" *)
Theorem set_vars_clock : forall ns vs (s : state a ffi_t), clock (set_vars ns vs s) = clock s.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "exit_loop_def" *)
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
  | Fail => (SOME Error, s)
  | Assign v exp =>
      match eval s exp with
      | NONE => (SOME Error, s)
      | SOME w => (NONE, set_var v w s)
      end
  | Primitive lhss pop rhss =>
      match get_vars rhss s with
      | SOME ws =>
          match loop_primop pop ws with
          | SOME res_ws =>
              if LENGTH lhss =? LENGTH res_ws
              then (NONE, set_vars lhss res_ws s)
              else (SOME Error, s)
          | NONE => (SOME Error, s)
          end
      | NONE => (SOME Error, s)
      end
  | Arith arith =>
      match loop_arith s arith with
      | NONE => (SOME Error, s)
      | SOME s' => (NONE, s')
      end
  | Store exp v =>
      match eval s exp, lookup v (locals s) with
      | SOME (Word adr), SOME w =>
          match mem_store adr w s with
          | SOME st => (NONE, st)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | SetGlobal dst exp =>
      match eval s exp with
      | SOME w => (NONE, set_globals dst w s)
      | _ => (SOME Error, s)
      end
  | Load32 ad v =>
      match lookup ad (locals s) with
      | SOME (Word w) =>
          match mem_load_32 (memory s) (mdomain s) (be s) w with
          | SOME b => (NONE, set_var v (Word (w2w b)) s)
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | LoadByte ad v =>
      match lookup ad (locals s) with
      | SOME (Word w) =>
          match mem_load_byte_aux (memory s) (mdomain s) (be s) w with
          | SOME b => (NONE, set_var v (Word (w2w b)) s)
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | Store32 ad w =>
      match lookup ad (locals s), lookup w (locals s) with
      | SOME (Word w), SOME (Word b) =>
          match mem_store_32 (memory s) (mdomain s) (be s) w (w2w b) with
          | SOME m => (NONE, set_memory m s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | StoreByte ad w =>
      match lookup ad (locals s), lookup w (locals s) with
      | SOME (Word w), SOME (Word b) =>
          match mem_store_byte_aux (memory s) (mdomain s) (be s) w (w2w b) with
          | SOME m => (NONE, set_memory m s)
          | _ => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | Seq c1 c2 =>
      let '(res, s1) := fcl go c1 s in
      match res with NONE => go c2 s1 | _ => (res, s1) end
  | If cmp r1 ri c1 c2 live_out =>
      match lookup r1 (locals s), get_var_imm ri s with
      | SOME (Word x), SOME (Word y) =>
          let b := word_cmp cmp x y in
          cut_res live_out (go (if b then c1 else c2) s)
      | _, _ => (SOME Error, s)
      end
  | Mark p => go p s
  | loopLang.Break k => (SOME (Break k), s)
  | loopLang.Continue k => (SOME (Continue k), s)
  | Loop live_in body live_out =>
      match cut_res live_in (NONE, s) with
      | (NONE, s) =>
          match fcl go body s with
          | (NONE, s) => lower (Loop live_in body live_out) s
          | (SOME (Continue 0), s) => lower (Loop live_in body live_out) s
          | (SOME (Break 0), s) => cut_res live_out (NONE, s)
          | (res, s) => (exit_loop res, s)
          end
      | res => res
      end
  | Raise n =>
      match lookup n (locals s) with
      | NONE => (SOME Error, s)
      | SOME w => (SOME (Exception w), call_env [] s)
      end
  | Return ns =>
      match get_vars ns s with
      | SOME vs => (SOME (Result vs), call_env [] s)
      | _ => (SOME Error, s)
      end
  | ShMem op v ad =>
      match eval s ad with
      | SOME (Word addr) =>
          if is_load op then
            match lookup v (locals s) with
            | SOME _ => sh_mem_op op v addr s
            | _ => (SOME Error, s)
            end
          else
            match lookup v (locals s) with
            | SOME (Word _) => sh_mem_op op v addr s
            | _ => (SOME Error, s)
            end
      | _ => (SOME Error, s)
      end
  | Tick =>
      if (clock s =? 0)%N then (SOME TimeOut, set_locals LN s)
      else (NONE, dec_clock s)
  | LocValue r l1 =>
      if classical_dec (l1 IN domain (code s)) then (NONE, set_var r (Loc l1 0) s)
      else (SOME Error, s)
  | Call ret dest argvars handler =>
      match get_vars argvars s with
      | NONE => (SOME Error, s)
      | SOME argvals =>
          match find_code dest argvals (code s) with
          | NONE => (SOME Error, s)
          | SOME (env, prog0) =>
              match ret with
              | NONE =>
                  if IS_SOME handler then (SOME Error, s) else
                  if (clock s =? 0)%N then (SOME TimeOut, set_locals LN s)
                  else
                    match lower prog0 (set_locals env (dec_clock s)) with
                    | (NONE, s) => (SOME Error, s)
                    | (SOME (Continue _), s) => (SOME Error, s)
                    | (SOME (Break _), s) => (SOME Error, s)
                    | (SOME res, s) => (SOME res, s)
                    end
              | SOME (ns, live) =>
                  if negb (ALL_DISTINCT ns) then (SOME Error, s) else
                  match cut_res live (NONE, s) with
                  | (NONE, s) =>
                      match fcl lower prog0 (set_locals env s) with
                      | (SOME (Result retvs), st) =>
                          if negb (LENGTH retvs =? LENGTH ns) then (SOME Error, st) else
                          match handler with
                          | NONE => (NONE, set_vars ns retvs (set_locals (locals s) st))
                          | SOME (_, (_, (r, live_out))) =>
                              cut_res live_out
                                (lower r (set_vars ns retvs (set_locals (locals s) st)))
                          end
                      | (SOME (Exception exn), st) =>
                          match handler with
                          | NONE => (SOME (Exception exn), set_locals LN st)
                          | SOME (n, (h, (_, live_out))) =>
                              cut_res live_out
                                (lower h (set_var n exn (set_locals (locals s) st)))
                          end
                      | (SOME (Continue _), st) => (SOME Error, st)
                      | (SOME (Break _), st) => (SOME Error, st)
                      | (NONE, st) => (SOME Error, st)
                      | res => res
                      end
                  | res => res
                  end
              end
          end
      end
  | FFI ffi_index ptr1 len1 ptr2 len2 cutset =>
      match lookup len1 (locals s), lookup ptr1 (locals s), lookup len2 (locals s),
            lookup ptr2 (locals s), cut_state cutset s with
      | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4), SOME s =>
          match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
                read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
          | SOME bytes, SOME bytes2 =>
              match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (SOME (FinalFFI outcome), call_env [] s)
              | FFI_return new_ffi new_bytes =>
                  let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                  (NONE, set_ffi new_ffi (set_memory new_m s))
              end
          | _, _ => (SOME Error, s)
          end
      | _, _, _, _, _ => (SOME Error, s)
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

Lemma cut_state_clock live (s s' : state a ffi_t) :
  cut_state live s = SOME s' -> clock s' = clock s.
Proof.
  unfold cut_state; destruct (classical_dec _); intros H; inversion H; reflexivity.
Qed.

Lemma cut_res_clock live (r : option (result a)) (s : state a ffi_t) r' t :
  cut_res live (r, s) = (r', t) -> (clock t <= clock s)%N.
Proof.
  unfold cut_res; destruct (IS_SOME r).
  - intros H; inversion H; subst; lia.
  - destruct (cut_state live s) as [s0|] eqn:E.
    + apply cut_state_clock in E.
      destruct (clock s0 =? 0)%N; intros H; inversion H; subst; cbn; lia.
    + intros H; inversion H; subst; lia.
Qed.

Lemma cut_res_NONE_clock live (s : state a ffi_t) t :
  cut_res live (NONE, s) = (NONE, t) -> (clock t < clock s)%N.
Proof.
  cbn [cut_res IS_SOME].
  destruct (cut_state live s) as [s0|] eqn:E; [|discriminate].
  apply cut_state_clock in E.
  destruct (N.eqb_spec (clock s0) 0); [discriminate|].
  intros H; inversion H; subst; cbn; lia.
Qed.

Lemma mem_store_clock adr w (s st : state a ffi_t) :
  mem_store adr w s = SOME st -> clock st = clock s.
Proof.
  unfold mem_store; destruct (classical_dec _); intros H; inversion H; reflexivity.
Qed.

Lemma loop_arith_clock (s s' : state a ffi_t) ar :
  loop_arith s ar = SOME s' -> clock s' = clock s.
Proof.
  intros H; destruct ar; cbn [loop_arith] in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         end; try discriminate; injection H as <-; reflexivity.
Qed.

Lemma sh_mem_op_clock op v (addr : word a) (s : state a ffi_t) r s' :
  sh_mem_op op v addr s = (r, s') -> clock s' = clock s.
Proof.
  intros H; destruct op; cbn [sh_mem_op] in H; unfold sh_mem_load, sh_mem_store in H;
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in H
         end; injection H as <- <-; reflexivity.
Qed.

Fixpoint psize (p : prog a) : nat :=
  match p with
  | Seq c1 c2 => Datatypes.S (psize c1 + psize c2)
  | If _ _ _ c1 c2 _ => Datatypes.S (psize c1 + psize c2)
  | Loop _ body _ => Datatypes.S (psize body)
  | Mark p => Datatypes.S (psize p)
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
         | H : cut_res _ (None, _) = (None, _) |- _ =>
             let Hle := fresh "Hle" in
             pose proof (cut_res_NONE_clock _ _ _ H) as Hle; clear H
         | H : cut_res _ (_, _) = (_, _) |- _ =>
             let Hle := fresh "Hle" in
             pose proof (cut_res_clock _ _ _ _ _ H) as Hle; clear H
         | H : cut_state _ _ = Some _ |- _ => apply cut_state_clock in H
         | H : mem_store _ _ _ = Some _ |- _ => apply mem_store_clock in H
         | H : loop_arith _ _ = Some _ |- _ => apply loop_arith_clock in H
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         end;
  cbn [clock set_locals set_memory set_ffi set_clock set_var set_vars set_globals
       call_env dec_clock psize] in *.

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
      | cut_res _ (_, _) = (_, _) =>
          apply cut_res_clock in H; clock_facts; lia
      | (_, _) = (_, _) => injection H as <- <-; clock_facts; lia
      end
    | match goal with
      | E : evaluate (if ?b then _ else _, _) = _ |- _ => destruct b
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t E));
          clear E
      | E : fix_clock _ _ = (_, _) |- _ =>
          let Hle := fresh "Hle" in
          pose proof (fix_clock_IMP_LESS_EQ _ _ _ _ E) as Hle; clear E
      | E : cut_res _ (None, _) = (None, _) |- _ =>
          let Hle := fresh "Hle" in
          pose proof (cut_res_NONE_clock _ _ _ E) as Hle; clear E
      | E : cut_res _ (_, _) = (?o, _) |- _ =>
          tryif is_var o then fail else
          (let Hle := fresh "Hle" in
           pose proof (cut_res_clock _ _ _ _ _ E) as Hle; clear E)
      | E : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in E
      | E : mem_store _ _ _ = Some _ |- _ => apply mem_store_clock in E
      | E : loop_arith _ _ = Some _ |- _ => apply loop_arith_clock in E
      | E : cut_state _ _ = Some _ |- _ => apply cut_state_clock in E
      end
    | match type of H with
      | cut_res _ ?X = _ =>
          lazymatch X with
          | (_, _) => fail
          | _ => let E := fresh "E" in destruct X eqn:E
          end
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_clock" *)
Theorem evaluate_clock : forall (xs : prog a) (s1 : state a ffi_t) vs s2,
  evaluate (xs, s1) = (vs, s2) -> (clock s2 <= clock s1)%N.
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

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "fix_clock_evaluate" *)
Theorem fix_clock_evaluate : forall (c1 : prog a) (s : state a ffi_t),
  fix_clock s (evaluate (c1, s)) = evaluate (c1, s).
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
(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_def" 498 *)
Theorem evaluate_def :
  (forall (s : state a ffi_t),
     evaluate (Skip, s) =
     (NONE, s)) /\
  (forall (s : state a ffi_t),
     evaluate (Fail, s) =
     (SOME Error, s)) /\
  (forall v exp (s : state a ffi_t),
     evaluate (Assign v exp, s) =
     match eval s exp with
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v w s)
     end) /\
  (forall lhss pop rhss (s : state a ffi_t),
     evaluate (Primitive lhss pop rhss, s) =
     match get_vars rhss s with
     | SOME ws =>
         match loop_primop pop ws with
         | SOME res_ws =>
             if LENGTH lhss =? LENGTH res_ws
             then (NONE, set_vars lhss res_ws s)
             else (SOME Error, s)
         | NONE => (SOME Error, s)
         end
     | NONE => (SOME Error, s)
     end) /\
  (forall arith (s : state a ffi_t),
     evaluate (Arith arith, s) =
     match loop_arith s arith with
     | NONE => (SOME Error, s)
     | SOME s' => (NONE, s')
     end) /\
  (forall exp v (s : state a ffi_t),
     evaluate (Store exp v, s) =
     match eval s exp, lookup v (locals s) with
     | SOME (Word adr), SOME w =>
         match mem_store adr w s with
         | SOME st => (NONE, st)
         | NONE => (SOME Error, s)
         end
     | _, _ => (SOME Error, s)
     end) /\
  (forall dst exp (s : state a ffi_t),
     evaluate (SetGlobal dst exp, s) =
     match eval s exp with
     | SOME w => (NONE, set_globals dst w s)
     | _ => (SOME Error, s)
     end) /\
  (forall ad v (s : state a ffi_t),
     evaluate (Load32 ad v, s) =
     match lookup ad (locals s) with
     | SOME (Word w) =>
         match mem_load_32 (memory s) (mdomain s) (be s) w with
         | SOME b => (NONE, set_var v (Word (w2w b)) s)
         | _ => (SOME Error, s)
         end
     | _ => (SOME Error, s)
     end) /\
  (forall ad v (s : state a ffi_t),
     evaluate (LoadByte ad v, s) =
     match lookup ad (locals s) with
     | SOME (Word w) =>
         match mem_load_byte_aux (memory s) (mdomain s) (be s) w with
         | SOME b => (NONE, set_var v (Word (w2w b)) s)
         | _ => (SOME Error, s)
         end
     | _ => (SOME Error, s)
     end) /\
  (forall ad w (s : state a ffi_t),
     evaluate (Store32 ad w, s) =
     match lookup ad (locals s), lookup w (locals s) with
     | SOME (Word w), SOME (Word b) =>
         match mem_store_32 (memory s) (mdomain s) (be s) w (w2w b) with
         | SOME m => (NONE, set_memory m s)
         | _ => (SOME Error, s)
         end
     | _, _ => (SOME Error, s)
     end) /\
  (forall ad w (s : state a ffi_t),
     evaluate (StoreByte ad w, s) =
     match lookup ad (locals s), lookup w (locals s) with
     | SOME (Word w), SOME (Word b) =>
         match mem_store_byte_aux (memory s) (mdomain s) (be s) w (w2w b) with
         | SOME m => (NONE, set_memory m s)
         | _ => (SOME Error, s)
         end
     | _, _ => (SOME Error, s)
     end) /\
  (forall c1 c2 (s : state a ffi_t),
     evaluate (Seq c1 c2, s) =
     let '(res, s1) := evaluate (c1, s) in
     match res with NONE => evaluate (c2, s1) | _ => (res, s1) end) /\
  (forall cmp r1 ri c1 c2 live_out (s : state a ffi_t),
     evaluate (If cmp r1 ri c1 c2 live_out, s) =
     match lookup r1 (locals s), get_var_imm ri s with
     | SOME (Word x), SOME (Word y) =>
         let b := word_cmp cmp x y in
         cut_res live_out (evaluate (if b then c1 else c2, s))
     | _, _ => (SOME Error, s)
     end) /\
  (forall p (s : state a ffi_t),
     evaluate (Mark p, s) =
     evaluate (p, s)) /\
  (forall k (s : state a ffi_t),
     evaluate (loopLang.Break k, s) =
     (SOME (Break k), s)) /\
  (forall k (s : state a ffi_t),
     evaluate (loopLang.Continue k, s) =
     (SOME (Continue k), s)) /\
  (forall live_in body live_out (s : state a ffi_t),
     evaluate (Loop live_in body live_out, s) =
     match cut_res live_in (NONE, s) with
     | (NONE, s) =>
         match evaluate (body, s) with
         | (NONE, s) => evaluate (Loop live_in body live_out, s)
         | (SOME (Continue 0), s) => evaluate (Loop live_in body live_out, s)
         | (SOME (Break 0), s) => cut_res live_out (NONE, s)
         | (res, s) => (exit_loop res, s)
         end
     | res => res
     end) /\
  (forall n (s : state a ffi_t),
     evaluate (Raise n, s) =
     match lookup n (locals s) with
     | NONE => (SOME Error, s)
     | SOME w => (SOME (Exception w), call_env [] s)
     end) /\
  (forall ns (s : state a ffi_t),
     evaluate (Return ns, s) =
     match get_vars ns s with
     | SOME vs => (SOME (Result vs), call_env [] s)
     | _ => (SOME Error, s)
     end) /\
  (forall op v ad (s : state a ffi_t),
     evaluate (ShMem op v ad, s) =
     match eval s ad with
     | SOME (Word addr) =>
         if is_load op then
           match lookup v (locals s) with
           | SOME _ => sh_mem_op op v addr s
           | _ => (SOME Error, s)
           end
         else
           match lookup v (locals s) with
           | SOME (Word _) => sh_mem_op op v addr s
           | _ => (SOME Error, s)
           end
     | _ => (SOME Error, s)
     end) /\
  (forall (s : state a ffi_t),
     evaluate (Tick, s) =
     if (clock s =? 0)%N then (SOME TimeOut, set_locals LN s)
     else (NONE, dec_clock s)) /\
  (forall r l1 (s : state a ffi_t),
     evaluate (LocValue r l1, s) =
     if classical_dec (l1 IN domain (code s)) then (NONE, set_var r (Loc l1 0) s)
     else (SOME Error, s)) /\
  (forall ret dest argvars handler (s : state a ffi_t),
     evaluate (Call ret dest argvars handler, s) =
     match get_vars argvars s with
     | NONE => (SOME Error, s)
     | SOME argvals =>
         match find_code dest argvals (code s) with
         | NONE => (SOME Error, s)
         | SOME (env, prog0) =>
             match ret with
             | NONE =>
                 if IS_SOME handler then (SOME Error, s) else
                 if (clock s =? 0)%N then (SOME TimeOut, set_locals LN s)
                 else
                   match evaluate (prog0, set_locals env (dec_clock s)) with
                   | (NONE, s) => (SOME Error, s)
                   | (SOME (Continue _), s) => (SOME Error, s)
                   | (SOME (Break _), s) => (SOME Error, s)
                   | (SOME res, s) => (SOME res, s)
                   end
             | SOME (ns, live) =>
                 if negb (ALL_DISTINCT ns) then (SOME Error, s) else
                 match cut_res live (NONE, s) with
                 | (NONE, s) =>
                     match evaluate (prog0, set_locals env s) with
                     | (SOME (Result retvs), st) =>
                         if negb (LENGTH retvs =? LENGTH ns) then (SOME Error, st) else
                         match handler with
                         | NONE => (NONE, set_vars ns retvs (set_locals (locals s) st))
                         | SOME (_, (_, (r, live_out))) =>
                             cut_res live_out
                               (evaluate (r, set_vars ns retvs (set_locals (locals s) st)))
                         end
                     | (SOME (Exception exn), st) =>
                         match handler with
                         | NONE => (SOME (Exception exn), set_locals LN st)
                         | SOME (n, (h, (_, live_out))) =>
                             cut_res live_out
                               (evaluate (h, set_var n exn (set_locals (locals s) st)))
                         end
                     | (SOME (Continue _), st) => (SOME Error, st)
                     | (SOME (Break _), st) => (SOME Error, st)
                     | (NONE, st) => (SOME Error, st)
                     | res => res
                     end
                 | res => res
                 end
             end
         end
     end) /\
  (forall ffi_index ptr1 len1 ptr2 len2 cutset (s : state a ffi_t),
     evaluate (FFI ffi_index ptr1 len1 ptr2 len2 cutset, s) =
     match lookup len1 (locals s), lookup ptr1 (locals s), lookup len2 (locals s),
           lookup ptr2 (locals s), cut_state cutset s with
     | SOME (Word w), SOME (Word w2), SOME (Word w3), SOME (Word w4), SOME s =>
         match read_bytearray w2 (w2n w) (mem_load_byte_aux (memory s) (mdomain s) (be s)),
               read_bytearray w4 (w2n w3) (mem_load_byte_aux (memory s) (mdomain s) (be s)) with
         | SOME bytes, SOME bytes2 =>
             match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
             | FFI_final outcome => (SOME (FinalFFI outcome), call_env [] s)
             | FFI_return new_ffi new_bytes =>
                 let new_m := write_bytearray w4 new_bytes (memory s) (mdomain s) (be s) in
                 (NONE, set_ffi new_ffi (set_memory new_m s))
             end
         | _, _ => (SOME Error, s)
         end
     | _, _, _, _, _ => (SOME Error, s)
     end).

Proof.
  repeat split; intros; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite ?fcl_evaluate; reflexivity.
Qed.

End EvaluateEqns.

(** ** Observable semantics *)
Section Semantics.
Context {a : N} {ffi_t : Type}.

#[local] Instance behaviour_inhabited : Inhabited behaviour := ffi.Fail.

(*! HOL "cakeml/pancake/semantics/loopSemScript.sml" "semantics_def" *)
Definition semantics (s : state a ffi_t) (start : N) : behaviour :=
  let prog0 := @loopLang.Call a NONE (SOME start) [] NONE in
  if classical_dec (exists k,
       match fst (evaluate (prog0, set_clock k s)) with
       | SOME TimeOut => False
       | SOME (FinalFFI _) => False
       | SOME (Result _) => False
       | _ => True
       end)
  then ffi.Fail
  else
    match some (fun res => exists k t r outcome,
             evaluate (prog0, set_clock k s) = (r, t) /\
             match r with
             | SOME (FinalFFI e) => outcome = FFI_outcome e
             | SOME (Result _) => outcome = Success
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => llist.fromList (io_events (ffi (snd (evaluate (prog0, set_clock k s))))))
                          UNIV))
    end.

End Semantics.
