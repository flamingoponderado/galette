(** * CakeML [presLang]: displaying intermediate languages

    Port of [cakeml/compiler/backend/presLangScript.sml]: conversion of
    intermediate programs to [displayLang] S-expressions, used by the
    compiler's [--explore] output.

    Ported: the tap configuration, the generic helpers, the ASM displays,
    and the wordLang, stackLang and labLang displays with their [*_to_strs]
    printers (all that the Pancake path reaches).  Not ported (they need the
    source/flat/clos/bvl/bvi/data languages): [int_to_display],
    [lit_to_display], the [fp_*], [word_size], [opb], [opw], [thunk_*],
    [test], [arith], [prim_type], [lop], [op], [id], [ast_t], [pat], [exp],
    [source], [flat], [clos], [bvl], [bvi], [data] displays,
    [num_to_varn_aux] ... [num_to_varn_list], [const_*], [commas]' clients
    other than [num_set_to_display], and [source_to_strs] ... [data_to_strs].
    [num_to_hex_digit_eq] and [num_to_hex_eq] (about HOL's
    [word_to_hex_string]) are not ported either.

    Names: [displayLang]'s constructors [String] and [List] shadow Rocq's
    [String.String] and [misc]'s [app_list] constructor [List], which is
    written [misc.List] here.  The languages ([asm], [wordLang],
    [stackLang], [labLang], [ast]) are required, not imported: their
    constructor names clash, and are written qualified.

    Fuel: [word_prog_to_display] and [stack_prog_to_display] recurse on a
    HOL [num] fuel [k] (callers pass [1000000000]).  They are defined by
    structural recursion on a [nat] fuel ([*_nat], extracted to Zarith
    integers like [N]) and wrapped with [N.to_nat]; HOL's equations, stated
    on [N] with [SUC], are the tagged [_def] theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mlstring mlint.
From Galette.cakeml.basis.pure Require mlsexp.
From Galette.cakeml.semantics Require ast.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.compiler.backend Require stackLang wordLang labLang.
From Galette.cakeml.compiler.backend Require Import jsonLang displayLang.
Open Scope N_scope.
Open Scope hol_string_scope.
Local Set Warnings "-register-all".

(** ** Tap configuration *)

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "tap_config" *)
Record tap_config : Type := { explore_flag : bool }.

#[global] Instance tap_config_inhabited : Inhabited tap_config := {| explore_flag := false |}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "default_tap_config_def" *)
Definition default_tap_config : tap_config := {| explore_flag := false |}.

(** ** Basics *)

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "empty_item_def" *)
Definition empty_item (name : mlstring) : sExp := String name.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "num_to_display_def" *)
Definition num_to_display (n : N) : sExp := String (num_to_str n).

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "string_imp_def" *)
Definition string_imp (s : mlstring) : sExp := String s.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "item_with_num_def" *)
Definition item_with_num (name : mlstring) (n : N) : sExp :=
  Item None name [num_to_display n].

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "item_with_nums_def" *)
Definition item_with_nums (name : mlstring) (ns : list N) : sExp :=
  Item None name (MAP num_to_display ns).

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "bool_to_display_def" *)
Definition bool_to_display (b : bool) : sExp :=
  empty_item (if b then strlit "True" else strlit "False").

(** [num_to_hex] recurses on [n DIV 16]; it is defined with a [nat] fuel
    larger than [n] and HOL's equation is the tagged [num_to_hex_def]. *)
Fixpoint num_to_hex_aux (fuel : nat) (n : N) : list ascii :=
  match fuel with
  | O => []
  | S f => (if n <? 16 then [] else num_to_hex_aux f (n / 16)) ++ num_to_hex_digit (n mod 16)
  end.

Definition num_to_hex (n : N) : list ascii := num_to_hex_aux (S (N.to_nat n)) n.

Lemma num_to_hex_aux_fuel : forall f g n,
  (N.to_nat n < f)%nat -> (N.to_nat n < g)%nat -> num_to_hex_aux f n = num_to_hex_aux g n.
Proof.
  induction f as [|f IH]; intros [|g] n Hf Hg; try lia; cbn.
  destruct (n <? 16) eqn:E; [reflexivity|].
  apply N.ltb_ge in E.
  assert (n / 16 < n) by (apply N.div_lt; lia).
  rewrite (IH g); [reflexivity|lia|lia].
Qed.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "num_to_hex_def" *)
Theorem num_to_hex_def : forall n,
  num_to_hex n =
    (if n <? 16 then [] else num_to_hex (n DIV 16)) ++ num_to_hex_digit (n MOD 16).
Proof.
  intros n; unfold num_to_hex at 1; cbn [num_to_hex_aux].
  destruct (n <? 16) eqn:E.
  - reflexivity.
  - apply N.ltb_ge in E.
    unfold num_to_hex. f_equal. apply num_to_hex_aux_fuel; [|lia].
    assert (n / 16 < n) by (apply N.div_lt; lia). lia.
Qed.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "separate_lines_def" *)
Definition separate_lines (name : mlstring) (xs : list sExp) : sExp :=
  List (String name :: xs).

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "num_to_hex_mlstring_def" *)
Definition num_to_hex_mlstring (n : N) : mlstring := implode ("0x" ++ num_to_hex n).

Section Words.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "word_to_display_def" *)
Definition word_to_display (w : word a) : sExp :=
  empty_item (num_to_hex_mlstring (w2n w)).

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "item_with_word_def" *)
Definition item_with_word (name : mlstring) (w : word a) : sExp :=
  Item None name [word_to_display w].

End Words.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "list_to_display" *)
Abbreviation list_to_display f xs := (Tuple (MAP f xs)).

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "option_to_display" *)
Abbreviation option_to_display f opt :=
  (match opt with
   | None => empty_item (strlit "none")
   | Some opt' => Item None (strlit "some") [f opt']
   end).

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "shift_to_display_def" *)
Definition shift_to_display (s : ast.shift) : sExp :=
  match s with
  | ast.Lsl => empty_item (strlit "Lsl")
  | ast.Lsr => empty_item (strlit "Lsr")
  | ast.Asr => empty_item (strlit "Asr")
  | ast.Ror => empty_item (strlit "Ror")
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "attach_name_def" *)
Definition attach_name (ns : num_map mlstring) (o_ : option N) : mlstring :=
  match o_ with
  | None => strlit "none"
  | Some d =>
      match lookup d ns with
      | None => num_to_str d
      | Some name => concat [name; strlit "@"; num_to_str d]
      end
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "commas_def" *)
Fixpoint commas (l : list mlstring) : mlstring :=
  match l with
  | [] => strlit ""
  | [x] => x
  | x :: ((_ :: _) as xs) => strcat x (strcat (strlit ",") (commas xs))
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "num_set_to_display_def" *)
Definition num_set_to_display (ns : num_set) : sExp :=
  String (concat [strlit "{";
                  commas (MAP num_to_str (MAP FST (toSortedAList ns)));
                  strlit "}"]).

(** ** ASM *)

Section Asm.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_binop_to_display_def" *)
Definition asm_binop_to_display (op : asm.binop) : sExp :=
  match op with
  | asm.Add => empty_item (strlit "Add")
  | asm.Sub => empty_item (strlit "Sub")
  | asm.And => empty_item (strlit "And")
  | asm.Or => empty_item (strlit "Or")
  | asm.Xor => empty_item (strlit "Xor")
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_reg_imm_to_display_def" *)
Definition asm_reg_imm_to_display (reg_imm : asm.reg_imm a) : sExp :=
  match reg_imm with
  | asm.Reg reg => item_with_num (strlit "Reg") reg
  | asm.Imm imm => item_with_word (strlit "Imm") imm
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_arith_to_display_def" *)
Definition asm_arith_to_display (op : asm.arith a) : sExp :=
  match op with
  | asm.Binop bop n1 n2 reg_imm =>
      Item None (strlit "Binop")
        [asm_binop_to_display bop; num_to_display n1; num_to_display n2;
         asm_reg_imm_to_display reg_imm]
  | asm.Shift sh n1 n2 n3 =>
      Item None (strlit "Shift")
        [shift_to_display sh; num_to_display n1; num_to_display n2;
         asm_reg_imm_to_display n3]
  | asm.Div n1 n2 n3 => item_with_nums (strlit "Div") [n1; n2; n3]
  | asm.LongMul n1 n2 n3 n4 => item_with_nums (strlit "LongMul") [n1; n2; n3; n4]
  | asm.LongDiv n1 n2 n3 n4 n5 => item_with_nums (strlit "LongDiv") [n1; n2; n3; n4; n5]
  | asm.AddCarry n1 n2 n3 n4 => item_with_nums (strlit "AddCarry") [n1; n2; n3; n4]
  | asm.AddOverflow n1 n2 n3 n4 => item_with_nums (strlit "AddOverflow") [n1; n2; n3; n4]
  | asm.SubOverflow n1 n2 n3 n4 => item_with_nums (strlit "SubOverflow") [n1; n2; n3; n4]
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_addr_to_display_def" *)
Definition asm_addr_to_display (addr : asm.addr a) : sExp :=
  match addr with
  | asm.Addr reg w => Item None (strlit "Addr") [num_to_display reg; word_to_display w]
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_memop_to_display_def" *)
Definition asm_memop_to_display (op : asm.memop) : sExp :=
  match op with
  | asm.Load => empty_item (strlit "Load")
  | asm.Load8 => empty_item (strlit "Load8")
  | asm.Load16 => empty_item (strlit "Load16")
  | asm.Load32 => empty_item (strlit "Load32")
  | asm.Store => empty_item (strlit "Store")
  | asm.Store8 => empty_item (strlit "Store8")
  | asm.Store16 => empty_item (strlit "Store16")
  | asm.Store32 => empty_item (strlit "Store32")
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_cmp_to_display_def" *)
Definition asm_cmp_to_display (op : asm.cmp) : sExp :=
  match op with
  | asm.Equal => empty_item (strlit "Equal")
  | asm.Lower => empty_item (strlit "Lower")
  | asm.Less => empty_item (strlit "Less")
  | asm.Test => empty_item (strlit "Test")
  | asm.NotEqual => empty_item (strlit "NotEqual")
  | asm.NotLower => empty_item (strlit "NotLower")
  | asm.NotLess => empty_item (strlit "NotLess")
  | asm.NotTest => empty_item (strlit "NotTest")
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_fp_to_display_def" *)
Definition asm_fp_to_display (op : asm.fp) : sExp :=
  match op with
  | asm.FPLess n1 n2 n3 => item_with_nums (strlit "FPLess") [n1; n2; n3]
  | asm.FPLessEqual n1 n2 n3 => item_with_nums (strlit "FPLessEqual") [n1; n2; n3]
  | asm.FPEqual n1 n2 n3 => item_with_nums (strlit "FPEqual") [n1; n2; n3]
  | asm.FPAbs n1 n2 => item_with_nums (strlit "FPAbs") [n1; n2]
  | asm.FPNeg n1 n2 => item_with_nums (strlit "FPNeg") [n1; n2]
  | asm.FPSqrt n1 n2 => item_with_nums (strlit "FPSqrt") [n1; n2]
  | asm.FPAdd n1 n2 n3 => item_with_nums (strlit "FPAdd") [n1; n2; n3]
  | asm.FPSub n1 n2 n3 => item_with_nums (strlit "FPSub") [n1; n2; n3]
  | asm.FPMul n1 n2 n3 => item_with_nums (strlit "FPMul") [n1; n2; n3]
  | asm.FPDiv n1 n2 n3 => item_with_nums (strlit "FPDiv") [n1; n2; n3]
  | asm.FPFma n1 n2 n3 => item_with_nums (strlit "FPFma") [n1; n2; n3]
  | asm.FPMov n1 n2 => item_with_nums (strlit "FPMov") [n1; n2]
  | asm.FPMovToReg n1 n2 n3 => item_with_nums (strlit "FPMovToReg") [n1; n2; n3]
  | asm.FPMovFromReg n1 n2 n3 => item_with_nums (strlit "FPMovFromReg") [n1; n2; n3]
  | asm.FPToInt n1 n2 => item_with_nums (strlit "FPToInt") [n1; n2]
  | asm.FPFromInt n1 n2 => item_with_nums (strlit "FPFromInt") [n1; n2]
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_inst_to_display_def" *)
Definition asm_inst_to_display (inst : asm.inst a) : sExp :=
  match inst with
  | asm.Skip => empty_item (strlit "Skip")
  | asm.Const reg w => Item None (strlit "Const") [num_to_display reg; word_to_display w]
  | asm.Arith a0 => Item None (strlit "Arith") [asm_arith_to_display a0]
  | asm.Mem mop r addr =>
      Item None (strlit "Mem")
        [asm_memop_to_display mop; num_to_display r; asm_addr_to_display addr]
  | asm.FP fp => Item None (strlit "FP") [asm_fp_to_display fp]
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "asm_asm_to_display_def" *)
Definition asm_asm_to_display (inst : asm.asm a) : sExp :=
  match inst with
  | asm.Inst i => asm_inst_to_display i
  | asm.Jump w => item_with_word (strlit "Jump") w
  | asm.JumpCmp c r to w =>
      Item None (strlit "JumpCmp")
        [asm_cmp_to_display c; num_to_display r; asm_reg_imm_to_display to;
         word_to_display w]
  | asm.Call w => item_with_word (strlit "Call") w
  | asm.JumpReg r => item_with_num (strlit "JumpReg>") r
  | asm.Loc r w => Item None (strlit "Loc") [num_to_display r; word_to_display w]
  end.

End Asm.

(** ** stackLang *)

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "store_name_to_display_def" *)
Definition store_name_to_display (st : stackLang.store_name) : sExp :=
  match st with
  | stackLang.NextFree => empty_item (strlit "NextFree")
  | stackLang.EndOfHeap => empty_item (strlit "EndOfHeap")
  | stackLang.TriggerGC => empty_item (strlit "TriggerGC")
  | stackLang.HeapLength => empty_item (strlit "HeapLength")
  | stackLang.ProgStart => empty_item (strlit "ProgStart")
  | stackLang.BitmapBase => empty_item (strlit "BitmapBase")
  | stackLang.CurrHeap => empty_item (strlit "CurrHeap")
  | stackLang.OtherHeap => empty_item (strlit "OtherHeap")
  | stackLang.AllocSize => empty_item (strlit "AllocSize")
  | stackLang.Globals => empty_item (strlit "Globals")
  | stackLang.GlobReal => empty_item (strlit "GlobReal")
  | stackLang.Handler => empty_item (strlit "Handler")
  | stackLang.GenStart => empty_item (strlit "GenStart")
  | stackLang.CodeBuffer => empty_item (strlit "CodeBuffer")
  | stackLang.CodeBufferEnd => empty_item (strlit "CodeBufferEnd")
  | stackLang.BitmapBuffer => empty_item (strlit "BitmapBuffer")
  | stackLang.BitmapBufferEnd => empty_item (strlit "BitmapBufferEnd")
  | stackLang.Temp w => item_with_word (strlit "Temp") w
  end.

Section Stack.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "stack_seqs_def" *)
Fixpoint stack_seqs (z : stackLang.prog a) : app_list (stackLang.prog a) :=
  match z with
  | stackLang.Seq x y => Append (stack_seqs x) (stack_seqs y)
  | _ => misc.List [z]
  end.

(** [stack_prog_to_display] with a [nat] fuel (see the header). *)
Fixpoint stack_prog_to_display_nat (k : nat) (ns : num_map mlstring)
    (prog : stackLang.prog a) {struct k} : sExp :=
  match k with
  | O => empty_item (strlit "...")
  | S k =>
  match prog with
  | stackLang.Skip => empty_item (strlit "skip")
  | stackLang.Inst i => asm_inst_to_display i
  | stackLang.Get n sn =>
      Tuple [num_to_display n; String (strlit "<-"); store_name_to_display sn]
  | stackLang.Set_ sn n =>
      Tuple [store_name_to_display sn; String (strlit "<-"); num_to_display n]
  | stackLang.OpCurrHeap b n1 n2 =>
      Tuple [num_to_display n1; String (strlit ":="); String (strlit "CurrHeap");
             asm_binop_to_display b; num_to_display n2]
  | stackLang.Call rh tgt eh =>
      Item None (strlit "call")
        [(match rh with
          | None => empty_item (strlit "tail")
          | Some (p, (lr, (l1, l2))) =>
              Item None (strlit "returning")
                [num_to_display lr;
                 String (attach_name ns (Some l1));
                 num_to_display l2;
                 stack_prog_to_display_nat k ns p]
          end);
         (match tgt with
          | inl l => Item None (strlit "direct") [String (attach_name ns (Some l))]
          | inr r => item_with_num (strlit "reg") r
          end);
         (match eh with
          | None => empty_item (strlit "no_handler")
          | Some (p, (l1, l2)) =>
              Item None (strlit "handler")
                [String (attach_name ns (Some l1));
                 num_to_display l2;
                 stack_prog_to_display_nat k ns p]
          end)]
  | stackLang.Seq x y =>
      let xs := append (Append (stack_seqs x) (stack_seqs y)) in
      separate_lines (strlit "seq") (stack_prog_to_display_list_nat k ns xs)
  | stackLang.If c n to x y =>
      Item None (strlit "if")
        [Tuple [asm_cmp_to_display c; num_to_display n; asm_reg_imm_to_display to];
         stack_prog_to_display_nat k ns x;
         stack_prog_to_display_nat k ns y]
  | stackLang.Loop x => Item None (strlit "loop") [stack_prog_to_display_nat k ns x]
  | stackLang.JumpLower n1 n2 n3 => item_with_nums (strlit "jump_lower") [n1; n2; n3]
  | stackLang.Alloc n => item_with_num (strlit "alloc") n
  | stackLang.StoreConsts n1 n2 _ => item_with_nums (strlit "store_consts") [n1; n2]
  | stackLang.Raise n => item_with_num (strlit "raise") n
  | stackLang.Return n => item_with_num (strlit "return") n
  | stackLang.Break n => item_with_num (strlit "break") n
  | stackLang.Continue n => item_with_num (strlit "continue") n
  | stackLang.FFI nm cp cl ap al ra =>
      Item None (strlit "ffi") (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra])
  | stackLang.Tick => empty_item (strlit "tick")
  | stackLang.LocValue n1 n2 n3 =>
      Item None (strlit "loc_value")
        [num_to_display n1; String (attach_name ns (Some n2)); num_to_display n3]
  | stackLang.Install n1 n2 n3 n4 n5 =>
      item_with_nums (strlit "install") [n1; n2; n3; n4; n5]
  | stackLang.ShMemOp mop r a0 =>
      Item None (strlit "sh_mem")
        [asm_memop_to_display mop; num_to_display r; asm_addr_to_display a0]
  | stackLang.CodeBufferWrite n1 n2 => item_with_nums (strlit "code_buffer_write") [n1; n2]
  | stackLang.DataBufferWrite n1 n2 => item_with_nums (strlit "data_buffer_write") [n1; n2]
  | stackLang.RawCall n => Item None (strlit "raw_call") [String (attach_name ns (Some n))]
  | stackLang.StackAlloc n => item_with_num (strlit "stack_alloc") n
  | stackLang.StackFree n => item_with_num (strlit "stack_free") n
  | stackLang.StackStore n m =>
      Tuple [String (strcat (strcat (strcat (strlit "stack[") (num_to_hex_mlstring n))
                                    (strlit "] := ")) (num_to_str m))]
  | stackLang.StackStoreAny n m =>
      Tuple [String (strcat (strcat (strcat (strlit "stack[var ") (num_to_str n))
                                    (strlit "] := ")) (num_to_str m))]
  | stackLang.StackLoad n m =>
      Tuple [String (concat [num_to_str n; strlit " := stack["; num_to_hex_mlstring m;
                             strlit "]"])]
  | stackLang.StackLoadAny n m =>
      Tuple [String (concat [num_to_str n; strlit " := stack[var "; num_to_str m;
                             strlit "]"])]
  | stackLang.StackGetSize n => item_with_num (strlit "stack_get_size") n
  | stackLang.StackSetSize n => item_with_num (strlit "stack_set_size") n
  | stackLang.BitmapLoad n m =>
      Tuple [String (concat [num_to_str n; strlit " := bitmap["; num_to_hex_mlstring m;
                             strlit "]"])]
  | stackLang.Halt n => item_with_num (strlit "halt") n
  end
  end
with stack_prog_to_display_list_nat (k : nat) (ns : num_map mlstring)
    (l : list (stackLang.prog a)) {struct k} : list sExp :=
  match l with
  | [] => []
  | x :: xs =>
      match k with
      | O => []
      | S k => stack_prog_to_display_nat k ns x :: stack_prog_to_display_list_nat k ns xs
      end
  end.

Definition stack_prog_to_display (k : N) (ns : num_map mlstring) (prog : stackLang.prog a) : sExp :=
  stack_prog_to_display_nat (N.to_nat k) ns prog.

Definition stack_prog_to_display_list (k : N) (ns : num_map mlstring)
    (l : list (stackLang.prog a)) : list sExp :=
  stack_prog_to_display_list_nat (N.to_nat k) ns l.

Local Ltac solve_fuel_eqs :=
  repeat split; intros;
  unfold stack_prog_to_display, stack_prog_to_display_list;
  repeat match goal with
         | |- context [N.to_nat (N.succ ?k)] => rewrite (N2Nat.inj_succ k)
         end;
  first [reflexivity | destruct (N.to_nat _); reflexivity].

(** HOL's equations.  HOL's last clause
    [stack_prog_to_display_list k ns (x::xs) = case k of 0 => [] | SUC k => ...]
    is stated as its two cases. *)
(*! HOL "cakeml/compiler/backend/presLangScript.sml" "stack_prog_to_display_def" *)
Theorem stack_prog_to_display_def :
  (forall ns prog, stack_prog_to_display 0 ns prog = empty_item (strlit "...")) /\
  (forall k ns, stack_prog_to_display (SUC k) ns stackLang.Skip = empty_item (strlit "skip")) /\
  (forall k ns i, stack_prog_to_display (SUC k) ns (stackLang.Inst i) = asm_inst_to_display i) /\
  (forall k ns n sn, stack_prog_to_display (SUC k) ns (stackLang.Get n sn) =
     Tuple [num_to_display n; String (strlit "<-"); store_name_to_display sn]) /\
  (forall k ns sn n, stack_prog_to_display (SUC k) ns (stackLang.Set_ sn n) =
     Tuple [store_name_to_display sn; String (strlit "<-"); num_to_display n]) /\
  (forall k ns b n1 n2, stack_prog_to_display (SUC k) ns (stackLang.OpCurrHeap b n1 n2) =
     Tuple [num_to_display n1; String (strlit ":="); String (strlit "CurrHeap");
            asm_binop_to_display b; num_to_display n2]) /\
  (forall k ns rh tgt eh, stack_prog_to_display (SUC k) ns (stackLang.Call rh tgt eh) =
     Item None (strlit "call")
       [(match rh with
         | None => empty_item (strlit "tail")
         | Some (p, (lr, (l1, l2))) =>
             Item None (strlit "returning")
               [num_to_display lr;
                String (attach_name ns (Some l1));
                num_to_display l2;
                stack_prog_to_display k ns p]
         end);
        (match tgt with
         | inl l => Item None (strlit "direct") [String (attach_name ns (Some l))]
         | inr r => item_with_num (strlit "reg") r
         end);
        (match eh with
         | None => empty_item (strlit "no_handler")
         | Some (p, (l1, l2)) =>
             Item None (strlit "handler")
               [String (attach_name ns (Some l1));
                num_to_display l2;
                stack_prog_to_display k ns p]
         end)]) /\
  (forall k ns x y, stack_prog_to_display (SUC k) ns (stackLang.Seq x y) =
     let xs := append (Append (stack_seqs x) (stack_seqs y)) in
     separate_lines (strlit "seq") (stack_prog_to_display_list k ns xs)) /\
  (forall k ns c n to x y, stack_prog_to_display (SUC k) ns (stackLang.If c n to x y) =
     Item None (strlit "if")
       [Tuple [asm_cmp_to_display c; num_to_display n; asm_reg_imm_to_display to];
        stack_prog_to_display k ns x;
        stack_prog_to_display k ns y]) /\
  (forall k ns x, stack_prog_to_display (SUC k) ns (stackLang.Loop x) =
     Item None (strlit "loop") [stack_prog_to_display k ns x]) /\
  (forall k ns n1 n2 n3, stack_prog_to_display (SUC k) ns (stackLang.JumpLower n1 n2 n3) =
     item_with_nums (strlit "jump_lower") [n1; n2; n3]) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.Alloc n) =
     item_with_num (strlit "alloc") n) /\
  (forall k ns n1 n2 o_, stack_prog_to_display (SUC k) ns (stackLang.StoreConsts n1 n2 o_) =
     item_with_nums (strlit "store_consts") [n1; n2]) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.Raise n) =
     item_with_num (strlit "raise") n) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.Return n) =
     item_with_num (strlit "return") n) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.Break n) =
     item_with_num (strlit "break") n) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.Continue n) =
     item_with_num (strlit "continue") n) /\
  (forall k ns nm cp cl ap al ra,
     stack_prog_to_display (SUC k) ns (stackLang.FFI nm cp cl ap al ra) =
     Item None (strlit "ffi") (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra])) /\
  (forall k ns, stack_prog_to_display (SUC k) ns stackLang.Tick = empty_item (strlit "tick")) /\
  (forall k ns n1 n2 n3, stack_prog_to_display (SUC k) ns (stackLang.LocValue n1 n2 n3) =
     Item None (strlit "loc_value")
       [num_to_display n1; String (attach_name ns (Some n2)); num_to_display n3]) /\
  (forall k ns n1 n2 n3 n4 n5,
     stack_prog_to_display (SUC k) ns (stackLang.Install n1 n2 n3 n4 n5) =
     item_with_nums (strlit "install") [n1; n2; n3; n4; n5]) /\
  (forall k ns mop r a0, stack_prog_to_display (SUC k) ns (stackLang.ShMemOp mop r a0) =
     Item None (strlit "sh_mem")
       [asm_memop_to_display mop; num_to_display r; asm_addr_to_display a0]) /\
  (forall k ns n1 n2, stack_prog_to_display (SUC k) ns (stackLang.CodeBufferWrite n1 n2) =
     item_with_nums (strlit "code_buffer_write") [n1; n2]) /\
  (forall k ns n1 n2, stack_prog_to_display (SUC k) ns (stackLang.DataBufferWrite n1 n2) =
     item_with_nums (strlit "data_buffer_write") [n1; n2]) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.RawCall n) =
     Item None (strlit "raw_call") [String (attach_name ns (Some n))]) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.StackAlloc n) =
     item_with_num (strlit "stack_alloc") n) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.StackFree n) =
     item_with_num (strlit "stack_free") n) /\
  (forall k ns n m, stack_prog_to_display (SUC k) ns (stackLang.StackStore n m) =
     Tuple [String (strcat (strcat (strcat (strlit "stack[") (num_to_hex_mlstring n))
                                   (strlit "] := ")) (num_to_str m))]) /\
  (forall k ns n m, stack_prog_to_display (SUC k) ns (stackLang.StackStoreAny n m) =
     Tuple [String (strcat (strcat (strcat (strlit "stack[var ") (num_to_str n))
                                   (strlit "] := ")) (num_to_str m))]) /\
  (forall k ns n m, stack_prog_to_display (SUC k) ns (stackLang.StackLoad n m) =
     Tuple [String (concat [num_to_str n; strlit " := stack["; num_to_hex_mlstring m;
                            strlit "]"])]) /\
  (forall k ns n m, stack_prog_to_display (SUC k) ns (stackLang.StackLoadAny n m) =
     Tuple [String (concat [num_to_str n; strlit " := stack[var "; num_to_str m;
                            strlit "]"])]) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.StackGetSize n) =
     item_with_num (strlit "stack_get_size") n) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.StackSetSize n) =
     item_with_num (strlit "stack_set_size") n) /\
  (forall k ns n m, stack_prog_to_display (SUC k) ns (stackLang.BitmapLoad n m) =
     Tuple [String (concat [num_to_str n; strlit " := bitmap["; num_to_hex_mlstring m;
                            strlit "]"])]) /\
  (forall k ns n, stack_prog_to_display (SUC k) ns (stackLang.Halt n) =
     item_with_num (strlit "halt") n) /\
  (forall k ns, stack_prog_to_display_list k ns [] = []) /\
  (forall ns x xs, stack_prog_to_display_list 0 ns (x :: xs) = []) /\
  (forall k ns x xs, stack_prog_to_display_list (SUC k) ns (x :: xs) =
     stack_prog_to_display k ns x :: stack_prog_to_display_list k ns xs).
Proof. solve_fuel_eqs. Qed.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "stack_fun_to_display_def" *)
Definition stack_fun_to_display (names : num_map mlstring) (f : N * stackLang.prog a) : sExp :=
  match f with
  | (n, body) =>
      Tuple [String (strlit "func");
             String (attach_name names (Some n));
             stack_prog_to_display 1000000000 names body]
  end.

End Stack.

(** ** labLang *)

Section Lab.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "lab_asm_to_display_def" *)
Definition lab_asm_to_display (ns : num_map mlstring) (la : labLang.asm_with_lab a) : sExp :=
  match la with
  | labLang.Jump (labLang.Lab s n) =>
      Item None (strlit "jump") [String (attach_name ns (Some s)); num_to_display n]
  | labLang.JumpCmp c r ri (labLang.Lab s n) =>
      Item None (strlit "jump_cmp")
        [Tuple [asm_cmp_to_display c; num_to_display r; asm_reg_imm_to_display ri];
         String (attach_name ns (Some s)); num_to_display n]
  | labLang.Call (labLang.Lab s n) =>
      Item None (strlit "call") [String (attach_name ns (Some s)); num_to_display n]
  | labLang.LocValue r (labLang.Lab s n) =>
      Item None (strlit "loc_value")
        [num_to_display r; String (attach_name ns (Some s)); num_to_display n]
  | labLang.CallFFI name => Item None (strlit "call_FFI") [string_imp name]
  | labLang.Install => empty_item (strlit "install")
  | labLang.Halt => empty_item (strlit "halt")
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "lab_line_to_display_def" *)
Definition lab_line_to_display (ns : num_map mlstring) (line : labLang.line a) : sExp :=
  match line with
  | labLang.Label s n le =>
      Item None (strlit "label") [String (attach_name ns (Some s)); num_to_display n]
  | labLang.Asm aoc enc len =>
      match aoc with
      | labLang.Asmi i => Item None (strlit "asm") [asm_asm_to_display i]
      | labLang.Cbw r1 r2 => item_with_nums (strlit "cbw") [r1; r2]
      | labLang.ShareMem mop r a0 =>
          Item None (strlit "share_mem")
            [asm_memop_to_display mop; num_to_display r; asm_addr_to_display a0]
      end
  | labLang.LabAsm la pos enc len => lab_asm_to_display ns la
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "lab_fun_to_display_def" *)
Definition lab_fun_to_display (names : num_map mlstring) (s : labLang.sec a) : sExp :=
  match s with
  | labLang.Section_ n lines =>
      List (String (attach_name names (Some n)) :: MAP (lab_line_to_display names) lines)
  end.

End Lab.

(** ** wordLang *)

Section Word.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "word_seqs_def" *)
Fixpoint word_seqs (z : wordLang.prog a) : app_list (wordLang.prog a) :=
  match z with
  | wordLang.Seq x y => Append (word_seqs x) (word_seqs y)
  | _ => misc.List [z]
  end.

(** HOL's mutual [word_exp_to_display]/[word_exp_to_display_list]: the list
    function is a nested [fix] here; HOL's equations are the tagged
    [word_exp_to_display_def]. *)
Fixpoint word_exp_to_display (e : wordLang.exp a) : sExp :=
  let word_exp_to_display_list :=
    fix word_exp_to_display_list (l : list (wordLang.exp a)) : list sExp :=
      match l with
      | [] => []
      | x :: xs => word_exp_to_display x :: word_exp_to_display_list xs
      end in
  match e with
  | wordLang.Const v => item_with_word (strlit "Const") v
  | wordLang.Var n => item_with_num (strlit "Var") n
  | wordLang.Lookup st => Item None (strlit "Lookup") [store_name_to_display st]
  | wordLang.Load exp2 => Item None (strlit "MemLoad") [word_exp_to_display exp2]
  | wordLang.Op bop exs =>
      Item None (strlit "Op") (asm_binop_to_display bop :: word_exp_to_display_list exs)
  | wordLang.Shift sh exp exp1 =>
      Item None (strlit "Shift")
        [shift_to_display sh; word_exp_to_display exp; word_exp_to_display exp1]
  end.

Fixpoint word_exp_to_display_list (l : list (wordLang.exp a)) : list sExp :=
  match l with
  | [] => []
  | x :: xs => word_exp_to_display x :: word_exp_to_display_list xs
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "word_exp_to_display_def" *)
Theorem word_exp_to_display_def :
  (forall v, word_exp_to_display (wordLang.Const v) = item_with_word (strlit "Const") v) /\
  (forall n, word_exp_to_display (wordLang.Var n) = item_with_num (strlit "Var") n) /\
  (forall st, word_exp_to_display (wordLang.Lookup st) =
     Item None (strlit "Lookup") [store_name_to_display st]) /\
  (forall exp2, word_exp_to_display (wordLang.Load exp2) =
     Item None (strlit "MemLoad") [word_exp_to_display exp2]) /\
  (forall bop exs, word_exp_to_display (wordLang.Op bop exs) =
     Item None (strlit "Op") (asm_binop_to_display bop :: word_exp_to_display_list exs)) /\
  (forall sh exp exp1, word_exp_to_display (wordLang.Shift sh exp exp1) =
     Item None (strlit "Shift")
       [shift_to_display sh; word_exp_to_display exp; word_exp_to_display exp1]) /\
  (word_exp_to_display_list [] = []) /\
  (forall x xs, word_exp_to_display_list (x :: xs) =
     word_exp_to_display x :: word_exp_to_display_list xs).
Proof. repeat split. Qed.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "ws_to_display_def" *)
Fixpoint ws_to_display (l : list (bool * word a)) : list sExp :=
  match l with
  | [] => []
  | (b, x) :: xs => Tuple [bool_to_display b; word_to_display x] :: ws_to_display xs
  end.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "num_sets_to_display_def" *)
Definition num_sets_to_display (p : num_set * num_set) : sExp :=
  match p with
  | (l, r) => Tuple [num_set_to_display l; num_set_to_display r]
  end.

(** [word_prog_to_display] and its mutual companions with a [nat] fuel (see
    the header). *)
Fixpoint word_prog_to_display_nat (k : nat) (ns : num_map mlstring)
    (x : wordLang.prog a) {struct k} : sExp :=
  match k with
  | O => empty_item (strlit "...")
  | S k =>
  match x with
  | wordLang.Skip => empty_item (strlit "skip")
  | wordLang.Move n mvs =>
      Item None (strlit "move")
        [num_to_display n;
         Tuple (MAP (fun '(n1, n2) =>
                       Tuple [num_to_display n1; String (strlit ":="); num_to_display n2]) mvs)]
  | wordLang.Inst i => Item None (strlit "inst") [asm_inst_to_display i]
  | wordLang.Assign n exp =>
      Tuple [num_to_display n; String (strlit ":="); word_exp_to_display exp]
  | wordLang.Get n sn =>
      Tuple [num_to_display n; String (strlit "<-"); store_name_to_display sn]
  | wordLang.Set_ sn exp =>
      Tuple [store_name_to_display sn; String (strlit "<-"); word_exp_to_display exp]
  | wordLang.Store exp n =>
      Tuple [String (strlit "mem"); word_exp_to_display exp;
             String (strlit ":="); num_to_display n]
  | wordLang.ShareInst mop n exp =>
      Tuple [String (strlit "share_mem"); asm_memop_to_display mop;
             num_to_display n; word_exp_to_display exp]
  | wordLang.MustTerminate prog =>
      Item None (strlit "must_terminate") [word_prog_to_display_nat k ns prog]
  | wordLang.Call a0 b c d =>
      Item None (strlit "call")
        [word_prog_to_display_ret_nat k ns a0;
         option_to_display (fun n => String (attach_name ns (Some n))) b;
         list_to_display num_to_display c;
         word_prog_to_display_handler_nat k ns d]
  | wordLang.OpCurrHeap b n1 n2 =>
      Tuple [num_to_display n1; String (strlit ":="); String (strlit "CurrHeap");
             asm_binop_to_display b; num_to_display n2]
  | wordLang.Seq prog1 prog2 =>
      let xs := append (Append (word_seqs prog1) (word_seqs prog2)) in
      separate_lines (strlit "seq") (word_prog_to_display_list_nat k ns xs)
  | wordLang.If cmp n reg p1 p2 =>
      Item None (strlit "if")
        [Tuple [asm_cmp_to_display cmp; num_to_display n; asm_reg_imm_to_display reg];
         word_prog_to_display_nat k ns p1; word_prog_to_display_nat k ns p2]
  | wordLang.Loop ns1 p ns2 =>
      Item None (strlit "Loop")
        [num_set_to_display ns1; word_prog_to_display_nat k ns p; num_set_to_display ns2]
  | wordLang.Alloc n ms =>
      Item None (strlit "alloc") [num_to_display n; num_sets_to_display ms]
  | wordLang.StoreConsts a0 b c d ws =>
      Item None (strlit "store_consts")
        [num_to_display a0; num_to_display b; num_to_display c; num_to_display d;
         Tuple (ws_to_display ws)]
  | wordLang.Raise n => item_with_num (strlit "raise") n
  | wordLang.Break n => item_with_num (strlit "break") n
  | wordLang.Continue n => item_with_num (strlit "continue") n
  | wordLang.Return n vs =>
      Item None (strlit "return") [num_to_display n; Tuple (MAP num_to_display vs)]
  | wordLang.Tick => empty_item (strlit "tick")
  | wordLang.LocValue n1 n2 =>
      Item None (strlit "loc_value") [String (attach_name ns (Some n1)); num_to_display n2]
  | wordLang.Install n1 n2 n3 n4 ms =>
      Item None (strlit "install")
        (MAP num_to_display [n1; n2; n3; n4] ++ [num_sets_to_display ms])
  | wordLang.CodeBufferWrite n1 n2 => item_with_nums (strlit "code_buffer_write") [n1; n2]
  | wordLang.DataBufferWrite n1 n2 => item_with_nums (strlit "data_buffer_write") [n1; n2]
  | wordLang.FFI nm n1 n2 n3 n4 ms =>
      Item None (strlit "ffi")
        (string_imp nm :: MAP num_to_display [n1; n2; n3; n4] ++ [num_sets_to_display ms])
  end
  end
with word_prog_to_display_list_nat (k : nat) (ns : num_map mlstring)
    (l : list (wordLang.prog a)) {struct k} : list sExp :=
  match l with
  | [] => []
  | x :: xs =>
      match k with
      | O => []
      | S k => word_prog_to_display_nat k ns x :: word_prog_to_display_list_nat k ns xs
      end
  end
with word_prog_to_display_ret_nat (k : nat) (ns : num_map mlstring)
    (r : option (list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))) {struct k} : sExp :=
  match r with
  | None => empty_item (strlit "tail")
  | Some (vs, (ms, (prog, (n2, n3)))) =>
      match k with
      | O => empty_item (strlit "...")
      | S k =>
          Item None (strlit "returning")
            [Tuple [Tuple (MAP num_to_display vs); num_sets_to_display ms;
                    word_prog_to_display_nat k ns prog;
                    String (attach_name ns (Some n2));
                    num_to_display n3]]
      end
  end
with word_prog_to_display_handler_nat (k : nat) (ns : num_map mlstring)
    (h : option (N * (wordLang.prog a * (N * N)))) {struct k} : sExp :=
  match h with
  | None => empty_item (strlit "no_handler")
  | Some (n1, (prog, (n2, n3))) =>
      match k with
      | O => empty_item (strlit "...")
      | S k =>
          Item None (strlit "handler")
            [Tuple [num_to_display n1;
                    word_prog_to_display_nat k ns prog;
                    String (attach_name ns (Some n2));
                    num_to_display n3]]
      end
  end.

Definition word_prog_to_display (k : N) (ns : num_map mlstring) (x : wordLang.prog a) : sExp :=
  word_prog_to_display_nat (N.to_nat k) ns x.

Definition word_prog_to_display_list (k : N) (ns : num_map mlstring)
    (l : list (wordLang.prog a)) : list sExp :=
  word_prog_to_display_list_nat (N.to_nat k) ns l.

Definition word_prog_to_display_ret (k : N) (ns : num_map mlstring)
    (r : option (list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))) : sExp :=
  word_prog_to_display_ret_nat (N.to_nat k) ns r.

Definition word_prog_to_display_handler (k : N) (ns : num_map mlstring)
    (h : option (N * (wordLang.prog a * (N * N)))) : sExp :=
  word_prog_to_display_handler_nat (N.to_nat k) ns h.

(** HOL's equations.  HOL's clauses
    [word_prog_to_display_list k ns (x::xs) = case k of 0 => [] | SUC k => ...]
    (and likewise for [_ret] and [_handler] on [SOME]) are stated as their
    two cases. *)
(*! HOL "cakeml/compiler/backend/presLangScript.sml" "word_prog_to_display_def" *)
Theorem word_prog_to_display_def :
  (forall ns x, word_prog_to_display 0 ns x = empty_item (strlit "...")) /\
  (forall k ns, word_prog_to_display (SUC k) ns wordLang.Skip = empty_item (strlit "skip")) /\
  (forall k ns n mvs, word_prog_to_display (SUC k) ns (wordLang.Move n mvs) =
     Item None (strlit "move")
       [num_to_display n;
        Tuple (MAP (fun '(n1, n2) =>
                      Tuple [num_to_display n1; String (strlit ":="); num_to_display n2]) mvs)]) /\
  (forall k ns i, word_prog_to_display (SUC k) ns (wordLang.Inst i) =
     Item None (strlit "inst") [asm_inst_to_display i]) /\
  (forall k ns n exp, word_prog_to_display (SUC k) ns (wordLang.Assign n exp) =
     Tuple [num_to_display n; String (strlit ":="); word_exp_to_display exp]) /\
  (forall k ns n sn, word_prog_to_display (SUC k) ns (wordLang.Get n sn) =
     Tuple [num_to_display n; String (strlit "<-"); store_name_to_display sn]) /\
  (forall k ns sn exp, word_prog_to_display (SUC k) ns (wordLang.Set_ sn exp) =
     Tuple [store_name_to_display sn; String (strlit "<-"); word_exp_to_display exp]) /\
  (forall k ns exp n, word_prog_to_display (SUC k) ns (wordLang.Store exp n) =
     Tuple [String (strlit "mem"); word_exp_to_display exp;
            String (strlit ":="); num_to_display n]) /\
  (forall k ns mop n exp, word_prog_to_display (SUC k) ns (wordLang.ShareInst mop n exp) =
     Tuple [String (strlit "share_mem"); asm_memop_to_display mop;
            num_to_display n; word_exp_to_display exp]) /\
  (forall k ns prog, word_prog_to_display (SUC k) ns (wordLang.MustTerminate prog) =
     Item None (strlit "must_terminate") [word_prog_to_display k ns prog]) /\
  (forall k ns a0 b c d, word_prog_to_display (SUC k) ns (wordLang.Call a0 b c d) =
     Item None (strlit "call")
       [word_prog_to_display_ret k ns a0;
        option_to_display (fun n => String (attach_name ns (Some n))) b;
        list_to_display num_to_display c;
        word_prog_to_display_handler k ns d]) /\
  (forall k ns b n1 n2, word_prog_to_display (SUC k) ns (wordLang.OpCurrHeap b n1 n2) =
     Tuple [num_to_display n1; String (strlit ":="); String (strlit "CurrHeap");
            asm_binop_to_display b; num_to_display n2]) /\
  (forall k ns prog1 prog2, word_prog_to_display (SUC k) ns (wordLang.Seq prog1 prog2) =
     let xs := append (Append (word_seqs prog1) (word_seqs prog2)) in
     separate_lines (strlit "seq") (word_prog_to_display_list k ns xs)) /\
  (forall k ns cmp n reg p1 p2, word_prog_to_display (SUC k) ns (wordLang.If cmp n reg p1 p2) =
     Item None (strlit "if")
       [Tuple [asm_cmp_to_display cmp; num_to_display n; asm_reg_imm_to_display reg];
        word_prog_to_display k ns p1; word_prog_to_display k ns p2]) /\
  (forall k ns ns1 p ns2, word_prog_to_display (SUC k) ns (wordLang.Loop ns1 p ns2) =
     Item None (strlit "Loop")
       [num_set_to_display ns1; word_prog_to_display k ns p; num_set_to_display ns2]) /\
  (forall k ns n ms, word_prog_to_display (SUC k) ns (wordLang.Alloc n ms) =
     Item None (strlit "alloc") [num_to_display n; num_sets_to_display ms]) /\
  (forall k ns a0 b c d ws, word_prog_to_display (SUC k) ns (wordLang.StoreConsts a0 b c d ws) =
     Item None (strlit "store_consts")
       [num_to_display a0; num_to_display b; num_to_display c; num_to_display d;
        Tuple (ws_to_display ws)]) /\
  (forall k ns n, word_prog_to_display (SUC k) ns (wordLang.Raise n) =
     item_with_num (strlit "raise") n) /\
  (forall k ns n, word_prog_to_display (SUC k) ns (wordLang.Break n) =
     item_with_num (strlit "break") n) /\
  (forall k ns n, word_prog_to_display (SUC k) ns (wordLang.Continue n) =
     item_with_num (strlit "continue") n) /\
  (forall k ns n vs, word_prog_to_display (SUC k) ns (wordLang.Return n vs) =
     Item None (strlit "return") [num_to_display n; Tuple (MAP num_to_display vs)]) /\
  (forall k ns, word_prog_to_display (SUC k) ns wordLang.Tick = empty_item (strlit "tick")) /\
  (forall k ns n1 n2, word_prog_to_display (SUC k) ns (wordLang.LocValue n1 n2) =
     Item None (strlit "loc_value") [String (attach_name ns (Some n1)); num_to_display n2]) /\
  (forall k ns n1 n2 n3 n4 ms, word_prog_to_display (SUC k) ns (wordLang.Install n1 n2 n3 n4 ms) =
     Item None (strlit "install")
       (MAP num_to_display [n1; n2; n3; n4] ++ [num_sets_to_display ms])) /\
  (forall k ns n1 n2, word_prog_to_display (SUC k) ns (wordLang.CodeBufferWrite n1 n2) =
     item_with_nums (strlit "code_buffer_write") [n1; n2]) /\
  (forall k ns n1 n2, word_prog_to_display (SUC k) ns (wordLang.DataBufferWrite n1 n2) =
     item_with_nums (strlit "data_buffer_write") [n1; n2]) /\
  (forall k ns nm n1 n2 n3 n4 ms, word_prog_to_display (SUC k) ns (wordLang.FFI nm n1 n2 n3 n4 ms) =
     Item None (strlit "ffi")
       (string_imp nm :: MAP num_to_display [n1; n2; n3; n4] ++ [num_sets_to_display ms])) /\
  (forall k ns, word_prog_to_display_list k ns [] = []) /\
  (forall ns x xs, word_prog_to_display_list 0 ns (x :: xs) = []) /\
  (forall k ns x xs, word_prog_to_display_list (SUC k) ns (x :: xs) =
     word_prog_to_display k ns x :: word_prog_to_display_list k ns xs) /\
  (forall k ns, word_prog_to_display_ret k ns None = empty_item (strlit "tail")) /\
  (forall ns vs ms prog n2 n3,
     word_prog_to_display_ret 0 ns (Some (vs, (ms, (prog, (n2, n3))))) =
     empty_item (strlit "...")) /\
  (forall k ns vs ms prog n2 n3,
     word_prog_to_display_ret (SUC k) ns (Some (vs, (ms, (prog, (n2, n3))))) =
     Item None (strlit "returning")
       [Tuple [Tuple (MAP num_to_display vs); num_sets_to_display ms;
               word_prog_to_display k ns prog;
               String (attach_name ns (Some n2));
               num_to_display n3]]) /\
  (forall k ns, word_prog_to_display_handler k ns None = empty_item (strlit "no_handler")) /\
  (forall ns n1 prog n2 n3,
     word_prog_to_display_handler 0 ns (Some (n1, (prog, (n2, n3)))) =
     empty_item (strlit "...")) /\
  (forall k ns n1 prog n2 n3,
     word_prog_to_display_handler (SUC k) ns (Some (n1, (prog, (n2, n3)))) =
     Item None (strlit "handler")
       [Tuple [num_to_display n1;
               word_prog_to_display k ns prog;
               String (attach_name ns (Some n2));
               num_to_display n3]]).
Proof.
  repeat split; intros;
  unfold word_prog_to_display, word_prog_to_display_list, word_prog_to_display_ret,
    word_prog_to_display_handler;
  repeat match goal with
         | |- context [N.to_nat (N.succ ?k)] => rewrite (N2Nat.inj_succ k)
         end;
  first [reflexivity | destruct (N.to_nat _); reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "word_fun_to_display_def" *)
Definition word_fun_to_display (names : num_map mlstring)
    (f : N * (N * wordLang.prog a)) : sExp :=
  match f with
  | (n, (argc, body)) =>
      Tuple [String (strlit "func");
             String (attach_name names (Some n));
             Tuple (GENLIST (fun n => num_to_display (2 * n)) argc);
             word_prog_to_display 1000000000 names body]
  end.

End Word.

(** ** Printing *)

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "map_to_append_def" *)
Fixpoint map_to_append {A B} (f : A -> list B) (l : list A) : app_list B :=
  match l with
  | [] => Nil
  | x :: xs => Append (misc.List (f x)) (map_to_append f xs)
  end.

(** HOL's [«\n\n»]. *)
Definition double_newline : mlstring := strlit ["010"%char; "010"%char].

Section Strs.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "word_to_strs_def" *)
Definition word_to_strs (names : num_map mlstring)
    (xs : list (N * (N * wordLang.prog a))) : app_list mlstring :=
  map_to_append (mlsexp.str_tree_to_strs double_newline ∘
                 display_to_str_tree ∘
                 word_fun_to_display names) xs.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "stack_to_strs_def" *)
Definition stack_to_strs (names : num_map mlstring)
    (xs : list (N * stackLang.prog a)) : app_list mlstring :=
  map_to_append (mlsexp.str_tree_to_strs double_newline ∘
                 display_to_str_tree ∘
                 stack_fun_to_display names) xs.

(*! HOL "cakeml/compiler/backend/presLangScript.sml" "lab_to_strs_def" *)
Definition lab_to_strs (names : num_map mlstring)
    (xs : list (labLang.sec a)) : app_list mlstring :=
  map_to_append (mlsexp.str_tree_to_strs double_newline ∘
                 display_to_str_tree ∘
                 lab_fun_to_display names) xs.

End Strs.
