(** * Pancake [loop_call]: call optimisation for loopLang

    Port of [cakeml/pancake/loop_callScript.sml].

    HOL's [let (np, nl) = ...; (nq, nl) = ... in] is sequential.
    HOL [BUTLAST] is [FRONT].

    [list_delete] ([backend_commonScript], not ported yet) is a Galette-local
    copy. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require Import loopLang.
Open Scope N_scope.

(** HOL [list_delete] (from [backend_commonScript]; Galette-local until
    that script is ported). *)
#[local] Fixpoint list_delete {A} (l : list N) (s : spt A) : spt A :=
  match l with
  | [] => s
  | v :: vs => list_delete vs (delete v s)
  end.

(*! HOL "cakeml/pancake/loop_callScript.sml" "is_load_def" *)
Definition is_load (m : memop) : bool :=
  match m with
  | asm.Load => true
  | Load8 => true
  | Load16 => true
  | asm.Load32 => true
  | _ => false
  end.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/loop_callScript.sml" "comp_def" *)
Fixpoint comp (l : num_map N) (p : prog a) : prog a * num_map N :=
  match p with
  | Skip => (Skip, l)
  | Call ret dest args handler =>
      (match dest with
       | Some _ => Call ret dest args handler
       | None =>
           match args with
           | [] => Skip
           | _ =>
               match lookup (LAST args) l with
               | None => Call ret None args handler
               | Some n => Call ret (Some n) (FRONT args) handler
               end
           end
       end, LN)
  | LocValue n m => (LocValue n m, insert n m l)
  | Assign n (Var m) =>
      (Assign n (Var m),
       match lookup n l, lookup m l with
       | None, None => l
       | Some _, None => delete n l
       | _, Some loc => insert n loc l
       end)
  | Assign n e =>
      (Assign n e,
       match lookup n l with
       | None => l
       | _ => delete n l
       end)
  | ShMem op n e => (ShMem op n e, LN)
  | Load32 m n =>
      (Load32 m n,
       match lookup n l with
       | None => l
       | _ => delete n l
       end)
  | LoadByte m n =>
      (LoadByte m n,
       match lookup n l with
       | None => l
       | _ => delete n l
       end)
  | Seq p q =>
      let (np, nl) := comp l p in
      let (nq, nl) := comp nl q in
      (Seq np nq, LN)
  | If c n ri p q ns =>
      let (np, nl) := comp l p in
      let (nq, ml) := comp l q in
      (If c n ri np nq ns, LN)
  | Loop ns p ms =>
      let (np, nl) := comp LN p in
      (Loop ns np ms, LN)
  | Mark p =>
      let (np, nl) := comp l p in
      (Mark np, nl)
  | FFI str n m n' m' nl => (FFI str n m n' m' nl, LN)
  | Tick => (Tick, LN)
  | Raise n => (Raise n, LN)
  | Return n => (Return n, LN)
  | Primitive lhss pop rhss => (Primitive lhss pop rhss, list_delete lhss l)
  | Arith arith =>
      (Arith arith,
       match arith with
       | LLongMul r1 r2 r3 r4 =>
           match lookup r1 l, lookup r2 l with
           | None, None => l
           | Some _, None => delete r1 l
           | None, Some loc => delete r2 l
           | _, _ => delete r1 (delete r2 l)
           end
       | LLongDiv r1 r2 r3 r4 r5 =>
           match lookup r1 l, lookup r2 l with
           | None, None => l
           | Some _, None => delete r1 l
           | None, Some loc => delete r2 l
           | _, _ => delete r1 (delete r2 l)
           end
       | LDiv r1 r2 r3 =>
           match lookup r1 l with
           | None => l
           | _ => delete r1 l
           end
       end)
  | p => (p, l)
  end.

End Defs.
