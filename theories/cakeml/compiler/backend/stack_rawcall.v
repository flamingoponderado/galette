(** * CakeML [stack_rawcall]: calls past the stack allocation of a function

    Port of [cakeml/compiler/backend/stack_rawcallScript.sml].  The
    [_pmatch] theorems are not ported. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import stackLang.
Open Scope N_scope.

Section StackRawcall.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "seq_stack_alloc_def" *)
Definition seq_stack_alloc (p : prog a) : option N :=
  match p with Seq (StackAlloc k) _ => Some k | _ => None end.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "collect_info_def" *)
Fixpoint collect_info (l : list (N * prog a)) (f : spt N) : spt N :=
  match l with
  | [] => f
  | (n, b) :: xs =>
      collect_info xs (match seq_stack_alloc b with
                       | None => f
                       | Some k => insert n k f
                       end)
  end.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "dest_case_def" *)
Definition dest_case (p1 p2 : prog a) : option (N * N) :=
  match p1 with
  | StackFree k => match p2 with Call None (inl d) None => Some (k, d) | _ => None end
  | _ => None
  end.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "comp_seq_def" *)
Definition comp_seq (p1 p2 : prog a) (i : spt N) (default : prog a) : prog a :=
  match dest_case p1 p2 with
  | Some (k, dest) =>
      match lookup dest i with
      | None => default
      | Some l =>
          if l =? k then RawCall dest else
          if l <? k then Seq (StackFree (k - l)) (RawCall dest) else
            Seq Tick (Seq (StackAlloc (l - k)) (RawCall dest))
      end
  | _ => default
  end.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "comp_def" *)
Fixpoint comp (i : spt N) (p : prog a) : prog a :=
  match p with
  | Seq p1 p2 => comp_seq p1 p2 i (Seq (comp i p1) (comp i p2))
  | If c r ri p1 p2 => If c r ri (comp i p1) (comp i p2)
  | Loop p1 => Loop (comp i p1)
  | Call (Some (p1, (lr, (l1, l2)))) dest None =>
      Call (Some (comp i p1, (lr, (l1, l2)))) dest None
  | Call (Some (p1, (lr, (l1, l2)))) dest (Some (p2, (k1, k2))) =>
      Call (Some (comp i p1, (lr, (l1, l2)))) dest (Some (comp i p2, (k1, k2)))
  | _ => p
  end.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "comp_top_def" *)
Definition comp_top (i : spt N) (p : prog a) : prog a :=
  match p with Seq p1 p2 => Seq (comp i p1) (comp i p2) | _ => comp i p end.

(*! HOL "cakeml/compiler/backend/stack_rawcallScript.sml" "compile_def" *)
Definition compile (prog0 : list (N * prog a)) : list (N * prog a) :=
  let i := collect_info prog0 LN in
  MAP (fun '(n, b) => (n, comp_top i b)) prog0.

End StackRawcall.
