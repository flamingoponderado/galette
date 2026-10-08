(** * CakeML [backend_common]: definitions shared by the compiler backend

    Port of [cakeml/compiler/backend/backend_commonScript.sml].

    - [opw]'s constructors [Add], [Sub], [Xor] have the names of ASM's
      [binop] constructors (HOL keeps them apart by theory); a file
      importing both refers to the one it does not import last by its
      qualified name ([backend_common.Add] / [asm.Add]).
    - [tra]'s constructor [None] would shadow Rocq's [option] constructor
      in every importing file; it is named [tra_None] here.  The datatype is
      otherwise HOL's.  The [▷] / [§] infix overloads are not ported. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.finite_maps Require Import sptree.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "opw" *)
Inductive opw : Type := Andw | Orw | Xor | Add | Sub.

#[global] Instance opw_eq_dec : EqDecision opw.
Proof. intros x y; unfold Decision; decide equality. Defined.
#[global] Instance opw_inhabited : Inhabited opw := Andw.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "small_enough_int_def" *)
Definition small_enough_int (i : Z) : bool :=
  ((-268435457 <=? i)%Z && (i <=? 268435457)%Z)%bool.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "bind_tag_def" *)
Definition bind_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "chr_tag_def" *)
Definition chr_tag : N := 1.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "div_tag_def" *)
Definition div_tag : N := 2.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "subscript_tag_def" *)
Definition subscript_tag : N := 3.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "false_tag_def" *)
Definition false_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "true_tag_def" *)
Definition true_tag : N := 1.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "nil_tag_def" *)
Definition nil_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "cons_tag_def" *)
Definition cons_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "none_tag_def" *)
Definition none_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "some_tag_def" *)
Definition some_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "tuple_tag_def" *)
Definition tuple_tag : N := 0.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "closure_tag_def" *)
Definition closure_tag : N := 30.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "partial_app_tag_def" *)
Definition partial_app_tag : N := 31.
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "clos_tag_shift_def" *)
Definition clos_tag_shift (tag : N) : N := if tag <? 30 then tag else tag + 2.

(** Trace of an expression through the compiler.  HOL's constructor [None]
    is [tra_None] (see the file header). *)
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "tra" *)
Inductive tra : Type :=
| SourceLoc : N -> N -> N -> N -> tra
| Cons : tra -> N -> tra
| Union : tra -> tra -> tra
| tra_None : tra.

#[global] Instance tra_eq_dec : EqDecision tra.
Proof. intros x y; unfold Decision; repeat decide equality. Defined.
#[global] Instance tra_inhabited : Inhabited tra := tra_None.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "orphan_trace_def" *)
Definition orphan_trace : tra := SourceLoc 2 2 1 1.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "mk_cons_def" *)
Definition mk_cons (tr : tra) (n : N) : tra :=
  match tr with
  | tra_None => tra_None
  | _ => Cons tr n
  end.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "mk_union_def" *)
Definition mk_union (tr1 tr2 : tra) : tra :=
  match tr1 with
  | tra_None => tra_None
  | _ => match tr2 with
         | tra_None => tra_None
         | _ => Union tr1 tr2
         end
  end.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "bool_to_tag_def" *)
Definition bool_to_tag (b : bool) : N := if b then true_tag else false_tag.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "stack_num_stubs_def" *)
Definition stack_num_stubs : N := 5.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "word_num_stubs_def" *)
Definition word_num_stubs : N := stack_num_stubs + 1 + 1.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "data_num_stubs_def" *)
Definition data_num_stubs : N := word_num_stubs + 32 + 23.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "bvl_num_stubs_def" *)
Definition bvl_num_stubs : N := data_num_stubs + 9 + 1.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "bvl_to_bvi_namespaces_def" *)
Definition bvl_to_bvi_namespaces : N := 4.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "data_num_stubs_EVEN" *)
Theorem data_num_stubs_EVEN : EVEN data_num_stubs.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "bvl_num_stub_MOD" *)
Theorem bvl_num_stub_MOD : bvl_num_stubs MOD bvl_to_bvi_namespaces = 0.
Proof. reflexivity. Qed.

(** HOL [word_shift (:'a)]: the width index [a] is HOL's type argument. *)
(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "word_shift_def" *)
Definition word_shift (a : N) : N := if dimindex a =? 32 then 2 else 3.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "upper_w2w_def" *)
Definition upper_w2w {a : N} (w : word a) : word64 :=
  if dimindex a =? 32 then word_lsl (w2w w) 32 else w2w w.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "word_add_carry_def" *)
Definition word_add_carry {a : N} (l r c : word a) : word a * word a :=
  let res := w2n l + w2n r + (if decide (c = n2w 0) then 0 else 1) in
  (n2w res, if dimword a <=? res then n2w 1 else n2w 0).

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "list_delete_def" *)
Fixpoint list_delete {A} (l : list N) (s : spt A) : spt A :=
  match l with
  | [] => s
  | v :: vs => list_delete vs (delete v s)
  end.

(*! HOL "cakeml/compiler/backend/backend_commonScript.sml" "lookup_list_delete" *)
Theorem lookup_list_delete : forall {A} (xs : list N) (l : spt A) n,
  lookup n (list_delete xs l) = if MEM n xs then NONE else lookup n l.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros l n; cbn [list_delete MEM]; [reflexivity|].
  rewrite IH, lookup_delete; unfold bool_decide.
  destruct (decide (n = x)); destruct (MEM n xs); reflexivity.
Qed.
