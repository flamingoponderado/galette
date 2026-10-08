(** * CakeML [data_to_word]: configuration and GC parameters

    Partial port of [cakeml/compiler/backend/data_to_wordScript.sml]: the
    configuration record and the GC-related helpers used by the stackLang
    passes ([stack_alloc], [stack_to_lab]).  The dataLang-to-wordLang
    compiler itself is not part of the Pancake pipeline and is not ported.

    - HOL's type [gc_kind] has the name of a field of [config]; the Rocq
      type is [gc_kind_ty] (the field keeps HOL's name).  Its constructor
      [None] would shadow Rocq's [option] constructor; it is
      [gc_kind_None]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words byte.
From Galette.cakeml.compiler.backend Require Import backend_common.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/data_to_wordScript.sml" "gc_kind" *)
Inductive gc_kind_ty : Type :=
| gc_kind_None
| Simple
| Generational : list N -> gc_kind_ty.

#[global] Instance gc_kind_ty_eq_dec : EqDecision gc_kind_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance gc_kind_ty_inhabited : Inhabited gc_kind_ty := gc_kind_None.

(** The fields of HOL's record, in HOL's order. *)
(*! HOL "cakeml/compiler/backend/data_to_wordScript.sml" "config" *)
Record config : Type := {
  tag_bits : N;
  len_bits : N;
  pad_bits : N;
  len_size : N;
  has_div : bool;
  has_longdiv : bool;
  has_fp_ops : bool;
  has_fp_tern : bool;
  be : bool;
  call_empty_ffi : bool;
  gc_kind : gc_kind_ty
}.

(*! HOL "cakeml/compiler/backend/data_to_wordScript.sml" "small_shift_length_def" *)
Definition small_shift_length (conf : config) : N :=
  len_bits conf + tag_bits conf + 1.

(*! HOL "cakeml/compiler/backend/data_to_wordScript.sml" "shift_length_def" *)
Definition shift_length (conf : config) : N :=
  1 + pad_bits conf + len_bits conf + tag_bits conf + 1.

(** HOL [max_heap_limit (:'a) c]; HOL's [shift (:'a)] is [word_shift a]. *)
(*! HOL "cakeml/compiler/backend/data_to_wordScript.sml" "max_heap_limit_def" *)
Definition max_heap_limit (a : N) (c : config) : N :=
  MIN (dimword a DIV 2 ** shift_length c) (dimword a DIV 2 ** (word_shift a + 1)).

Section GenSize.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/data_to_wordScript.sml" "get_gen_size_def" *)
Definition get_gen_size (l : list N) : word a :=
  match l with
  | [] => bytes_in_word * (- n2w 1)
  | x :: xs =>
      if w2n (bytes_in_word : word a) * x <? dimword a
      then bytes_in_word * n2w x
      else bytes_in_word * (- n2w 1)
  end.

End GenSize.
