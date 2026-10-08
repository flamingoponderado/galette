(** * HOL4 [lprefix_lub]: least upper bounds of chains of lazy lists

    Used by CakeML's observational semantics: a diverging program's I/O
    trace is the least upper bound of the traces of its clocked runs.
    Only the definitions used by the semantics are ported so far. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coalgebras Require Import llist.
Open Scope N_scope.

Section Defs.
Context {A : Type} `{EqDecision A} `{Inhabited A}.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_def" *)
Definition lprefix_chain (ls : llist A -> Prop) : Prop :=
  forall ll1 ll2, ll1 IN ls /\ ll2 IN ls -> LPREFIX ll1 ll2 \/ LPREFIX ll2 ll1.

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_chain_nth_def" *)
Definition lprefix_chain_nth (n : N) (ls : llist A -> Prop) : option A :=
  some (fun x => exists l, l IN ls /\ LNTH n l = SOME x).

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "lprefix_lub_def" *)
Definition lprefix_lub (ls : llist A -> Prop) (lub : llist A) : Prop :=
  (forall ll, ll IN ls -> LPREFIX ll lub) /\
  (forall ub, (forall ll, ll IN ls -> LPREFIX ll ub) -> LPREFIX lub ub).

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_f_def" *)
Definition build_lprefix_lub_f (ls : llist A -> Prop) (n : N) : option (N * A) :=
  OPTION_MAP (fun x => (n + 1, x)) (lprefix_chain_nth n ls).

(*! HOL "HOL/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml" "build_lprefix_lub_def" *)
Definition build_lprefix_lub (ls : llist A -> Prop) : llist A :=
  LUNFOLD (build_lprefix_lub_f ls) 0.

End Defs.
