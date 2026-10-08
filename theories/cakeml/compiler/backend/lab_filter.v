(** * CakeML [lab_filter]: removing [Skip] instructions from labLang

    Port of [cakeml/compiler/backend/lab_filterScript.sml]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import labLang.
Open Scope N_scope.

Section LabFilter.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/lab_filterScript.sml" "not_skip_def" *)
Definition not_skip (l : line a) : bool :=
  match l with Asm (Asmi (Inst asm.Skip)) _ _ => false | _ => true end.

(*! HOL "cakeml/compiler/backend/lab_filterScript.sml" "filter_skip_def" *)
Fixpoint filter_skip (l : list (sec a)) : list (sec a) :=
  match l with
  | [] => []
  | Section_ n xs :: rest => Section_ n (FILTER not_skip xs) :: filter_skip rest
  end.

(*! HOL "cakeml/compiler/backend/lab_filterScript.sml" "filter_skip_MAP" *)
Theorem filter_skip_MAP : forall ls,
  filter_skip ls = MAP (fun x => match x with Section_ n xs => Section_ n (FILTER not_skip xs) end) ls.
Proof. induction ls as [|[n xs] ls IH]; cbn; [reflexivity|]; rewrite IH; reflexivity. Qed.

End LabFilter.
