(** * CakeML [word_remove]: removal of [MustTerminate]

    Port of [cakeml/compiler/backend/word_removeScript.sml].  The [_pmatch]
    theorem is not ported. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import wordLang.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/word_removeScript.sml" "remove_must_terminate_def" *)
Fixpoint remove_must_terminate {a : N} (p : prog a) : prog a :=
  match p with
  | Seq p0 p1 => Seq (remove_must_terminate p0) (remove_must_terminate p1)
  | If cmp r1 ri e2 e3 => If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)
  | MustTerminate p => remove_must_terminate p
  | Call ret dest args h =>
      let ret := match ret with
                 | None => None
                 | Some (v, (cutset, (ret_handler, (l1, l2)))) =>
                     Some (v, (cutset, (remove_must_terminate ret_handler, (l1, l2))))
                 end in
      let h := match h with
               | None => None
               | Some (v, (prog, (l1, l2))) => Some (v, (remove_must_terminate prog, (l1, l2)))
               end in
      Call ret dest args h
  | Loop names body exit_names => Loop names (remove_must_terminate body) exit_names
  | prog => prog
  end.
