(** * CakeML [word_unreach]: removal of trivially unreachable code

    Port of [cakeml/compiler/backend/word_unreachScript.sml].  HOL tuples
    nest to the right ([dest_Seq_Move] returns [(n, (l, rest))]).
    [SimpSeq]'s HOL tests [p2 = Skip] / [rest = Skip] are pattern matches
    here (same value). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require Import wordLang.
Open Scope N_scope.

Section Unreach.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/word_unreachScript.sml" "dest_Seq_Move_def" *)
Definition dest_Seq_Move (p : prog a) : option (N * (list (N * N) * prog a)) :=
  match p with
  | Move n l => Some (n, (l, Skip))
  | Seq (Move n l) rest => Some (n, (l, rest))
  | _ => None
  end.

(*! HOL "cakeml/compiler/backend/word_unreachScript.sml" "merge_moves_def" *)
Definition merge_moves (l1 l2 : list (N * N)) : list (N * N) :=
  let l2' := MAP (fun '(x, y) => match ALOOKUP l1 y with
                                 | None => (x, y)
                                 | Some v => (x, v)
                                 end) l2 in
  anub (l2' ++ l1) [].

(*! HOL "cakeml/compiler/backend/word_unreachScript.sml" "SimpSeq_def" *)
Definition SimpSeq (p1 p2 : prog a) : prog a :=
  let default := Seq p1 p2 in
  match p2 with
  | Skip => p1
  | _ =>
      match p1 with
      | Skip => p2
      | Raise _ => p1
      | Return _ _ => p1
      | Break _ => p1
      | Continue _ => p1
      | Move n1 l1 =>
          match dest_Seq_Move p2 with
          | None => default
          | Some (n2, (l2, rest)) =>
              let l := merge_moves l1 l2 in
              match rest with
              | Skip => Move (MAX n1 n2) l
              | _ => Seq (Move (MAX n1 n2) l) rest
              end
          end
      | _ => default
      end
  end.

(*! HOL "cakeml/compiler/backend/word_unreachScript.sml" "Seq_assoc_right_def" *)
Fixpoint Seq_assoc_right (p : prog a) (acc : prog a) : prog a :=
  match p with
  | Skip => acc
  | Seq q1 q2 => Seq_assoc_right q1 (Seq_assoc_right q2 acc)
  | If v n r q1 q2 =>
      SimpSeq (If v n r (Seq_assoc_right q1 Skip) (Seq_assoc_right q2 Skip)) acc
  | MustTerminate q => SimpSeq (MustTerminate (Seq_assoc_right q Skip)) acc
  | Call ret_prog dest args handler =>
      match ret_prog with
      | None => Call ret_prog dest args handler
      | Some (x1, (x2, (q1, (x3, x4)))) =>
          SimpSeq (Call (Some (x1, (x2, (Seq_assoc_right q1 Skip, (x3, x4)))))
                        dest args
                        (match handler with
                         | None => None
                         | Some (y1, (q2, (y2, y3))) => Some (y1, (Seq_assoc_right q2 Skip, (y2, y3)))
                         end)) acc
      end
  | Loop names body exit_names => SimpSeq (Loop names (Seq_assoc_right body Skip) exit_names) acc
  | p1 => SimpSeq p1 acc
  end.

(*! HOL "cakeml/compiler/backend/word_unreachScript.sml" "remove_unreach_def" *)
Definition remove_unreach (e : prog a) : prog a := Seq_assoc_right e Skip.

End Unreach.

(*! HOL "cakeml/compiler/backend/word_unreachScript.sml" "remove_unreach_test" *)
Theorem remove_unreach_test :
  remove_unreach (Seq (Move 1 [(1, 11); (2, 22); (3, 33)]) (Move 1 [(3, 1); (2, 99)]) : prog 64)
  = Move 1 [(3, 11); (2, 99); (1, 11)].
Proof. reflexivity. Qed.
