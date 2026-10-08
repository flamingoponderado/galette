(** * CakeML [word_depth]: call graphs and maximal stack depth

    Port of [cakeml/compiler/backend/word_depthScript.sml].

    The constructors [Const] and [Call] of [call_tree] shadow wordLang's
    [exp]/[prog] constructors of the same names; wordLang's are written
    [wordLang.Call] here.

    HOL defines [call_graph] by well-founded recursion on the
    lexicographic measure [(size funs, total - LENGTH ns, prog_size p)].
    Here the first two components are explicit fuel arguments ([cg]),
    started at exactly these values by [call_graph]; with this invariant
    the fuel never runs out, and [call_graph_eqns] proves HOL's clauses
    (the catch-all clause for each remaining constructor).  [call_graph]
    is therefore not tagged. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import wordLang.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/word_depthScript.sml" "call_tree" *)
Inductive call_tree : Type :=
| Leaf : call_tree
| Unknown : call_tree
| Const : N -> call_tree -> call_tree
| Call : N -> call_tree -> call_tree
| Branch : call_tree -> call_tree -> call_tree.

#[global] Instance call_tree_eq_dec : EqDecision call_tree.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance call_tree_inhabited : Inhabited call_tree := Leaf.

(*! HOL "cakeml/compiler/backend/word_depthScript.sml" "max_depth_def" *)
Fixpoint max_depth (frame_sizes : num_map N) (t : call_tree) : option N :=
  match t with
  | Leaf => Some 0
  | Unknown => None
  | Const n t => OPTION_MAP (N.add n) (max_depth frame_sizes t)
  | Branch t1 t2 => OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes t2)
  | Call n t => OPTION_MAP2 N.add (lookup n frame_sizes) (max_depth frame_sizes t)
  end.

(*! HOL "cakeml/compiler/backend/word_depthScript.sml" "mk_Branch_def" *)
Definition mk_Branch (t1 t2 : call_tree) : call_tree :=
  if decide (t1 = t2) then t1 else
  if decide (t1 = Leaf) then t2 else
  if decide (t2 = Leaf) then t1 else
  if decide (t1 = Unknown) then t1 else
  if decide (t2 = Unknown) then t2 else
  Branch t1 t2.

Section CallGraph.
Context {a : N}.

(** [cg f1 funs n ns total p] with [f1 = size funs]; the inner fuel [f2] is
    [total - LENGTH ns]. *)
Fixpoint cg (f1 : nat) (funs : num_map (N * prog a)) (n : N) (ns : list N) (total : N)
    (p : prog a) {struct f1} : call_tree :=
  let fix cg2 (f2 : nat) (n : N) (ns : list N) (p : prog a) {struct f2} : call_tree :=
    let fix cg3 (p : prog a) {struct p} : call_tree :=
      match p with
      | Seq p1 p2 => mk_Branch (cg3 p1) (cg3 p2)
      | If _ _ _ p1 p2 => mk_Branch (cg3 p1) (cg3 p2)
      | wordLang.Call ret dest args handler =>
          match dest with
          | None => Unknown
          | Some d =>
              if MEM d ns && match ret with None => true | Some _ => false end then Leaf else
              match lookup d funs with
              | None => Unknown
              | Some (_, body) =>
                  match ret with
                  | None =>
                      if LENGTH ns <? total then
                        mk_Branch (Call d Leaf)
                          (match f2 with O => Leaf | S f2' => cg2 f2' d (d :: ns) body end)
                      else Leaf
                  | Some (_, (_, (ret_prog, (_, _)))) =>
                      let new_funs := delete d funs in
                      let body_graph :=
                        match f1 with
                        | O => Leaf
                        | S f1' => cg f1' new_funs d [d] total body
                        end in
                      match handler with
                      | None =>
                          Branch (Call n (Call d Leaf))
                            (mk_Branch (Call n body_graph) (cg3 ret_prog))
                      | Some (_, (p, (_, _))) =>
                          Branch (Call n (Const 3 (Call d Leaf)))
                            (mk_Branch (Call n (Const 3 body_graph))
                               (mk_Branch (cg3 p) (cg3 ret_prog)))
                      end
                  end
              end
          end
      | MustTerminate p => cg3 p
      | Alloc _ _ => Call n Leaf
      | Install _ _ _ _ _ => Unknown
      | Loop _ body _ => cg3 body
      | _ => Leaf
      end in
    cg3 p in
  cg2 (N.to_nat (total - LENGTH ns)) n ns p.

(** HOL [call_graph]; see the file header. *)
Definition call_graph (funs : num_map (N * prog a)) (n : N) (ns : list N) (total : N)
    (p : prog a) : call_tree :=
  cg (N.to_nat (size funs)) funs n ns total p.

Lemma call_graph_eqns :
  (forall funs n ns total p1 p2,
     call_graph funs n ns total (Seq p1 p2) =
     mk_Branch (call_graph funs n ns total p1) (call_graph funs n ns total p2)) /\
  (forall funs n ns total c r ri p1 p2,
     call_graph funs n ns total (If c r ri p1 p2) =
     mk_Branch (call_graph funs n ns total p1) (call_graph funs n ns total p2)) /\
  (forall funs n ns total ret dest args handler,
     call_graph funs n ns total (wordLang.Call ret dest args handler) =
     match dest with
     | None => Unknown
     | Some d =>
         if MEM d ns && match ret with None => true | Some _ => false end then Leaf else
         match lookup d funs with
         | None => Unknown
         | Some (_, body) =>
             match ret with
             | None =>
                 if LENGTH ns <? total then
                   mk_Branch (Call d Leaf) (call_graph funs d (d :: ns) total body)
                 else Leaf
             | Some (_, (_, (ret_prog, (_, _)))) =>
                 let new_funs := delete d funs in
                 match handler with
                 | None => Branch (Call n (Call d Leaf))
                     (mk_Branch (Call n (call_graph new_funs d [d] total body))
                                (call_graph funs n ns total ret_prog))
                 | Some (_, (p, (_, _))) => Branch (Call n (Const 3 (Call d Leaf)))
                     (mk_Branch (Call n (Const 3 (call_graph new_funs d [d] total body)))
                     (mk_Branch (call_graph funs n ns total p)
                                (call_graph funs n ns total ret_prog)))
                 end
             end
         end
     end) /\
  (forall funs n ns total p,
     call_graph funs n ns total (MustTerminate p) = call_graph funs n ns total p) /\
  (forall funs n ns total x y, call_graph funs n ns total (Alloc x y) = Call n Leaf) /\
  (forall funs n ns total x1 x2 x3 x4 x5,
     call_graph funs n ns total (Install x1 x2 x3 x4 x5) = Unknown) /\
  (forall funs n ns total x body y,
     call_graph funs n ns total (Loop x body y) = call_graph funs n ns total body) /\
  (forall funs n ns total p,
     match p with
     | Seq _ _ | If _ _ _ _ _ | wordLang.Call _ _ _ _ | MustTerminate _ | Alloc _ _
     | Install _ _ _ _ _ | Loop _ _ _ => True
     | _ => call_graph funs n ns total p = Leaf
     end).
Proof.
  unfold call_graph.
  repeat split; intros;
    try (destruct (N.to_nat (size funs)); cbn [cg];
         destruct (N.to_nat (total - LENGTH ns)); reflexivity).
  - (* Call *)
    destruct dest as [d|];
      [|destruct (N.to_nat (size funs)); cbn [cg];
        destruct (N.to_nat (total - LENGTH ns)); reflexivity].
    destruct (MEM d ns && match ret with None => true | Some _ => false end) eqn:M;
      [destruct (N.to_nat (size funs)); cbn [cg];
       destruct (N.to_nat (total - LENGTH ns)); cbn; rewrite M; reflexivity|].
    destruct (lookup d funs) as [[x body]|] eqn:L;
      [|destruct (N.to_nat (size funs)); cbn [cg];
        destruct (N.to_nat (total - LENGTH ns)); cbn; rewrite M, L; reflexivity].
    assert (S1 : (0 < size funs)%N) by (eapply lookup_size; exact L).
    assert (E : N.to_nat (size funs) = S (N.to_nat (size (delete d funs)))).
    { rewrite size_delete; destruct (decide (lookup d funs = None)); [congruence|lia]. }
    rewrite E; cbn [cg].
    destruct ret as [[? [? [ret_prog [? ?]]]]|].
    + destruct (N.to_nat (total - LENGTH ns)); cbn; rewrite M, L;
        destruct handler as [[? [? [? ?]]]|]; reflexivity.
    + destruct (N.ltb_spec (LENGTH ns) total) as [H|H].
      * assert (E2 : N.to_nat (total - LENGTH ns) = S (N.to_nat (total - LENGTH (d :: ns)))).
        { cbn [LENGTH]; lia. }
        rewrite E2; cbn; rewrite M, L.
        destruct (N.ltb_spec (LENGTH ns) total); [reflexivity|lia].
      * destruct (N.to_nat (total - LENGTH ns)); cbn; rewrite M, L;
          (destruct (N.ltb_spec (LENGTH ns) total); [lia|reflexivity]).
  - destruct p; try exact I; destruct (N.to_nat (size funs)); cbn [cg];
      destruct (N.to_nat (total - LENGTH ns)); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/word_depthScript.sml" "full_call_graph_def" *)
Definition full_call_graph (n : N) (funs : num_map (N * prog a)) : call_tree :=
  match lookup n funs with
  | None => Unknown
  | Some (a0, prog) => Branch (Call n Leaf) (call_graph funs n [n] (size funs) prog)
  end.

(*! HOL "cakeml/compiler/backend/word_depthScript.sml" "max_depth_graphs_def" *)
Fixpoint max_depth_graphs (ss : num_map N) (l : list N) (all : list N)
    (funs : num_map (N * prog a)) (all_funs : num_map (N * prog a)) : option N :=
  match l with
  | [] => Some 0
  | n :: ns =>
      match lookup n all_funs with
      | None => None
      | Some (a0, body) =>
          OPTION_MAP2 MAX (lookup n ss)
            (OPTION_MAP2 MAX (max_depth ss (call_graph funs n all (size all_funs) body))
                             (max_depth_graphs ss ns all funs all_funs))
      end
  end.

End CallGraph.
