(** * Pancake [loop_live]: liveness analysis for loopLang

    Port of [cakeml/pancake/loop_liveScript.sml].

    [shrink] and [fixedpoint] are mutually recursive in HOL, terminating by
    a lexicographic measure (program size, then [size live_in - size l1]).
    Here [shrink] is a structural [Fixpoint] on the program; the fixpoint
    iteration of a [Loop] body is [fixedpoint_f], which runs on a fuel of
    [size live_in - size l1 + 1] iterations (always sufficient, since each
    continuing iteration strictly grows [size l1] within [size live_in]).
    HOL's equations, including the one for [fixedpoint], are the tagged
    [shrink_def] theorem.  [vars_of_exp_list] is the nested [fix] of
    [vars_of_exp] and the top-level [vars_of_exp_list]; HOL's equations are
    [vars_of_exp_def].

    [oEL] ([listScript]) and [list_delete] ([backend_commonScript]) are
    Galette-local copies until those are ported.

    Not ported: [exp_ind] (a specialisation of HOL's generated induction
    theorem). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.pancake Require Import loopLang.
From Galette.cakeml.pancake Require loop_call.
Open Scope N_scope.

(** HOL [oEL] (from [listScript]; Galette-local until ported there). *)
#[local] Fixpoint oEL {A} (n : N) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if decide (n = 0) then Some x else oEL (n - 1) xs
  end.

(** HOL [list_delete] (from [backend_commonScript]; Galette-local until
    that script is ported). *)
#[local] Fixpoint list_delete {A} (l : list N) (s : spt A) : spt A :=
  match l with
  | [] => s
  | v :: vs => list_delete vs (delete v s)
  end.

Section Defs.
Context {a : N}.

Fixpoint vars_of_exp (e : exp a) (l : num_set) : num_set :=
  match e with
  | Var v => insert v tt l
  | Const _ => l
  | BaseAddr => l
  | TopAddr => l
  | Lookup _ => l
  | Load a => vars_of_exp a l
  | Op x vs =>
      (fix vars_of_exp_list (xs : list (exp a)) (l : num_set) : num_set :=
         match xs with
         | [] => l
         | x :: xs => vars_of_exp x (vars_of_exp_list xs l)
         end) vs l
  | Shift _ x y => vars_of_exp x (vars_of_exp y l)
  end.

Fixpoint vars_of_exp_list (xs : list (exp a)) (l : num_set) : num_set :=
  match xs with
  | [] => l
  | x :: xs => vars_of_exp x (vars_of_exp_list xs l)
  end.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "vars_of_exp_def" *)
Theorem vars_of_exp_def :
  (forall v l, vars_of_exp (Var v) l = insert v tt l) /\
  (forall w l, vars_of_exp (Const w) l = l) /\
  (forall l, vars_of_exp BaseAddr l = l) /\
  (forall l, vars_of_exp TopAddr l = l) /\
  (forall w l, vars_of_exp (Lookup w) l = l) /\
  (forall e l, vars_of_exp (Load e) l = vars_of_exp e l) /\
  (forall x vs l, vars_of_exp (Op x vs) l = vars_of_exp_list vs l) /\
  (forall s x y l, vars_of_exp (Shift s x y) l = vars_of_exp x (vars_of_exp y l)) /\
  (forall xs l, vars_of_exp_list xs l =
     match xs with [] => l | x :: xs => vars_of_exp x (vars_of_exp_list xs l) end).
Proof.
  repeat split; try (intros; reflexivity).
  intros [|x xs] l; reflexivity.
Qed.

End Defs.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "size_mk_BN" *)
Theorem size_mk_BN : forall {A} (t1 t2 : spt A), size (mk_BN t1 t2) = size (BN t1 t2).
Proof. intros A [] []; reflexivity. Qed.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "size_mk_BS" *)
Theorem size_mk_BS : forall {A} (t1 t2 : spt A) x, size (mk_BS t1 x t2) = size (BS t1 x t2).
Proof. intros A [] [] x; reflexivity. Qed.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "size_inter" *)
Theorem size_inter : forall {A B} (l1 : spt A) (l2 : spt B), size (inter l1 l2) <= size l1.
Proof.
  intros A B l1; induction l1 as [|x|t1 IH1 t2 IH2|t1 IH1 x t2 IH2]; intros [|y|u1 u2|u1 y u2];
    cbn [inter size]; rewrite ?size_mk_BN, ?size_mk_BS; cbn [size];
    try (specialize (IH1 u1); specialize (IH2 u2)); lia.
Qed.

Lemma inter_inter_same {A B} : forall (t : spt A) (u : spt B), inter t (inter t u) = inter t u.
Proof.
  induction t as [|x|t1 IH1 t2 IH2|t1 IH1 x t2 IH2]; intros [|y|u1 u2|u1 y u2]; cbn [inter];
    try reflexivity;
    unfold mk_BN, mk_BS;
    destruct (inter t1 u1) eqn:E1, (inter t2 u2) eqn:E2; cbn [inter];
    rewrite <- ?E1, <- ?E2, ?IH1, ?IH2; rewrite ?E1, ?E2; reflexivity.
Qed.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "arith_vars" *)
Definition arith_vars (ar : loop_arith) (l : num_set) : num_set :=
  match ar with
  | LLongMul r1 r2 r3 r4 => insert r3 tt (insert r4 tt (delete r1 (delete r2 l)))
  | LDiv r1 r2 r3 => insert r2 tt (insert r3 tt (delete r1 l))
  | LLongDiv r1 r2 r3 r4 r5 =>
      insert r3 tt (insert r4 tt (insert r5 tt (delete r1 (delete r2 l))))
  end.

Section Shrink.
Context {a : N}.

(** The [Loop] fixpoint iteration of [shrink], on the shrinking function
    [shr lt l = shrink lt body l] of the loop body, with fuel. *)
Fixpoint fixedpoint_f (shr : list (num_set * num_set) -> num_set -> prog a * num_set)
    (fuel : nat) (lt : list (num_set * num_set)) (live_in l1 l2 : num_set)
    : option (prog a * num_set) :=
  match fuel with
  | O => None
  | S fuel =>
      let (b, l0) := shr ((inter live_in l1, l2) :: lt) l2 in
      let l0' := inter live_in l0 in
      if decide (l0' = l1) then Some (b, l0) else
      if decide (size l0' <= size l1) then None else
      fixedpoint_f shr fuel lt live_in l0' l2
  end.

(** Sufficient fuel for [fixedpoint_f]. *)
Definition fixedpoint_fuel (live_in l1 : num_set) : nat :=
  S (N.to_nat (size live_in - size l1)).

Fixpoint shrink (lt : list (num_set * num_set)) (prog : prog a) (l : num_set)
    : loopLang.prog a * num_set :=
  match prog with
  | Seq p1 p2 =>
      let (p2, l) := shrink lt p2 l in
      let (p1, l) := shrink lt p1 l in
      (Seq p1 p2, l)
  | Loop live_in body live_out =>
      let l2 := inter live_out l in
      let bex := union live_in l2 in
      match fixedpoint_f (fun lt l => shrink lt body l) (fixedpoint_fuel live_in LN)
              lt live_in LN bex with
      | Some (body, l0) => let l := inter live_in l0 in (Loop l body l2, l)
      | None => let (b, _) := shrink ((live_in, l2) :: lt) body bex in
                (Loop live_in b l2, live_in)
      end
  | If x1 x2 x3 p1 p2 l1 =>
      let l := inter l l1 in
      let (p1, l1) := shrink lt p1 l in
      let (p2, l2) := shrink lt p2 l in
      let l3 := match x3 with Reg r => insert r tt LN | _ => LN end in
      (If x1 x2 x3 p1 p2 l, insert x2 tt (union l3 (union l1 l2)))
  | Mark p1 => shrink lt p1 l
  | Break n => (Break n, match oEL n lt with Some (_, brk) => brk | None => LN end)
  | Continue n => (Continue n, match oEL n lt with Some (cont, _) => cont | None => LN end)
  | Fail => (Fail, LN)
  | Skip => (Skip, l)
  | Return vs => (Return vs, list_insert vs LN)
  | Raise v => (Raise v, insert v tt LN)
  | Arith arith => (Arith arith, arith_vars arith l)
  | Primitive lhss pop rhss =>
      (Primitive lhss pop rhss, list_insert rhss (list_delete lhss l))
  | LocValue n m =>
      match lookup n l with
      | None => (Skip, l)
      | Some _ => (LocValue n m, delete n l)
      end
  | Assign n x =>
      match lookup n l with
      | None => (Skip, l)
      | Some _ => (Assign n x, vars_of_exp x (delete n l))
      end
  | ShMem op r ad => (ShMem op r ad, vars_of_exp ad (insert r tt l))
  | Store e n => (Store e n, vars_of_exp e (insert n tt l))
  | SetGlobal name e => (SetGlobal name e, vars_of_exp e l)
  | Call ret dest args handler =>
      let a0 := fromAList (MAP (fun x => (x, tt)) args) in
      match ret with
      | None => (Call None dest args None, union a0 l)
      | Some (ns, l1) =>
          match handler with
          | None => let l3 := list_delete ns (inter l l1) in
                    (Call (Some (ns, l3)) dest args None, union a0 l3)
          | Some (e, (h, (r, live_out))) =>
              let (r, l2) := shrink lt r l in
              let (h, l3) := shrink lt h l in
              let l1 := inter l1 (union (list_delete ns l2) (delete e l3)) in
              (Call (Some (ns, l1)) dest args (Some (e, (h, (r, inter l live_out)))),
               union a0 l1)
          end
      end
  | FFI n r1 r2 r3 r4 l1 =>
      (FFI n r1 r2 r3 r4 (inter l1 l),
       insert r1 tt (insert r2 tt (insert r3 tt (insert r4 tt (inter l1 l)))))
  | Load32 x y => (Load32 x y, insert x tt (delete y l))
  | LoadByte x y => (LoadByte x y, insert x tt (delete y l))
  | Store32 x y => (Store32 x y, insert x tt (insert y tt l))
  | StoreByte x y => (StoreByte x y, insert x tt (insert y tt l))
  | prog => (prog, l)
  end.

Definition fixedpoint (lt : list (num_set * num_set)) (live_in l1 l2 : num_set)
    (body : prog a) : option (prog a * num_set) :=
  fixedpoint_f (fun lt l => shrink lt body l) (fixedpoint_fuel live_in l1) lt live_in l1 l2.

Lemma fixedpoint_f_fuel shr : forall f1 f2 lt live_in l1 l2,
  (N.to_nat (size live_in - size l1) < f1)%nat ->
  (N.to_nat (size live_in - size l1) < f2)%nat ->
  fixedpoint_f shr f1 lt live_in l1 l2 = fixedpoint_f shr f2 lt live_in l1 l2.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] lt live_in l1 l2 H1 H2; try lia.
  cbn [fixedpoint_f]; destruct (shr _ l2) as [b l0].
  destruct (decide (inter live_in l0 = l1)) as [|Hne]; [reflexivity|].
  destruct (decide (size (inter live_in l0) <= size l1)) as [|Hlt]; [reflexivity|].
  pose proof (size_inter live_in l0).
  apply IH; lia.
Qed.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "shrink_def" *)
Theorem shrink_def :
  (forall lt p1 p2 l, shrink lt (Seq p1 p2) l =
     let (p2, l) := shrink lt p2 l in
     let (p1, l) := shrink lt p1 l in
     (Seq p1 p2, l)) /\
  (forall lt live_in body live_out l, shrink lt (Loop live_in body live_out) l =
     let l2 := inter live_out l in
     let bex := union live_in l2 in
     match fixedpoint lt live_in LN bex body with
     | Some (body, l0) => let l := inter live_in l0 in (Loop l body l2, l)
     | None => let (b, _) := shrink ((live_in, l2) :: lt) body bex in
               (Loop live_in b l2, live_in)
     end) /\
  (forall lt x1 x2 x3 p1 p2 l1 l, shrink lt (If x1 x2 x3 p1 p2 l1) l =
     let l := inter l l1 in
     let (p1, l1) := shrink lt p1 l in
     let (p2, l2) := shrink lt p2 l in
     let l3 := match x3 with Reg r => insert r tt LN | _ => LN end in
     (If x1 x2 x3 p1 p2 l, insert x2 tt (union l3 (union l1 l2)))) /\
  (forall lt p1 l, shrink lt (Mark p1) l = shrink lt p1 l) /\
  (forall lt n l, shrink lt (Break n) l =
     (Break n, match oEL n lt with Some (_, brk) => brk | None => LN end)) /\
  (forall lt n l, shrink lt (Continue n) l =
     (Continue n, match oEL n lt with Some (cont, _) => cont | None => LN end)) /\
  (forall lt l, shrink lt Fail l = (Fail, LN)) /\
  (forall lt l, shrink lt Skip l = (Skip, l)) /\
  (forall lt vs l, shrink lt (Return vs) l = (Return vs, list_insert vs LN)) /\
  (forall lt v l, shrink lt (Raise v) l = (Raise v, insert v tt LN)) /\
  (forall lt arith l, shrink lt (Arith arith) l = (Arith arith, arith_vars arith l)) /\
  (forall b lhss pop rhss l, shrink b (Primitive lhss pop rhss) l =
     (Primitive lhss pop rhss, list_insert rhss (list_delete lhss l))) /\
  (forall lt n m l, shrink lt (LocValue n m) l =
     match lookup n l with
     | None => (Skip, l)
     | Some _ => (LocValue n m, delete n l)
     end) /\
  (forall lt n x l, shrink lt (Assign n x) l =
     match lookup n l with
     | None => (Skip, l)
     | Some _ => (Assign n x, vars_of_exp x (delete n l))
     end) /\
  (forall lt op r ad l, shrink lt (ShMem op r ad) l =
     (ShMem op r ad, vars_of_exp ad (insert r tt l))) /\
  (forall lt e n l, shrink lt (Store e n) l = (Store e n, vars_of_exp e (insert n tt l))) /\
  (forall lt name e l, shrink lt (SetGlobal name e) l = (SetGlobal name e, vars_of_exp e l)) /\
  (forall lt ret dest args handler l, shrink lt (Call ret dest args handler) l =
     let a0 := fromAList (MAP (fun x => (x, tt)) args) in
     match ret with
     | None => (Call None dest args None, union a0 l)
     | Some (ns, l1) =>
         match handler with
         | None => let l3 := list_delete ns (inter l l1) in
                   (Call (Some (ns, l3)) dest args None, union a0 l3)
         | Some (e, (h, (r, live_out))) =>
             let (r, l2) := shrink lt r l in
             let (h, l3) := shrink lt h l in
             let l1 := inter l1 (union (list_delete ns l2) (delete e l3)) in
             (Call (Some (ns, l1)) dest args (Some (e, (h, (r, inter l live_out)))),
              union a0 l1)
         end
     end) /\
  (forall lt n r1 r2 r3 r4 l1 l, shrink lt (FFI n r1 r2 r3 r4 l1) l =
     (FFI n r1 r2 r3 r4 (inter l1 l),
      insert r1 tt (insert r2 tt (insert r3 tt (insert r4 tt (inter l1 l)))))) /\
  (forall lt x y l, shrink lt (Load32 x y) l = (Load32 x y, insert x tt (delete y l))) /\
  (forall lt x y l, shrink lt (LoadByte x y) l = (LoadByte x y, insert x tt (delete y l))) /\
  (forall lt x y l, shrink lt (Store32 x y) l = (Store32 x y, insert x tt (insert y tt l))) /\
  (forall lt x y l, shrink lt (StoreByte x y) l = (StoreByte x y, insert x tt (insert y tt l))) /\
  (forall lt l, shrink lt Tick l = (Tick, l)) /\
  (forall lt live_in l1 l2 (body : loopLang.prog a), fixedpoint lt live_in l1 l2 body =
     let (b, l0) := shrink ((inter live_in l1, l2) :: lt) body l2 in
     let l0' := inter live_in l0 in
     if decide (l0' = l1) then Some (b, l0) else
     if decide (size l0' <= size l1) then None else
     fixedpoint lt live_in l0' l2 body).
Proof.
  repeat split; try reflexivity.
  intros lt live_in l1 l2 body; unfold fixedpoint at 1, fixedpoint_fuel at 1.
  cbn [fixedpoint_f]; destruct (shrink _ body l2) as [b l0].
  destruct (decide (inter live_in l0 = l1)) as [|Hne]; [reflexivity|].
  destruct (decide (size (inter live_in l0) <= size l1)) as [|Hlt]; [reflexivity|].
  pose proof (size_inter live_in l0).
  unfold fixedpoint, fixedpoint_fuel; apply fixedpoint_f_fuel; lia.
Qed.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "fixedpoint_thm" *)
Theorem fixedpoint_thm : forall lt live_in l1 l2 (body : loopLang.prog a) l0 b,
  fixedpoint lt live_in l1 l2 body = Some (b, l0) ->
  shrink ((inter live_in l0, l2) :: lt) body l2 = (b, l0).
Proof.
  intros lt live_in l1 l2 body; unfold fixedpoint.
  generalize (fixedpoint_fuel live_in l1) as f; intros f; revert l1.
  induction f as [|f IH]; intros l1 l0 b; cbn [fixedpoint_f]; [discriminate|].
  destruct (shrink _ body l2) as [b' l0'] eqn:E.
  destruct (decide (inter live_in l0' = l1)) as [<-|Hne].
  - intros H; injection H as <- <-.
    rewrite inter_inter_same in E; exact E.
  - destruct (decide (size (inter live_in l0') <= size l1)); [discriminate|].
    apply IH.
Qed.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "mark_all_def" *)
Fixpoint mark_all (prog : prog a) : loopLang.prog a * bool :=
  match prog with
  | Seq p1 p2 =>
      let (p1, t1) := mark_all p1 in
      let (p2, t2) := mark_all p2 in
      let t3 := t1 && t2 in
      (if t3 then Mark (Seq p1 p2) else Seq p1 p2, t3)
  | Loop l1 body l2 =>
      let (body, t1) := mark_all body in
      (Loop l1 body l2, false)
  | If x1 x2 x3 p1 p2 l1 =>
      let (p1, t1) := mark_all p1 in
      let (p2, t2) := mark_all p2 in
      let p3 := If x1 x2 x3 p1 p2 l1 in
      let t3 := t1 && t2 in
      (if t3 then Mark p3 else p3, t3)
  | Mark p1 => mark_all p1
  | Call ret dest args handler =>
      match handler with
      | None => (Mark (Call ret dest args handler), true)
      | Some (ns, (p1, (p2, l))) =>
          let (p1, t1) := mark_all p1 in
          let (p2, t2) := mark_all p2 in
          let t3 := t1 && t2 in
          let p3 := Call ret dest args (Some (ns, (p1, (p2, l)))) in
          (if t3 then Mark p3 else p3, t3)
      end
  | prog => (Mark prog, true)
  end.

(*! HOL "cakeml/pancake/loop_liveScript.sml" "comp_def" *)
Definition comp (prog : prog a) : loopLang.prog a :=
  FST (mark_all (FST (shrink [] prog LN))).

(*! HOL "cakeml/pancake/loop_liveScript.sml" "optimise_def" *)
Definition optimise (prog : prog a) : loopLang.prog a :=
  (comp ∘ FST ∘ loop_call.comp LN) prog.

End Shrink.
