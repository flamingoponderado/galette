(** * HOL4 [sptree]: sparse trees indexed by natural numbers

    A log-time random-access, extensible, gappy array ([num_map]).  Every
    executable definition follows HOL's equations constructor for
    constructor: the order of the lists produced by [toAList], [toList],
    [foldi], [spt_fold] and [toSortedAList] is observable in the compiler's
    output.

    HOL defines [lookup]/[delete] by recursion that is structural on the
    tree; they are [Fixpoint]s here with exactly HOL's clauses.  [insert],
    [lrnext] and [spt_acc] recurse on a number ([k] becomes [(k - 1) DIV 2]);
    they recurse structurally on the binary digits of the [positive] [k + 1],
    which is exactly HOL's (logarithmic) recursion, and HOL's defining
    equations are proved as theorems carrying the [_def] tags.
    [spts_to_alist] recurses on a measure; it uses a fuel argument that
    provably never runs out ([spts_to_alist_def] is HOL's equation).

    HOL's [pred_set] and [alist] theories are not ported yet: HOL sets
    (['a set]) are Rocq predicates [N -> Prop] and set operations are
    written out ([s UNION t] is [fun x => s x \/ t x], [IMAGE f s] is
    [fun y => exists x, y = f x /\ s x], ...), and [ALOOKUP] is defined
    locally (untagged) until [alistScript] is ported. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import alist.
Open Scope N_scope.



(** ** The datatype *)

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt" *)
Inductive spt (A : Type) : Type :=
| LN : spt A
| LS : A -> spt A
| BN : spt A -> spt A -> spt A
| BS : spt A -> A -> spt A -> spt A.
Arguments LN {A}.
Arguments LS {A} _.
Arguments BN {A} _ _.
Arguments BS {A} _ _ _.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "num_map" *)
Abbreviation num_map := spt.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "num_set" *)
Abbreviation num_set := (spt unit).

#[global] Instance spt_inhabited {A} : Inhabited (spt A) := LN.

#[global] Instance spt_eq_dec {A} `{EqDecision A} : EqDecision (spt A).
Proof.
  intros t1; induction t1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros [|b|u1 u2|u1 b u2];
    try (right; discriminate); try (left; reflexivity).
  - destruct (decide (a = b)) as [->|n]; [left; reflexivity|right; congruence].
  - destruct (IH1 u1) as [->|n]; [|right; congruence].
    destruct (IH2 u2) as [->|n]; [left; reflexivity|right; congruence].
  - destruct (IH1 u1) as [->|n]; [|right; congruence].
    destruct (decide (a = b)) as [->|n]; [|right; congruence].
    destruct (IH2 u2) as [->|n]; [left; reflexivity|right; congruence].
Defined.

(** HOL's generated size function (used in termination arguments). *)
(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_size_def" *)
Fixpoint spt_size {A} (f : A -> N) (t : spt A) : N :=
  match t with
  | LN => 0
  | LS a => 1 + f a
  | BN t1 t2 => 1 + (spt_size f t1 + spt_size f t2)
  | BS t1 a t2 => 1 + (spt_size f t1 + (f a + spt_size f t2))
  end.

(** HOL [isEmpty t] is [t = LN]. *)
(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "isEmpty" *)
Definition isEmpty {A} (t : spt A) : bool :=
  match t with LN => true | _ => false end.

(** ** Executable definitions *)

Section Defs.
Context {A : Type}.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_def" *)
Fixpoint wf (t : spt A) : bool :=
  match t with
  | LN => true
  | LS a => true
  | BN t1 t2 => wf t1 && (wf t2 && negb (isEmpty t1 && isEmpty t2))
  | BS t1 a t2 => wf t1 && (wf t2 && negb (isEmpty t1 && isEmpty t2))
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_def" *)
Fixpoint lookup (k : N) (t : spt A) : option A :=
  match t with
  | LN => None
  | LS a => if decide (k = 0) then Some a else None
  | BN t1 t2 =>
      if decide (k = 0) then None
      else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)
  | BS t1 a t2 =>
      if decide (k = 0) then Some a
      else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)
  end.

(** HOL's [insert] recurses on [(k - 1) DIV 2].  Writing [p = k + 1] (a
    [positive]), [k = 0] is [p = 1], an even [k <> 0] is [p = 2q + 1] and an
    odd [k] is [p = 2q], and in both cases [(k - 1) DIV 2 + 1 = q]; so
    [insert_pos (k + 1)] performs exactly HOL's recursion, structurally on the
    binary digits of [k + 1].  HOL's equations are [insert_def] below. *)
Fixpoint insert_pos (p : positive) (a : A) (t : spt A) : spt A :=
  match p with
  | xH =>
      match t with
      | LN => LS a
      | LS _ => LS a
      | BN t1 t2 => BS t1 a t2
      | BS t1 _ t2 => BS t1 a t2
      end
  | xI q =>
      match t with
      | LN => BN (insert_pos q a LN) LN
      | LS a' => BS (insert_pos q a LN) a' LN
      | BN t1 t2 => BN (insert_pos q a t1) t2
      | BS t1 a' t2 => BS (insert_pos q a t1) a' t2
      end
  | xO q =>
      match t with
      | LN => BN LN (insert_pos q a LN)
      | LS a' => BS LN a' (insert_pos q a LN)
      | BN t1 t2 => BN t1 (insert_pos q a t2)
      | BS t1 a' t2 => BS t1 a' (insert_pos q a t2)
      end
  end.

(** HOL [insert]; its defining equations are [insert_def] below. *)
Definition insert (k : N) (a : A) (t : spt A) : spt A := insert_pos (N.succ_pos k) a t.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mk_BN_def" *)
Definition mk_BN (t1 t2 : spt A) : spt A :=
  match t1, t2 with
  | LN, LN => LN
  | _, _ => BN t1 t2
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mk_BS_def" *)
Definition mk_BS (t1 : spt A) (x : A) (t2 : spt A) : spt A :=
  match t1, t2 with
  | LN, LN => LS x
  | _, _ => BS t1 x t2
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "delete_def" *)
Fixpoint delete (k : N) (t : spt A) : spt A :=
  match t with
  | LN => LN
  | LS a => if decide (k = 0) then LN else LS a
  | BN t1 t2 =>
      if decide (k = 0) then BN t1 t2
      else if EVEN k then mk_BN (delete ((k - 1) DIV 2) t1) t2
      else mk_BN t1 (delete ((k - 1) DIV 2) t2)
  | BS t1 a t2 =>
      if decide (k = 0) then BN t1 t2
      else if EVEN k then mk_BS (delete ((k - 1) DIV 2) t1) a t2
      else mk_BS t1 a (delete ((k - 1) DIV 2) t2)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "fromList_def" *)
Definition fromList (l : list A) : spt A :=
  snd (FOLDL (fun '(i, t) a => (i + 1, insert i a t)) (0, LN) l).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_def" *)
Fixpoint size (t : spt A) : N :=
  match t with
  | LN => 0
  | LS a => 1
  | BN t1 t2 => size t1 + size t2
  | BS t1 a t2 => size t1 + size t2 + 1
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_def" *)
Fixpoint union (t0 t : spt A) : spt A :=
  match t0 with
  | LN => t
  | LS a =>
      match t with
      | LN => LS a
      | LS b => LS a
      | BN t1 t2 => BS t1 a t2
      | BS t1 _ t2 => BS t1 a t2
      end
  | BN t1 t2 =>
      match t with
      | LN => BN t1 t2
      | LS a => BS t1 a t2
      | BN t1' t2' => BN (union t1 t1') (union t2 t2')
      | BS t1' a t2' => BS (union t1 t1') a (union t2 t2')
      end
  | BS t1 a t2 =>
      match t with
      | LN => BS t1 a t2
      | LS a' => BS t1 a t2
      | BN t1' t2' => BS (union t1 t1') a (union t2 t2')
      | BS t1' a' t2' => BS (union t1 t1') a (union t2 t2')
      end
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_def" *)
Fixpoint inter {B} (t0 : spt A) (t : spt B) : spt A :=
  match t0 with
  | LN => LN
  | LS a =>
      match t with
      | LN => LN
      | LS b => LS a
      | BN t1 t2 => LN
      | BS t1 _ t2 => LS a
      end
  | BN t1 t2 =>
      match t with
      | LN => LN
      | LS a => LN
      | BN t1' t2' => mk_BN (inter t1 t1') (inter t2 t2')
      | BS t1' a t2' => mk_BN (inter t1 t1') (inter t2 t2')
      end
  | BS t1 a t2 =>
      match t with
      | LN => LN
      | LS a' => LS a
      | BN t1' t2' => mk_BN (inter t1 t1') (inter t2 t2')
      | BS t1' a' t2' => mk_BS (inter t1 t1') a (inter t2 t2')
      end
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_eq_def" *)
Fixpoint inter_eq `{EqDecision A} (t0 t : spt A) : spt A :=
  match t0 with
  | LN => LN
  | LS a =>
      match t with
      | LN => LN
      | LS b => if decide (a = b) then LS a else LN
      | BN t1 t2 => LN
      | BS t1 b t2 => if decide (a = b) then LS a else LN
      end
  | BN t1 t2 =>
      match t with
      | LN => LN
      | LS a => LN
      | BN t1' t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
      | BS t1' a t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
      end
  | BS t1 a t2 =>
      match t with
      | LN => LN
      | LS a' => if decide (a' = a) then LS a else LN
      | BN t1' t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
      | BS t1' a' t2' =>
          if decide (a' = a) then mk_BS (inter_eq t1 t1') a (inter_eq t2 t2')
          else mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
      end
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "difference_def" *)
Fixpoint difference {B} (t0 : spt A) (t : spt B) : spt A :=
  match t0 with
  | LN => LN
  | LS a =>
      match t with
      | LN => LS a
      | LS b => LN
      | BN t1 t2 => LS a
      | BS t1 b t2 => LN
      end
  | BN t1 t2 =>
      match t with
      | LN => BN t1 t2
      | LS a => BN t1 t2
      | BN t1' t2' => mk_BN (difference t1 t1') (difference t2 t2')
      | BS t1' a t2' => mk_BN (difference t1 t1') (difference t2 t2')
      end
  | BS t1 a t2 =>
      match t with
      | LN => BS t1 a t2
      | LS a' => BN t1 t2
      | BN t1' t2' => mk_BS (difference t1 t1') a (difference t2 t2')
      | BS t1' a' t2' => mk_BN (difference t1 t1') (difference t2 t2')
      end
  end.

End Defs.

(** HOL [lrnext n = if n = 0 then 1 else 2 * lrnext ((n - 1) DIV 2)], by
    recursion on the binary digits of [n + 1] as for [insert]; HOL's equation
    is [lrnext_def] below. *)
Fixpoint lrnext_pos (p : positive) : N :=
  match p with
  | xH => 1
  | xI q => 2 * lrnext_pos q
  | xO q => 2 * lrnext_pos q
  end.

Definition lrnext (n : N) : N := lrnext_pos (N.succ_pos n).

Section Defs2.
Context {A : Type}.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_def" *)
Fixpoint domain (t : spt A) : N -> Prop :=
  match t with
  | LN => fun _ => False
  | LS _ => fun n => n = 0
  | BN t1 t2 => fun n =>
      (exists m, n = 2 * m + 2 /\ domain t1 m) \/
      (exists m, n = 2 * m + 1 /\ domain t2 m)
  | BS t1 _ t2 => fun n =>
      (n = 0 \/ (exists m, n = 2 * m + 2 /\ domain t1 m)) \/
      (exists m, n = 2 * m + 1 /\ domain t2 m)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "foldi_def" *)
Fixpoint foldi {B} (f : N -> A -> B -> B) (i : N) (acc : B) (t : spt A) : B :=
  match t with
  | LN => acc
  | LS a => f i a acc
  | BN t1 t2 =>
      let inc := lrnext i in
      foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2
  | BS t1 a t2 =>
      let inc := lrnext i in
      foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mapi0_def" *)
Fixpoint mapi0 {B} (f : N -> A -> B) (i : N) (t : spt A) : spt B :=
  match t with
  | LN => LN
  | LS a => LS (f i a)
  | BN t1 t2 =>
      let inc := lrnext i in
      mk_BN (mapi0 f (i + 2 * inc) t1) (mapi0 f (i + inc) t2)
  | BS t1 a t2 =>
      let inc := lrnext i in
      mk_BS (mapi0 f (i + 2 * inc) t1) (f i a) (mapi0 f (i + inc) t2)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mapi_def" *)
Definition mapi {B} (f : N -> A -> B) (pt : spt A) : spt B := mapi0 f 0 pt.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "toAList_def" *)
Definition toAList : spt A -> list (N * A) := foldi (fun k v a => (k, v) :: a) 0 [].

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "toListA_def" *)
Fixpoint toListA (acc : list A) (t : spt A) : list A :=
  match t with
  | LN => acc
  | LS a => a :: acc
  | BN t1 t2 => toListA (toListA acc t2) t1
  | BS t1 a t2 => toListA (a :: toListA acc t2) t1
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "toList_def" *)
Definition toList (m : spt A) : list A := toListA [] m.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mk_wf_def" *)
Fixpoint mk_wf (t : spt A) : spt A :=
  match t with
  | LN => LN
  | LS x => LS x
  | BN t1 t2 => mk_BN (mk_wf t1) (mk_wf t2)
  | BS t1 x t2 => mk_BS (mk_wf t1) x (mk_wf t2)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "fromAList_def" *)
Fixpoint fromAList (l : list (N * A)) : spt A :=
  match l with
  | [] => LN
  | (x, y) :: xs => insert x y (fromAList xs)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_def" *)
Fixpoint map {B} (f : A -> B) (t : spt A) : spt B :=
  match t with
  | LN => LN
  | LS a => LS (f a)
  | BN t1 t2 => BN (map f t1) (map f t2)
  | BS t1 a t2 => BS (map f t1) (f a) (map f t2)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_left_def" *)
Definition spt_left (t : spt A) : spt A :=
  match t with
  | LN => LN
  | LS x => LN
  | BN t1 t2 => t1
  | BS t1 x t2 => t1
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_right_def" *)
Definition spt_right (t : spt A) : spt A :=
  match t with
  | LN => LN
  | LS x => LN
  | BN t1 t2 => t2
  | BS t1 x t2 => t2
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_center_def" *)
Definition spt_center (t : spt A) : option A :=
  match t with
  | LS x => Some x
  | BS t1 x t2 => Some x
  | _ => None
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_eq" *)
Fixpoint subspt `{EqDecision A} (t0 t : spt A) : bool :=
  match t0 with
  | LN => true
  | LS x => bool_decide (spt_center t = Some x)
  | BN t1 t2 => subspt t1 (spt_left t) && subspt t2 (spt_right t)
  | BS t1 x t2 =>
      bool_decide (spt_center t = Some x) &&
      (subspt t1 (spt_left t) && subspt t2 (spt_right t))
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "filter_v_def" *)
Fixpoint filter_v (f : A -> bool) (t : spt A) : spt A :=
  match t with
  | LN => LN
  | LS x => if f x then LS x else LN
  | BN l r => mk_BN (filter_v f l) (filter_v f r)
  | BS l x r =>
      if f x then mk_BS (filter_v f l) x (filter_v f r)
      else mk_BN (filter_v f l) (filter_v f r)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_fold_def" *)
Fixpoint spt_fold {B} (f : A -> B -> B) (acc : B) (t : spt A) : B :=
  match t with
  | LN => acc
  | LS a => f a acc
  | BN t1 t2 => spt_fold f (spt_fold f acc t1) t2
  | BS t1 a t2 => spt_fold f (f a (spt_fold f acc t1)) t2
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "alist_insert_def" *)
Fixpoint alist_insert (vs : list N) (xs : list A) (t : spt A) : spt A :=
  match vs, xs with
  | [], _ => t
  | _, [] => t
  | v :: vs, x :: xs => insert v x (alist_insert vs xs t)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spts_to_alist_add_pause_def" *)
Definition spts_to_alist_add_pause (j : N) (q : list (N * spt A)) : list (N * spt A) :=
  match q with
  | [] => [(j, LN)]
  | (i, t) :: q => (i + j, t) :: q
  end.

(** HOL tuples nest to the right: [(a, b, c, d)] is [(a, (b, (c, d)))]. *)
(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spts_to_alist_aux_def" *)
Fixpoint spts_to_alist_aux (i : N) (xs : list (N * spt A)) (acc_cent : list (N * A))
    (acc_right acc_left : list (N * spt A)) (repeat : bool)
    : N * (list (N * spt A) * (list (N * A) * bool)) :=
  match xs with
  | [] => (i, (REVERSE acc_right ++ REVERSE acc_left, (acc_cent, repeat)))
  | (j, t) :: ys =>
      if isEmpty t then
        spts_to_alist_aux (i + j) ys acc_cent
          (spts_to_alist_add_pause j acc_right) (spts_to_alist_add_pause j acc_left)
          repeat
      else
        spts_to_alist_aux (i + j) ys
          ((match spt_center t with None => [] | Some c => [(i, c)] end) ++ acc_cent)
          ((j, spt_right t) :: acc_right) ((j, spt_left t) :: acc_left)
          true
  end.

(** The termination measure of [spts_to_alist]. *)
Fixpoint spt_nodes (t : spt A) : nat :=
  match t with
  | LN => O
  | LS _ => S O
  | BN t1 t2 => S (Nat.add (spt_nodes t1) (spt_nodes t2))
  | BS t1 _ t2 => S (Nat.add (spt_nodes t1) (spt_nodes t2))
  end.

Definition spts_measure (xs : list (N * spt A)) : nat :=
  List.fold_right (fun p n => Nat.add (spt_nodes (snd p)) n) O xs.

(** [spts_to_alist_f fuel i xs acc] is [spts_to_alist i xs acc] whenever
    [spts_measure xs < fuel]. *)
Fixpoint spts_to_alist_f (fuel : nat) (i : N) (xs : list (N * spt A)) (acc_cent : list (N * A))
    : list (N * A) :=
  match fuel with
  | O => REVERSE acc_cent
  | S fuel =>
      let '(i, (xs, (acc_cent, repeat))) := spts_to_alist_aux i xs acc_cent [] [] false in
      if repeat then spts_to_alist_f fuel i xs acc_cent
      else REVERSE acc_cent
  end.

(** HOL [spts_to_alist]; its defining equation is [spts_to_alist_def]. *)
Definition spts_to_alist (i : N) (xs : list (N * spt A)) (acc_cent : list (N * A))
    : list (N * A) :=
  spts_to_alist_f (S (spts_measure xs)) i xs acc_cent.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "toSortedAList_def" *)
Definition toSortedAList (t : spt A) : list (N * A) := spts_to_alist 0 [(1, t)] [].

End Defs2.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "list_to_num_set_def" *)
Fixpoint list_to_num_set (l : list N) : num_set :=
  match l with
  | [] => LN
  | n :: ns => insert n tt (list_to_num_set ns)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "list_insert_def" *)
Fixpoint list_insert (l : list N) (t : num_set) : num_set :=
  match l with
  | [] => t
  | n :: ns => list_insert ns (insert n tt t)
  end.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "gather_inclist_offsets_def" *)
Fixpoint gather_inclist_offsets {A} (l : list (N * A)) : list (N * A) :=
  match l with
  | [] => []
  | (inc, x) :: xs =>
      (0, x) :: MAP (fun p => (inc + fst p, snd p)) (gather_inclist_offsets xs)
  end.

(** HOL [spt_acc], by recursion on the binary digits of [k + 1] as for
    [insert]; HOL's equation is [spt_acc_def] below. *)
Fixpoint spt_acc_pos (i : N) (p : positive) : N :=
  match p with
  | xH => i
  | xI q => spt_acc_pos (i + 2 * lrnext i) q
  | xO q => spt_acc_pos (i + lrnext i) q
  end.

Definition spt_acc (i k : N) : N := spt_acc_pos i (N.succ_pos k).

(** ** Arithmetic helpers (Galette) *)

Lemma EVEN_odd_form m : EVEN (2 * m + 1) = false.
Proof.
  destruct (EVEN (2 * m + 1)) eqn:E; [|reflexivity].
  apply N.even_spec in E as [c Hc]; lia.
Qed.

Lemma EVEN_even_form m : EVEN (2 * m + 2) = true.
Proof. apply N.even_spec; exists (m + 1); lia. Qed.

Lemma DIV_odd_form m : (2 * m + 1 - 1) DIV 2 = m.
Proof. symmetry; apply (N.div_unique _ _ _ 0); lia. Qed.

Lemma DIV_even_form m : (2 * m + 2 - 1) DIV 2 = m.
Proof. symmetry; apply (N.div_unique _ _ _ 1); lia. Qed.

Lemma bit_cases n : n = 0 \/ (exists m, n = 2 * m + 1) \/ (exists m, n = 2 * m + 2).
Proof.
  induction n as [|n [->|[[m ->]|[m ->]]]] using N.peano_ind; auto.
  - right; left; exists 0; lia.
  - right; right; exists m; lia.
  - right; left; exists (m + 1); lia.
Qed.

Lemma bit_induction (P : N -> Prop) :
  P 0 -> (forall n, P n -> P (2 * n + 1)) -> (forall n, P n -> P (2 * n + 2)) ->
  forall n, P n.
Proof.
  intros H0 H1 H2 n.
  induction n as [n IH] using (well_founded_induction N.lt_wf_0).
  destruct (bit_cases n) as [->|[[m ->]|[m ->]]]; auto.
  - apply H1, IH; lia.
  - apply H2, IH; lia.
Qed.

Ltac bitcase k :=
  let m := fresh "m" in
  destruct (bit_cases k) as [->|[[m ->]|[m ->]]].

(** Destruct every [decide (x = y)] on numbers, discarding impossible cases. *)
Ltac dec :=
  repeat match goal with
  | |- context [decide (?x = ?y :> N)] =>
      destruct (decide (x = y)); try (exfalso; lia)
  | H : context [decide (?x = ?y :> N)] |- _ =>
      destruct (decide (x = y)); try (exfalso; lia)
  end.

Ltac bsimp :=
  rewrite ?EVEN_odd_form, ?EVEN_even_form, ?DIV_odd_form, ?DIV_even_form in *;
  dec; cbv beta iota in *.

Lemma succ_pos_0 : N.succ_pos 0 = xH.
Proof. reflexivity. Qed.

Lemma succ_pos_odd m : N.succ_pos (2 * m + 1) = xO (N.succ_pos m).
Proof.
  enough (E : Npos (N.succ_pos (2 * m + 1)) = Npos (xO (N.succ_pos m))) by (injection E; auto).
  change (Npos (xO (N.succ_pos m))) with (2 * Npos (N.succ_pos m)).
  rewrite !N.succ_pos_spec; lia.
Qed.

Lemma succ_pos_even m : N.succ_pos (2 * m + 2) = xI (N.succ_pos m).
Proof.
  enough (E : Npos (N.succ_pos (2 * m + 2)) = Npos (xI (N.succ_pos m))) by (injection E; auto).
  change (Npos (xI (N.succ_pos m))) with (2 * Npos (N.succ_pos m) + 1).
  rewrite !N.succ_pos_spec; lia.
Qed.

(** ** Defining equations of the definitions recursing on numbers *)

Section Equations.
Context {A : Type}.

Lemma insert_eqs k (a a' : A) t1 t2 :
  (insert k a LN = if decide (k = 0) then LS a
                     else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                     else BN LN (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (LS a') =
     if decide (k = 0) then LS a
     else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
     else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (BN t1 t2) =
     if decide (k = 0) then BS t1 a t2
     else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
     else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
  (insert k a (BS t1 a' t2) =
     if decide (k = 0) then BS t1 a t2
     else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
     else BS t1 a' (insert ((k - 1) DIV 2) a t2)).
Proof.
  bitcase k; bsimp; unfold insert;
    rewrite ?succ_pos_0, ?succ_pos_odd, ?succ_pos_even; repeat split.
Qed.

End Equations.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_def" *)
Theorem insert_def : forall {A} k (a : A) a' t1 t2,
  (insert k a LN = if decide (k = 0) then LS a
                     else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                     else BN LN (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (LS a') =
     if decide (k = 0) then LS a
     else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
     else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (BN t1 t2) =
     if decide (k = 0) then BS t1 a t2
     else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
     else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
  (insert k a (BS t1 a' t2) =
     if decide (k = 0) then BS t1 a t2
     else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
     else BS t1 a' (insert ((k - 1) DIV 2) a t2)).
Proof. intros; apply insert_eqs. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lrnext_def" *)
Theorem lrnext_def : forall n,
  lrnext n = if decide (n = 0) then 1 else 2 * lrnext ((n - 1) DIV 2).
Proof.
  intros n; bitcase n; bsimp; unfold lrnext;
    rewrite ?succ_pos_0, ?succ_pos_odd, ?succ_pos_even; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_acc_thm" *)
Theorem spt_acc_thm : forall i k,
  spt_acc i k = if decide (k = 0) then i
                else spt_acc (i + if EVEN k then 2 * lrnext i else lrnext i) ((k - 1) DIV 2).
Proof.
  intros i k; bitcase k; bsimp; unfold spt_acc;
    rewrite ?succ_pos_0, ?succ_pos_odd, ?succ_pos_even; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_acc_def" *)
Theorem spt_acc_def : forall i k,
  spt_acc i 0 = i /\
  spt_acc i (SUC k) =
    spt_acc (i + if EVEN (SUC k) then 2 * lrnext i else lrnext i) (k DIV 2).
Proof.
  intros i k; split; [reflexivity|].
  rewrite spt_acc_thm; dec. replace (SUC k - 1) with k by lia. reflexivity.
Qed.

(** ** Lookup, insert, delete, union, intersection, difference *)

(** A decision procedure for [o = None] that needs no equality on the
    contents (used where HOL tests [lookup k t = NONE]). *)
#[local] Instance option_None_dec {B} (o : option B) : Decision (o = None).
Proof. destruct o; [right; discriminate|left; reflexivity]. Defined.

Ltac bsplit :=
  unfold is_true in *;
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  | |- (_ && _) = true => apply andb_true_intro; split
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | |- negb _ = true => apply negb_true_iff
  end.

Section Core.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_rwts" *)
Theorem lookup_rwts : forall k (a : A) t1 t2,
  lookup k (@LN A) = None /\ lookup 0 (LS a) = Some a /\
  lookup 0 (BN t1 t2) = None /\ lookup 0 (BS t1 a t2) = Some a.
Proof. intros; cbn [lookup]; dec; repeat split. Qed.

Lemma lookup_LN k : lookup k (@LN A) = None.
Proof. reflexivity. Qed.

Lemma lookup_0 t : lookup 0 t = spt_center t.
Proof. destruct t; cbn [lookup spt_center]; dec; reflexivity. Qed.

Lemma lookup_1 m t : lookup (2 * m + 1) t = lookup m (spt_right t).
Proof. destruct t; cbn [lookup spt_right]; bsimp; reflexivity. Qed.

Lemma lookup_2 m t : lookup (2 * m + 2) t = lookup m (spt_left t).
Proof. destruct t; cbn [lookup spt_left]; bsimp; reflexivity. Qed.

Lemma insert_0 (a : A) t :
  insert 0 a t = match t with
                 | LN => LS a | LS _ => LS a
                 | BN t1 t2 => BS t1 a t2 | BS t1 _ t2 => BS t1 a t2 end.
Proof. destruct t; reflexivity. Qed.

Lemma insert_1 m (a : A) t :
  insert (2 * m + 1) a t =
  match t with
  | LN => BN LN (insert m a LN)
  | LS a' => BS LN a' (insert m a LN)
  | BN t1 t2 => BN t1 (insert m a t2)
  | BS t1 a' t2 => BS t1 a' (insert m a t2)
  end.
Proof.
  pose proof (insert_eqs (2 * m + 1) a) as E.
  destruct t as [|a'|t1 t2|t1 a' t2];
    [rewrite (proj1 (E a LN LN)) | rewrite (proj1 (proj2 (E a' LN LN)))
    | rewrite (proj1 (proj2 (proj2 (E a t1 t2)))) | rewrite (proj2 (proj2 (proj2 (E a' t1 t2))))];
    bsimp; reflexivity.
Qed.

Lemma insert_2 m (a : A) t :
  insert (2 * m + 2) a t =
  match t with
  | LN => BN (insert m a LN) LN
  | LS a' => BS (insert m a LN) a' LN
  | BN t1 t2 => BN (insert m a t1) t2
  | BS t1 a' t2 => BS (insert m a t1) a' t2
  end.
Proof.
  pose proof (insert_eqs (2 * m + 2) a) as E.
  destruct t as [|a'|t1 t2|t1 a' t2];
    [rewrite (proj1 (E a LN LN)) | rewrite (proj1 (proj2 (E a' LN LN)))
    | rewrite (proj1 (proj2 (proj2 (E a t1 t2)))) | rewrite (proj2 (proj2 (proj2 (E a' t1 t2))))];
    bsimp; reflexivity.
Qed.

Lemma delete_0 t :
  delete 0 t = match t with
               | LN => LN | LS _ => LN
               | BN t1 t2 => BN t1 t2 | BS t1 _ t2 => BN t1 t2 end.
Proof. destruct t; cbn [delete]; dec; reflexivity. Qed.

Lemma delete_1 m t :
  delete (2 * m + 1) t =
  match t with
  | LN => LN | LS a => LS a
  | BN t1 t2 => mk_BN t1 (delete m t2)
  | BS t1 a t2 => mk_BS t1 a (delete m t2)
  end.
Proof. destruct t; cbn [delete]; bsimp; reflexivity. Qed.

Lemma delete_2 m t :
  delete (2 * m + 2) t =
  match t with
  | LN => LN | LS a => LS a
  | BN t1 t2 => mk_BN (delete m t1) t2
  | BS t1 a t2 => mk_BS (delete m t1) a t2
  end.
Proof. destruct t; cbn [delete]; bsimp; reflexivity. Qed.

(** HOL's local [lookup_mk_BN] (the public theorem of that name is below). *)
Lemma lookup_mk_BN_BN k t1 t2 : lookup k (mk_BN t1 t2) = lookup k (BN t1 t2).
Proof.
  destruct t1, t2; cbn [mk_BN]; try reflexivity.
  cbn [lookup]; dec; destruct (EVEN k); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_mk_BS" *)
Theorem lookup_mk_BS : forall k t1 x t2, lookup k (mk_BS t1 x t2) = lookup k (BS t1 x t2).
Proof.
  intros k t1 x t2; destruct t1, t2; cbn [mk_BS]; try reflexivity.
  cbn [lookup]; dec; destruct (EVEN k); reflexivity.
Qed.

Lemma wf_mk_BN_eq t1 t2 : wf (mk_BN t1 t2) = wf t1 && wf t2.
Proof. destruct t1, t2; cbn; rewrite ?andb_true_r; reflexivity. Qed.

Lemma wf_mk_BS_eq t1 x t2 : wf (mk_BS t1 x t2) = wf t1 && wf t2.
Proof. destruct t1, t2; cbn; rewrite ?andb_true_r; reflexivity. Qed.

End Core.

Ltac spt_simp :=
  repeat progress (
    rewrite ?insert_0, ?insert_1, ?insert_2, ?delete_0, ?delete_1, ?delete_2,
      ?lookup_mk_BN_BN, ?lookup_mk_BS, ?lookup_0, ?lookup_1, ?lookup_2, ?lookup_LN in *;
    cbn [spt_center spt_left spt_right] in *; cbv beta iota in *).

Ltac opt_cases :=
  repeat match goal with
  | |- context [match ?x with None => _ | Some _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x end
  end.

Ltac isEmpty_brute :=
  repeat match goal with H : _ = false |- _ => revert H end;
  repeat match goal with |- context [isEmpty ?x] => destruct (isEmpty x) end;
  cbn; intros; first [reflexivity | discriminate | congruence].

Section Core2.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_notEmpty" *)
Theorem insert_notEmpty : forall k (a : A) t, ~ isEmpty (insert k a t).
Proof.
  intros k a t; bitcase k; destruct t; spt_simp; cbn; discriminate.
Qed.

Lemma isEmpty_insert k (a : A) t : isEmpty (insert k a t) = false.
Proof. pose proof (insert_notEmpty k a t). destruct (isEmpty _); auto. exfalso; auto. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_insert" *)
Theorem wf_insert : forall k (a : A) t, wf t -> wf (insert k a t).
Proof.
  intros k; induction k as [|k IH|k IH] using bit_induction; intros a t W;
    destruct t; spt_simp; cbn [wf] in *; bsplit; auto;
    rewrite ?isEmpty_insert, ?andb_false_r; auto; try reflexivity; apply IH; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_delete" *)
Theorem wf_delete : forall t k, wf t -> wf (delete k t).
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros k W; bitcase k; spt_simp;
    cbn [wf] in *; rewrite ?wf_mk_BN_eq, ?wf_mk_BS_eq; bsplit; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_insert1" *)
Theorem lookup_insert1 : forall k (a : A) t, lookup k (insert k a t) = Some a.
Proof.
  intros k; induction k as [|k IH|k IH] using bit_induction; intros a t;
    destruct t; spt_simp; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_insert" *)
Theorem lookup_insert : forall k2 (v : A) t k1,
  lookup k1 (insert k2 v t) = if decide (k1 = k2) then Some v else lookup k1 t.
Proof.
  intros k2; induction k2 as [|k2 IH|k2 IH] using bit_induction; intros v t k1;
    bitcase k1; destruct t; spt_simp; rewrite ?IH; dec; subst; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "isEmpty_union" *)
Theorem isEmpty_union : forall (m1 m2 : spt A), isEmpty (union m1 m2) <-> isEmpty m1 /\ isEmpty m2.
Proof. intros [] []; cbn; intuition discriminate. Qed.

Lemma isEmpty_union_eq (m1 m2 : spt A) : isEmpty (union m1 m2) = isEmpty m1 && isEmpty m2.
Proof. destruct m1, m2; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_union" *)
Theorem wf_union : forall (m1 m2 : spt A), wf m1 /\ wf m2 -> wf (union m1 m2).
Proof.
  induction m1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros m2 [W1 W2]; [exact W2|..];
    destruct m2; cbn [union wf] in *; bsplit; auto;
    try (apply IH1; split; assumption); try (apply IH2; split; assumption);
    rewrite ?isEmpty_union_eq; isEmpty_brute.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_union" *)
Theorem lookup_union : forall (m1 m2 : spt A) k,
  lookup k (union m1 m2) = match lookup k m1 with None => lookup k m2 | Some v => Some v end.
Proof.
  induction m1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros m2 k; [reflexivity|..];
    destruct m2; bitcase k; cbn [union]; spt_simp; rewrite ?IH1, ?IH2; opt_cases; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_inter" *)
Theorem wf_inter : forall {B} (m1 : spt A) (m2 : spt B), wf (inter m1 m2).
Proof.
  intros B; induction m1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros m2; [reflexivity|..];
    destruct m2; cbn [inter]; rewrite ?wf_mk_BN_eq, ?wf_mk_BS_eq; bsplit; auto; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_inter" *)
Theorem lookup_inter : forall {B} (m1 : spt A) (m2 : spt B) k,
  lookup k (inter m1 m2) =
  match lookup k m1, lookup k m2 with Some v, Some w => Some v | _, _ => None end.
Proof.
  intros B; induction m1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros m2 k; [reflexivity|..];
    destruct m2; bitcase k; cbn [inter]; spt_simp; rewrite ?IH1, ?IH2; opt_cases; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_inter_eq" *)
Theorem lookup_inter_eq : forall `{EqDecision A} (m1 m2 : spt A) k,
  lookup k (inter_eq m1 m2) =
  match lookup k m1 with
  | None => None
  | Some v => if decide (lookup k m2 = Some v) then Some v else None
  end.
Proof.
  intros EA; induction m1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros m2 k; [reflexivity|..];
    destruct m2; bitcase k; cbn [inter_eq];
    repeat match goal with |- context [decide (?x = ?y :> A)] => destruct (decide (x = y)) end;
    subst; spt_simp; rewrite ?IH1, ?IH2; opt_cases;
    repeat match goal with |- context [decide ?P] => destruct (decide P) end;
    try reflexivity; congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_inter_EQ" *)
Theorem lookup_inter_EQ : forall {B} x (t1 : spt A) (t2 : spt B) y,
  (lookup x (inter t1 t2) = Some y <-> lookup x t1 = Some y /\ lookup x t2 <> None) /\
  (lookup x (inter t1 t2) = None <-> lookup x t1 = None \/ lookup x t2 = None).
Proof.
  intros; rewrite lookup_inter.
  destruct (lookup x t1), (lookup x t2); intuition congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_difference" *)
Theorem lookup_difference : forall {B} (m1 : spt A) (m2 : spt B) k,
  lookup k (difference m1 m2) = if decide (lookup k m2 = None) then lookup k m1 else None.
Proof.
  intros B; induction m1 as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros m2 k;
    [destruct (decide _); reflexivity|..];
    destruct m2; bitcase k; cbn [difference]; spt_simp; rewrite ?IH1, ?IH2;
    repeat match goal with |- context [decide ?P] => destruct (decide P) end;
    try reflexivity; try congruence; opt_cases; try reflexivity; congruence.
Qed.

End Core2.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_inter_assoc" *)
Theorem lookup_inter_assoc : forall {A B C} x (t1 : spt A) (t2 : spt B) (t3 : spt C),
  lookup x (inter t1 (inter t2 t3)) = lookup x (inter (inter t1 t2) t3).
Proof.
  intros; repeat rewrite lookup_inter.
  destruct (lookup x t1), (lookup x t2), (lookup x t3); reflexivity.
Qed.


(** ** Domains *)

Lemma set_ext {X} (s1 s2 : X -> Prop) : (forall x, s1 x <-> s2 x) -> s1 = s2.
Proof.
  intros H; apply functional_extensionality; intros x.
  apply propositional_extensionality, H.
Qed.

Section Domain.
Context {A : Type}.
Implicit Types (t : spt A).

Lemma domain_0 t : domain t 0 <-> spt_center t <> None.
Proof.
  destruct t as [|a|t1 t2|t1 a t2]; cbn [domain spt_center spt_left spt_right].
  - split; [tauto|intros H; apply H; reflexivity].
  - split; [discriminate|reflexivity].
  - split; [intros [[m [H _]]|[m [H _]]]; lia|intros H; exfalso; apply H; reflexivity].
  - split; [discriminate|left; left; reflexivity].
Qed.

Lemma domain_1 m t : domain t (2 * m + 1) <-> domain (spt_right t) m.
Proof.
  destruct t as [|a|t1 t2|t1 a t2]; cbn [domain spt_center spt_left spt_right].
  - tauto.
  - split; [lia|tauto].
  - split; [intros [[m' [H D]]|[m' [H D]]]; [lia|replace m with m' by lia; exact D]|].
    intros D; right; exists m; split; [lia|exact D].
  - split; [intros [[H|[m' [H D]]]|[m' [H D]]]; [lia|lia|replace m with m' by lia; exact D]|].
    intros D; right; exists m; split; [lia|exact D].
Qed.

Lemma domain_2 m t : domain t (2 * m + 2) <-> domain (spt_left t) m.
Proof.
  destruct t as [|a|t1 t2|t1 a t2]; cbn [domain spt_center spt_left spt_right].
  - tauto.
  - split; [lia|tauto].
  - split; [intros [[m' [H D]]|[m' [H D]]]; [replace m with m' by lia; exact D|lia]|].
    intros D; left; exists m; split; [lia|exact D].
  - split; [intros [[H|[m' [H D]]]|[m' [H D]]]; [lia|replace m with m' by lia; exact D|lia]|].
    intros D; left; right; exists m; split; [lia|exact D].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "IN_domain" *)
Theorem IN_domain : forall n (x : A) t1 t2,
  (domain (@LN A) n <-> False) /\
  (domain (LS x) n <-> n = 0) /\
  (domain (BN t1 t2) n <->
     n <> 0 /\ (if EVEN n then domain t1 ((n - 1) DIV 2) else domain t2 ((n - 1) DIV 2))) /\
  (domain (BS t1 x t2) n <->
     n = 0 \/ (if EVEN n then domain t1 ((n - 1) DIV 2) else domain t2 ((n - 1) DIV 2))).
Proof.
  intros n x t1 t2; bitcase n;
    rewrite ?domain_0, ?domain_1, ?domain_2; cbn [spt_center spt_left spt_right domain];
    bsimp; repeat split; try tauto; try congruence; try lia; intuition (congruence || lia).
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_lookup" *)
Theorem domain_lookup : forall t k, domain t k <-> exists v, lookup k t = Some v.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros k; bitcase k;
    rewrite ?domain_0, ?domain_1, ?domain_2; spt_simp; cbn [domain];
    try apply IH1; try apply IH2;
    split; try (intros [v H]; discriminate); try tauto;
    try (intros _; eexists; reflexivity); intros H; congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_NONE_domain" *)
Theorem lookup_NONE_domain : forall k t, lookup k t = None <-> ~ domain t k.
Proof.
  intros k t; rewrite domain_lookup; destruct (lookup k t); split; intros H.
  - discriminate.
  - exfalso; eauto.
  - intros [v Hv]; discriminate.
  - reflexivity.
Qed.

End Domain.

(** Membership in [domain] is decided by [lookup]. *)
#[global] Instance domain_dec {A} (t : spt A) (k : N) : Decision (domain t k).
Proof.
  destruct (lookup k t) as [v|] eqn:E; [left|right].
  - apply domain_lookup; eauto.
  - apply lookup_NONE_domain, E.
Defined.

Lemma ex_Some_iff {B} (o : option B) : (exists v, o = Some v) <-> o <> None.
Proof. destruct o; split; intros H; eauto; try congruence; destruct H; congruence. Qed.

Section Domain2.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_inter_alt" *)
Theorem lookup_inter_alt : forall {B} x t1 (t2 : spt B),
  lookup x (inter t1 t2) = if decide (domain t2 x) then lookup x t1 else None.
Proof.
  intros B x t1 t2; rewrite lookup_inter; destruct (decide (domain t2 x)) as [D|D].
  - apply domain_lookup in D as [v ->]; destruct (lookup x t1); reflexivity.
  - apply lookup_NONE_domain in D as ->; destruct (lookup x t1); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_union" *)
Theorem domain_union : forall t1 t2, domain (union t1 t2) = (fun x => domain t1 x \/ domain t2 x).
Proof.
  intros t1 t2; apply set_ext; intros x; rewrite !domain_lookup, !ex_Some_iff, lookup_union.
  destruct (lookup x t1); intuition congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_inter" *)
Theorem domain_inter : forall {B} t1 (t2 : spt B),
  domain (inter t1 t2) = (fun x => domain t1 x /\ domain t2 x).
Proof.
  intros B t1 t2; apply set_ext; intros x; rewrite !domain_lookup, !ex_Some_iff, lookup_inter.
  destruct (lookup x t1), (lookup x t2); intuition congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_insert" *)
Theorem domain_insert : forall k (v : A) t, domain (insert k v t) = (fun x => x = k \/ domain t x).
Proof.
  intros k v t; apply set_ext; intros x; rewrite !domain_lookup, !ex_Some_iff, lookup_insert.
  destruct (decide (x = k)); intuition congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_difference" *)
Theorem domain_difference : forall {B} t1 (t2 : spt B),
  domain (difference t1 t2) = (fun x => domain t1 x /\ ~ domain t2 x).
Proof.
  intros B t1 t2; apply set_ext; intros x; rewrite !domain_lookup, !ex_Some_iff, lookup_difference.
  destruct (decide (lookup x t2 = None)) as [E|E]; rewrite ?E.
  - intuition congruence.
  - destruct (lookup x t2); [|congruence]. intuition congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_sing" *)
Theorem domain_sing : forall k (v : A), domain (insert k v LN) = (fun x => x = k).
Proof.
  intros k v; rewrite domain_insert; apply set_ext; intros x; cbn; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_insert" *)
Theorem size_insert : forall k (v : A) m,
  size (insert k v m) = if decide (domain m k) then size m else size m + 1.
Proof.
  intros k; induction k as [|k IH|k IH] using bit_induction; intros v m;
    destruct (decide _) as [D|D];
    rewrite ?domain_0, ?domain_1, ?domain_2 in D;
    destruct m; cbn [spt_center spt_left spt_right domain] in D; spt_simp;
    cbn [size]; rewrite ?IH;
    repeat match goal with |- context [decide ?P] => destruct (decide P) end;
    cbn [size]; try tauto; try congruence; try (exfalso; apply D; discriminate); lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_fromList" *)
Theorem lookup_fromList : forall `{Inhabited A} n (l : list A),
  lookup n (fromList l) = if decide (n < LENGTH l) then Some (EL n l) else None.
Proof.
  intros IA n l; unfold fromList.
  assert (G : forall l i (t : spt A),
    lookup n (snd (FOLDL (fun '(i, t) a => (i + 1, insert i a t)) (i, t) l)) =
    if decide (n < i) then lookup n t
    else if decide (n < LENGTH l + i) then Some (EL (n - i) l) else lookup n t).
  { clear l; induction l as [|x l IH]; intros i t; cbn [FOLDL LENGTH].
    - repeat destruct (decide _); try reflexivity; lia.
    - rewrite IH, lookup_insert.
      repeat destruct (decide _); try reflexivity; try lia; subst.
      + replace (i - i) with 0 by lia. reflexivity.
      + replace (n - i) with (SUC (n - (i + 1))) by lia. rewrite EL_SUC; reflexivity. }
  rewrite G. repeat destruct (decide _); try lia; try reflexivity.
  rewrite N.sub_0_r, N.add_0_r in *; reflexivity || lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_fromList" *)
Theorem domain_fromList : forall (l : list A), domain (fromList l) = (fun x => x < LENGTH l).
Proof.
  intros l; apply set_ext; intros x. rewrite domain_lookup.
  destruct l as [|a l0]; [cbn; split; [intros [v H]; discriminate|lia]|].
  assert (IA' : Inhabited A) by exact a.
  rewrite (@lookup_fromList IA'). destruct (decide _); split; try lia; eauto.
  intros [v H]; discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_delete" *)
Theorem lookup_delete : forall t k1 k2,
  lookup k1 (delete k2 t) = if decide (k1 = k2) then None else lookup k1 t.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros k1 k2;
    bitcase k1; bitcase k2; spt_simp; rewrite ?IH1, ?IH2; dec; subst; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_delete" *)
Theorem domain_delete : forall k t, domain (delete k t) = (fun x => domain t x /\ x <> k).
Proof.
  intros k t; apply set_ext; intros x; rewrite !domain_lookup, !ex_Some_iff, lookup_delete.
  destruct (decide (x = k)); intuition congruence.
Qed.

End Domain2.

(** ** [lrnext], [foldi], [toAList], [mapi] *)

Lemma lrnext_0 : lrnext 0 = 1.
Proof. reflexivity. Qed.

Lemma lrnext_odd m : lrnext (2 * m + 1) = 2 * lrnext m.
Proof. rewrite lrnext_def; bsimp; reflexivity. Qed.

Lemma lrnext_even m : lrnext (2 * m + 2) = 2 * lrnext m.
Proof. rewrite lrnext_def; bsimp; reflexivity. Qed.

Lemma lrnext_gt_0 n : 0 < lrnext n.
Proof.
  induction n as [|n IH|n IH] using bit_induction;
    rewrite ?lrnext_0, ?lrnext_odd, ?lrnext_even; lia.
Qed.

Lemma lrlemma1 i : lrnext (i + lrnext i) = 2 * lrnext i.
Proof.
  induction i as [|i IH|i IH] using bit_induction.
  - rewrite lrnext_0; change (0 + 1) with (2 * 0 + 1); rewrite lrnext_odd, lrnext_0; reflexivity.
  - rewrite lrnext_odd. replace (2 * i + 1 + 2 * lrnext i) with (2 * (i + lrnext i) + 1) by lia.
    rewrite lrnext_odd, IH; reflexivity.
  - rewrite lrnext_even. replace (2 * i + 2 + 2 * lrnext i) with (2 * (i + lrnext i) + 2) by lia.
    rewrite lrnext_even, IH; reflexivity.
Qed.

Lemma lrlemma2 i : lrnext (i + 2 * lrnext i) = 2 * lrnext i.
Proof.
  induction i as [|i IH|i IH] using bit_induction.
  - rewrite lrnext_0; change (0 + 2 * 1) with (2 * 0 + 2); rewrite lrnext_even, lrnext_0; reflexivity.
  - rewrite lrnext_odd.
    replace (2 * i + 1 + 2 * (2 * lrnext i)) with (2 * (i + 2 * lrnext i) + 1) by lia.
    rewrite lrnext_odd, IH; reflexivity.
  - rewrite lrnext_even.
    replace (2 * i + 2 + 2 * (2 * lrnext i)) with (2 * (i + 2 * lrnext i) + 2) by lia.
    rewrite lrnext_even, IH; reflexivity.
Qed.

Lemma mul_cancel_pos L a b : 0 < L -> L * a = L * b -> a = b.
Proof. intros HL H. apply N.mul_cancel_l in H; lia. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_acc_eqn" *)
Theorem spt_acc_eqn : forall k i, spt_acc i k = lrnext i * k + i.
Proof.
  intros k; induction k as [|k IH|k IH] using bit_induction; intros i.
  - rewrite (proj1 (spt_acc_def i 0)); lia.
  - rewrite spt_acc_thm; bsimp. rewrite IH, lrlemma1; lia.
  - rewrite spt_acc_thm; bsimp. rewrite IH, lrlemma2; lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_acc_0" *)
Theorem spt_acc_0 : forall k, spt_acc 0 k = k.
Proof. intros k; rewrite spt_acc_eqn, lrnext_0; lia. Qed.

Section Foldi.
Context {A : Type}.
Implicit Types (t : spt A).

Lemma In_foldi t : forall i acc k v,
  In (k, v) (foldi (fun k v a => (k, v) :: a) i acc t) <->
  In (k, v) acc \/ exists n, k = i + lrnext i * n /\ lookup n t = Some v.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros i acc k v; cbn [foldi].
  - split; [tauto|intros [H|[n [_ H]]]; [exact H|discriminate]].
  - cbn [In]. split.
    + intros [H|H]; [right; exists 0; injection H as -> ->; split; [lia|reflexivity]|tauto].
    + intros [H|[n [-> H]]]; [tauto|]. bitcase n; spt_simp; try discriminate.
      left; injection H as ->; f_equal; lia.
  - rewrite IH2, IH1, lrlemma1, lrlemma2.
    pose proof (lrnext_gt_0 i) as HL. split.
    + intros [[H|[n [-> H]]]|[n [-> H]]]; [tauto|right..].
      * exists (2 * n + 2); spt_simp; split; [nia|exact H].
      * exists (2 * n + 1); spt_simp; split; [nia|exact H].
    + intros [H|[n [-> H]]]; [tauto|]. bitcase n; spt_simp; try discriminate.
      * right; exists m; split; [nia|exact H].
      * left; right; exists m; split; [nia|exact H].
  - rewrite IH2, lrlemma1. cbn [In]. rewrite IH1, lrlemma2.
    pose proof (lrnext_gt_0 i) as HL. split.
    + intros [[H|[H|[n [-> H]]]]|[n [-> H]]]; [|tauto|right..].
      * right; exists 0; injection H as -> ->; split; [lia|reflexivity].
      * exists (2 * n + 2); spt_simp; split; [nia|exact H].
      * exists (2 * n + 1); spt_simp; split; [nia|exact H].
    + intros [H|[n [-> H]]]; [tauto|]. bitcase n; spt_simp.
      * left; left; injection H as ->; f_equal; lia.
      * right; exists m; split; [nia|exact H].
      * left; right; right; exists m; split; [nia|exact H].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "MEM_toAList" *)
Theorem MEM_toAList : forall `{EqDecision A} t k v, MEM (k, v) (toAList t) <-> lookup k t = Some v.
Proof.
  intros EA t k v; unfold is_true, toAList; rewrite MEM_In, In_foldi, lrnext_0; cbn [In]. split.
  - intros [[]|[n [-> H]]]; replace (0 + 1 * n) with n by lia; exact H.
  - intros H; right; exists k; split; [lia|exact H].
Qed.

Lemma length_foldi t : forall i acc,
  LENGTH (foldi (fun k v a => (k, v) :: a) i acc t) = LENGTH acc + size t.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros i acc; cbn [foldi size];
    rewrite ?IH2; cbn [LENGTH]; rewrite ?IH1; cbn [LENGTH]; lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "LENGTH_toAList" *)
Theorem LENGTH_toAList : forall t, LENGTH (toAList t) = size t.
Proof. intros t; unfold toAList; rewrite length_foldi; reflexivity. Qed.

Lemma NoDup_foldi t : forall i acc,
  NoDup (List.map fst acc) ->
  (forall n v, lookup n t = Some v -> ~ In (i + lrnext i * n) (List.map fst acc)) ->
  NoDup (List.map fst (foldi (fun k v a => (k, v) :: a) i acc t)).
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros i acc ND Dis; cbn [foldi].
  - exact ND.
  - cbn [List.map fst]. constructor; [|exact ND].
    specialize (Dis 0 a eq_refl). rewrite N.mul_0_r, N.add_0_r in Dis; exact Dis.
  - pose proof (lrnext_gt_0 i) as HL.
    apply IH2.
    + apply IH1; [exact ND|]. intros n v Hn. rewrite lrlemma2.
      specialize (Dis (2 * n + 2) v). spt_simp.
      replace (i + 2 * lrnext i + 2 * lrnext i * n) with (i + lrnext i * (2 * n + 2)) by nia.
      exact (Dis Hn).
    + intros n v Hn Hin. rewrite lrlemma1 in Hin.
      apply in_map_iff in Hin as [[k w] [Hk Hin]]; cbn [fst] in Hk; subst k.
      apply In_foldi in Hin as [Hin|[n1 [E Hn1]]].
      * apply (Dis (2 * n + 1) v); [spt_simp; exact Hn|].
        replace (i + lrnext i * (2 * n + 1)) with (i + lrnext i + 2 * lrnext i * n) by nia.
        apply in_map_iff; exists (i + lrnext i + 2 * lrnext i * n, w); auto.
      * rewrite lrlemma2 in E.
        assert (EQ : lrnext i * (2 * n + 1) = lrnext i * (2 * n1 + 2)) by nia.
        apply mul_cancel_pos in EQ; lia.
  - pose proof (lrnext_gt_0 i) as HL.
    apply IH2.
    + cbn [List.map fst]. constructor.
      * intros Hin. apply in_map_iff in Hin as [[k w] [Hk Hin]]; cbn [fst] in Hk; subst k.
        apply In_foldi in Hin as [Hin|[n1 [E Hn1]]].
        -- apply (Dis 0 a); [reflexivity|]. rewrite N.mul_0_r, N.add_0_r.
           apply in_map_iff; exists (i, w); auto.
        -- rewrite lrlemma2 in E. nia.
      * apply IH1; [exact ND|]. intros n v Hn. rewrite lrlemma2.
        specialize (Dis (2 * n + 2) v). spt_simp.
        replace (i + 2 * lrnext i + 2 * lrnext i * n) with (i + lrnext i * (2 * n + 2)) by nia.
        exact (Dis Hn).
    + intros n v Hn Hin. rewrite lrlemma1 in Hin. cbn [List.map fst In] in Hin.
      destruct Hin as [E|Hin]; [nia|].
      apply in_map_iff in Hin as [[k w] [Hk Hin]]; cbn [fst] in Hk; subst k.
      apply In_foldi in Hin as [Hin|[n1 [E Hn1]]].
      * apply (Dis (2 * n + 1) v); [spt_simp; exact Hn|].
        replace (i + lrnext i * (2 * n + 1)) with (i + lrnext i + 2 * lrnext i * n) by nia.
        apply in_map_iff; exists (i + lrnext i + 2 * lrnext i * n, w); auto.
      * rewrite lrlemma2 in E.
        assert (EQ : lrnext i * (2 * n + 1) = lrnext i * (2 * n1 + 2)) by nia.
        apply mul_cancel_pos in EQ; lia.
Qed.

End Foldi.

Lemma ALL_DISTINCT_NoDup {X} `{EqDecision X} (l : list X) : ALL_DISTINCT l = true <-> NoDup l.
Proof.
  induction l as [|x l IH]; cbn [ALL_DISTINCT].
  - split; [constructor|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH. split.
    + intros [H1 H2]; constructor; [|exact H2]. intros Hin.
      apply MEM_In in Hin; congruence.
    + intros HN; inversion HN as [|? ? Hn Hd]; subst; split; [|exact Hd].
      destruct (MEM x l) eqn:E; [|reflexivity]. apply MEM_In in E; contradiction.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "ALL_DISTINCT_MAP_FST_toAList" *)
Theorem ALL_DISTINCT_MAP_FST_toAList : forall {A} (t : spt A), ALL_DISTINCT (MAP fst (toAList t)).
Proof.
  intros A t; unfold is_true; rewrite ALL_DISTINCT_NoDup; unfold toAList.
  apply NoDup_foldi; [constructor|]. intros n v _ [].
Qed.

Lemma ALOOKUP_In {K V} `{EqDecision K} (l : list (K * V)) q v :
  ALOOKUP l q = Some v -> In (q, v) l.
Proof.
  induction l as [|[x y] l IH]; cbn; [discriminate|].
  destruct (decide (x = q)); [intros HE; injection HE as ->; subst; auto|auto].
Qed.

Lemma ALOOKUP_None {K V} `{EqDecision K} (l : list (K * V)) q :
  ALOOKUP l q = None -> forall v, ~ In (q, v) l.
Proof.
  induction l as [|[x y] l IH]; cbn; [auto|].
  destruct (decide (x = q)); [discriminate|]. intros HE v [E|Hin]; [congruence|eapply IH; eauto].
Qed.

Lemma ALOOKUP_toAList_In {A} (t : spt A) k v : In (k, v) (toAList t) <-> lookup k t = Some v.
Proof.
  unfold toAList; rewrite In_foldi, lrnext_0; cbn [In]. split.
  - intros [[]|[n [-> H]]]; replace (0 + 1 * n) with n by lia; exact H.
  - intros H; right; exists k; split; [lia|exact H].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "ALOOKUP_toAList" *)
Theorem ALOOKUP_toAList : forall {A} (t : spt A) x, ALOOKUP (toAList t) x = lookup x t.
Proof.
  intros A t x.
  assert (M : forall k v, In (k, v) (toAList t) <-> lookup k t = Some v).
  { intros k v; unfold toAList; rewrite In_foldi, lrnext_0; cbn [In]. split.
    - intros [[]|[n [-> H]]]; replace (0 + 1 * n) with n by lia; exact H.
    - intros H; right; exists k; split; [lia|exact H]. }
  destruct (ALOOKUP (toAList t) x) as [v|] eqn:E.
  - symmetry; apply M, ALOOKUP_In, E.
  - destruct (lookup x t) as [v|] eqn:L; [|reflexivity].
    exfalso; apply (ALOOKUP_None _ _ E v), M, L.
Qed.

Section Foldi2.
Context {A : Type}.
Implicit Types (t : spt A).

Lemma foldi_FOLDR_lemma {B} (f : N -> A -> B -> B) t : forall n a ls,
  foldi f n (FOLDR (fun p acc => f (fst p) (snd p) acc) a ls) t =
  FOLDR (fun p acc => f (fst p) (snd p) acc) a (foldi (fun k v a => (k, v) :: a) n ls t).
Proof.
  induction t as [|x|t1 IH1 t2 IH2|t1 IH1 x t2 IH2]; intros n a ls; cbn [foldi];
    [reflexivity|reflexivity|..].
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH1. change (f n x (FOLDR (fun p acc => f (fst p) (snd p) acc) a
      (foldi (fun k v a => (k, v) :: a) (n + 2 * lrnext n) ls t1)))
      with (FOLDR (fun p acc => f (fst p) (snd p) acc) a
      ((n, x) :: foldi (fun k v a => (k, v) :: a) (n + 2 * lrnext n) ls t1)).
    rewrite IH2; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "foldi_FOLDR_toAList" *)
Theorem foldi_FOLDR_toAList : forall {B} (f : N -> A -> B -> B) a t,
  foldi f 0 a t = FOLDR (fun p acc => f (fst p) (snd p) acc) a (toAList t).
Proof. intros B f a t; exact (foldi_FOLDR_lemma f t 0 a []). Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "set_foldi_keys" *)
Theorem set_foldi_keys : forall t (a : N -> Prop) i,
  foldi (fun k v a => fun x => x = k \/ a x) i a t =
  (fun x => a x \/ exists n, x = i + lrnext i * n /\ domain t n).
Proof.
  intros t a i.
  pose proof (foldi_FOLDR_lemma (fun k (v : A) (a : N -> Prop) => fun x => x = k \/ a x) t i a [])
    as E; cbn [FOLDR] in E; rewrite E; clear E.
  apply set_ext; intros x.
  assert (G : forall l, FOLDR (fun (p : N * A) (acc : N -> Prop) x => x = fst p \/ acc x) a l x <->
                       a x \/ exists v, In (x, v) l).
  { induction l as [|[k v] l IH]; cbn [FOLDR fst In].
    - split; [tauto|intros [H|[v [] ]]; exact H].
    - rewrite IH. split.
      + intros [->|[H|[w H]]]; eauto.
      + intros [H|[w [E|H]]]; [tauto|injection E as -> ->; tauto|eauto]. }
  rewrite G. split.
  - intros [H|[v H]]; [tauto|]. apply In_foldi in H as [[]|[n [-> H]]].
    right; exists n; split; [reflexivity|apply domain_lookup; eauto].
  - intros [H|[n [-> H]]]; [tauto|]. apply domain_lookup in H as [v H].
    right; exists v; apply In_foldi; right; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_foldi" *)
Theorem domain_foldi : forall t,
  domain t = foldi (fun k v a => fun x => x = k \/ a x) 0 (fun _ => False) t.
Proof.
  intros t; rewrite set_foldi_keys, lrnext_0; apply set_ext; intros x. split.
  - intros H; right; exists x; split; [lia|exact H].
  - intros [[]|[n [-> H]]]; replace (0 + 1 * n) with n by lia; exact H.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_mapi0" *)
Theorem lookup_mapi0 : forall {B} (f : N -> A -> B) pt i k,
  lookup k (mapi0 f i pt) =
  match lookup k pt with None => None | Some v => Some (f (spt_acc i k) v) end.
Proof.
  intros B f; induction pt as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros i k;
    bitcase k; cbn [mapi0]; spt_simp; rewrite ?IH1, ?IH2; opt_cases; try reflexivity;
    rewrite !spt_acc_eqn, ?lrlemma1, ?lrlemma2; do 2 f_equal; nia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_mapi" *)
Theorem lookup_mapi : forall {B} (f : N -> A -> B) k pt,
  lookup k (mapi f pt) = option_map (f k) (lookup k pt).
Proof.
  intros B f k pt; unfold mapi; rewrite lookup_mapi0, spt_acc_0.
  destruct (lookup k pt); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "MAP_foldi" *)
Theorem MAP_foldi : forall {B} (f : N * A -> B) pt n acc,
  MAP f (foldi (fun k v a => (k, v) :: a) n acc pt) =
  foldi (fun k v a => f (k, v) :: a) n (MAP f acc) pt.
Proof.
  intros B f; induction pt as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros n acc; cbn [foldi];
    [reflexivity|reflexivity|..]; rewrite IH2; cbn [List.map]; rewrite IH1; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "toListA_append" *)
Theorem toListA_append : forall t acc, toListA acc t = toListA [] t ++ acc.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros acc; cbn [toListA]; [reflexivity|reflexivity|..].
  - rewrite IH1, (IH1 (toListA [] t2)), IH2, app_assoc; reflexivity.
  - rewrite IH1, (IH1 (a :: toListA [] t2)), IH2, <- app_assoc; reflexivity.
Qed.

Lemma length_toListA t acc : LENGTH (toListA acc t) = size t + LENGTH acc.
Proof.
  revert acc; induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros acc; cbn [toListA size LENGTH];
    rewrite ?IH1; cbn [LENGTH]; rewrite ?IH2; lia.
Qed.

Lemma wf_size_pos t : wf t -> t <> LN -> 0 < size t.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros W NE; cbn [size] in *;
    [congruence|lia|..]; cbn [wf] in W; bsplit; [|lia].
  destruct t1; [destruct t2; [discriminate|..]|..];
    first [specialize (IH1 ltac:(assumption) ltac:(discriminate)); lia
          |specialize (IH2 ltac:(assumption) ltac:(discriminate)); lia].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "isEmpty_toListA" *)
Theorem isEmpty_toListA : forall t acc, wf t -> (t = LN <-> toListA acc t = acc).
Proof.
  intros t acc W; split; [intros ->; reflexivity|intros E].
  destruct t; [reflexivity|..]; exfalso;
    pose proof (f_equal (@LENGTH A) E) as L; rewrite length_toListA in L;
    pose proof (wf_size_pos _ W ltac:(discriminate)); lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "isEmpty_toList" *)
Theorem isEmpty_toList : forall t, wf t -> (t = LN <-> toList t = []).
Proof. intros t W; apply isEmpty_toListA, W. Qed.

Lemma In_toListA t : forall acc x, In x (toListA acc t) <-> In x acc \/ exists k, lookup k t = Some x.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros acc x; cbn [toListA In].
  - split; [tauto|intros [H|[k H]]; [exact H|discriminate]].
  - split.
    + intros [<-|H]; [right; exists 0; reflexivity|tauto].
    + intros [H|[k H]]; [tauto|]. bitcase k; spt_simp; try discriminate.
      left; congruence.
  - rewrite IH1, IH2. split.
    + intros [[H|[k H]]|[k H]]; [tauto|right; exists (2 * k + 1)|right; exists (2 * k + 2)];
        spt_simp; exact H.
    + intros [H|[k H]]; [tauto|]. bitcase k; spt_simp; try discriminate; eauto.
  - rewrite IH1. cbn [In]. rewrite IH2. split.
    + intros [[H|[H|[k H]]]|[k H]];
        [right; exists 0; spt_simp; congruence|tauto
        |right; exists (2 * k + 1)|right; exists (2 * k + 2)]; spt_simp; exact H.
    + intros [H|[k H]]; [tauto|]. bitcase k; spt_simp; eauto.
      left; left; congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "MEM_toList" *)
Theorem MEM_toList : forall `{EqDecision A} x t, MEM x (toList t) <-> exists k, lookup k t = Some x.
Proof.
  intros EA x t; unfold is_true, toList; rewrite MEM_In, In_toListA; cbn [In]; tauto.
Qed.

(** ** Extensionality *)

Lemma wf_left t : wf t -> wf (spt_left t).
Proof. destruct t; cbn; intros; bsplit; auto. Qed.

Lemma wf_right t : wf t -> wf (spt_right t).
Proof. destruct t; cbn; intros; bsplit; auto. Qed.

Lemma spt_LN_dec t : {t = LN} + {t <> LN}.
Proof. destruct t; [left; reflexivity|right; discriminate..]. Defined.

Lemma wf_nonempty t : wf t -> t <> LN -> exists n v, lookup n t = Some v.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros W NE; [congruence|..].
  - exists 0, a; reflexivity.
  - cbn [wf] in W; bsplit.
    destruct (spt_LN_dec t1) as [->|N1].
    + assert (N2 : t2 <> LN) by (intros ->; cbn in *; discriminate).
      destruct (IH2 ltac:(assumption) N2) as [n [v Hv]].
      exists (2 * n + 1), v; spt_simp; exact Hv.
    + destruct (IH1 ltac:(assumption) N1) as [n [v Hv]].
      exists (2 * n + 2), v; spt_simp; exact Hv.
  - exists 0, a; reflexivity.
Qed.

Lemma all_None_LN t : wf t -> (forall n, lookup n t = None) -> t = LN.
Proof.
  intros W H; destruct t; [reflexivity|..]; exfalso;
    destruct (wf_nonempty _ W ltac:(discriminate)) as [n [v Hv]]; congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_empty" *)
Theorem domain_empty : forall t, wf t -> (t = LN <-> domain t = (fun _ => False)).
Proof.
  intros t W; split; [intros ->; reflexivity|intros D].
  apply all_None_LN; [exact W|]. intros n.
  apply lookup_NONE_domain; rewrite D; tauto.
Qed.

Lemma lookup_split t1 t2 : (forall n, lookup n t1 = lookup n t2) ->
  spt_center t1 = spt_center t2 /\
  (forall n, lookup n (spt_left t1) = lookup n (spt_left t2)) /\
  (forall n, lookup n (spt_right t1) = lookup n (spt_right t2)).
Proof.
  intros H; split; [rewrite <- !lookup_0; auto|split; intros n];
    [rewrite <- !lookup_2|rewrite <- !lookup_1]; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spt_eq_thm" *)
Theorem spt_eq_thm : forall t1 t2, wf t1 /\ wf t2 -> (t1 = t2 <-> forall n, lookup n t1 = lookup n t2).
Proof.
  induction t1 as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros t2 [W1 W2];
    (split; [intros ->; reflexivity|intros H]).
  1: { symmetry; apply all_None_LN; [exact W2|]. intros n; rewrite <- H; reflexivity. }
  all: destruct (lookup_split _ _ H) as (C & L & R).
  all: pose proof (wf_left _ W2) as WL; pose proof (wf_right _ W2) as WR.
  all: destruct t2 as [|b|v1 v2|v1 b v2]; cbn [spt_center spt_left spt_right] in C, L, R, WL, WR;
    try discriminate.
  all: try (exfalso; specialize (H 0); cbn [lookup] in H; dec; discriminate).
  - injection C as ->; reflexivity.
  - cbn [wf] in W2; bsplit.
    rewrite (all_None_LN v1 WL (fun n => eq_sym (L n))),
            (all_None_LN v2 WR (fun n => eq_sym (R n))) in *; discriminate.
  - exfalso; enough (E : BN u1 u2 = LN) by discriminate.
    apply all_None_LN; [exact W1|intros n; rewrite H; reflexivity].
  - cbn [wf] in W1; bsplit. f_equal; [apply IH1|apply IH2]; auto.
  - pose proof (wf_left _ W1) as WL1; pose proof (wf_right _ W1) as WR1.
    cbn [spt_left spt_right] in WL1, WR1; cbn [wf] in W1; bsplit.
    rewrite (all_None_LN u1 WL1 L), (all_None_LN u2 WR1 R) in *; discriminate.
  - cbn [wf] in W1; bsplit. injection C as ->. f_equal; [apply IH1|apply IH2]; auto.
Qed.

End Foldi2.

(** ** [mk_wf], [union], [inter], [fromAList], [map] *)

Section MkWf.
Context {A : Type}.
Implicit Types (t : spt A).

Lemma mk_BN_thm t1 t2 : mk_BN t1 t2 = if isEmpty t1 && isEmpty t2 then LN else BN t1 t2.
Proof. destruct t1, t2; reflexivity. Qed.

Lemma mk_BS_thm t1 x t2 : mk_BS t1 x t2 = if isEmpty t1 && isEmpty t2 then LS x else BS t1 x t2.
Proof. destruct t1, t2; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_mk_wf" *)
Theorem wf_mk_wf : forall t, wf (mk_wf t).
Proof.
  induction t; cbn [mk_wf]; rewrite ?wf_mk_BN_eq, ?wf_mk_BS_eq; bsplit; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_mk_id" *)
Theorem wf_mk_id : forall t, wf t -> mk_wf t = t.
Proof.
  induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros W; cbn [mk_wf wf] in *; bsplit;
    try reflexivity; rewrite IH1, IH2 by assumption;
    rewrite ?mk_BN_thm, ?mk_BS_thm; match goal with H : _ = false |- _ => rewrite H end;
    reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_mk_wf" *)
Theorem lookup_mk_wf : forall x t, lookup x (mk_wf t) = lookup x t.
Proof.
  intros x t; revert x; induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros x;
    bitcase x; cbn [mk_wf]; spt_simp; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_mk_wf" *)
Theorem domain_mk_wf : forall t, domain (mk_wf t) = domain t.
Proof.
  intros t; apply set_ext; intros x; rewrite !domain_lookup, lookup_mk_wf; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mk_wf_eq" *)
Theorem mk_wf_eq : forall t1 t2, mk_wf t1 = mk_wf t2 <-> forall x, lookup x t1 = lookup x t2.
Proof.
  intros t1 t2; rewrite spt_eq_thm by (split; apply wf_mk_wf).
  setoid_rewrite lookup_mk_wf; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_eq" 1323 *)
Theorem inter_eq_thm : forall {B C} t1 (t2 : spt B) t3 (t4 : spt C),
  inter t1 t2 = inter t3 t4 <-> forall x, lookup x (inter t1 t2) = lookup x (inter t3 t4).
Proof. intros; apply spt_eq_thm; split; apply wf_inter. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_mk_wf" *)
Theorem union_mk_wf : forall t1 t2, union (mk_wf t1) (mk_wf t2) = mk_wf (union t1 t2).
Proof.
  intros t1 t2; apply spt_eq_thm; [split; [apply wf_union; split|]; apply wf_mk_wf|].
  intros n; rewrite lookup_mk_wf, !lookup_union, !lookup_mk_wf; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_mk_wf" *)
Theorem insert_mk_wf : forall x (v : A) t, insert x v (mk_wf t) = mk_wf (insert x v t).
Proof.
  intros x v t; apply spt_eq_thm; [split; [apply wf_insert|]; apply wf_mk_wf|].
  intros n; rewrite lookup_mk_wf, !lookup_insert, lookup_mk_wf; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "delete_mk_wf" *)
Theorem delete_mk_wf : forall x t, delete x (mk_wf t) = mk_wf (delete x t).
Proof.
  intros x t; apply spt_eq_thm; [split; [apply wf_delete|]; apply wf_mk_wf|].
  intros n; rewrite lookup_mk_wf, !lookup_delete, lookup_mk_wf; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_LN" *)
Theorem union_LN : forall t, union t LN = t /\ union LN t = t.
Proof. intros []; split; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_LN" *)
Theorem inter_LN : forall {B C} t, inter t (@LN B) = LN /\ inter (@LN C) t = LN.
Proof. intros B C []; split; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_assoc" *)
Theorem union_assoc : forall t1 t2 t3, union t1 (union t2 t3) = union (union t1 t2) t3.
Proof.
  induction t1 as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros [] []; cbn [union];
    rewrite ?IH1, ?IH2; reflexivity.
Qed.

End MkWf.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_mk_wf" *)
Theorem inter_mk_wf : forall {A B} (t1 : spt A) (t2 : spt B), inter (mk_wf t1) (mk_wf t2) = mk_wf (inter t1 t2).
Proof.
  intros A B t1 t2; apply spt_eq_thm; [split; [apply wf_inter|apply wf_mk_wf]|].
  intros n; rewrite lookup_mk_wf. rewrite (lookup_inter (mk_wf t1)), lookup_inter, !lookup_mk_wf.
  reflexivity.
Qed.


(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_assoc" *)
Theorem inter_assoc : forall {A B C} (t1 : spt A) (t2 : spt B) (t3 : spt C),
  inter t1 (inter t2 t3) = inter (inter t1 t2) t3.
Proof.
  intros A B C t1 t2 t3; apply spt_eq_thm; [split; apply wf_inter|].
  intros n; apply lookup_inter_assoc.
Qed.

Section FromAList.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_union" *)
Theorem insert_union : forall k (v : A) s, insert k v s = union (insert k v LN) s.
Proof.
  intros k; induction k as [|k IH|k IH] using bit_induction; intros v s;
    destruct s; spt_simp; cbn [union]; rewrite <- ?IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_fromAList" *)
Theorem lookup_fromAList : forall (ls : list (N * A)) x, lookup x (fromAList ls) = ALOOKUP ls x.
Proof.
  induction ls as [|[k v] ls IH]; intros x; [reflexivity|].
  cbn [fromAList ALOOKUP]; rewrite lookup_insert, IH; dec; subst; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_fromAList" *)
Theorem domain_fromAList : forall (ls : list (N * A)),
  domain (fromAList ls) = (fun x => MEM x (MAP fst ls)).
Proof.
  intros ls; apply set_ext; intros x; rewrite domain_lookup, lookup_fromAList.
  unfold is_true; rewrite MEM_In. induction ls as [|[k v] ls IH]; cbn [ALOOKUP List.map In fst].
  - split; [intros [v H]; discriminate|tauto].
  - dec; subst.
    + split; [tauto|eauto].
    + rewrite IH; split; [tauto|intros [E|H]; [congruence|exact H]].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_fromAList_toAList" *)
Theorem lookup_fromAList_toAList : forall t x, lookup x (fromAList (toAList t)) = lookup x t.
Proof. intros t x; rewrite lookup_fromAList, ALOOKUP_toAList; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_fromAList" *)
Theorem wf_fromAList : forall (ls : list (N * A)), wf (fromAList ls).
Proof.
  induction ls as [|[k v] ls IH]; [reflexivity|]. cbn [fromAList]; apply wf_insert, IH.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "fromAList_toAList" *)
Theorem fromAList_toAList : forall t, wf t -> fromAList (toAList t) = t.
Proof.
  intros t W; apply spt_eq_thm; [split; [apply wf_fromAList|exact W]|].
  intros n; apply lookup_fromAList_toAList.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_insert_LN" *)
Theorem union_insert_LN : forall x (y : A) t2, union (insert x y LN) t2 = insert x y t2.
Proof. intros; symmetry; apply insert_union. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "fromAList_append" *)
Theorem fromAList_append : forall (l1 l2 : list (N * A)),
  fromAList (l1 ++ l2) = union (fromAList l1) (fromAList l2).
Proof.
  induction l1 as [|[k v] l1 IH]; intros l2; [reflexivity|].
  cbn [app fromAList]. rewrite IH, insert_union, (insert_union k v (fromAList l1)), union_assoc.
  reflexivity.
Qed.

End FromAList.

Section Map.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "toList_map" *)
Theorem toList_map : forall {B} (f : A -> B) s, toList (map f s) = MAP f (toList s).
Proof.
  intros B f s; unfold toList.
  induction s as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; cbn [map toListA]; [reflexivity|reflexivity|..].
  - rewrite (toListA_append (map f t1)), (toListA_append t1), IH1, IH2, map_app; reflexivity.
  - rewrite (toListA_append (map f t1)), (toListA_append t1), IH1, IH2, map_app; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_map" *)
Theorem lookup_map : forall {B} (f : A -> B) s x, lookup x (map f s) = option_map f (lookup x s).
Proof.
  intros B f; induction s as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros x;
    bitcase x; cbn [map]; spt_simp; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_map" *)
Theorem domain_map : forall {B} (f : A -> B) s, domain (map f s) = domain s.
Proof.
  intros B f s; apply set_ext; intros x; rewrite !domain_lookup, lookup_map.
  destruct (lookup x s); cbn; split; intros [v H]; eauto; discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_LN" *)
Theorem map_LN : forall {B} (f : A -> B) t, map f t = LN <-> t = LN.
Proof. intros B f []; cbn; split; congruence. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_map" *)
Theorem wf_map : forall {B} t (f : A -> B), wf (map f t) = wf t.
Proof.
  intros B; induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros f; cbn [map wf];
    rewrite ?IH1, ?IH2; try reflexivity; destruct t1, t2; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_map_o" *)
Theorem map_map_o : forall {B C} t (f : B -> C) (g : A -> B), map f (map g t) = map (f ∘ g) t.
Proof.
  intros B C; induction t as [|a|t1 IH1 t2 IH2|t1 IH1 a t2 IH2]; intros f g; cbn [map];
    rewrite ?IH1, ?IH2; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_insert" *)
Theorem map_insert : forall {B} (f : A -> B) x y z, map f (insert x y z) = insert x (f y) (map f z).
Proof.
  intros B f x; induction x as [|x IH|x IH] using bit_induction; intros y z;
    destruct z; spt_simp; cbn [map]; rewrite ?IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_fromAList" *)
Theorem map_fromAList : forall {B} (f : A -> B) ls,
  map f (fromAList ls) = fromAList (MAP (fun '(k, v) => (k, f v)) ls).
Proof.
  intros B f; induction ls as [|[k v] ls IH]; [reflexivity|].
  cbn [fromAList List.map]; rewrite map_insert, IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_insert" *)
Theorem insert_insert : forall x1 x2 (v1 v2 : A) t,
  insert x1 v1 (insert x2 v2 t) =
  if decide (x1 = x2) then insert x1 v1 t else insert x2 v2 (insert x1 v1 t).
Proof.
  intros x1; induction x1 as [|x1 IH|x1 IH] using bit_induction; intros x2 v1 v2 t;
    bitcase x2; destruct t; spt_simp; rewrite ?IH; dec; subst; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_shadow" *)
Theorem insert_shadow : forall t a (b c : A), insert a b (insert a c t) = insert a b t.
Proof. intros; rewrite insert_insert; dec; reflexivity. Qed.

End Map.

(** ** Sub-maps, filtering and miscellaneous theorems *)

Section Misc.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_lookup" *)
Theorem subspt_lookup : forall `{EqDecision A} (t1 t2 : spt A),
  subspt t1 t2 <-> forall x y, lookup x t1 = Some y -> lookup x t2 = Some y.
Proof.
  intros EA; induction t1 as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros t2; cbn [subspt];
    unfold is_true in *.
  - split; [intros _ x y H; discriminate|reflexivity].
  - rewrite bool_decide_spec. split.
    + intros C x y H. bitcase x; spt_simp; try discriminate. congruence.
    + intros H. rewrite <- lookup_0. apply H. rewrite lookup_0; reflexivity.
  - rewrite andb_true_iff, IH1, IH2. split.
    + intros [L R] x y H; bitcase x; spt_simp; try discriminate; auto.
    + intros H; split; intros x y Hx;
        [specialize (H (2 * x + 2) y)|specialize (H (2 * x + 1) y)]; spt_simp; auto.
  - rewrite !andb_true_iff, bool_decide_spec, IH1, IH2. split.
    + intros [C [L R]] x y H; bitcase x; spt_simp; try congruence; auto.
    + intros H; split; [|split].
      * rewrite <- lookup_0. apply H. rewrite lookup_0; reflexivity.
      * intros x y Hx; specialize (H (2 * x + 2) y); spt_simp; auto.
      * intros x y Hx; specialize (H (2 * x + 1) y); spt_simp; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_def" *)
Theorem subspt_def : forall `{EqDecision A} (sp1 sp2 : spt A),
  subspt sp1 sp2 <-> forall k, domain sp1 k -> domain sp2 k /\ lookup k sp2 = lookup k sp1.
Proof.
  intros EA sp1 sp2; rewrite subspt_lookup. setoid_rewrite domain_lookup. split.
  - intros H k [v Hv]. rewrite Hv, (H _ _ Hv). eauto.
  - intros H x y Hx. destruct (H x (ex_intro _ y Hx)) as [_ E]. congruence.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_refl" *)
Theorem subspt_refl : forall `{EqDecision A} (sp : spt A), subspt sp sp.
Proof. intros EA sp; apply subspt_lookup; auto. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_trans" *)
Theorem subspt_trans : forall `{EqDecision A} (sp1 sp2 sp3 : spt A),
  subspt sp1 sp2 /\ subspt sp2 sp3 -> subspt sp1 sp3.
Proof. intros EA sp1 sp2 sp3; rewrite !subspt_lookup; firstorder. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_LN" *)
Theorem subspt_LN : forall `{EqDecision A} (sp : spt A),
  (subspt LN sp <-> True) /\ (subspt sp LN <-> domain sp = (fun _ => False)).
Proof.
  intros EA sp; split; [cbn; split; auto|].
  rewrite subspt_lookup; split.
  - intros H; apply set_ext; intros x; rewrite domain_lookup; split; [|tauto].
    intros [v Hv]; apply H in Hv; discriminate.
  - intros D x y Hx. assert (Dx : domain sp x) by (apply domain_lookup; eauto).
    rewrite D in Dx; contradiction.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_union" *)
Theorem subspt_union : forall `{EqDecision A} (s t : spt A), subspt s (union s t).
Proof. intros EA s t; apply subspt_lookup; intros x y H; rewrite lookup_union, H; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_FOLDL_union" *)
Theorem subspt_FOLDL_union : forall `{EqDecision A} ls (t : spt A), subspt t (FOLDL union t ls).
Proof.
  intros EA ls; induction ls as [|t' ls IH]; intros t; cbn [FOLDL]; [apply subspt_refl|].
  apply (subspt_trans _ (union t t')); split; [apply subspt_union|apply IH].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_mapi" *)
Theorem domain_mapi : forall {B} (f : N -> A -> B) x, domain (mapi f x) = domain x.
Proof.
  intros B f x; apply set_ext; intros k; rewrite !domain_lookup, lookup_mapi.
  destruct (lookup k x); cbn; split; intros [v H]; eauto; discriminate.
Qed.

(** HOL [OPTION_CHOICE] is written out (its theory is not imported here). *)
(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_FOLDL_union" *)
Theorem lookup_FOLDL_union : forall k (t : spt A) ls,
  lookup k (FOLDL union t ls) =
  FOLDL (fun m1 m2 => match m1 with None => m2 | Some x => Some x end)
    (lookup k t) (MAP (lookup k) ls).
Proof.
  intros k t ls; revert t; induction ls as [|t' ls IH]; intros t; cbn [FOLDL List.map];
    [reflexivity|]. rewrite IH, lookup_union; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_union" *)
Theorem map_union : forall {B} (f : A -> B) t1 t2, map f (union t1 t2) = union (map f t1) (map f t2).
Proof.
  intros B f; induction t1 as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros t2;
    [reflexivity|..]; destruct t2; cbn [union map]; rewrite ?IH1, ?IH2; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_eq" *)
Theorem domain_eq : forall {B} t1 (t2 : spt B),
  domain t1 = domain t2 <-> forall k, lookup k t1 = None <-> lookup k t2 = None.
Proof.
  intros B t1 t2; split.
  - intros D k; rewrite !lookup_NONE_domain, D; reflexivity.
  - intros H; apply set_ext; intros k. specialize (H k).
    rewrite !domain_lookup, !ex_Some_iff; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_filter_v" *)
Theorem lookup_filter_v : forall k t (f : A -> bool),
  lookup k (filter_v f t) =
  match lookup k t with Some v => if f v then Some v else None | None => None end.
Proof.
  intros k t f; revert k; induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros k;
    cbn [filter_v]; [reflexivity|..];
    repeat match goal with |- context [if f ?a then _ else _] => destruct (f a) eqn:? end;
    bitcase k; spt_simp; rewrite ?IH1, ?IH2;
    repeat match goal with H : f ?a = _ |- context [f ?a] => rewrite H end; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_filter_v" *)
Theorem wf_filter_v : forall t (f : A -> bool), wf t -> wf (filter_v f t).
Proof.
  induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros f W; cbn [filter_v wf] in *;
    try destruct (f a); try reflexivity; rewrite ?wf_mk_BN_eq, ?wf_mk_BS_eq; bsplit; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_mk_BN" 1832 *)
Theorem wf_mk_BN : forall t1 t2, wf t1 /\ wf t2 -> wf (mk_BN t1 t2).
Proof. intros t1 t2 [W1 W2]; rewrite wf_mk_BN_eq; bsplit; auto. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_mk_BS" 1838 *)
Theorem wf_mk_BS : forall t1 (a : A) t2, wf t1 /\ wf t2 -> wf (mk_BS t1 a t2).
Proof. intros t1 a t2 [W1 W2]; rewrite wf_mk_BS_eq; bsplit; auto. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_mapi" *)
Theorem wf_mapi : forall {B} (f : N -> A -> B) pt, wf (mapi f pt).
Proof.
  intros B f pt; unfold mapi; generalize 0.
  induction pt as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros n; cbn [mapi0];
    rewrite ?wf_mk_BN_eq, ?wf_mk_BS_eq; bsplit; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_mk_BN" 1859 *)
Theorem lookup_mk_BN : forall i t1 t2,
  lookup i (mk_BN t1 t2) =
  if decide (i = 0) then None else lookup ((i - 1) DIV 2) (if EVEN i then t1 else t2).
Proof. intros; rewrite lookup_mk_BN_BN; reflexivity. Qed.

Lemma ALOOKUP_MAP_lemma {B} (f : N -> A -> B) (al : list (N * A)) n :
  ALOOKUP (MAP (fun kv => (fst kv, f (fst kv) (snd kv))) al) n =
  option_map (fun v => f n v) (ALOOKUP al n).
Proof.
  induction al as [|[k v] al IH]; [reflexivity|]. cbn [List.map ALOOKUP fst snd].
  destruct (decide (k = n)); [subst; reflexivity|exact IH].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "mapi_Alist" *)
Theorem mapi_Alist : forall {B} (f : N -> A -> B) pt,
  mapi f pt = fromAList (MAP (fun kv => (fst kv, f (fst kv) (snd kv))) (toAList pt)).
Proof.
  intros B f pt; apply spt_eq_thm; [split; [apply wf_mapi|apply wf_fromAList]|].
  intros n; rewrite lookup_fromAList, ALOOKUP_MAP_lemma, ALOOKUP_toAList, lookup_mapi; reflexivity.
Qed.

End Misc.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "subspt_domain" *)
Theorem subspt_domain : forall (t1 t2 : num_set), subspt t1 t2 <-> (forall x, domain t1 x -> domain t2 x).
Proof.
  intros t1 t2; rewrite subspt_lookup. setoid_rewrite domain_lookup. split.
  - intros H x [[] Hx]; eauto.
  - intros H x [] Hx. destruct (H x (ex_intro _ tt Hx)) as [[] Hy]; exact Hy.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "num_set_domain_eq" *)
Theorem num_set_domain_eq : forall (t1 t2 : num_set), wf t1 /\ wf t2 -> (domain t1 = domain t2 <-> t1 = t2).
Proof.
  intros t1 t2 W; rewrite (spt_eq_thm _ _ W). split; [|intros H; apply set_ext; intros x;
    rewrite !domain_lookup, H; reflexivity].
  intros D n. assert (E : domain t1 n <-> domain t2 n) by (rewrite D; reflexivity).
  rewrite !domain_lookup in E. destruct (lookup n t1) as [[]|], (lookup n t2) as [[]|];
    try reflexivity; exfalso.
  - destruct (proj1 E (ex_intro _ tt eq_refl)); discriminate.
  - destruct (proj2 E (ex_intro _ tt eq_refl)); discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_num_set_sym" *)
Theorem union_num_set_sym : forall (t1 t2 : num_set), union t1 t2 = union t2 t1.
Proof.
  induction t1 as [|[]|u1 IH1 u2 IH2|u1 IH1 [] u2 IH2]; intros [|[]|v1 v2|v1 [] v2]; cbn [union];
    rewrite ?IH1, ?IH2; reflexivity.
Qed.

Section Misc2.
Context {A : Type}.
Implicit Types (t : spt A).

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "union_disjoint_sym" *)
Theorem union_disjoint_sym : forall t1 t2,
  wf t1 /\ wf t2 /\ (fun x => domain t1 x /\ domain t2 x) = (fun _ => False) ->
  union t1 t2 = union t2 t1.
Proof.
  intros t1 t2 (W1 & W2 & D). apply spt_eq_thm; [split; apply wf_union; auto|].
  intros n. rewrite !lookup_union.
  assert (Dn : ~ (domain t1 n /\ domain t2 n)).
  { intros H. pose proof (f_equal (fun s => s n) D) as E; cbn beta in E. rewrite E in H; exact H. }
  rewrite !domain_lookup in Dn.
  destruct (lookup n t1), (lookup n t2); try reflexivity. exfalso; eauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "difference_sub" *)
Theorem difference_sub : forall {B} t1 (t2 : spt B),
  difference t1 t2 = LN -> (forall x, domain t1 x -> domain t2 x).
Proof.
  intros B a b E x Dx. apply (f_equal domain) in E. rewrite domain_difference in E.
  destruct (decide (domain b x)) as [|ND]; [assumption|].
  assert (H : domain a x /\ ~ domain b x) by auto.
  pose proof (f_equal (fun s => s x) E) as E'; cbn beta in E'. rewrite E' in H.
  cbn [domain] in H; contradiction.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_difference" *)
Theorem wf_difference : forall {B} t1 (t2 : spt B), wf t1 /\ wf t2 -> wf (difference t1 t2).
Proof.
  intros B; induction t1 as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros t2 [W1 W2];
    [reflexivity|..]; destruct t2; cbn [difference wf] in *;
    rewrite ?wf_mk_BN_eq, ?wf_mk_BS_eq; bsplit; auto; try reflexivity;
    first [apply IH1 | apply IH2]; cbn [wf]; bsplit; auto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "delete_fail" *)
Theorem delete_fail : forall n t, wf t -> (~ domain t n <-> delete n t = t).
Proof.
  intros n t W; rewrite (spt_eq_thm _ _ (conj (wf_delete t n W) W)), <- lookup_NONE_domain.
  split.
  - intros H k; rewrite lookup_delete; dec; subst; auto.
  - intros H; rewrite <- (H n), lookup_delete; dec; reflexivity.
Qed.

Lemma size_mk_BN t1 t2 : size (mk_BN t1 t2) = size t1 + size t2.
Proof. destruct t1, t2; reflexivity. Qed.

Lemma size_mk_BS t1 (a : A) t2 : size (mk_BS t1 a t2) = size t1 + size t2 + 1.
Proof. destruct t1, t2; reflexivity. Qed.

Lemma lookup_size k t v : lookup k t = Some v -> 0 < size t.
Proof.
  revert k; induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros k H; cbn [size];
    [discriminate|lia|..|lia]. bitcase k; spt_simp; [discriminate|..].
  - specialize (IH2 _ H); lia.
  - specialize (IH1 _ H); lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_delete" *)
Theorem size_delete : forall n t,
  size (delete n t) = if decide (lookup n t = None) then size t else size t - 1.
Proof.
  intros n t; revert n; induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros n;
    bitcase n; spt_simp; cbn [size]; rewrite ?size_mk_BN, ?size_mk_BS, ?IH1, ?IH2;
    repeat match goal with |- context [decide ?P] => destruct (decide P) as [E|E] end;
    cbn [size] in *; try congruence; try lia;
    match goal with E : lookup ?k ?u <> None |- _ =>
      destruct (lookup k u) eqn:L; [apply lookup_size in L|congruence] end; lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_fromList_outside" *)
Theorem lookup_fromList_outside : forall (args : list A) k,
  LENGTH args <= k -> lookup k (fromList args) = None.
Proof.
  intros args k H; apply lookup_NONE_domain; rewrite domain_fromList; lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "inter_eq_LN" *)
Theorem inter_eq_LN : forall {B} (x : spt A) (y : spt B),
  inter x y = LN <-> (fun z => domain x z /\ domain y z) = (fun _ => False).
Proof.
  intros B x y; rewrite <- (domain_inter x y); split; [intros ->; reflexivity|intros D].
  apply all_None_LN; [apply wf_inter|]. intros n; apply lookup_NONE_domain; rewrite D; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "map_map_K" *)
Theorem map_map_K : forall {B C} (a : C) (f : A -> B) t,
  map (fun _ => a) (map f t) = map (fun _ => a) t.
Proof.
  intros B C a f; induction t as [|x|u1 IH1 u2 IH2|u1 IH1 x u2 IH2]; cbn [map];
    rewrite ?IH1, ?IH2; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_map_K" *)
Theorem lookup_map_K : forall {B} (x : B) t n,
  lookup n (map (fun _ => x) t) = if decide (domain t n) then Some x else None.
Proof.
  intros B x t n; rewrite lookup_map. destruct (decide (domain t n)) as [D|D].
  - apply domain_lookup in D as [v ->]; reflexivity.
  - apply lookup_NONE_domain in D as ->; reflexivity.
Qed.

Lemma LENGTH_cons_inj {X Y} (x : X) (y : Y) xs ys :
  LENGTH (x :: xs) = LENGTH (y :: ys) -> LENGTH xs = LENGTH ys.
Proof. cbn [LENGTH]; lia. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_alist_insert" *)
Theorem lookup_alist_insert : forall x (y : list A) t z,
  LENGTH x = LENGTH y ->
  lookup z (alist_insert x y t) =
  match ALOOKUP (ZIP (x, y)) z with Some a => Some a | None => lookup z t end.
Proof.
  induction x as [|k x IH]; intros [|v y] t z H; cbn [LENGTH] in H; try lia; [reflexivity|].
  cbn [alist_insert]. rewrite lookup_insert, IH by lia.
  change (ZIP (k :: x, v :: y)) with ((k, v) :: ZIP (x, y)). cbn [ALOOKUP].
  dec; subst; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_alist_insert" *)
Theorem domain_alist_insert : forall a (b : list A) locs,
  LENGTH a = LENGTH b -> domain (alist_insert a b locs) = (fun x => domain locs x \/ MEM x a).
Proof.
  induction a as [|k a IH]; intros [|v b] locs H; cbn [LENGTH] in H; try lia.
  - apply set_ext; intros x; unfold is_true; cbn [MEM alist_insert]. split; [now left|intros [H1|H1]; [exact H1|discriminate]].
  - cbn [alist_insert]. rewrite domain_insert, IH by lia. apply set_ext; intros x.
    unfold is_true; cbn [MEM]. rewrite orb_true_iff, bool_decide_spec. tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "alist_insert_append" *)
Theorem alist_insert_append : forall a1 (a2 : list A) s b1 b2,
  LENGTH a1 = LENGTH a2 ->
  alist_insert (a1 ++ b1) (a2 ++ b2) s = alist_insert a1 a2 (alist_insert b1 b2 s).
Proof.
  induction a1 as [|k a1 IH]; intros [|v a2] s b1 b2 H; cbn [LENGTH] in H; try lia;
    [reflexivity|]. cbn [app alist_insert]. rewrite IH by lia; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_swap" *)
Theorem insert_swap : forall t a (b : A) c d,
  a <> c -> insert a b (insert c d t) = insert c d (insert a b t).
Proof. intros t a b c d H; rewrite insert_insert; dec; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "alist_insert_pull_insert" *)
Theorem alist_insert_pull_insert : forall x (y : A) xs ys z,
  ~ MEM x xs -> alist_insert xs ys (insert x y z) = insert x y (alist_insert xs ys z).
Proof.
  intros x y; induction xs as [|k xs IH]; intros [|v ys] z H; try reflexivity.
  cbn [alist_insert]. unfold is_true in H; cbn [MEM] in H.
  rewrite orb_true_iff, bool_decide_spec in H.
  rewrite IH by tauto. apply insert_swap. intros ->; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "alist_insert_REVERSE" *)
Theorem alist_insert_REVERSE : forall xs (ys : list A) s,
  ALL_DISTINCT xs /\ LENGTH xs = LENGTH ys ->
  alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] s [D H]; cbn [LENGTH] in H; try lia; [reflexivity|].
  unfold is_true in D; cbn [ALL_DISTINCT] in D; apply andb_prop in D as [Dx D].
  cbn [List.rev]. rewrite alist_insert_append
    by (rewrite !LENGTH_length, !length_rev, <- !LENGTH_length; lia).
  cbn [alist_insert]. rewrite IH by (split; [exact D|lia]).
  apply alist_insert_pull_insert. intros M; unfold is_true in M; rewrite M in Dx; discriminate.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "insert_unchanged" *)
Theorem insert_unchanged : forall t x (y : A), lookup x t = Some y -> insert x y t = t.
Proof.
  intros t x; revert t; induction x as [|x IH|x IH] using bit_induction; intros t y H;
    destruct t; spt_simp; try discriminate; try congruence; rewrite IH; auto.
Qed.

Lemma size_0_iff t : size t = 0 <-> forall n, lookup n t = None.
Proof.
  induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; cbn [size].
  - split; auto.
  - split; [lia|intros H; specialize (H 0); discriminate].
  - split.
    + intros H n; bitcase n; spt_simp; [reflexivity|apply IH2|apply IH1]; lia.
    + intros H. assert (size u1 = 0) by (apply IH1; intros n; specialize (H (2 * n + 2)); spt_simp; auto).
      assert (size u2 = 0) by (apply IH2; intros n; specialize (H (2 * n + 1)); spt_simp; auto).
      lia.
  - split; [lia|intros H; specialize (H 0); discriminate].
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_zero_empty" *)
Theorem size_zero_empty : forall (x : spt A), size x = 0 <-> domain x = (fun _ => False).
Proof.
  intros x; rewrite size_0_iff; split.
  - intros H; apply set_ext; intros n; rewrite domain_lookup, H; split; [intros [v E]; discriminate|tauto].
  - intros D n; apply lookup_NONE_domain; rewrite D; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_map" *)
Theorem size_map : forall {B} (f : A -> B) t, size (map f t) = size t.
Proof.
  intros B f; induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; cbn [map size];
    rewrite ?IH1, ?IH2; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_0_spt_center" *)
Theorem lookup_0_spt_center : forall t, lookup 0 t = spt_center t.
Proof. exact lookup_0. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_spt_right" *)
Theorem lookup_spt_right : forall i t, lookup i (spt_right t) = lookup (i * 2 + 1) t.
Proof. intros i t; rewrite N.mul_comm, lookup_1; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_spt_left" *)
Theorem lookup_spt_left : forall i t, lookup i (spt_left t) = lookup (i * 2 + 2) t.
Proof. intros i t; rewrite N.mul_comm, lookup_2; reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "set_MAP_FST_toAList_domain" *)
Theorem set_MAP_FST_toAList_domain : forall t, (fun x => is_true (MEM x (MAP fst (toAList t)))) = domain t.
Proof.
  intros t; apply set_ext; intros x; unfold is_true; rewrite MEM_In, domain_lookup, in_map_iff.
  split.
  - intros [[k v] [<- H]]; exists v. apply ALOOKUP_toAList_In, H.
  - intros [v H]; exists (x, v); split; [reflexivity|apply ALOOKUP_toAList_In, H].
Qed.

Lemma FOLDL_fromList_inv (l : list A) : forall i t,
  wf t -> (forall x, domain t x -> x < i) ->
  wf (snd (FOLDL (fun '(i, t) a => (i + 1, insert i a t)) (i, t) l)) /\
  size (snd (FOLDL (fun '(i, t) a => (i + 1, insert i a t)) (i, t) l)) = size t + LENGTH l.
Proof.
  induction l as [|a l IH]; intros i t W D; cbn [FOLDL LENGTH snd]; [split; [exact W|lia]|].
  destruct (IH (i + 1) (insert i a t)) as [W' S'].
  - apply wf_insert, W.
  - intros x; rewrite domain_insert; intros [->|Dx]; [lia|specialize (D x Dx); lia].
  - split; [exact W'|]. rewrite S', size_insert. destruct (decide _) as [Di|]; [|lia].
    specialize (D i Di); lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_fromList" *)
Theorem wf_fromList : forall (ls : list A), wf (fromList ls).
Proof. intros ls; apply (FOLDL_fromList_inv ls 0 LN); [reflexivity|intros x []]. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_fromList" *)
Theorem size_fromList : forall (ls : list A), size (fromList ls) = LENGTH ls.
Proof. intros ls; apply (FOLDL_fromList_inv ls 0 LN); [reflexivity|intros x []]. Qed.

End Misc2.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "size_mapi" *)
Theorem size_mapi : forall {A B} (f : N -> A -> B) (t : spt A), size (mapi f t) = size t.
Proof.
  intros A B f t; unfold mapi; generalize 0.
  induction t as [|a|u1 IH1 u2 IH2|u1 IH1 a u2 IH2]; intros i; cbn [mapi0 size];
    rewrite ?size_mk_BN, ?size_mk_BS, ?IH1, ?IH2; reflexivity.
Qed.


(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_LN" *)
Theorem wf_LN : forall {A}, wf (@LN A).
Proof. reflexivity. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_list_to_num_set" *)
Theorem domain_list_to_num_set : forall x xs, domain (list_to_num_set xs) x <-> MEM x xs.
Proof.
  intros x; induction xs as [|n xs IH]; cbn [list_to_num_set]; unfold is_true in *; cbn [MEM].
  - split; [intros []|discriminate].
  - rewrite domain_insert, orb_true_iff, bool_decide_spec, IH; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_list_insert" *)
Theorem domain_list_insert : forall xs x t,
  domain (list_insert xs t) x <-> MEM x xs \/ domain t x.
Proof.
  induction xs as [|n xs IH]; intros x t; cbn [list_insert]; unfold is_true in *; cbn [MEM].
  - split; [tauto|intros [H|H]; [discriminate|exact H]].
  - rewrite IH, domain_insert, orb_true_iff, bool_decide_spec; tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "domain_FOLDR_delete" *)
Theorem domain_FOLDR_delete : forall {A} ls (live : spt A),
  domain (FOLDR delete live ls) = (fun x => domain live x /\ ~ MEM x ls).
Proof.
  intros A; induction ls as [|n ls IH]; intros live; apply set_ext; intros x;
    cbn [FOLDR]; unfold is_true; cbn [MEM].
  - split; [intros H; split; [exact H|discriminate]|tauto].
  - rewrite domain_delete, IH, orb_true_iff, bool_decide_spec. tauto.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "lookup_list_to_num_set" *)
Theorem lookup_list_to_num_set : forall x xs,
  lookup x (list_to_num_set xs) = if MEM x xs then Some tt else None.
Proof.
  intros x; induction xs as [|n xs IH]; [reflexivity|]. cbn [list_to_num_set MEM].
  rewrite lookup_insert, IH. unfold bool_decide. destruct (decide (x = n)); reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "list_to_num_set_append" *)
Theorem list_to_num_set_append : forall l1 l2,
  list_to_num_set (l1 ++ l2) = union (list_to_num_set l1) (list_to_num_set l2).
Proof.
  induction l1 as [|n l1 IH]; intros l2; [reflexivity|]. cbn [app list_to_num_set].
  rewrite IH, insert_union, (insert_union n tt (list_to_num_set l1)), union_assoc; reflexivity.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "wf_list_to_num_set" *)
Theorem wf_list_to_num_set : forall ls, wf (list_to_num_set ls).
Proof. induction ls; [reflexivity|]; apply wf_insert; assumption. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "gather_inclist_offsets_append" *)
Theorem gather_inclist_offsets_append : forall {A} (xs ys : list (N * A)),
  gather_inclist_offsets (xs ++ ys) =
  gather_inclist_offsets xs ++
  MAP (fun p => (SUM (MAP fst xs) + fst p, snd p)) (gather_inclist_offsets ys).
Proof.
  intros A; induction xs as [|[inc x] xs IH]; intros ys; cbn [app gather_inclist_offsets List.map SUM fst].
  - rewrite <- (map_id (gather_inclist_offsets ys)) at 1.
    apply map_ext; intros [k v]; cbn [fst snd]; f_equal; lia.
  - rewrite IH, map_app, !map_map. cbn [app]. f_equal. f_equal.
    apply map_ext; intros [k v]; cbn [fst snd]; f_equal; lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "MAP_SND_gather_inclist_offsets" *)
Theorem MAP_SND_gather_inclist_offsets : forall {A} (xs : list (N * A)),
  MAP snd (gather_inclist_offsets xs) = MAP snd xs.
Proof.
  intros A; induction xs as [|[inc x] xs IH]; [reflexivity|].
  cbn [gather_inclist_offsets List.map snd]. rewrite map_map; cbn [snd]. f_equal; exact IH.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "list_size_APPEND" *)
Theorem list_size_APPEND : forall {A} (f : A -> N) xs ys,
  list_size f (xs ++ ys) = list_size f xs + list_size f ys.
Proof. intros A f; induction xs as [|x xs IH]; intros ys; cbn [app list_size]; rewrite ?IH; lia. Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "SUM_MAP_same_LE" *)
Theorem SUM_MAP_same_LE : forall {A} (f g : A -> N) xs,
  EVERY (fun x => f x <=? g x) xs -> SUM (MAP f xs) <= SUM (MAP g xs).
Proof.
  intros A f g; induction xs as [|x xs IH]; intros H; cbn [SUM List.map]; [lia|].
  unfold is_true in *; cbn [EVERY] in H; apply andb_prop in H as [H1 H2].
  apply N.leb_le in H1; specialize (IH H2); lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "SUM_MAP_same_LESS" *)
Theorem SUM_MAP_same_LESS : forall {A} (f g : A -> N) xs,
  EVERY (fun x => f x <=? g x) xs /\ EXISTS (fun x => f x <? g x) xs ->
  SUM (MAP f xs) < SUM (MAP g xs).
Proof.
  intros A f g; induction xs as [|x xs IH]; intros [H E]; cbn [SUM List.map];
    unfold is_true in *; cbn [EVERY EXISTS] in *; [discriminate|].
  apply andb_prop in H as [H1 H2]. apply N.leb_le in H1.
  apply orb_true_iff in E as [E|E].
  - apply N.ltb_lt in E. pose proof (SUM_MAP_same_LE f g xs H2); lia.
  - specialize (IH (conj H2 E)); lia.
Qed.

(** ** [spts_to_alist] terminates (Galette) *)

Section SptsToAlist.
Context {A : Type}.

Lemma spts_measure_cons (p : N * spt A) l :
  spts_measure (p :: l) = Nat.add (spt_nodes (snd p)) (spts_measure l).
Proof. reflexivity. Qed.

Lemma spts_measure_app (l1 l2 : list (N * spt A)) :
  spts_measure (l1 ++ l2) = Nat.add (spts_measure l1) (spts_measure l2).
Proof.
  induction l1 as [|p l1 IH]; [reflexivity|].
  cbn [app]; rewrite !spts_measure_cons, IH; lia.
Qed.

Lemma spts_measure_rev (l : list (N * spt A)) : spts_measure (REVERSE l) = spts_measure l.
Proof.
  induction l as [|p l IH]; [reflexivity|].
  cbn [List.rev]; rewrite spts_measure_app, !spts_measure_cons, IH.
  change (spts_measure []) with O; lia.
Qed.

Lemma spts_measure_add_pause j (q : list (N * spt A)) :
  spts_measure (spts_to_alist_add_pause j q) = spts_measure q.
Proof. destruct q as [|[i t] q]; reflexivity. Qed.

Lemma spt_nodes_lr (t : spt A) :
  isEmpty t = false -> (Nat.add (spt_nodes (spt_left t)) (spt_nodes (spt_right t)) < spt_nodes t)%nat.
Proof. destruct t; cbn; intros; try discriminate; lia. Qed.

Lemma spts_to_alist_aux_measure (xs : list (N * spt A)) : forall i (acc : list (N * A)) ar al rep j ys acc2 rep2,
  spts_to_alist_aux i xs acc ar al rep = (j, (ys, (acc2, rep2))) ->
  (spts_measure ys <= spts_measure xs + spts_measure ar + spts_measure al)%nat /\
  (rep2 = true -> rep = false ->
   (spts_measure ys < spts_measure xs + spts_measure ar + spts_measure al)%nat).
Proof.
  induction xs as [|[j0 t] xs IH]; intros i acc ar al rep j ys acc2 rep2; cbn [spts_to_alist_aux].
  - intros E; injection E as <- <- <- <-. rewrite spts_measure_app, !spts_measure_rev.
    split; [cbn; lia|congruence].
  - rewrite spts_measure_cons; cbn [snd].
    destruct (isEmpty t) eqn:Et; intros E; apply IH in E as [E1 E2];
      rewrite ?spts_measure_add_pause, ?spts_measure_cons in *; cbn [snd] in *.
    + destruct t; try discriminate. cbn [spt_nodes] in *. split; [lia|].
      intros H1 H2; specialize (E2 H1 H2); lia.
    + pose proof (spt_nodes_lr t Et). split; [lia|intros _ _; lia].
Qed.

Lemma spts_to_alist_f_fuel : forall f1 f2 i xs (acc : list (N * A)),
  (spts_measure xs < f1)%nat -> (spts_measure xs < f2)%nat ->
  spts_to_alist_f f1 i xs acc = spts_to_alist_f f2 i xs acc.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] i xs acc H1 H2; try lia.
  cbn [spts_to_alist_f].
  destruct (spts_to_alist_aux i xs acc [] [] false) as [i' [xs' [acc' rep]]] eqn:E.
  destruct rep; [|reflexivity].
  apply spts_to_alist_aux_measure in E as [_ E]. specialize (E eq_refl eq_refl).
  cbn in E. apply IH; lia.
Qed.

(*! HOL "HOL/src/finite_maps/sptreeScript.sml" "spts_to_alist_def" *)
Theorem spts_to_alist_def : forall i xs (acc_cent : list (N * A)),
  spts_to_alist i xs acc_cent =
  let '(i, (xs, (acc_cent, repeat))) := spts_to_alist_aux i xs acc_cent [] [] false in
  if repeat then spts_to_alist i xs acc_cent else REVERSE acc_cent.
Proof.
  intros i xs acc; unfold spts_to_alist at 1; cbn [spts_to_alist_f].
  destruct (spts_to_alist_aux i xs acc [] [] false) as [i' [xs' [acc' rep]]] eqn:E.
  destruct rep; [|reflexivity]. unfold spts_to_alist.
  apply spts_to_alist_aux_measure in E as [_ E]. specialize (E eq_refl eq_refl). cbn in E.
  apply spts_to_alist_f_fuel; lia.
Qed.

End SptsToAlist.
