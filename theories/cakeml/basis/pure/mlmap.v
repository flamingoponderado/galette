(** * CakeML [mlmap]: maps carrying their comparison function

    Port of [cakeml/basis/pure/mlmapScript.sml], executable definitions
    used by the compiler (the Pancake static checker), on top of
    [balanced_map].  [map K V] is HOL's [('a,'b) map]; its constructor
    [Map] pairs a comparison with a [balanced_map] tree.

    Names such as [lookup], [insert], [delete], [empty], [union],
    [member] clash with other theories; client files [Require] this module
    without importing it and write [mlmap.lookup] etc.

    Galette-local (pending addition to [balanced_map.v], which this file
    does not own): HOL's [balanced_map] union machinery ([trim_help_*],
    [trim], [link], [filterLt]/[filterGt] and their helpers, [hedgeUnion],
    [union], [hedgeUnionWithKey], [unionWithKey], [unionWith]) is not yet in
    [balanced_map.v].  The section [balanced_map_union] below transcribes
    those HOL definitions clause by clause (first-match order kept); they
    are untagged here because tags must live in the counterpart file
    ([HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml] ->
    [balanced_map.v]).  [link] recurses on either argument and is a nested
    structural [fix] (outer on the left tree, inner on the right one).

    Not ported: [map_def] (the function [map]; its name clashes with the
    type [map] and the compiler does not use it), [filter],
    [filterWithKey], [isSubmapBy], [isSubmap], [all], [exists], [compare]
    (need [balanced_map] definitions not yet ported), and the proof part
    ([map_ok], [to_fmap] and the theorems about them). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.sort Require Import ternaryComparisons.
From Galette.HOL.examples.data_structures.balanced_bst Require balanced_map.
Open Scope N_scope.


(** ** [balanced_map] union operations (Galette-local, see the header) *)

Module balanced_map_union.
Import balanced_map.

Section Defs.
Context {K V : Type}.

(** HOL [balanced_map$trim_help_greater]. *)
Fixpoint trim_help_greater (cmp : K -> K -> ordering) (lo : K) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Bin s' k v' l' r =>
      if decide (cmp k lo = LESS \/ cmp k lo = EQUAL) then trim_help_greater cmp lo r
      else Bin s' k v' l' r
  | Tip => Tip
  end.

(** HOL [balanced_map$trim_help_lesser]. *)
Fixpoint trim_help_lesser (cmp : K -> K -> ordering) (hi : K) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Bin s' k v' l r' =>
      if decide (cmp k hi = GREATER \/ cmp k hi = EQUAL) then trim_help_lesser cmp hi l
      else Bin s' k v' l r'
  | Tip => Tip
  end.

(** HOL [balanced_map$trim_help_middle]. *)
Fixpoint trim_help_middle (cmp : K -> K -> ordering) (lo hi : K) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Bin s' k v' l r =>
      if decide (cmp k lo = LESS \/ cmp k lo = EQUAL) then trim_help_middle cmp lo hi r
      else if decide (cmp k hi = GREATER \/ cmp k hi = EQUAL) then trim_help_middle cmp lo hi l
      else Bin s' k v' l r
  | Tip => Tip
  end.

(** HOL [balanced_map$trim]. *)
Definition trim (cmp : K -> K -> ordering) (lo hi : option K) (t : balanced_map K V)
    : balanced_map K V :=
  match lo, hi with
  | None, None => t
  | Some lk, None => trim_help_greater cmp lk t
  | None, Some hk => trim_help_lesser cmp hk t
  | Some lk, Some hk => trim_help_middle cmp lk hk t
  end.

(** HOL [balanced_map$link]. *)
Fixpoint link (k : K) (v : V) (l : balanced_map K V) {struct l}
    : balanced_map K V -> balanced_map K V :=
  fix link_r (r : balanced_map K V) : balanced_map K V :=
  match l, r with
  | Tip, r => insertMin k v r
  | l, Tip => insertMax k v l
  | Bin sizeL ky y ly ry, Bin sizeR kz z lz rz =>
      if delta * sizeL <? sizeR then
        balanceL kz z (link_r lz) rz
      else if delta * sizeR <? sizeL then
        balanceR ky y ly (link k v ry (Bin sizeR kz z lz rz))
      else
        bin k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz)
  end.

Lemma link_def (k : K) (v : V) l r :
  link k v l r =
  match l, r with
  | Tip, r => insertMin k v r
  | l, Tip => insertMax k v l
  | Bin sizeL ky y ly ry, Bin sizeR kz z lz rz =>
      if delta * sizeL <? sizeR then
        balanceL kz z (link k v (Bin sizeL ky y ly ry) lz) rz
      else if delta * sizeR <? sizeL then
        balanceR ky y ly (link k v ry (Bin sizeR kz z lz rz))
      else
        bin k v (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz)
  end.
Proof. destruct l, r; reflexivity. Qed.

(** HOL [balanced_map$filterLt_help]. *)
Fixpoint filterLt_help (cmp : K -> K -> ordering) (b' : K) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Tip => Tip
  | Bin s kx x l r =>
      match cmp kx b' with
      | LESS => link kx x l (filterLt_help cmp b' r)
      | EQUAL => l
      | GREATER => filterLt_help cmp b' l
      end
  end.

(** HOL [balanced_map$filterLt]. *)
Definition filterLt (cmp : K -> K -> ordering) (b : option K) (t : balanced_map K V)
    : balanced_map K V :=
  match b with None => t | Some b => filterLt_help cmp b t end.

(** HOL [balanced_map$filterGt_help]. *)
Fixpoint filterGt_help (cmp : K -> K -> ordering) (b' : K) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Tip => Tip
  | Bin s kx x l r =>
      match cmp b' kx with
      | LESS => link kx x (filterGt_help cmp b' l) r
      | EQUAL => r
      | GREATER => filterGt_help cmp b' r
      end
  end.

(** HOL [balanced_map$filterGt]. *)
Definition filterGt (cmp : K -> K -> ordering) (b : option K) (t : balanced_map K V)
    : balanced_map K V :=
  match b with None => t | Some b => filterGt_help cmp b t end.

(** HOL [balanced_map$hedgeUnion] (first-match clauses). *)
Fixpoint hedgeUnion (cmp : K -> K -> ordering) (blo bhi : option K)
    (t1 t2 : balanced_map K V) {struct t1} : balanced_map K V :=
  match t1, t2 with
  | t1, Tip => t1
  | Tip, Bin _ kx x l r => link kx x (filterGt cmp blo l) (filterLt cmp bhi r)
  | t1, Bin _ kx x Tip Tip => insertR cmp kx x t1
  | Bin s kx x l r, t2 =>
      link kx x (hedgeUnion cmp blo (Some kx) l (trim cmp blo (Some kx) t2))
                (hedgeUnion cmp (Some kx) bhi r (trim cmp (Some kx) bhi t2))
  end.

(** HOL [balanced_map$union]. *)
Definition union (cmp : K -> K -> ordering) (t1 t2 : balanced_map K V) : balanced_map K V :=
  match t1, t2 with
  | Tip, t2 => t2
  | t1, Tip => t1
  | t1, t2 => hedgeUnion cmp None None t1 t2
  end.

(** HOL [balanced_map$hedgeUnionWithKey] (first-match clauses). *)
Fixpoint hedgeUnionWithKey (cmp : K -> K -> ordering) (f : K -> V -> V -> V)
    (blo bhi : option K) (t1 t2 : balanced_map K V) {struct t1} : balanced_map K V :=
  match t1, t2 with
  | t1, Tip => t1
  | Tip, Bin _ kx x l r => link kx x (filterGt cmp blo l) (filterLt cmp bhi r)
  | Bin _ kx x l r, t2 =>
      let newx := match lookup cmp kx t2 with None => x | Some y => f kx x y end in
      link kx newx
        (hedgeUnionWithKey cmp f blo (Some kx) l (trim cmp blo (Some kx) t2))
        (hedgeUnionWithKey cmp f (Some kx) bhi r (trim cmp (Some kx) bhi t2))
  end.

(** HOL [balanced_map$unionWithKey]. *)
Definition unionWithKey (cmp : K -> K -> ordering) (f : K -> V -> V -> V)
    (t1 t2 : balanced_map K V) : balanced_map K V :=
  match t1, t2 with
  | Tip, t2 => t2
  | t1, Tip => t1
  | t1, t2 => hedgeUnionWithKey cmp f None None t1 t2
  end.

(** HOL [balanced_map$unionWith]. *)
Definition unionWith (cmp : K -> K -> ordering) (f : V -> V -> V)
    (t1 t2 : balanced_map K V) : balanced_map K V :=
  unionWithKey cmp (fun k x y => f x y) t1 t2.

End Defs.
End balanced_map_union.

(** ** The [map] type *)

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "map" 21 *)
Inductive map (K V : Type) : Type :=
| Map : (K -> K -> ordering) -> balanced_map.balanced_map K V -> map K V.
Arguments Map {K V} _ _.

Section Defs.
Context {K V : Type}.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "lookup_def" *)
Definition lookup (m : map K V) (k : K) : option V :=
  match m with Map cmp t => balanced_map.lookup cmp k t end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "insert_def" *)
Definition insert (m : map K V) (k : K) (v : V) : map K V :=
  match m with Map cmp t => Map cmp (balanced_map.insert cmp k v t) end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "delete_def" *)
Definition delete `{Inhabited K} `{Inhabited V} (m : map K V) (k : K) : map K V :=
  match m with Map cmp t => Map cmp (balanced_map.delete cmp k t) end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "null_def" *)
Definition null (m : map K V) : bool :=
  match m with Map cmp t => balanced_map.null t end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "size_def" *)
Definition size (m : map K V) : N :=
  match m with Map cmp t => balanced_map.size t end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "empty_def" *)
Definition empty (cmp : K -> K -> ordering) : map K V := Map cmp balanced_map.empty.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "union_def" *)
Definition union (m1 m2 : map K V) : map K V :=
  match m1, m2 with
  | Map cmp t1, Map _ t2 => Map cmp (balanced_map_union.union cmp t1 t2)
  end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "unionWith_def" *)
Definition unionWith (f : V -> V -> V) (m1 m2 : map K V) : map K V :=
  match m1, m2 with
  | Map cmp t1, Map _ t2 => Map cmp (balanced_map_union.unionWith cmp f t1 t2)
  end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "unionWithKey_def" *)
Definition unionWithKey (f : K -> V -> V -> V) (m1 m2 : map K V) : map K V :=
  match m1, m2 with
  | Map cmp t1, Map _ t2 => Map cmp (balanced_map_union.unionWithKey cmp f t1 t2)
  end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "foldrWithKey_def" *)
Definition foldrWithKey {B} (f : K -> V -> B -> B) (x : B) (m : map K V) : B :=
  match m with Map cmp t => balanced_map.foldrWithKey f x t end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "mapWithKey_def" *)
Definition mapWithKey {W} (f : K -> V -> W) (m : map K V) : map K W :=
  match m with Map cmp t => Map cmp (balanced_map.mapWithKey f t) end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "toAscList_def" *)
Definition toAscList (m : map K V) : list (K * V) :=
  match m with Map cmp t => balanced_map.toAscList t end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "fromList_def" *)
Definition fromList (cmp : K -> K -> ordering) (l : list (K * V)) : map K V :=
  Map cmp (balanced_map.fromList cmp l).

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "member_def" *)
Definition member (k : K) (m : map K V) : bool :=
  match m with Map cmp t => balanced_map.member cmp k t end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "singleton_def" *)
Definition singleton (cmp : K -> K -> ordering) (k : K) (v : V) : map K V :=
  Map cmp (balanced_map.singleton k v).

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "cmp_of_def" *)
Definition cmp_of (m : map K V) : K -> K -> ordering :=
  match m with Map cmp t => cmp end.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "cmp_of_insert" *)
Theorem cmp_of_insert : forall (t : map K V) k v, cmp_of (insert t k v) = cmp_of t.
Proof. intros [cmp t] k v; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "cmp_of_delete" *)
Theorem cmp_of_delete : forall `{Inhabited K} `{Inhabited V} (t : map K V) k,
  cmp_of (delete t k) = cmp_of t.
Proof. intros ? ? [cmp t] k; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlmapScript.sml" "cmp_of_empty" *)
Theorem cmp_of_empty : forall cmp, cmp_of (empty cmp : map K V) = cmp.
Proof. reflexivity. Qed.

End Defs.
