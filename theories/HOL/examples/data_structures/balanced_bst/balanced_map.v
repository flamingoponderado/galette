(** * HOL4 [balanced_map]: balanced binary search trees (Haskell's Data.Map)

    Port of [HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml],
    executable definitions only (the part used by the compiler, e.g.
    [word_cse]).  A comparison [cmp] is a function into [ordering]
    (HOL's [cpn]); HOL's [Less]/[Equal]/[Greater] (comparisonTheory
    overloads) are [LESS]/[EQUAL]/[GREATER].

    Names such as [lookup], [insert], [delete], [size], [empty], [map] are
    those of HOL's [balanced_map] theory and clash with sptree's; client
    files [Require] this module without importing it and write
    [balanced_map.lookup] etc.

    Not ported: the invariant/proof part of the script ([key_set],
    [invariant], [to_fmap], ...), the trimming/union/filter/split
    operations ([trim], [link], [hedgeUnion], [union], [filterWithKey],
    [splitLookup], [submap'], ...), and the [balanceL']/[balanceR']
    variants. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.sort Require Import ternaryComparisons.
Open Scope N_scope.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_map" *)
Inductive balanced_map (K V : Type) : Type :=
| Tip : balanced_map K V
| Bin : N -> K -> V -> balanced_map K V -> balanced_map K V -> balanced_map K V.
Arguments Tip {K V}.
Arguments Bin {K V} _ _ _ _ _.

#[global] Instance balanced_map_inhabited {K V} : Inhabited (balanced_map K V) := Tip.

#[global] Instance balanced_map_eq_dec {K V} `{EqDecision K} `{EqDecision V} :
  EqDecision (balanced_map K V).
Proof.
  intros x y; unfold Decision; decide equality; apply decide; exact _.
Defined.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "ratio_def" *)
Definition ratio : N := 2.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "delta_def" *)
Definition delta : N := 3.

Section Defs.
Context {K V : Type}.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "size_def" *)
Definition size (t : balanced_map K V) : N :=
  match t with Tip => 0 | Bin s k v l r => s end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "bin_def" *)
Definition bin (k : K) (x : V) (l r : balanced_map K V) : balanced_map K V :=
  Bin (size l + size r + 1) k x l r.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "null_def" *)
Definition null (t : balanced_map K V) : bool :=
  match t with Tip => true | Bin _ _ _ _ _ => false end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "lookup_def" *)
Fixpoint lookup (cmp : K -> K -> ordering) (k : K) (t : balanced_map K V) : option V :=
  match t with
  | Tip => None
  | Bin s k' v l r =>
      match cmp k k' with
      | LESS => lookup cmp k l
      | GREATER => lookup cmp k r
      | EQUAL => Some v
      end
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "member_def" *)
Fixpoint member (cmp : K -> K -> ordering) (k : K) (t : balanced_map K V) : bool :=
  match t with
  | Tip => false
  | Bin s k' v l r =>
      match cmp k k' with
      | LESS => member cmp k l
      | GREATER => member cmp k r
      | EQUAL => true
      end
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "empty_def" *)
Definition empty : balanced_map K V := Tip.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "singleton_def" *)
Definition singleton (k : K) (x : V) : balanced_map K V := Bin 1 k x Tip Tip.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceL_def" *)
Definition balanceL (k : K) (x : V) (l r : balanced_map K V) : balanced_map K V :=
  match l, r with
  | Tip, Tip => Bin 1 k x Tip Tip
  | Bin s' k' v' Tip Tip, Tip => Bin 2 k x (Bin s' k' v' Tip Tip) Tip
  | Bin _ lk lx Tip (Bin _ lrk lrx _ _), Tip =>
      Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
  | Bin _ lk lx (Bin s' k' v' l' r') Tip, Tip =>
      Bin 3 lk lx (Bin s' k' v' l' r') (Bin 1 k x Tip Tip)
  | Bin ls lk lx (Bin lls k' v' l' r') (Bin lrs lrk lrx lrl lrr), Tip =>
      if lrs <? ratio * lls then
        Bin (1 + ls) lk lx (Bin lls k' v' l' r')
                           (Bin (1 + lrs) k x (Bin lrs lrk lrx lrl lrr) Tip)
      else
        Bin (1 + ls) lrk lrx (Bin (1 + lls + size lrl) lk lx (Bin lls k' v' l' r') lrl)
                             (Bin (1 + size lrr) k x lrr Tip)
  | Tip, Bin rs k' v' l' r' => Bin (1 + rs) k x Tip (Bin rs k' v' l' r')
  | Bin ls lk lx ll lr, Bin rs k' v' l' r' =>
      if delta * rs <? ls then
        match ll, lr with
        | Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr =>
            if lrs <? ratio * lls then
              Bin (1 + ls + rs) lk lx ll (Bin (1 + rs + lrs) k x lr (Bin rs k' v' l' r'))
            else
              Bin (1 + ls + rs) lrk lrx (Bin (1 + lls + size lrl) lk lx ll lrl)
                                        (Bin (1 + rs + size lrr) k x lrr (Bin rs k' v' l' r'))
        | _, _ => Tip
        end
      else
        Bin (1 + ls + rs) k x (Bin ls lk lx ll lr) (Bin rs k' v' l' r')
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceR_def" *)
Definition balanceR (k : K) (x : V) (l r : balanced_map K V) : balanced_map K V :=
  match l, r with
  | Tip, Tip => Bin 1 k x Tip Tip
  | Tip, Bin s' k' v' Tip Tip => Bin 2 k x Tip (Bin s' k' v' Tip Tip)
  | Tip, Bin _ rk rx Tip (Bin s' k' v' l' r') =>
      Bin 3 rk rx (Bin 1 k x Tip Tip) (Bin s' k' v' l' r')
  | Tip, Bin _ rk rx (Bin _ rlk rlx _ _) Tip =>
      Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
  | Tip, Bin rs rk rx (Bin rls rlk rlx rll rlr) (Bin rrs k' v' l' r') =>
      if rls <? ratio * rrs then
        Bin (1 + rs) rk rx (Bin (1 + rls) k x Tip (Bin rls rlk rlx rll rlr)) (Bin rrs k' v' l' r')
      else
        Bin (1 + rs) rlk rlx (Bin (1 + size rll) k x Tip rll)
                             (Bin (1 + rrs + size rlr) rk rx rlr (Bin rrs k' v' l' r'))
  | Bin ls k' v' l' r', Tip => Bin (1 + ls) k x (Bin ls k' v' l' r') Tip
  | Bin ls k' v' l' r', Bin rs rk rx rl rr =>
      if delta * ls <? rs then
        match rl, rr with
        | Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _ =>
            if rls <? ratio * rrs then
              Bin (1 + ls + rs) rk rx (Bin (1 + ls + rls) k x (Bin ls k' v' l' r') rl) rr
            else
              Bin (1 + ls + rs) rlk rlx (Bin (1 + ls + size rll) k x (Bin ls k' v' l' r') rll)
                                        (Bin (1 + rrs + size rlr) rk rx rlr rr)
        | _, _ => Tip
        end
      else
        Bin (1 + ls + rs) k x (Bin ls k' v' l' r') (Bin rs rk rx rl rr)
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "insert_def" *)
Fixpoint insert (cmp : K -> K -> ordering) (k : K) (v : V) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Tip => singleton k v
  | Bin s k' v' l r =>
      match cmp k k' with
      | LESS => balanceL k' v' (insert cmp k v l) r
      | GREATER => balanceR k' v' l (insert cmp k v r)
      | EQUAL => Bin s k v l r
      end
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "insertR_def" *)
Fixpoint insertR (cmp : K -> K -> ordering) (k : K) (v : V) (t : balanced_map K V)
    : balanced_map K V :=
  match t with
  | Tip => singleton k v
  | Bin s k' v' l r =>
      match cmp k k' with
      | LESS => balanceL k' v' (insertR cmp k v l) r
      | GREATER => balanceR k' v' l (insertR cmp k v r)
      | EQUAL => Bin s k' v' l r
      end
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "insertMax_def" *)
Fixpoint insertMax (k : K) (v : V) (t : balanced_map K V) : balanced_map K V :=
  match t with
  | Tip => singleton k v
  | Bin s k' v' l r => balanceR k' v' l (insertMax k v r)
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "insertMin_def" *)
Fixpoint insertMin (k : K) (v : V) (t : balanced_map K V) : balanced_map K V :=
  match t with
  | Tip => singleton k v
  | Bin s k' v' l r => balanceL k' v' (insertMin k v l) r
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "deleteFindMax_def" *)
Fixpoint deleteFindMax `{Inhabited K} `{Inhabited V} (t : balanced_map K V)
    : (K * V) * balanced_map K V :=
  match t with
  | Bin s k x l Tip => ((k, x), l)
  | Bin s k x l r =>
      let '(km, r') := deleteFindMax r in (km, balanceL k x l r')
  | Tip => (ARB, Tip)
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "deleteFindMin_def" *)
Fixpoint deleteFindMin `{Inhabited K} `{Inhabited V} (t : balanced_map K V)
    : (K * V) * balanced_map K V :=
  match t with
  | Bin s k x Tip r => ((k, x), r)
  | Bin s k x l r =>
      let '(km, l') := deleteFindMin l in (km, balanceR k x l' r)
  | Tip => (ARB, Tip)
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "glue_def" *)
Definition glue `{Inhabited K} `{Inhabited V} (l r : balanced_map K V) : balanced_map K V :=
  match l, r with
  | Tip, r => r
  | l, Tip => l
  | l, r =>
      if size r <? size l then
        let '((km, m), l') := deleteFindMax l in balanceR km m l' r
      else
        let '((km, m), r') := deleteFindMin r in balanceL km m l r'
  end.

(** HOL's last case is the variable pattern [Eq] (a catch-all), i.e. the
    [EQUAL] case. *)
(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "delete_def" *)
Fixpoint delete `{Inhabited K} `{Inhabited V} (cmp : K -> K -> ordering) (k : K)
    (t : balanced_map K V) : balanced_map K V :=
  match t with
  | Tip => Tip
  | Bin s k' v l r =>
      match cmp k k' with
      | LESS => balanceR k' v (delete cmp k l) r
      | GREATER => balanceL k' v l (delete cmp k r)
      | _ => glue l r
      end
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "foldrWithKey_def" *)
Fixpoint foldrWithKey {B} (f : K -> V -> B -> B) (z' : B) (t : balanced_map K V) : B :=
  match t with
  | Tip => z'
  | Bin _ kx x l r => foldrWithKey f (f kx x (foldrWithKey f z' r)) l
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "toAscList_def" *)
Definition toAscList (t : balanced_map K V) : list (K * V) :=
  foldrWithKey (fun k x xs => (k, x) :: xs) [] t.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "mapWithKey_def" *)
Fixpoint mapWithKey {W} (f : K -> V -> W) (t : balanced_map K V) : balanced_map K W :=
  match t with
  | Tip => Tip
  | Bin sx kx x l r => Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)
  end.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "map_def" *)
Definition map {W} (f : V -> W) (t : balanced_map K V) : balanced_map K W :=
  mapWithKey (fun k x => f x) t.

(*! HOL "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "fromList_def" *)
Definition fromList (cmp : K -> K -> ordering) (l : list (K * V)) : balanced_map K V :=
  FOLDR (fun '(k, v) t => insert cmp k v t) empty l.

End Defs.
