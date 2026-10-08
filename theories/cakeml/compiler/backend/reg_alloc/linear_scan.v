(** * CakeML [linear_scan]: a linear-scan register allocator

    A port of [compiler/backend/reg_alloc/linear_scanScript.sml]
    (definitions only; the commented-out translator section of the script is
    not ported).

    The monadic part runs in [M linear_scan_hidden_state A state_exn]
    (abbreviated [LSM A]); the exception type is [reg_alloc]'s [state_exn]
    (the script's own [state_exn] datatype is commented out in HOL).  As in [reg_alloc.v], the functions HOL generates
    with ML code are written out by hand with HOL's names and definitions,
    untagged: [get_f]/[set_f] for the fields of [linear_scan_hidden_state]
    ([define_monad_access_funs]); [raise_Fail], [raise_Subscript],
    [handle_Fail], [handle_Subscript] ([define_monad_exception_functions]);
    [f_length], [f_sub], [update_f] for the five array fields
    ([define_MFarray_manip_funs], raising [Subscript]); and the record
    [i_linear_scan_hidden_state] with [run_i_linear_scan_hidden_state]
    ([define_run]; its fields are prefixed with the record name because
    they would clash with [linear_scan_hidden_state]'s).

    [live_tree] has constructors [Branch]/[Seq] like [reg_alloc$clash_tree];
    the clash-tree constructors are written qualified ([reg_alloc.Branch]).
    HOL [option_CASE o d (\x. x)] is written as a [match].  HOL's [end]
    argument of [check_startlive_prop] is [end_] ([end] is a Rocq keyword).

    Recursion: [remove_inactive_intervals] (HOL: measure [LENGTH st.active])
    is computed by the structural [remove_inactive_intervals_aux] on
    [st.active]; [partition_regs], [sort_regs], [sorted_regs_to_list],
    [partition_moves], [sort_moves], [sorted_moves_to_list] use [Fix] on
    HOL's measures; [MAP_colors] recurses on [SUC n] with [num_rec].  HOL's
    equations are the tagged [_def] theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list numposrep.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From Stdlib Require Import Wellfounded.Inverse_Image.
Open Scope N_scope.
Open Scope monad_scope.

(** [<] on a measure into [N], guarded by [Acc_intro_generator] so that the
    [Fix]-based definitions also compute in the kernel. *)
Definition measure_wf {T} (f : T -> N) : well_founded (fun a b => f a < f b) :=
  Acc_intro_generator 32 (wf_inverse_image T N N.lt f N.lt_wf_0).
#[global] Opaque measure_wf.

(** [Fix_eq]'s side condition, for any functional. *)
Lemma Fix_F_ext {T} {R : T -> T -> Prop} {P : T -> Type}
    (F : forall x, (forall y, R y x -> P y) -> P x) :
  forall x f g, (forall y p, f y p = g y p) -> F x f = F x g.
Proof.
  intros x f g H; assert (f = g) as ->; [|reflexivity].
  do 2 (apply functional_extensionality_dep; intros); apply H.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "live_tree" *)
Inductive live_tree : Type :=
| Writes : list N -> live_tree
| Reads : list N -> live_tree
| Branch : live_tree -> live_tree -> live_tree
| Seq : live_tree -> live_tree -> live_tree.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_insert_def" *)
Fixpoint numset_list_insert (l : list N) (t : num_set) : num_set :=
  match l with
  | [] => t
  | x :: xs => numset_list_insert xs (insert x tt t)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_insert_nottailrec_def" *)
Fixpoint numset_list_insert_nottailrec (l : list N) (t : num_set) : num_set :=
  match l with
  | [] => t
  | x :: xs => insert x tt (numset_list_insert_nottailrec xs t)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_live_tree_def" *)
Fixpoint get_live_tree (ct : clash_tree) : live_tree :=
  match ct with
  | Delta wr rd => Seq (Reads rd) (Writes wr)
  | Set_ cutset =>
      let cutlist := MAP FST (toAList cutset) in
      Reads cutlist
  | reg_alloc.Branch optcutset ct1 ct2 =>
      let lt1 := get_live_tree ct1 in
      let lt2 := get_live_tree ct2 in
      match optcutset with
      | Some cutset =>
          let cutlist := MAP FST (toAList cutset) in
          Seq (Reads cutlist) (Branch lt1 lt2)
      | None => Branch lt1 lt2
      end
  | reg_alloc.Seq ct1 ct2 =>
      let lt2 := get_live_tree ct2 in
      let lt1 := get_live_tree ct1 in
      Seq lt1 lt2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_live_tree_def" *)
Fixpoint check_live_tree (f : N -> N) (lt : live_tree) (live flive : num_set)
    : option (num_set * num_set) :=
  match lt with
  | Writes l =>
      match check_partial_col f l live flive with
      | None => None
      | Some _ =>
          let livein := numset_list_delete l live in
          let flivein := numset_list_delete (MAP f l) flive in
          Some (livein, flivein)
      end
  | Reads l => check_partial_col f l live flive
  | Branch lt1 lt2 =>
      match check_live_tree f lt1 live flive with
      | None => None
      | Some (livein1, flivein1) =>
          match check_live_tree f lt2 live flive with
          | None => None
          | Some (livein2, flivein2) =>
              check_partial_col f (MAP FST (toAList (difference livein2 livein1)))
                livein1 flivein1
          end
      end
  | Seq lt1 lt2 =>
      match check_live_tree f lt2 live flive with
      | None => None
      | Some (livein2, flivein2) => check_live_tree f lt1 livein2 flivein2
      end
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_live_backward_def" *)
Fixpoint get_live_backward (lt : live_tree) (live : num_set) : num_set :=
  match lt with
  | Writes l => numset_list_delete l live
  | Reads l => numset_list_insert l live
  | Branch lt1 lt2 =>
      let live1 := get_live_backward lt1 live in
      let live2 := get_live_backward lt2 live in
      numset_list_insert (MAP FST (toAList (difference live2 live1))) live1
  | Seq lt1 lt2 => get_live_backward lt1 (get_live_backward lt2 live)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "fix_domination_def" *)
Definition fix_domination (lt : live_tree) : live_tree :=
  let live := get_live_backward lt LN in
  if bool_decide (live = LN) then lt
  else Seq (Writes (MAP FST (toAList live))) lt.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_add_if_def" *)
Fixpoint numset_list_add_if (l : list N) (v : Z) (s : num_map Z) (P : Z -> Z -> bool)
    : num_map Z :=
  match l with
  | [] => s
  | x :: xs =>
      match lookup x s with
      | Some v' =>
          if P v v' then numset_list_add_if xs v (insert x v s) P
          else numset_list_add_if xs v s P
      | None => numset_list_add_if xs v (insert x v s) P
      end
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_add_if_lt_def" *)
Definition numset_list_add_if_lt (l : list N) (v : Z) (s : num_map Z) : num_map Z :=
  numset_list_add_if l v s Z.leb.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_add_if_gt_def" *)
Definition numset_list_add_if_gt (l : list N) (v : Z) (s : num_map Z) : num_map Z :=
  numset_list_add_if l v s (fun a b => (b <=? a)%Z).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "size_of_live_tree_def" *)
Fixpoint size_of_live_tree (lt : live_tree) : Z :=
  match lt with
  | Writes l => 1%Z
  | Reads l => 1%Z
  | Branch lt1 lt2 => (size_of_live_tree lt1 + size_of_live_tree lt2)%Z
  | Seq lt1 lt2 => (size_of_live_tree lt1 + size_of_live_tree lt2)%Z
  end.

(** HOL's [(n, int_beg, int_end)] is the right-nested [(n, (int_beg, int_end))]. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_def" *)
Fixpoint get_intervals (lt : live_tree) (n : Z) (int_beg int_end : num_map Z)
    : Z * (num_map Z * num_map Z) :=
  match lt with
  | Writes l =>
      ((n - 1)%Z, (numset_list_add_if_lt l n int_beg, numset_list_add_if_gt l n int_end))
  | Reads l => ((n - 1)%Z, (int_beg, numset_list_add_if_gt l n int_end))
  | Branch lt1 lt2 =>
      let '(n2, (int_beg2, int_end2)) := get_intervals lt2 n int_beg int_end in
      get_intervals lt1 n2 int_beg2 int_end2
  | Seq lt1 lt2 =>
      let '(n2, (int_beg2, int_end2)) := get_intervals lt2 n int_beg int_end in
      get_intervals lt1 n2 int_beg2 int_end2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_withlive_def" *)
Fixpoint get_intervals_withlive (lt : live_tree) (n : Z) (int_beg int_end : num_map Z)
    (live : num_set) : Z * (num_map Z * num_map Z) :=
  match lt with
  | Writes l =>
      ((n - 1)%Z, (numset_list_add_if_lt l n int_beg, numset_list_add_if_gt l n int_end))
  | Reads l =>
      ((n - 1)%Z, (numset_list_delete l int_beg, numset_list_add_if_gt l n int_end))
  | Branch lt1 lt2 =>
      let '(n2, (int_beg2, int_end2)) := get_intervals_withlive lt2 n int_beg int_end live in
      let '(n1, (int_beg1, int_end1)) :=
        get_intervals_withlive lt1 n2 (difference int_beg2 live) int_end2 live in
      (n1, (difference int_beg1
              (union (get_live_backward lt1 live) (get_live_backward lt2 live)), int_end1))
  | Seq lt1 lt2 =>
      let '(n2, (int_beg2, int_end2)) := get_intervals_withlive lt2 n int_beg int_end live in
      let '(n1, (int_beg1, int_end1)) :=
        get_intervals_withlive lt1 n2 int_beg2 int_end2 (get_live_backward lt2 live) in
      (n1, (int_beg1, int_end1))
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_number_property_def" *)
Fixpoint check_number_property (P : Z -> num_set -> bool) (lt : live_tree) (n : Z)
    (live : num_set) : bool :=
  match lt with
  | Writes l =>
      let n_out := (n - 1)%Z in
      let live_out := numset_list_delete l live in
      P n_out live_out
  | Reads l =>
      let n_out := (n - 1)%Z in
      let live_out := numset_list_insert l live in
      P n_out live_out
  | Branch lt1 lt2 =>
      let r2 := check_number_property P lt2 n live in
      let r1 := check_number_property P lt1 (n - size_of_live_tree lt2)%Z live in
      r1 && r2
  | Seq lt1 lt2 =>
      let r2 := check_number_property P lt2 n live in
      let r1 := check_number_property P lt1 (n - size_of_live_tree lt2)%Z
                  (get_live_backward lt2 live) in
      r1 && r2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_number_property_strong_def" *)
Fixpoint check_number_property_strong (P : Z -> num_set -> bool) (lt : live_tree) (n : Z)
    (live : num_set) : bool :=
  match lt with
  | Writes l =>
      let n_out := (n - 1)%Z in
      let live_out := numset_list_delete l live in
      P n_out live_out
  | Reads l =>
      let n_out := (n - 1)%Z in
      let live_out := numset_list_insert l live in
      P n_out live_out
  | Branch lt1 lt2 =>
      let r2 := check_number_property_strong P lt2 n live in
      let r1 := check_number_property_strong P lt1 (n - size_of_live_tree lt2)%Z live in
      r1 && r2 &&
      P (n - size_of_live_tree (Branch lt1 lt2))%Z (get_live_backward (Branch lt1 lt2) live)
  | Seq lt1 lt2 =>
      let r2 := check_number_property_strong P lt2 n live in
      let r1 := check_number_property_strong P lt1 (n - size_of_live_tree lt2)%Z
                  (get_live_backward lt2 live) in
      r1 && r2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_startlive_prop_def" *)
Fixpoint check_startlive_prop (lt : live_tree) (n : Z) (beg end_ : num_map Z) (ndef : Z)
    : Prop :=
  match lt with
  | Writes l =>
      forall r, MEM r l ->
        ((match lookup r beg with None => ndef | Some x => x end) <= n)%Z /\
        (exists v, lookup r end_ = Some v /\ (n <= v)%Z)
  | Reads l => True
  | Branch lt1 lt2 =>
      let r2 := check_startlive_prop lt2 n beg end_ ndef in
      let r1 := check_startlive_prop lt1 (n - size_of_live_tree lt2)%Z beg end_ ndef in
      r1 /\ r2
  | Seq lt1 lt2 =>
      let r2 := check_startlive_prop lt2 n beg end_ ndef in
      let r1 := check_startlive_prop lt1 (n - size_of_live_tree lt2)%Z beg end_ ndef in
      r1 /\ r2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "live_tree_registers_def" *)
Fixpoint live_tree_registers (lt : live_tree) : N -> Prop :=
  match lt with
  | Writes l => set l
  | Reads l => set l
  | Branch lt1 lt2 => live_tree_registers lt1 UNION live_tree_registers lt2
  | Seq lt1 lt2 => live_tree_registers lt1 UNION live_tree_registers lt2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "interval_intersect_def" *)
Definition interval_intersect (i1 i2 : Z * Z) : bool :=
  let '(l1, r1) := i1 in let '(l2, r2) := i2 in (l1 <=? r2)%Z && (l2 <=? r1)%Z.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "point_inside_interval_def" *)
Definition point_inside_interval (i : Z * Z) (n : Z) : bool :=
  let '(l, r) := i in (l <=? n)%Z && (n <=? r)%Z.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_intervals_def" *)
Definition check_intervals (f : N -> N) (int_beg int_end : num_map Z) : Prop :=
  forall r1 r2,
    r1 IN domain int_beg /\ r2 IN domain int_beg /\
    interval_intersect (THE (lookup r1 int_beg), THE (lookup r1 int_end))
      (THE (lookup r2 int_beg), THE (lookup r2 int_end)) /\
    f r1 = f r2 ->
    r1 = r2.

(** HOL's [(n, int_beg, int_end, live)] is right-nested. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_ct_aux_def" *)
Fixpoint get_intervals_ct_aux (ct : clash_tree) (n : Z) (int_beg int_end : num_map Z)
    (live : num_set) : Z * (num_map Z * (num_map Z * num_set)) :=
  match ct with
  | Delta wr rd =>
      ((n - 2)%Z, (numset_list_add_if_lt wr n int_beg,
        (numset_list_add_if_gt rd (n - 1)%Z (numset_list_add_if_gt wr n int_end),
         numset_list_insert rd (numset_list_delete wr live))))
  | Set_ cutset =>
      ((n - 1)%Z, (int_beg,
        (numset_list_add_if_gt (MAP FST (toAList cutset)) n int_end, union cutset live)))
  | reg_alloc.Branch optcutset ct1 ct2 =>
      let '(n2, (int_beg2, (int_end2, live2))) := get_intervals_ct_aux ct2 n int_beg int_end live in
      let '(n1, (int_beg1, (int_end1, live1))) :=
        get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live in
      match optcutset with
      | None => (n1, (int_beg1, (int_end1, union live1 live2)))
      | Some cutset =>
          ((n1 - 1)%Z, (int_beg1,
            (numset_list_add_if_gt (MAP FST (toAList cutset)) n1 int_end1,
             union cutset (union live1 live2))))
      end
  | reg_alloc.Seq ct1 ct2 =>
      let '(n2, (int_beg2, (int_end2, live2))) := get_intervals_ct_aux ct2 n int_beg int_end live in
      get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_ct_def" *)
Definition get_intervals_ct (ct : clash_tree) : Z * (num_map Z * num_map Z) :=
  let '(n, (int_beg, (int_end, live))) := get_intervals_ct_aux ct 0%Z LN LN LN in
  let listlive := MAP FST (toAList live) in
  ((n - 1)%Z, (numset_list_add_if_lt listlive n int_beg, numset_list_add_if_gt listlive n int_end)).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_scan_state" *)
Record linear_scan_state : Type := mk_linear_scan_state {
  active : list (Z * N);
  colorpool : list N;
  phyregs : num_set;
  colornum : N;
  colormax : N;
  stacknum : N
}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_scan_hidden_state" *)
Record linear_scan_hidden_state : Type := mk_linear_scan_hidden_state {
  colors : marray N;
  int_beg : marray Z;
  int_end : marray Z;
  sorted_regs : marray N;
  sorted_moves : marray (N * (N * N))
}.

(** The monad of the linear-scan allocator. *)
Abbreviation LSM A := (M linear_scan_hidden_state A state_exn).

(** ** Generated accessors, exception and array functions *)

(** Generated by HOL's [define_monad_access_funs] (no HOL source declaration). *)
Definition get_colors {E} : M linear_scan_hidden_state (list N) E := fun state => (M_success state.(colors), state).
Definition set_colors {E} (x : list N) : M linear_scan_hidden_state unit E :=
  fun state => (M_success tt, mk_linear_scan_hidden_state x state.(int_beg) state.(int_end) state.(sorted_regs) state.(sorted_moves)).

(** Generated by HOL's [define_monad_access_funs] (no HOL source declaration). *)
Definition get_int_beg {E} : M linear_scan_hidden_state (list Z) E := fun state => (M_success state.(int_beg), state).
Definition set_int_beg {E} (x : list Z) : M linear_scan_hidden_state unit E :=
  fun state => (M_success tt, mk_linear_scan_hidden_state state.(colors) x state.(int_end) state.(sorted_regs) state.(sorted_moves)).

(** Generated by HOL's [define_monad_access_funs] (no HOL source declaration). *)
Definition get_int_end {E} : M linear_scan_hidden_state (list Z) E := fun state => (M_success state.(int_end), state).
Definition set_int_end {E} (x : list Z) : M linear_scan_hidden_state unit E :=
  fun state => (M_success tt, mk_linear_scan_hidden_state state.(colors) state.(int_beg) x state.(sorted_regs) state.(sorted_moves)).

(** Generated by HOL's [define_monad_access_funs] (no HOL source declaration). *)
Definition get_sorted_regs {E} : M linear_scan_hidden_state (list N) E := fun state => (M_success state.(sorted_regs), state).
Definition set_sorted_regs {E} (x : list N) : M linear_scan_hidden_state unit E :=
  fun state => (M_success tt, mk_linear_scan_hidden_state state.(colors) state.(int_beg) state.(int_end) x state.(sorted_moves)).

(** Generated by HOL's [define_monad_access_funs] (no HOL source declaration). *)
Definition get_sorted_moves {E} : M linear_scan_hidden_state (list (N * (N * N))) E := fun state => (M_success state.(sorted_moves), state).
Definition set_sorted_moves {E} (x : list (N * (N * N))) : M linear_scan_hidden_state unit E :=
  fun state => (M_success tt, mk_linear_scan_hidden_state state.(colors) state.(int_beg) state.(int_end) state.(sorted_regs) x).

(** Generated by HOL's [define_MFarray_manip_funs]. *)
Definition colors_length {E} : M linear_scan_hidden_state N E := Marray_length (fun s => s.(colors)).
Definition colors_sub : N -> M linear_scan_hidden_state N state_exn := Marray_sub (fun s => s.(colors)) Subscript.
Definition update_colors : N -> N -> M linear_scan_hidden_state unit state_exn :=
  Marray_update (fun s => s.(colors)) (fun x s => mk_linear_scan_hidden_state x s.(int_beg) s.(int_end) s.(sorted_regs) s.(sorted_moves)) Subscript.

(** Generated by HOL's [define_MFarray_manip_funs]. *)
Definition int_beg_length {E} : M linear_scan_hidden_state N E := Marray_length (fun s => s.(int_beg)).
Definition int_beg_sub : N -> M linear_scan_hidden_state Z state_exn := Marray_sub (fun s => s.(int_beg)) Subscript.
Definition update_int_beg : N -> Z -> M linear_scan_hidden_state unit state_exn :=
  Marray_update (fun s => s.(int_beg)) (fun x s => mk_linear_scan_hidden_state s.(colors) x s.(int_end) s.(sorted_regs) s.(sorted_moves)) Subscript.

(** Generated by HOL's [define_MFarray_manip_funs]. *)
Definition int_end_length {E} : M linear_scan_hidden_state N E := Marray_length (fun s => s.(int_end)).
Definition int_end_sub : N -> M linear_scan_hidden_state Z state_exn := Marray_sub (fun s => s.(int_end)) Subscript.
Definition update_int_end : N -> Z -> M linear_scan_hidden_state unit state_exn :=
  Marray_update (fun s => s.(int_end)) (fun x s => mk_linear_scan_hidden_state s.(colors) s.(int_beg) x s.(sorted_regs) s.(sorted_moves)) Subscript.

(** Generated by HOL's [define_MFarray_manip_funs]. *)
Definition sorted_regs_length {E} : M linear_scan_hidden_state N E := Marray_length (fun s => s.(sorted_regs)).
Definition sorted_regs_sub : N -> M linear_scan_hidden_state N state_exn := Marray_sub (fun s => s.(sorted_regs)) Subscript.
Definition update_sorted_regs : N -> N -> M linear_scan_hidden_state unit state_exn :=
  Marray_update (fun s => s.(sorted_regs)) (fun x s => mk_linear_scan_hidden_state s.(colors) s.(int_beg) s.(int_end) x s.(sorted_moves)) Subscript.

(** Generated by HOL's [define_MFarray_manip_funs]. *)
Definition sorted_moves_length {E} : M linear_scan_hidden_state N E := Marray_length (fun s => s.(sorted_moves)).
Definition sorted_moves_sub : N -> M linear_scan_hidden_state (N * (N * N)) state_exn := Marray_sub (fun s => s.(sorted_moves)) Subscript.
Definition update_sorted_moves : N -> (N * (N * N)) -> M linear_scan_hidden_state unit state_exn :=
  Marray_update (fun s => s.(sorted_moves)) (fun x s => mk_linear_scan_hidden_state s.(colors) s.(int_beg) s.(int_end) s.(sorted_regs) x) Subscript.


(** Generated by HOL's [define_monad_exception_functions]. *)
Definition raise_Fail {A} (e1 : string) : LSM A := fun state => (M_failure (Fail e1), state).
Definition raise_Subscript {A} : LSM A := fun state => (M_failure Subscript, state).

Definition handle_Fail {A} (x : LSM A) (f : string -> LSM A) : LSM A :=
  fun state =>
    let '(res, state) := x state in
    match res with
    | M_success y => (M_success y, state)
    | M_failure e =>
        match e with
        | Fail e1 => f e1 state
        | Subscript => (M_failure Subscript, state)
        end
    end.

Definition handle_Subscript {A} (x : LSM A) (f : LSM A) : LSM A :=
  fun state =>
    let '(res, state) := x state in
    match res with
    | M_success y => (M_success y, state)
    | M_failure e =>
        match e with
        | Fail e1 => (M_failure (Fail e1), state)
        | Subscript => f state
        end
    end.

(** ** The monadic allocator *)

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_add_if_lt_monad_def" *)
Fixpoint numset_list_add_if_lt_monad (l : list N) (v : Z) : LSM unit :=
  match l with
  | [] => st_ex_return tt
  | r :: rs =>
      begr <- int_beg_sub r ;;
      if (0 <? begr)%Z then
        update_int_beg r v ;;
        numset_list_add_if_lt_monad rs v
      else if (v <=? begr)%Z then
        update_int_beg r v ;;
        numset_list_add_if_lt_monad rs v
      else numset_list_add_if_lt_monad rs v
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "numset_list_add_if_gt_monad_def" *)
Fixpoint numset_list_add_if_gt_monad (l : list N) (v : Z) : LSM unit :=
  match l with
  | [] => st_ex_return tt
  | r :: rs =>
      begr <- int_end_sub r ;;
      if (0 <? begr)%Z then
        update_int_end r v ;;
        numset_list_add_if_gt_monad rs v
      else if (begr <=? v)%Z then
        update_int_end r v ;;
        numset_list_add_if_gt_monad rs v
      else numset_list_add_if_gt_monad rs v
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_ct_monad_aux_def" *)
Fixpoint get_intervals_ct_monad_aux (ct : clash_tree) (n : Z) (live : num_set)
    : LSM (Z * num_set) :=
  match ct with
  | Delta wr rd =>
      numset_list_add_if_lt_monad wr n ;;
      numset_list_add_if_gt_monad wr n ;;
      numset_list_add_if_gt_monad rd (n - 1)%Z ;;
      st_ex_return ((n - 2)%Z, numset_list_insert rd (numset_list_delete wr live))
  | Set_ cutset =>
      numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n ;;
      st_ex_return ((n - 1)%Z, union cutset live)
  | reg_alloc.Branch optcutset ct1 ct2 =>
      '(n2, live2) <- get_intervals_ct_monad_aux ct2 n live ;;
      '(n1, live1) <- get_intervals_ct_monad_aux ct1 n2 live ;;
      match optcutset with
      | None => st_ex_return (n1, union live1 live2)
      | Some cutset =>
          numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n1 ;;
          st_ex_return ((n1 - 1)%Z, union cutset (union live1 live2))
      end
  | reg_alloc.Seq ct1 ct2 =>
      '(n2, live2) <- get_intervals_ct_monad_aux ct2 n live ;;
      get_intervals_ct_monad_aux ct1 n2 live2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_ct_monad_def" *)
Definition get_intervals_ct_monad (ct : clash_tree) : LSM Z :=
  '(n, live) <- get_intervals_ct_monad_aux ct 0%Z LN ;;
  numset_list_add_if_lt_monad (MAP FST (toAList live)) n ;;
  numset_list_add_if_gt_monad (MAP FST (toAList live)) n ;;
  st_ex_return (n - 1)%Z.

(** [remove_inactive_intervals_aux beg st.(active) st] computes
    [remove_inactive_intervals beg st] by structural recursion on the active
    list (HOL's termination measure). *)
Fixpoint remove_inactive_intervals_aux (beg : Z) (act : list (Z * N)) (st : linear_scan_state)
    : LSM linear_scan_state :=
  match act with
  | [] => st_ex_return st
  | (e, r) :: activetail =>
      if (e <? beg)%Z then
        col <- colors_sub r ;;
        let st' := {| active := activetail;
                      colorpool := col :: st.(colorpool);
                      phyregs := st.(phyregs);
                      colornum := st.(colornum);
                      colormax := st.(colormax);
                      stacknum := st.(stacknum) |} in
        remove_inactive_intervals_aux beg activetail st'
      else st_ex_return st
  end.

(** HOL [remove_inactive_intervals] (see [remove_inactive_intervals_def]). *)
Definition remove_inactive_intervals (beg : Z) (st : linear_scan_state) : LSM linear_scan_state :=
  remove_inactive_intervals_aux beg st.(active) st.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "remove_inactive_intervals_def" *)
Theorem remove_inactive_intervals_def : forall beg st,
  remove_inactive_intervals beg st =
  match st.(active) with
  | [] => st_ex_return st
  | (e, r) :: activetail =>
      if (e <? beg)%Z then
        col <- colors_sub r ;;
        let st' := {| active := activetail;
                      colorpool := col :: st.(colorpool);
                      phyregs := st.(phyregs);
                      colornum := st.(colornum);
                      colormax := st.(colormax);
                      stacknum := st.(stacknum) |} in
        remove_inactive_intervals beg st'
      else st_ex_return st
  end.
Proof. intros beg st; unfold remove_inactive_intervals; destruct (active st) as [|[e r] tl]; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "add_active_interval_def" *)
Fixpoint add_active_interval (v1 : Z * N) (l : list (Z * N)) : list (Z * N) :=
  match l with
  | [] => [v1]
  | v2 :: tail =>
      if (FST v1 <=? FST v2)%Z then v1 :: v2 :: tail
      else v2 :: add_active_interval v1 tail
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_color_in_list_def" *)
Fixpoint find_color_in_list (l : list N) (forbidden : num_set) : option (N * list N) :=
  match l with
  | [] => None
  | r :: rs =>
      if bool_decide (lookup r forbidden = None) then Some (r, rs)
      else
        match find_color_in_list rs forbidden with
        | None => None
        | Some (col, rest) => Some (col, r :: rest)
        end
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_color_in_colornum_def" *)
Definition find_color_in_colornum (st : linear_scan_state) (forbidden : num_set)
    : linear_scan_state * option N :=
  if st.(colormax) <=? st.(colornum) then (st, None)
  else
    ({| active := st.(active); colorpool := st.(colorpool); phyregs := st.(phyregs);
        colornum := st.(colornum) + 1; colormax := st.(colormax); stacknum := st.(stacknum) |},
     Some st.(colornum)).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_color_def" *)
Definition find_color (st : linear_scan_state) (forbidden : num_set)
    : linear_scan_state * option N :=
  match find_color_in_list st.(colorpool) forbidden with
  | Some (col, rest) =>
      ({| active := st.(active); colorpool := rest; phyregs := st.(phyregs);
          colornum := st.(colornum); colormax := st.(colormax); stacknum := st.(stacknum) |},
       Some col)
  | None => find_color_in_colornum st forbidden
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "spill_register_def" *)
Definition spill_register (st : linear_scan_state) (reg : N) : LSM linear_scan_state :=
  update_colors reg st.(stacknum) ;;
  st_ex_return {| active := st.(active); colorpool := st.(colorpool); phyregs := st.(phyregs);
                  colornum := st.(colornum); colormax := st.(colormax);
                  stacknum := st.(stacknum) + 1 |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "color_register_def" *)
Definition color_register (st : linear_scan_state) (reg col : N) (rend : Z)
    : LSM linear_scan_state :=
  update_colors reg col ;;
  if is_phy_var reg then
    st_ex_return {| active := add_active_interval (rend, reg) st.(active);
                    colorpool := st.(colorpool);
                    phyregs := insert col tt st.(phyregs);
                    colornum := st.(colornum); colormax := st.(colormax);
                    stacknum := st.(stacknum) |}
  else
    st_ex_return {| active := add_active_interval (rend, reg) st.(active);
                    colorpool := st.(colorpool); phyregs := st.(phyregs);
                    colornum := st.(colornum); colormax := st.(colormax);
                    stacknum := st.(stacknum) |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_last_stealable_def" *)
Fixpoint find_last_stealable (l : list (Z * N)) (forbidden : num_set)
    : LSM (option ((Z * N) * list (Z * N))) :=
  match l with
  | [] => st_ex_return None
  | x :: xs =>
      recursion <- find_last_stealable xs forbidden ;;
      match recursion with
      | Some (steal, rest) => st_ex_return (Some (steal, x :: rest))
      | None =>
          xcol <- colors_sub (SND x) ;;
          if negb (is_phy_var (SND x)) && bool_decide (lookup xcol forbidden = None) then
            st_ex_return (Some (x, xs))
          else st_ex_return None
      end
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_spill_def" *)
Definition find_spill (st : linear_scan_state) (forbidden : num_set) (reg : N) (rend : Z)
    (force : bool) : LSM linear_scan_state :=
  stealable <- find_last_stealable st.(active) forbidden ;;
  match stealable with
  | None => spill_register st reg
  | Some ((stealend, stealreg), newactive) =>
      if force || (rend <? stealend)%Z then
        stealcolor <- colors_sub stealreg ;;
        st' <- spill_register
                 {| active := newactive; colorpool := st.(colorpool); phyregs := st.(phyregs);
                    colornum := st.(colornum); colormax := st.(colormax);
                    stacknum := st.(stacknum) |} stealreg ;;
        color_register st' reg stealcolor rend
      else spill_register st reg
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_step_aux_def" *)
Definition linear_reg_alloc_step_aux (st : linear_scan_state) (forbidden : num_set)
    (preferred : list N) (reg : N) (rend : Z) (force : bool) : LSM linear_scan_state :=
  let preferred_filtered := FILTER (fun c => MEM c st.(colorpool)) preferred in
  match find_color_in_list preferred_filtered forbidden with
  | Some (col, _) =>
      color_register
        {| active := st.(active);
           colorpool := FILTER (fun x => negb (col =? x)) st.(colorpool);
           phyregs := st.(phyregs); colornum := st.(colornum); colormax := st.(colormax);
           stacknum := st.(stacknum) |} reg col rend
  | None =>
      match find_color st forbidden with
      | (st', Some col) => color_register st' reg col rend
      | (st', None) => find_spill st' forbidden reg rend force
      end
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_step_pass1_def" *)
Definition linear_reg_alloc_step_pass1 (forced moves : num_map (list N))
    (st : linear_scan_state) (reg : N) : LSM linear_scan_state :=
  rbeg <- int_beg_sub reg ;;
  rend <- int_end_sub reg ;;
  st' <- remove_inactive_intervals rbeg st ;;
  if is_stack_var reg then spill_register st' reg
  else
    forced_forbidden_list <- st_ex_MAP colors_sub (the [] (lookup reg forced)) ;;
    let forced_forbidden := fromAList (MAP (fun c => (c, tt)) forced_forbidden_list) in
    if is_phy_var reg then
      if reg <? 2 * st'.(colormax) then
        let forbidden := union st'.(phyregs) forced_forbidden in
        linear_reg_alloc_step_aux st' forbidden [] reg rend true
      else spill_register st' reg
    else
      moves_preferred <- st_ex_MAP colors_sub (the [] (lookup reg moves)) ;;
      linear_reg_alloc_step_aux st' forced_forbidden moves_preferred reg rend false.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_step_pass2_def" *)
Definition linear_reg_alloc_step_pass2 (forced moves : num_map (list N))
    (st : linear_scan_state) (reg : N) : LSM linear_scan_state :=
  rbeg <- int_beg_sub reg ;;
  rend <- int_end_sub reg ;;
  st' <- remove_inactive_intervals rbeg st ;;
  forced_forbidden_list <- st_ex_MAP colors_sub (the [] (lookup reg forced)) ;;
  forced_forbidden <- st_ex_return (fromAList (MAP (fun c => (c, tt)) forced_forbidden_list)) ;;
  moves_preferred <- st_ex_MAP colors_sub (the [] (lookup reg moves)) ;;
  if is_phy_var reg then
    let forbidden := union st'.(phyregs) forced_forbidden in
    linear_reg_alloc_step_aux st' forbidden [] reg rend false
  else linear_reg_alloc_step_aux st' forced_forbidden moves_preferred reg rend false.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_pass1_initial_state_def" *)
Definition linear_reg_alloc_pass1_initial_state (k : N) : linear_scan_state :=
  {| active := []; colorpool := []; colornum := 0; colormax := k; phyregs := LN;
     stacknum := k |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_pass2_initial_state_def" *)
Definition linear_reg_alloc_pass2_initial_state (k nreg : N) : linear_scan_state :=
  {| active := []; colorpool := []; colornum := k; colormax := k + nreg; phyregs := LN;
     stacknum := k + nreg |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_reg_exchange_def" *)
Fixpoint find_reg_exchange (l : list N) (exch invexch : num_map N)
    : LSM (num_map N * num_map N) :=
  match l with
  | [] => st_ex_return (exch, invexch)
  | r :: rs =>
      col1 <- colors_sub r ;;
      let fcol1 := r DIV 2 in
      let col2 := match lookup fcol1 invexch with None => fcol1 | Some x => x end in
      let fcol2 := match lookup col1 exch with None => col1 | Some x => x end in
      find_reg_exchange rs (insert col1 fcol1 (insert col2 fcol2 exch))
        (insert fcol1 col1 (insert fcol2 col2 invexch))
  end.

(** HOL [MAP_colors] (see [MAP_colors_def]). *)
Definition MAP_colors (f : N -> N) (n : N) : LSM unit :=
  num_rec (st_ex_return tt)
    (fun n r => col <- colors_sub n ;; update_colors n (f col) ;; r) n.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "MAP_colors_def" *)
Theorem MAP_colors_def : forall f n,
  MAP_colors f 0 = st_ex_return tt /\
  MAP_colors f (SUC n) = (col <- colors_sub n ;; update_colors n (f col) ;; MAP_colors f n).
Proof. intros; split; [reflexivity|unfold MAP_colors; rewrite num_rec_SUC; reflexivity]. Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "apply_reg_exchange_def" *)
Definition apply_reg_exchange (phyregs : list N) : LSM unit :=
  '(exch, invexch) <- find_reg_exchange phyregs LN LN ;;
  col_size <- colors_length ;;
  MAP_colors (fun c => match lookup c exch with None => c | Some x => x end) col_size.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "st_ex_FOLDL_def" *)
Fixpoint st_ex_FOLDL {S A B E} (f : B -> A -> M S B E) (e : B) (l : list A) : M S B E :=
  match l with
  | [] => st_ex_return e
  | x :: xs =>
      e' <- f e x ;;
      st_ex_FOLDL f e' xs
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "st_ex_FILTER_good_def" *)
Fixpoint st_ex_FILTER_good {S A E} (P : A -> M S bool E) (l : list A) : M S (list A) E :=
  match l with
  | [] => st_ex_return []
  | x :: xs =>
      Px <- P x ;;
      if Px then
        filter_xs <- st_ex_FILTER_good P xs ;;
        st_ex_return (x :: filter_xs)
      else st_ex_FILTER_good P xs
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "edges_to_adjlist_def" *)
Fixpoint edges_to_adjlist (l : list (N * N)) (acc : num_map (list N)) : LSM (num_map (list N)) :=
  match l with
  | [] => st_ex_return acc
  | (a, b) :: abs =>
      if a =? b then edges_to_adjlist abs acc
      else
        bega <- int_beg_sub a ;;
        begb <- int_beg_sub b ;;
        if (bega <? begb)%Z || ((bega =? begb)%Z && (a <=? b)) then
          edges_to_adjlist abs (insert b (a :: the [] (lookup b acc)) acc)
        else
          edges_to_adjlist abs (insert a (b :: the [] (lookup a acc)) acc)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sort_moves_rev_def" *)
Definition sort_moves_rev {A} (ls : list (N * A)) : list (N * A) :=
  sort (fun '(p, x) '(p', x') => p <? p') ls.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "swap_regs_def" *)
Definition swap_regs (i1 i2 : N) : LSM unit :=
  r1 <- sorted_regs_sub i1 ;;
  r2 <- sorted_regs_sub i2 ;;
  update_sorted_regs i1 r2 ;;
  update_sorted_regs i2 r1.

(** [partition_regs], [sort_regs]: [Fix] on HOL's measures [r - l]. *)
Definition partition_regs_meas (a : N * (N * (Z * N))) : N :=
  let '(l, (_, (_, r))) := a in r - l.

Lemma partition_regs_dec1 l r : (r <=? l) = false -> r - (l + 1) < r - l.
Proof. intros H; apply N.leb_gt in H; lia. Qed.
Lemma partition_regs_dec2 l r : (r <=? l) = false -> (r - 1) - l < r - l.
Proof. intros H; apply N.leb_gt in H; lia. Qed.

Definition partition_regs_F (a : N * (N * (Z * N)))
    (rec : forall b, partition_regs_meas b < partition_regs_meas a -> LSM N) : LSM N :=
  match a as a0 return (forall b, partition_regs_meas b < partition_regs_meas a0 -> LSM N) -> LSM N with
  | (l, (rpiv, (begrpiv, r))) => fun rec =>
      match Sumbool.sumbool_of_bool (r <=? l) with
      | left _ => st_ex_return l
      | right H =>
          reg <- sorted_regs_sub l ;;
          begreg <- int_beg_sub reg ;;
          if (begreg <? begrpiv)%Z || ((begreg =? begrpiv)%Z && (reg <=? rpiv)) then
            rec (l + 1, (rpiv, (begrpiv, r))) (partition_regs_dec1 l r H)
          else
            swap_regs l (r - 1) ;;
            rec (l, (rpiv, (begrpiv, r - 1))) (partition_regs_dec2 l r H)
      end
  end rec.

(** HOL [partition_regs] (see [partition_regs_def]). *)
Definition partition_regs (l rpiv : N) (begrpiv : Z) (r : N) : LSM N :=
  Fix (measure_wf partition_regs_meas) (fun _ => LSM N) partition_regs_F (l, (rpiv, (begrpiv, r))).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "partition_regs_def" *)
Theorem partition_regs_def : forall l rpiv begrpiv r,
  partition_regs l rpiv begrpiv r =
  if r <=? l then st_ex_return l
  else
    reg <- sorted_regs_sub l ;;
    begreg <- int_beg_sub reg ;;
    if (begreg <? begrpiv)%Z || ((begreg =? begrpiv)%Z && (reg <=? rpiv)) then
      partition_regs (l + 1) rpiv begrpiv r
    else
      swap_regs l (r - 1) ;;
      partition_regs l rpiv begrpiv (r - 1).
Proof.
  intros; unfold partition_regs at 1; rewrite Fix_eq by apply Fix_F_ext.
  cbn [partition_regs_F]; destruct (Sumbool.sumbool_of_bool (r <=? l)) as [E|E];
    rewrite E; reflexivity.
Qed.

Definition sort_regs_meas (a : N * N) : N := let '(l, r) := a in r - l.

Lemma sort_regs_dec1 l r m : ((m <=? l) || (r <? m)) = false -> (m - 1) - l < r - l.
Proof. intros H; apply orb_false_iff in H as [H1 H2]; apply N.leb_gt in H1; apply N.ltb_ge in H2; lia. Qed.
Lemma sort_regs_dec2 l r m : ((m <=? l) || (r <? m)) = false -> r - m < r - l.
Proof. intros H; apply orb_false_iff in H as [H1 H2]; apply N.leb_gt in H1; apply N.ltb_ge in H2; lia. Qed.

Definition sort_regs_F (a : N * N) (rec : forall b, sort_regs_meas b < sort_regs_meas a -> LSM unit)
    : LSM unit :=
  match a as a0 return (forall b, sort_regs_meas b < sort_regs_meas a0 -> LSM unit) -> LSM unit with
  | (l, r) => fun rec =>
      if r <=? l + 1 then st_ex_return tt
      else
        rpiv <- sorted_regs_sub l ;;
        begrpiv <- int_beg_sub rpiv ;;
        m <- partition_regs (l + 1) rpiv begrpiv r ;;
        swap_regs l (m - 1) ;;
        match Sumbool.sumbool_of_bool ((m <=? l) || (r <? m)) with
        | left _ => st_ex_return tt
        | right H =>
            rec (l, m - 1) (sort_regs_dec1 l r m H) ;;
            rec (m, r) (sort_regs_dec2 l r m H)
        end
  end rec.

(** HOL [sort_regs] (see [sort_regs_def]). *)
Definition sort_regs (l r : N) : LSM unit :=
  Fix (measure_wf sort_regs_meas) (fun _ => LSM unit) sort_regs_F (l, r).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sort_regs_def" *)
Theorem sort_regs_def : forall l r,
  sort_regs l r =
  if r <=? l + 1 then st_ex_return tt
  else
    rpiv <- sorted_regs_sub l ;;
    begrpiv <- int_beg_sub rpiv ;;
    m <- partition_regs (l + 1) rpiv begrpiv r ;;
    swap_regs l (m - 1) ;;
    if (m <=? l) || (r <? m) then st_ex_return tt
    else
      sort_regs l (m - 1) ;;
      sort_regs m r.
Proof.
  intros; unfold sort_regs at 1; rewrite Fix_eq by apply Fix_F_ext.
  cbn [sort_regs_F]; destruct (r <=? l + 1); [reflexivity|].
  do 3 (f_equal; apply functional_extensionality; intros). f_equal.
  match goal with |- context [Sumbool.sumbool_of_bool ?b] =>
    destruct (Sumbool.sumbool_of_bool b) as [E|E]; rewrite E; reflexivity end.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "list_to_sorted_regs_def" *)
Fixpoint list_to_sorted_regs (l : list N) (n : N) : LSM unit :=
  match l with
  | [] => st_ex_return tt
  | r :: rs =>
      update_sorted_regs n r ;;
      list_to_sorted_regs rs (n + 1)
  end.

Definition to_list_meas (a : N * N) : N := let '(n, last) := a in last - n.

Lemma to_list_dec n last : (last <=? n) = false -> last - (n + 1) < last - n.
Proof. intros H; apply N.leb_gt in H; lia. Qed.

Definition sorted_regs_to_list_F (a : N * N)
    (rec : forall b, to_list_meas b < to_list_meas a -> LSM (list N)) : LSM (list N) :=
  match a as a0 return (forall b, to_list_meas b < to_list_meas a0 -> LSM (list N)) -> LSM (list N) with
  | (n, last) => fun rec =>
      match Sumbool.sumbool_of_bool (last <=? n) with
      | left _ => st_ex_return []
      | right H =>
          r <- sorted_regs_sub n ;;
          l <- rec (n + 1, last) (to_list_dec n last H) ;;
          st_ex_return (r :: l)
      end
  end rec.

(** HOL [sorted_regs_to_list] (see [sorted_regs_to_list_def]). *)
Definition sorted_regs_to_list (n last : N) : LSM (list N) :=
  Fix (measure_wf to_list_meas) (fun _ => LSM (list N)) sorted_regs_to_list_F (n, last).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_regs_to_list_def" *)
Theorem sorted_regs_to_list_def : forall n last,
  sorted_regs_to_list n last =
  if last <=? n then st_ex_return []
  else
    r <- sorted_regs_sub n ;;
    l <- sorted_regs_to_list (n + 1) last ;;
    st_ex_return (r :: l).
Proof.
  intros; unfold sorted_regs_to_list at 1; rewrite Fix_eq by apply Fix_F_ext.
  cbn [sorted_regs_to_list_F]; destruct (Sumbool.sumbool_of_bool (last <=? n)) as [E|E];
    rewrite E; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "swap_moves_def" *)
Definition swap_moves (i1 i2 : N) : LSM unit :=
  r1 <- sorted_moves_sub i1 ;;
  r2 <- sorted_moves_sub i2 ;;
  update_sorted_moves i1 r2 ;;
  update_sorted_moves i2 r1.

Definition partition_moves_meas (a : N * (N * N)) : N := let '(l, (_, r)) := a in r - l.

Definition partition_moves_F (a : N * (N * N))
    (rec : forall b, partition_moves_meas b < partition_moves_meas a -> LSM N) : LSM N :=
  match a as a0 return (forall b, partition_moves_meas b < partition_moves_meas a0 -> LSM N) -> LSM N with
  | (l, (ppiv, r)) => fun rec =>
      match Sumbool.sumbool_of_bool (r <=? l) with
      | left _ => st_ex_return l
      | right H =>
          move <- sorted_moves_sub l ;;
          if FST move <? ppiv then
            rec (l + 1, (ppiv, r)) (partition_regs_dec1 l r H)
          else
            swap_moves l (r - 1) ;;
            rec (l, (ppiv, r - 1)) (partition_regs_dec2 l r H)
      end
  end rec.

(** HOL [partition_moves] (see [partition_moves_def]). *)
Definition partition_moves (l ppiv r : N) : LSM N :=
  Fix (measure_wf partition_moves_meas) (fun _ => LSM N) partition_moves_F (l, (ppiv, r)).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "partition_moves_def" *)
Theorem partition_moves_def : forall l ppiv r,
  partition_moves l ppiv r =
  if r <=? l then st_ex_return l
  else
    move <- sorted_moves_sub l ;;
    if FST move <? ppiv then partition_moves (l + 1) ppiv r
    else
      swap_moves l (r - 1) ;;
      partition_moves l ppiv (r - 1).
Proof.
  intros; unfold partition_moves at 1; rewrite Fix_eq by apply Fix_F_ext.
  cbn [partition_moves_F]; destruct (Sumbool.sumbool_of_bool (r <=? l)) as [E|E];
    rewrite E; reflexivity.
Qed.

Definition sort_moves_F (a : N * N) (rec : forall b, sort_regs_meas b < sort_regs_meas a -> LSM unit)
    : LSM unit :=
  match a as a0 return (forall b, sort_regs_meas b < sort_regs_meas a0 -> LSM unit) -> LSM unit with
  | (l, r) => fun rec =>
      if r <=? l + 1 then st_ex_return tt
      else
        piv <- sorted_moves_sub l ;;
        m <- partition_moves (l + 1) (FST piv) r ;;
        swap_moves l (m - 1) ;;
        match Sumbool.sumbool_of_bool ((m <=? l) || (r <? m)) with
        | left _ => st_ex_return tt
        | right H =>
            rec (l, m - 1) (sort_regs_dec1 l r m H) ;;
            rec (m, r) (sort_regs_dec2 l r m H)
        end
  end rec.

(** HOL [linear_scan$sort_moves] (see [sort_moves_def]); it shadows
    [reg_alloc$sort_moves] in this module. *)
Definition sort_moves (l r : N) : LSM unit :=
  Fix (measure_wf sort_regs_meas) (fun _ => LSM unit) sort_moves_F (l, r).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sort_moves_def" *)
Theorem sort_moves_def : forall l r,
  sort_moves l r =
  if r <=? l + 1 then st_ex_return tt
  else
    piv <- sorted_moves_sub l ;;
    m <- partition_moves (l + 1) (FST piv) r ;;
    swap_moves l (m - 1) ;;
    if (m <=? l) || (r <? m) then st_ex_return tt
    else
      sort_moves l (m - 1) ;;
      sort_moves m r.
Proof.
  intros; unfold sort_moves at 1; rewrite Fix_eq by apply Fix_F_ext.
  cbn [sort_moves_F]; destruct (r <=? l + 1); [reflexivity|].
  do 2 (f_equal; apply functional_extensionality; intros). f_equal.
  match goal with |- context [Sumbool.sumbool_of_bool ?b] =>
    destruct (Sumbool.sumbool_of_bool b) as [E|E]; rewrite E; reflexivity end.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "list_to_sorted_moves_def" *)
Fixpoint list_to_sorted_moves (l : list (N * (N * N))) (n : N) : LSM unit :=
  match l with
  | [] => st_ex_return tt
  | r :: rs =>
      update_sorted_moves n r ;;
      list_to_sorted_moves rs (n + 1)
  end.

Definition sorted_moves_to_list_F (a : N * N)
    (rec : forall b, to_list_meas b < to_list_meas a -> LSM (list (N * (N * N))))
    : LSM (list (N * (N * N))) :=
  match a as a0 return (forall b, to_list_meas b < to_list_meas a0 -> LSM (list (N * (N * N))))
                       -> LSM (list (N * (N * N))) with
  | (n, len) => fun rec =>
      match Sumbool.sumbool_of_bool (len <=? n) with
      | left _ => st_ex_return []
      | right H =>
          r <- sorted_moves_sub n ;;
          l <- rec (n + 1, len) (to_list_dec n len H) ;;
          st_ex_return (r :: l)
      end
  end rec.

(** HOL [sorted_moves_to_list] (see [sorted_moves_to_list_def]). *)
Definition sorted_moves_to_list (n len : N) : LSM (list (N * (N * N))) :=
  Fix (measure_wf to_list_meas) (fun _ => LSM (list (N * (N * N)))) sorted_moves_to_list_F (n, len).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_moves_to_list_def" *)
Theorem sorted_moves_to_list_def : forall n len,
  sorted_moves_to_list n len =
  if len <=? n then st_ex_return []
  else
    r <- sorted_moves_sub n ;;
    l <- sorted_moves_to_list (n + 1) len ;;
    st_ex_return (r :: l).
Proof.
  intros; unfold sorted_moves_to_list at 1; rewrite Fix_eq by apply Fix_F_ext.
  cbn [sorted_moves_to_list_F]; destruct (Sumbool.sumbool_of_bool (len <=? n)) as [E|E];
    rewrite E; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_intervals_def" *)
Definition linear_reg_alloc_intervals (k : N) (forced : list (N * N))
    (moves : list (N * (N * N))) (reglist_unsorted : list N) : LSM unit :=
  let lenreg := LENGTH reglist_unsorted in
  let lenmoves := LENGTH moves in
  let st_init_pass1 := linear_reg_alloc_pass1_initial_state k in
  list_to_sorted_regs reglist_unsorted 0 ;;
  sort_regs 0 lenreg ;;
  reglist <- sorted_regs_to_list 0 lenreg ;;
  phyregs <- st_ex_return (FILTER is_phy_var reglist) ;;
  phyphyregs <- st_ex_return (FILTER (fun r => r <? 2 * k) phyregs) ;;
  stackphyregs <- st_ex_return (FILTER (fun r => 2 * k <=? r) phyregs) ;;
  list_to_sorted_moves moves 0 ;;
  sort_moves 0 lenmoves ;;
  smoves <- sorted_moves_to_list 0 lenmoves ;;
  moves_adjlist <- edges_to_adjlist (MAP SND smoves) LN ;;
  forced_adjlist <- edges_to_adjlist forced LN ;;
  st_end_pass1 <- st_ex_FOLDL (linear_reg_alloc_step_pass1 forced_adjlist moves_adjlist)
                    st_init_pass1 reglist ;;
  apply_reg_exchange phyphyregs ;;
  stacklist <- st_ex_FILTER_good (fun r =>
                 col <- colors_sub r ;;
                 st_ex_return (is_stack_var r || (k <=? col))) reglist ;;
  st_init_pass2 <- st_ex_return (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)) ;;
  stackset <- st_ex_return (fromAList (MAP (fun r => (r, tt)) stacklist)) ;;
  forced_adjlist' <- st_ex_return
    (sptree.map (FILTER (fun r => negb (bool_decide (lookup r stackset = None)))) forced_adjlist) ;;
  moves_adjlist' <- st_ex_return
    (sptree.map (FILTER (fun r => negb (bool_decide (lookup r stackset = None)))) moves_adjlist) ;;
  st_end_pass2 <- st_ex_FOLDL (linear_reg_alloc_step_pass2 forced_adjlist' moves_adjlist')
                    st_init_pass2 stacklist ;;
  apply_reg_exchange stackphyregs.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "extract_coloration_def" *)
Fixpoint extract_coloration (invbij : num_map N) (l : list N) (acc : num_map N)
    : LSM (num_map N) :=
  match l with
  | [] => st_ex_return acc
  | r :: rs =>
      col <- colors_sub r ;;
      extract_coloration invbij rs (insert (the 0 (lookup r invbij)) col acc)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "bijection_state" *)
Record bijection_state : Type := mk_bijection_state {
  bij : num_map N;
  invbij : num_map N;
  nmax : N;
  nstack : N;
  nalloc : N
}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_bijection_init_def" *)
Definition find_bijection_init : bijection_state :=
  {| bij := LN; invbij := LN; nmax := 0; nstack := 3; nalloc := 1 |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_bijection_step_def" *)
Definition find_bijection_step (state : bijection_state) (r : N) : bijection_state :=
  if negb (bool_decide (lookup r state.(bij) = None)) then state
  else if is_phy_var r then
    {| bij := insert r r state.(bij);
       invbij := insert r r state.(invbij);
       nmax := MAX r state.(nmax);
       nstack := state.(nstack);
       nalloc := state.(nalloc) |}
  else if is_stack_var r then
    {| bij := insert r state.(nstack) state.(bij);
       invbij := insert state.(nstack) r state.(invbij);
       nmax := MAX state.(nstack) state.(nmax);
       nstack := state.(nstack) + 4;
       nalloc := state.(nalloc) |}
  else
    {| bij := insert r state.(nalloc) state.(bij);
       invbij := insert state.(nalloc) r state.(invbij);
       nmax := MAX state.(nalloc) state.(nmax);
       nstack := state.(nstack);
       nalloc := state.(nalloc) + 4 |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_bijection_clash_tree_def" *)
Fixpoint find_bijection_clash_tree (state : bijection_state) (ct : clash_tree)
    : bijection_state :=
  match ct with
  | Delta wr rd => FOLDL find_bijection_step (FOLDL find_bijection_step state rd) wr
  | Set_ cutset => foldi (fun r v acc => find_bijection_step acc r) 0 state cutset
  | reg_alloc.Branch optcutset ct1 ct2 =>
      let state1 := find_bijection_clash_tree state ct1 in
      let state2 := find_bijection_clash_tree state1 ct2 in
      match optcutset with
      | None => state2
      | Some cutset => foldi (fun r v acc => find_bijection_step acc r) 0 state2 cutset
      end
  | reg_alloc.Seq ct1 ct2 =>
      let state1 := find_bijection_clash_tree state ct1 in
      find_bijection_clash_tree state1 ct2
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "apply_bijection_def" *)
Definition apply_bijection (bij : num_map N) (interval : num_map Z) : num_map Z :=
  foldi (fun r i acc => insert (the 0 (lookup r bij)) i acc) 0 LN interval.

(** Generated by HOL's [define_run ``:linear_scan_hidden_state`` [...]
    "i_linear_scan_hidden_state"] (array fields hold [(size, initial value)]). *)
Record i_linear_scan_hidden_state : Type := mk_i_linear_scan_hidden_state {
  i_linear_scan_hidden_state_colors : N * N;
  i_linear_scan_hidden_state_int_beg : N * Z;
  i_linear_scan_hidden_state_int_end : N * Z;
  i_linear_scan_hidden_state_sorted_regs : N * N;
  i_linear_scan_hidden_state_sorted_moves : N * (N * (N * N))
}.

(** Generated by HOL's [define_run]. *)
(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "run_i_linear_scan_hidden_state_def" *)
Definition run_i_linear_scan_hidden_state {A E} (x : M linear_scan_hidden_state A E)
    (state : i_linear_scan_hidden_state) : exc A E :=
  run x (mk_linear_scan_hidden_state
    (marray_replicate (FST state.(i_linear_scan_hidden_state_colors))
               (SND state.(i_linear_scan_hidden_state_colors)))
    (marray_replicate (FST state.(i_linear_scan_hidden_state_int_beg))
               (SND state.(i_linear_scan_hidden_state_int_beg)))
    (marray_replicate (FST state.(i_linear_scan_hidden_state_int_end))
               (SND state.(i_linear_scan_hidden_state_int_end)))
    (marray_replicate (FST state.(i_linear_scan_hidden_state_sorted_regs))
               (SND state.(i_linear_scan_hidden_state_sorted_regs)))
    (marray_replicate (FST state.(i_linear_scan_hidden_state_sorted_moves))
               (SND state.(i_linear_scan_hidden_state_sorted_moves)))).

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_reg_alloc_and_extract_coloration_def" *)
Definition linear_reg_alloc_and_extract_coloration (ct : clash_tree) (k : N)
    (forced : list (N * N)) (moves : list (N * (N * N))) (reglist_unsorted : list N)
    (invbij : num_map N) (nmax : N) : LSM (num_map N) :=
  get_intervals_ct_monad ct ;;
  linear_reg_alloc_intervals k forced moves reglist_unsorted ;;
  extract_coloration invbij reglist_unsorted LN.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "size_of_clash_tree_def" *)
Fixpoint size_of_clash_tree (ct : clash_tree) : Z :=
  match ct with
  | Delta wr rd => 2%Z
  | Set_ cutset => 1%Z
  | reg_alloc.Branch optcutset ct1 ct2 =>
      ((if IS_SOME optcutset then 1 else 0) + size_of_clash_tree ct1 + size_of_clash_tree ct2)%Z
  | reg_alloc.Seq ct1 ct2 => (size_of_clash_tree ct1 + size_of_clash_tree ct2)%Z
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "run_linear_reg_alloc_intervals_def" *)
Definition run_linear_reg_alloc_intervals (ct : clash_tree) (k : N) (forced : list (N * N))
    (moves : list (N * (N * N))) (reglist_unsorted : list N) (invbij : num_map N) (nmax : N)
    : exc (num_map N) state_exn :=
  run_i_linear_scan_hidden_state
    (linear_reg_alloc_and_extract_coloration ct k forced moves reglist_unsorted invbij nmax)
    {| i_linear_scan_hidden_state_colors := (nmax + 1, 0);
       i_linear_scan_hidden_state_int_beg := (nmax + 1, 1%Z);
       i_linear_scan_hidden_state_int_end := (nmax + 1, 1%Z);
       i_linear_scan_hidden_state_sorted_regs := (nmax + 1, 0);
       i_linear_scan_hidden_state_sorted_moves := (LENGTH moves, (0, (0, 0))) |}.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "apply_bij_on_clash_tree_def" *)
Fixpoint apply_bij_on_clash_tree (ct : clash_tree) (bij : num_map N) : clash_tree :=
  match ct with
  | Delta wr rd =>
      Delta (MAP (fun r => the 0 (lookup r bij)) wr) (MAP (fun r => the 0 (lookup r bij)) rd)
  | Set_ cutset =>
      Set_ (foldi (fun r _ acc => insert (the 0 (lookup r bij)) tt acc) 0 LN cutset)
  | reg_alloc.Branch optcutset ct1 ct2 =>
      reg_alloc.Branch
        (OPTION_MAP (foldi (fun r _ acc => insert (the 0 (lookup r bij)) tt acc) 0 LN) optcutset)
        (apply_bij_on_clash_tree ct1 bij) (apply_bij_on_clash_tree ct2 bij)
  | reg_alloc.Seq ct1 ct2 =>
      reg_alloc.Seq (apply_bij_on_clash_tree ct1 bij) (apply_bij_on_clash_tree ct2 bij)
  end.

(*! HOL "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_scan_reg_alloc_def" *)
Definition linear_scan_reg_alloc (k : N) (moves : list (N * (N * N))) (ct : clash_tree)
    (forced : list (N * N)) : exc (num_map N) state_exn :=
  let bijstate := find_bijection_clash_tree find_bijection_init ct in
  let ct' := apply_bij_on_clash_tree ct bijstate.(bij) in
  let forced' := MAP (fun '(r1, r2) => (the 0 (lookup r1 bijstate.(bij)),
                                        the 0 (lookup r2 bijstate.(bij)))) forced in
  let moves' := MAP (fun '(p, (r1, r2)) => (p, (the 0 (lookup r1 bijstate.(bij)),
                                               the 0 (lookup r2 bijstate.(bij))))) moves in
  let reglist_unsorted := MAP SND (toAList bijstate.(bij)) in
  run_linear_reg_alloc_intervals ct' k forced' moves' reglist_unsorted bijstate.(invbij)
    bijstate.(nmax).
