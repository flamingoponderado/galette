(** * CakeML [lab_to_target]: the assembler

    Port of [cakeml/compiler/backend/lab_to_targetScript.sml]: label offsets
    are computed by iterating encoding to a fixpoint of instruction lengths
    ([remove_labels]); the bytes are extracted by [prog_to_bytes].

    - labLang's [Jump], [JumpCmp], [Call], [Halt] shadow ASM's; ASM's are
      written [asm.X].
    - [prog_to_bytes] and [find_ffi_names] recurse on [Section k ys :: xs]
      (not a subterm); they are computed by an outer recursion on sections
      and an inner one on lines, and HOL's equations are the tagged [_def]
      theorems.  Likewise [get_shmem_info].
    - [remove_labels_loop] recurses on [clock - 1]; it is computed with
      [num_rec] and HOL's equation is the tagged [_def] theorem.
    - HOL's overload [all_enc_ok_light] is an abbreviation.
    - The field [reg] of [shmem_info_num] keeps HOL's name (it shadows
      ASM's type abbreviation [reg] where this file is imported last). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import labLang lab_filter.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "ffi_offset_def" *)
Definition ffi_offset : N := 16.

Section LabToTarget.
Context {a : N}.

(** ** Basic assemble function *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "lab_inst_def" *)
Definition lab_inst (w : word a) (l : asm_with_lab a) : asm a :=
  match l with
  | Jump _ => asm.Jump w
  | JumpCmp c r ri _ => asm.JumpCmp c r ri w
  | Call _ => asm.Call w
  | LocValue r _ => Loc r w
  | Halt => asm.Jump w
  | Install => asm.Jump w
  | CallFFI n => asm.Jump w
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "cbw_to_asm_def" *)
Definition cbw_to_asm (x : asm_or_cbw a) : asm a :=
  match x with
  | Asmi a0 => a0
  | Cbw r1 r2 => Inst (Mem Store8 r2 (Addr r1 (n2w 0)))
  | ShareMem m r ad => Inst (Mem m r ad)
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_line_def" *)
Definition enc_line (enc : asm a -> list word8) (skip_len : N) (l : line a) : line a :=
  match l with
  | Label n1 n2 n3 => Label n1 n2 skip_len
  | Asm x _ _ => let bs := enc (cbw_to_asm x) in Asm x bs (LENGTH bs)
  | LabAsm l _ _ _ => let bs := enc (lab_inst (n2w 0) l) in LabAsm l (n2w 0) bs (LENGTH bs)
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_sec_def" *)
Definition enc_sec (enc : asm a -> list word8) (skip_len : N) (s : sec a) : sec a :=
  match s with Section_ k xs => Section_ k (MAP (enc_line enc skip_len) xs) end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_sec_list_def" *)
Definition enc_sec_list (enc : asm a -> list word8) (xs : list (sec a)) : list (sec a) :=
  let skip_len := LENGTH (enc (Inst asm.Skip)) in
  MAP (enc_sec enc skip_len) xs.

(** ** Computing labels *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "section_labels_def" *)
Fixpoint section_labels (pos : N) (l : list (line a)) (labs : list (N * N)) : N * list (N * N) :=
  match l with
  | [] => (pos, labs)
  | Label _ l2 len :: xs =>
      if l2 =? 0 then section_labels (pos + len) xs labs
      else section_labels (pos + len) xs ((l2, pos + len) :: labs)
  | Asm _ _ len :: xs => section_labels (pos + len) xs labs
  | LabAsm _ _ _ len :: xs => section_labels (pos + len) xs labs
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "compute_labels_alt_def" *)
Fixpoint compute_labels_alt (pos : N) (l : list (sec a)) (labs : spt (spt N)) : spt (spt N) :=
  match l with
  | [] => labs
  | Section_ k lines :: rest =>
      let '(new_pos, sec_labs) := section_labels pos lines [] in
      compute_labels_alt new_pos rest (insert k (fromAList ((0, pos) :: sec_labs)) labs)
  end.

(** ** Updating code, but not label lengths *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "find_pos_def" *)
Definition find_pos (l : lab) (labs : spt (spt N)) : N :=
  match l with Lab k1 k2 => lookup_any k2 (lookup_any k1 labs LN) 0 end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_label_def" *)
Definition get_label (x : asm_with_lab a) : lab :=
  match x with
  | Jump l => l
  | JumpCmp c r ri l => l
  | Call l => l
  | LocValue r l => l
  | _ => Lab 0 0
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_ffi_index_def" *)
Definition get_ffi_index (ffis : list ffiname) (s : ffiname) : N :=
  the 0 (find_index s ffis 0).

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_jump_offset_def" *)
Definition get_jump_offset (x : asm_with_lab a) (ffis : list ffiname) (labs : spt (spt N))
    (pos : N) : word a :=
  match x with
  | CallFFI s => word_sub (n2w 0) (n2w (pos + (3 + get_ffi_index ffis (ExtCall s)) * ffi_offset))
  | Install => word_sub (n2w 0) (n2w (pos + 2 * ffi_offset))
  | Halt => word_sub (n2w 0) (n2w (pos + ffi_offset))
  | x => word_sub (n2w (find_pos (get_label x) labs)) (n2w pos)
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_lines_again_def" *)
Fixpoint enc_lines_again (labs : spt (spt N)) (ffis : list ffiname) (pos : N)
    (enc : asm a -> list word8) (l : list (line a)) (acc_ok : list (line a) * bool)
    : list (line a) * (N * bool) :=
  let '(acc, ok) := acc_ok in
  match l with
  | [] => (REVERSE acc, (pos, ok))
  | Label k1 k2 l :: xs =>
      enc_lines_again labs ffis (pos + l) enc xs (Label k1 k2 l :: acc, ok)
  | Asm x1 x2 l :: xs =>
      enc_lines_again labs ffis (pos + l) enc xs (Asm x1 x2 l :: acc, ok)
  | LabAsm x w bytes l :: xs =>
      let w1 := get_jump_offset x ffis labs pos in
      if decide (w = w1) then
        enc_lines_again labs ffis (pos + l) enc xs (LabAsm x w bytes l :: acc, ok)
      else
        let bs := enc (lab_inst w1 x) in
        let l1 := MAX (LENGTH bs) l in
        enc_lines_again labs ffis (pos + l1) enc xs
          (LabAsm x w1 bs l1 :: acc, ok && (l1 =? l))
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_secs_again_def" *)
Fixpoint enc_secs_again (pos : N) (labs : spt (spt N)) (ffis : list ffiname)
    (enc : asm a -> list word8) (l : list (sec a)) : list (sec a) * bool :=
  match l with
  | [] => ([], true)
  | Section_ s lines :: rest =>
      let '(lines1, (pos1, ok)) := enc_lines_again labs ffis pos enc lines ([], true) in
      let '(rest1, ok1) := enc_secs_again pos1 labs ffis enc rest in
      (Section_ s lines1 :: rest1, ok && ok1)
  end.

(** ** Updating labels *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "lines_upd_lab_len_def" *)
Fixpoint lines_upd_lab_len (pos : N) (l : list (line a)) (acc : list (line a))
    : list (line a) * N :=
  match l with
  | [] => (REVERSE acc, pos)
  | Label k1 k2 l :: xs =>
      let l1 := if EVEN pos then 0 else 1 in
      lines_upd_lab_len (pos + l1) xs (Label k1 k2 l1 :: acc)
  | Asm x1 x2 l :: xs => lines_upd_lab_len (pos + l) xs (Asm x1 x2 l :: acc)
  | LabAsm x w bytes l :: xs => lines_upd_lab_len (pos + l) xs (LabAsm x w bytes l :: acc)
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "upd_lab_len_def" *)
Fixpoint upd_lab_len (pos : N) (l : list (sec a)) : list (sec a) :=
  match l with
  | [] => []
  | Section_ s lines :: rest =>
      let '(lines1, pos1) := lines_upd_lab_len pos lines [] in
      let rest1 := upd_lab_len pos1 rest in
      Section_ s lines1 :: rest1
  end.

(** ** Checking that all labelled asm instructions are [asm_ok] *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "line_ok_light_def" *)
Definition line_ok_light (c : asm_config a) (l : line a) : bool :=
  match l with
  | Label _ _ l => true
  | Asm b bytes l => true
  | LabAsm Halt w bytes l => asm_ok (asm.Jump w) c
  | LabAsm Install w bytes l => asm_ok (asm.Jump w) c
  | LabAsm (CallFFI index) w bytes l => asm_ok (asm.Jump w) c
  | LabAsm (Call v24) w bytes l => false
  | LabAsm x w bytes l => asm_ok (lab_inst w x) c
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "sec_ok_light_def" *)
Definition sec_ok_light (c : asm_config a) (s : sec a) : bool :=
  match s with Section_ k ls => EVERY (line_ok_light c) ls end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "all_enc_ok_light" *)
Abbreviation all_enc_ok_light c ls := (EVERY (sec_ok_light c) ls).

(** ** Padding with nop bytes and the nop instruction *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_bytes_def" *)
Definition pad_bytes (bytes : list word8) (len : N) (nop : list word8) : list word8 :=
  let len_bytes := LENGTH bytes in
  if len <=? len_bytes then bytes else
    TAKE len (bytes ++ FLAT (REPLICATE len nop)).

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "add_nop_def" *)
Fixpoint add_nop (nop : list word8) (l : list (line a)) : list (line a) :=
  match l with
  | [] => []
  | Label l1 l2 len :: xs => Label l1 l2 len :: add_nop nop xs
  | Asm x bytes len :: xs => Asm x (bytes ++ nop) (len + 1) :: xs
  | LabAsm y w bytes len :: xs => LabAsm y w (bytes ++ nop) (len + 1) :: xs
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_section_def" *)
Fixpoint pad_section (nop : list word8) (l : list (line a)) (aux : list (line a)) : list (line a) :=
  match l with
  | [] => REVERSE aux
  | Label l1 l2 len :: xs =>
      pad_section nop xs (Label l1 l2 0 :: (if len =? 0 then aux else add_nop nop aux))
  | Asm x bytes len :: xs =>
      pad_section nop xs (Asm x (pad_bytes bytes len nop) len :: aux)
  | LabAsm y w bytes len :: xs =>
      pad_section nop xs (LabAsm y w (pad_bytes bytes len nop) len :: aux)
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_code_def" *)
Fixpoint pad_code (nop : list word8) (l : list (sec a)) : list (sec a) :=
  match l with
  | [] => []
  | Section_ n xs :: ys => Section_ n (pad_section nop xs []) :: pad_code nop ys
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_code_MAP" *)
Theorem pad_code_MAP : forall nop,
  pad_code nop = MAP (fun x => Section_ (Section_num x) (pad_section nop (Section_lines x) [])).
Proof.
  intros nop; apply functional_extensionality; intros ls.
  induction ls as [|[n xs] ls IH]; cbn; [reflexivity|]; rewrite IH; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "sec_length_def" *)
Fixpoint sec_length (l : list (line a)) (k : N) : N :=
  match l with
  | [] => k
  | Label _ _ l :: xs => sec_length xs (k + l)
  | Asm x1 x2 l :: xs => sec_length xs (k + l)
  | LabAsm x w bytes l :: xs => sec_length xs (k + l)
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_symbols_def" *)
Fixpoint get_symbols (pos : N) (l : list (sec a)) : list (N * (N * N)) :=
  match l with
  | [] => []
  | Section_ k l :: secs =>
      let len := sec_length l 0 in (k, (pos, len)) :: get_symbols (pos + len) secs
  end.

(** ** Labels whose second part is 0 *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "zero_labs_acc_of_def" *)
Definition zero_labs_acc_of (x : asm_with_lab a) (acc : num_set) : num_set :=
  match x with
  | LocValue _ (Lab n1 n2) => if n2 =? 0 then insert n1 tt acc else acc
  | Jump (Lab n1 n2) => if n2 =? 0 then insert n1 tt acc else acc
  | JumpCmp _ _ _ (Lab n1 n2) => if n2 =? 0 then insert n1 tt acc else acc
  | _ => acc
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "line_get_zero_labs_acc_def" *)
Definition line_get_zero_labs_acc (l : line a) (acc : num_set) : num_set :=
  match l with
  | LabAsm x _ _ _ => zero_labs_acc_of x acc
  | _ => acc
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "sec_get_zero_labs_acc_def" *)
Definition sec_get_zero_labs_acc (s : sec a) (acc : num_set) : num_set :=
  match s with Section_ _ lines => FOLDR line_get_zero_labs_acc acc lines end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_zero_labs_acc_def" *)
Definition get_zero_labs_acc (code : list (sec a)) : num_set :=
  FOLDR sec_get_zero_labs_acc LN code.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "zero_labs_acc_exist_def" *)
Definition zero_labs_acc_exist (labs : spt (spt N)) (code : list (sec a)) : bool :=
  let zlabs := toAList (get_zero_labs_acc code) in
  EVERY (fun '(n, _) =>
           match lookup n labs with
           | None => false
           | Some l => match lookup 0 l with None => false | Some _ => true end
           end) zlabs.

(** ** The top-level assembler function *)

(** One iteration of [remove_labels_loop]; [k] is the continuation for the
    next iteration ([None] when the clock is exhausted). *)
Definition remove_labels_loop_body (c : asm_config a) (pos : N) (init_labs : spt (spt N))
    (ffis : list ffiname) (k : option (list (sec a) -> option (list (sec a) * spt (spt N))))
    (sec_list : list (sec a)) : option (list (sec a) * spt (spt N)) :=
  let labs := compute_labels_alt pos sec_list init_labs in
  let '(sec_list, done) := enc_secs_again pos labs ffis (encode c) sec_list in
  if done then
    let sec_list := upd_lab_len pos sec_list in
    let labs := compute_labels_alt pos sec_list init_labs in
    let '(sec_list, done) := enc_secs_again pos labs ffis (encode c) sec_list in
    let sec_list := pad_code (encode c (Inst asm.Skip)) sec_list in
    if done && all_enc_ok_light c sec_list && zero_labs_acc_exist labs sec_list
    then Some (sec_list, labs)
    else None
  else
    match k with
    | None => None
    | Some r => r sec_list
    end.

(** HOL [remove_labels_loop] (recursion on [clock - 1]). *)
Definition remove_labels_loop (clock : N) (c : asm_config a) (pos : N) (init_labs : spt (spt N))
    (ffis : list ffiname) : list (sec a) -> option (list (sec a) * spt (spt N)) :=
  num_rec (remove_labels_loop_body c pos init_labs ffis None)
    (fun _ r => remove_labels_loop_body c pos init_labs ffis (Some r)) clock.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "remove_labels_loop_def" *)
Theorem remove_labels_loop_def : forall clock c pos init_labs ffis sec_list,
  remove_labels_loop clock c pos init_labs ffis sec_list =
    let labs := compute_labels_alt pos sec_list init_labs in
    let '(sec_list, done) := enc_secs_again pos labs ffis (encode c) sec_list in
    if done then
      let sec_list := upd_lab_len pos sec_list in
      let labs := compute_labels_alt pos sec_list init_labs in
      let '(sec_list, done) := enc_secs_again pos labs ffis (encode c) sec_list in
      let sec_list := pad_code (encode c (Inst asm.Skip)) sec_list in
      if done && all_enc_ok_light c sec_list && zero_labs_acc_exist labs sec_list
      then Some (sec_list, labs)
      else None
    else
      if clock =? 0 then None else
        remove_labels_loop (clock - 1) c pos init_labs ffis sec_list.
Proof.
  intros clock c pos init_labs ffis sec_list.
  destruct (N.eqb_spec clock 0) as [->|Hc].
  - unfold remove_labels_loop; rewrite num_rec_0; unfold remove_labels_loop_body.
    cbv zeta; destruct (enc_secs_again _ _ _ _ _) as [s d]; destruct d; reflexivity.
  - unfold remove_labels_loop at 1; replace clock with (SUC (clock - 1)) at 1 by lia.
    rewrite num_rec_SUC; unfold remove_labels_loop_body at 1.
    cbv zeta; destruct (enc_secs_again _ _ _ _ _) as [s d]; destruct d; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "remove_labels_def" *)
Definition remove_labels (init_clock : N) (c : asm_config a) (pos : N) (labs : spt (spt N))
    (ffis : list ffiname) (sec_list : list (sec a)) : option (list (sec a) * spt (spt N)) :=
  remove_labels_loop init_clock c pos labs ffis (enc_sec_list (encode c) sec_list).

(** ** Code extraction *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "line_bytes_def" *)
Definition line_bytes (l : line a) : list word8 :=
  match l with
  | Label _ _ _ => []
  | Asm _ bytes _ => bytes
  | LabAsm _ _ bytes _ => bytes
  end.

(** HOL [prog_to_bytes]: outer recursion on sections, inner on lines. *)
Fixpoint prog_to_bytes (l : list (sec a)) : list word8 :=
  match l with
  | [] => []
  | Section_ k ys :: xs =>
      (fix lines (ys : list (line a)) : list word8 :=
         match ys with
         | [] => prog_to_bytes xs
         | y :: ys => line_bytes y ++ lines ys
         end) ys
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "prog_to_bytes_def" *)
Theorem prog_to_bytes_def : forall k y ys xs,
  prog_to_bytes [] = [] /\
  prog_to_bytes (Section_ k [] :: xs) = prog_to_bytes xs /\
  prog_to_bytes (Section_ k (y :: ys) :: xs) = line_bytes y ++ prog_to_bytes (Section_ k ys :: xs).
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "prog_to_bytes_MAP" *)
Theorem prog_to_bytes_MAP : forall ls,
  prog_to_bytes ls = FLAT (MAP (fun s => FLAT (MAP line_bytes (Section_lines s))) ls).
Proof.
  assert (H : forall k ys xs,
    prog_to_bytes (Section_ k ys :: xs) = FLAT (MAP line_bytes ys) ++ prog_to_bytes xs).
  { intros k ys xs; induction ys as [|y ys IHy]; [reflexivity|].
    change (line_bytes y ++ prog_to_bytes (Section_ k ys :: xs) =
            (line_bytes y ++ FLAT (MAP line_bytes ys)) ++ prog_to_bytes xs).
    rewrite IHy, app_assoc; reflexivity. }
  induction ls as [|[k ys] ls IH]; [reflexivity|].
  rewrite H, IH; reflexivity.
Qed.

End LabToTarget.

(** ** Compiling labels *)

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "shmem_info_num" *)
Record shmem_info_num : Type := {
  entry_pc : N;
  nbytes : word8;
  addr_reg : N;
  addr_off : N;
  reg : N;
  exit_pc : N
}.

(** The fields of HOL's record, in HOL's order. *)
(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "config" *)
Record config : Type := {
  labels : spt (spt N);
  sec_pos_len : list (N * (N * N));
  pos : N;
  init_clock : N;
  ffi_names : option (list ffiname);
  shmem_extra : list shmem_info_num;
  hash_size : N
}.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "list_add_if_fresh_def" *)
Fixpoint list_add_if_fresh {A} `{EqDecision A} (e : A) (l : list A) : list A :=
  match l with
  | [] => [e]
  | f :: r => if decide (e = f) then f :: r else f :: list_add_if_fresh e r
  end.

Section Compile.
Context {a : N}.

(** HOL [find_ffi_names]: outer recursion on sections, inner on lines. *)
Fixpoint find_ffi_names (l : list (sec a)) : list ffiname :=
  match l with
  | [] => []
  | Section_ k xs :: rest =>
      (fix lines (xs : list (line a)) : list ffiname :=
         match xs with
         | [] => find_ffi_names rest
         | x :: xs =>
             match x with
             | LabAsm (CallFFI s) _ _ _ => list_add_if_fresh (ExtCall s) (lines xs)
             | _ => lines xs
             end
         end) xs
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "find_ffi_names_def" *)
Theorem find_ffi_names_def : forall k x xs rest,
  find_ffi_names [] = [] /\
  find_ffi_names (Section_ k [] :: rest) = find_ffi_names rest /\
  find_ffi_names (Section_ k (x :: xs) :: rest) =
    match x with
    | LabAsm (CallFFI s) _ _ _ => list_add_if_fresh (ExtCall s) (find_ffi_names (Section_ k xs :: rest))
    | _ => find_ffi_names (Section_ k xs :: rest)
    end.
Proof. intros; repeat split; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_memop_info_def" *)
Definition get_memop_info (m : memop) : shmem_op * word8 :=
  match m with
  | Load => (MappedRead, n2w 0)
  | Load32 => (MappedRead, n2w 4)
  | Load16 => (MappedRead, n2w 2)
  | Load8 => (MappedRead, n2w 1)
  | Store => (MappedWrite, n2w 0)
  | Store32 => (MappedWrite, n2w 4)
  | Store16 => (MappedWrite, n2w 2)
  | Store8 => (MappedWrite, n2w 1)
  end.

(** HOL [get_shmem_info]: outer recursion on sections, inner on lines. *)
Fixpoint get_shmem_info (l : list (sec a)) (pos : N) (ffi_names : list ffiname)
    (shmem_info : list shmem_info_num) {struct l} : list ffiname * list shmem_info_num :=
  match l with
  | [] => (ffi_names, shmem_info)
  | Section_ k xs :: rest =>
      (fix lines (xs : list (line a)) (pos : N) (ffi_names : list ffiname)
           (shmem_info : list shmem_info_num) : list ffiname * list shmem_info_num :=
         match xs with
         | [] => get_shmem_info rest pos ffi_names shmem_info
         | Label _ _ _ :: xs => lines xs pos ffi_names shmem_info
         | Asm (ShareMem m r ad) bytes _ :: xs =>
             let '(name, nb) := get_memop_info m in
             lines xs (pos + LENGTH bytes)
               (ffi_names ++ [SharedMem name])
               (shmem_info ++
                [{| entry_pc := pos;
                    nbytes := nb;
                    addr_reg := match ad with Addr r off => r end;
                    addr_off := match ad with Addr r off => w2n off end;
                    reg := r;
                    exit_pc := pos + LENGTH bytes |}])
         | LabAsm _ _ bytes _ :: xs => lines xs (pos + LENGTH bytes) ffi_names shmem_info
         | Asm _ bytes _ :: xs => lines xs (pos + LENGTH bytes) ffi_names shmem_info
         end) xs pos ffi_names shmem_info
  end.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "get_shmem_info_def" *)
Theorem get_shmem_info_def : forall k rest pos ffi_names shmem_info xs n1 n2 n3 m r ad bytes l
    x1 x2 i r1 r2,
  get_shmem_info [] pos ffi_names shmem_info = (ffi_names, shmem_info) /\
  get_shmem_info (Section_ k [] :: rest) pos ffi_names shmem_info =
    get_shmem_info rest pos ffi_names shmem_info /\
  get_shmem_info (Section_ k (Label n1 n2 n3 :: xs) :: rest) pos ffi_names shmem_info =
    get_shmem_info (Section_ k xs :: rest) pos ffi_names shmem_info /\
  get_shmem_info (Section_ k (Asm (ShareMem m r ad) bytes l :: xs) :: rest) pos ffi_names
    shmem_info =
    (let '(name, nb) := get_memop_info m in
     get_shmem_info (Section_ k xs :: rest) (pos + LENGTH bytes)
       (ffi_names ++ [SharedMem name])
       (shmem_info ++
        [{| entry_pc := pos;
            nbytes := nb;
            addr_reg := match ad with Addr r off => r end;
            addr_off := match ad with Addr r off => w2n off end;
            reg := r;
            exit_pc := pos + LENGTH bytes |}])) /\
  get_shmem_info (Section_ k (LabAsm x1 x2 bytes l :: xs) :: rest) pos ffi_names shmem_info =
    get_shmem_info (Section_ k xs :: rest) (pos + LENGTH bytes) ffi_names shmem_info /\
  get_shmem_info (Section_ k (Asm (Asmi i) bytes l :: xs) :: rest) pos ffi_names shmem_info =
    get_shmem_info (Section_ k xs :: rest) (pos + LENGTH bytes) ffi_names shmem_info /\
  get_shmem_info (Section_ k (Asm (Cbw r1 r2) bytes l :: xs) :: rest) pos ffi_names shmem_info =
    get_shmem_info (Section_ k xs :: rest) (pos + LENGTH bytes) ffi_names shmem_info.
Proof.
  intros; repeat split; cbn; try reflexivity; destruct (get_memop_info m); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "compile_lab_def" 453 *)
Definition compile_lab (asm_conf : asm_config a) (c : config) (sec_list : list (sec a))
    : option (list word8 * config) :=
  let current_ffis := find_ffi_names sec_list in
  let '(ffis, ffis_ok) :=
    match ffi_names c with
    | Some ffis => (ffis, list_subset current_ffis ffis)
    | _ => (current_ffis, true)
    end in
  if ffis_ok then
    match remove_labels (init_clock c) asm_conf (pos c) (labels c) ffis sec_list with
    | Some (sec_list, l1) =>
        let bytes := prog_to_bytes sec_list in
        let '(new_ffis, shmem_infos) := get_shmem_info sec_list (pos c) [] [] in
        Some (bytes,
              {| labels := l1;
                 sec_pos_len := get_symbols (pos c) sec_list;
                 pos := LENGTH bytes + pos c;
                 init_clock := init_clock c;
                 ffi_names := Some (ffis ++ new_ffis);
                 shmem_extra := shmem_infos;
                 hash_size := hash_size c |})
    | None => None
    end
  else None.

(*! HOL "cakeml/compiler/backend/lab_to_targetScript.sml" "compile_def" *)
Definition compile (asm_conf : asm_config a) (c : config) (sec_list : list (sec a))
    : option (list word8 * config) :=
  compile_lab asm_conf c (filter_skip sec_list).

End Compile.
