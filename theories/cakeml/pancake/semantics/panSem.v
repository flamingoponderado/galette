(** * CakeML Pancake [panSem]: semantics of panLang

    Functional big-step semantics with a clock, as in HOL.  Carrier notes:
    - [state] is a Rocq record with HOL's field names; HOL's
      [s with f := v] is [set_<f> v s] (helpers below).
    - Finite maps are [fmap], sets are [pred_set] sets ([_ -> Prop]); the
      semantics is not executable (it quantifies over clocks), so classical
      decisions ([classical_dec], [⌜_⌝]) are used where HOL tests membership
      in a set.
    - [mem_load]/[mem_loads]/[mem_load_flds] (HOL: well-founded recursion on
      the struct-context length, then the shape) are computed with a fuel
      that is at least the context length; HOL's equations are the tagged
      [mem_load_def].
    - [evaluate] (HOL: well-founded recursion on (clock, program size)) is
      defined with [Function] on that lexicographic measure; HOL's equations
      are the tagged [evaluate_def]. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
Import byte.ByteBits.
From Galette.HOL.src.n_bit.byte Require Import word_of_bytes4.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang backend_common.
From Galette.cakeml.pancake Require Import panLang.
Open Scope N_scope.

Section Sem.
Context {a : N}.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "word_lab" *)
Inductive word_lab : Type := Word : word a -> word_lab.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "v" *)
Inductive v : Type :=
| Val : word_lab -> v
| RStruct : list v -> v
| NStruct : stcname -> list (fldname * v) -> v.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "ValWord" *)
Definition ValWord (w : word a) : v := Val (Word w).

#[global] Instance word_lab_inhabited : Inhabited word_lab := Word (n2w 0).
#[global] Instance v_inhabited : Inhabited v := ValWord (n2w 0).

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "isWord_def" *)
Definition isWord (w : word_lab) : bool := match w with Word _ => true end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "theWord_def" *)
Definition theWord (w : word_lab) : word a := match w with Word w => w end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "isValWord_def" *)
Definition isValWord (x : v) : bool := match x with Val (Word _) => true | _ => false end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "theValWord_def" *)
Definition theValWord (x : v) : word a :=
  match x with Val (Word w) => w | _ => ARB end.

End Sem.
Arguments word_lab : clear implicits.
Arguments v : clear implicits.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "state" *)
Record state (a : N) (ffi : Type) : Type := mk_state {
  locals : fmap varname (v a);
  globals : fmap varname (v a);
  structs : list (stcname * struct_info);
  code : fmap funname (list (varname * shape) * (prog a * shape));
  eshapes : fmap eid shape;
  memory : word a -> word_lab a;
  memaddrs : word a -> Prop;
  sh_memaddrs : word a -> Prop;
  clock : N;
  be : bool;
  ffi : ffi_state ffi;
  base_addr : word a;
  top_addr : word a
}.
Arguments mk_state {a ffi}.
Arguments locals {a ffi}. Arguments globals {a ffi}. Arguments structs {a ffi}.
Arguments code {a ffi}. Arguments eshapes {a ffi}. Arguments memory {a ffi}.
Arguments memaddrs {a ffi}. Arguments sh_memaddrs {a ffi}. Arguments clock {a ffi}.
Arguments be {a ffi}. Arguments ffi {a ffi}. Arguments base_addr {a ffi}.
Arguments top_addr {a ffi}.

(** HOL [s with f := x] for each field. *)
Section Updates.
Context {a : N} {ffi_t : Type}.
Definition set_locals x (s : state a ffi_t) := mk_state x s.(globals) s.(structs) s.(code) s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_globals x (s : state a ffi_t) := mk_state s.(locals) x s.(structs) s.(code) s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_structs x (s : state a ffi_t) := mk_state s.(locals) s.(globals) x s.(code) s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_memory x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) s.(code) s.(eshapes) x s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_clock x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) s.(code) s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) x s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_ffi (x : ffi_state ffi_t) (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) s.(code) s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) x s.(base_addr) s.(top_addr).
End Updates.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "result" *)
Inductive result (a : N) : Type :=
| Error : result a
| TimeOut : result a
| Break : result a
| Continue : result a
| Return : v a -> result a
| Exception : mlstring -> v a -> result a
| FinalFFI : final_event -> result a.
Arguments Error {a}. Arguments TimeOut {a}. Arguments Break {a}. Arguments Continue {a}.
Arguments Return {a} _. Arguments Exception {a} _ _. Arguments FinalFFI {a} _.

Section Helpers.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "shape_of_def" *)
Fixpoint shape_of (x : v a) : shape :=
  match x with
  | Val _ => One
  | RStruct vs => Comb (MAP shape_of vs)
  | NStruct nm _ => Named nm
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_load_byte_def" *)
Definition mem_load_byte (m : word a -> word_lab a) (dm : word a -> Prop) (be : bool)
    (w : word a) : option word8 :=
  match m (byte_align w) with
  | Word v => if classical_dec (byte_align w IN dm) then SOME (get_byte w v be) else NONE
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_load_32_def" *)
Definition mem_load_32 (m : word a -> word_lab a) (dm : word a -> Prop) (be : bool)
    (w : word a) : option word32 :=
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm)
        then SOME (word_of_bytes be (n2w 0 : word32)
                     [get_byte w v be; get_byte (w + n2w 1) v be;
                      get_byte (w + n2w 2) v be; get_byte (w + n2w 3) v be])
        else NONE
    end
  else NONE.

(** [mem_load]/[mem_loads]/[mem_load_flds] computed with a fuel that bounds
    the descent into struct definitions (the [Named] case moves to the
    shorter context [stcs']); recursion on shapes is structural. *)
Fixpoint mem_load_f (fuel : nat) (stcs : list (stcname * struct_info))
    (sh : shape) (addr : word a) (dm : word a -> Prop) (m : word a -> word_lab a)
    {struct fuel} : option (v a) :=
  let fix go (sh : shape) (addr : word a) {struct sh} : option (v a) :=
    match sh with
    | One => if classical_dec (addr IN dm) then SOME (Val (m addr)) else NONE
    | Comb shapes =>
        let fix loads (shapes : list shape) (addr : word a) : option (list (v a)) :=
          match shapes with
          | [] => SOME []
          | shape :: shapes =>
              match go shape addr,
                    loads shapes (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) with
              | Some v, Some vs => SOME (v :: vs)
              | _, _ => NONE
              end
          end in
        match loads shapes addr with Some vs => SOME (RStruct vs) | None => NONE end
    | Named nm =>
        match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
        | (nm, info) :: stcs' =>
            match fuel with
            | O => NONE
            | Datatypes.S fuel' =>
                let fix flds (fields : list (fldname * shape)) (addr : word a)
                    : option (list (fldname * v a)) :=
                  match fields with
                  | [] => SOME []
                  | (fld, shape) :: fields =>
                      match mem_load_f fuel' stcs' shape addr dm m,
                            flds fields (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs' shape)) with
                      | Some v, Some vflds => SOME ((fld, v) :: vflds)
                      | _, _ => NONE
                      end
                  end in
                match flds (fields info) addr with
                | Some vflds => SOME (NStruct nm vflds)
                | None => NONE
                end
            end
        | _ => NONE
        end
    end in
  go sh addr.

Definition mem_loads_f (fuel : nat) (stcs : list (stcname * struct_info))
    : list shape -> word a -> (word a -> Prop) -> (word a -> word_lab a) -> option (list (v a)) :=
  fix loads shapes addr dm m :=
    match shapes with
    | [] => SOME []
    | shape :: shapes =>
        match mem_load_f fuel stcs shape addr dm m,
              loads shapes (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) dm m with
        | Some v, Some vs => SOME (v :: vs)
        | _, _ => NONE
        end
    end.

Definition mem_load_flds_f (fuel : nat) (stcs : list (stcname * struct_info))
    : list (fldname * shape) -> word a -> (word a -> Prop) -> (word a -> word_lab a)
      -> option (list (fldname * v a)) :=
  fix flds fields addr dm m :=
    match fields with
    | [] => SOME []
    | (fld, shape) :: fields =>
        match mem_load_f fuel stcs shape addr dm m,
              flds fields (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) dm m with
        | Some v, Some vflds => SOME ((fld, v) :: vflds)
        | _, _ => NONE
        end
    end.

Definition mem_load (sh : shape) (addr : word a) (dm : word a -> Prop)
    (m : word a -> word_lab a) (stcs : list (stcname * struct_info)) : option (v a) :=
  mem_load_f (Datatypes.S (List.length stcs)) stcs sh addr dm m.

Definition mem_loads (shapes : list shape) (addr : word a) (dm : word a -> Prop)
    (m : word a -> word_lab a) (stcs : list (stcname * struct_info)) : option (list (v a)) :=
  mem_loads_f (Datatypes.S (List.length stcs)) stcs shapes addr dm m.

Definition mem_load_flds (fields : list (fldname * shape)) (addr : word a)
    (dm : word a -> Prop) (m : word a -> word_lab a) (stcs : list (stcname * struct_info))
    : option (list (fldname * v a)) :=
  mem_load_flds_f (Datatypes.S (List.length stcs)) stcs fields addr dm m.

End Helpers.

(** ** HOL's [mem_load_def]

    Nested induction on shapes and the fuel lemma: any fuel above the
    struct-context length computes the same result. *)

Fixpoint shape_nested_ind (P : shape -> Prop) (H1 : P One)
    (H2 : forall l, Forall P l -> P (Comb l)) (H3 : forall n, P (Named n)) (sh : shape)
    : P sh :=
  match sh with
  | One => H1
  | Comb l => H2 l ((fix go (l : list shape) : Forall P l :=
                       match l with
                       | [] => Forall_nil _
                       | x :: xs => Forall_cons _ (shape_nested_ind P H1 H2 H3 x) (go xs)
                       end) l)
  | Named n => H3 n
  end.

Lemma length_dropWhile {A} (P : A -> bool) (l : list A) :
  (List.length (dropWhile P l) <= List.length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (P x); cbn; lia. Qed.

Section MemLoad.
Context {a : N}.

Lemma mem_load_f_Comb f (stcs : list (stcname * struct_info)) l (addr : word a) dm m :
  mem_load_f (Datatypes.S f) stcs (Comb l) addr dm m =
  match mem_loads_f (Datatypes.S f) stcs l addr dm m with
  | Some vs => SOME (RStruct vs) | None => NONE end.
Proof.
  cbn [mem_load_f].
  match goal with |- match ?F l addr with _ => _ end = _ =>
    assert (E : forall l0 addr0, F l0 addr0 = mem_loads_f (Datatypes.S f) stcs l0 addr0 dm m)
  end.
  { intros l0; induction l0 as [|x xs IH]; intros addr0; [reflexivity|].
    cbn [mem_loads_f]. rewrite <- IH. reflexivity. }
  rewrite E; reflexivity.
Qed.

Lemma mem_load_f_Named f (stcs : list (stcname * struct_info)) nm (addr : word a) dm m :
  mem_load_f f stcs (Named nm) addr dm m =
  match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
  | (nm, info) :: stcs' =>
      match f with
      | O => NONE
      | Datatypes.S f' =>
          match mem_load_flds_f f' stcs' (fields info) addr dm m with
          | Some vflds => SOME (NStruct nm vflds) | None => NONE
          end
      end
  | _ => NONE
  end.
Proof.
  destruct f as [|f]; cbn [mem_load_f];
    destruct (dropWhile _ stcs) as [|[nm' info] stcs']; try reflexivity.
  match goal with |- match ?F (fields info) addr with _ => _ end = _ =>
    assert (E : forall fl addr0, F fl addr0 = mem_load_flds_f f stcs' fl addr0 dm m)
  end.
  { intros fl; induction fl as [|[fld sh] fl IH]; intros addr0; [reflexivity|].
    cbn [mem_load_flds_f]. rewrite <- IH. reflexivity. }
  rewrite E; reflexivity.
Qed.

Lemma mem_load_f_fuel : forall f1 f2 (stcs : list (stcname * struct_info)) sh
    (addr : word a) dm m,
  (List.length stcs < f1)%nat -> (List.length stcs < f2)%nat ->
  mem_load_f f1 stcs sh addr dm m = mem_load_f f2 stcs sh addr dm m.
Proof.
  induction f1 as [|f1 IH]; intros f2 stcs sh addr dm m H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  revert addr; induction sh as [| l Hl | nm] using shape_nested_ind; intros addr.
  - reflexivity.
  - rewrite !mem_load_f_Comb.
    enough (E : forall addr0, mem_loads_f (Datatypes.S f1) stcs l addr0 dm m =
                              mem_loads_f (Datatypes.S f2) stcs l addr0 dm m)
      by (rewrite E; reflexivity).
    induction Hl as [|x xs Hx Hxs IHl]; intros addr0; [reflexivity|].
    cbn [mem_loads_f]. rewrite Hx, IHl. reflexivity.
  - rewrite !mem_load_f_Named.
    pose proof (length_dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs) as Hd.
    destruct (dropWhile _ stcs) as [|[nm' info] stcs'] eqn:E; [reflexivity|].
    cbn [List.length] in Hd.
    enough (Efl : forall fl addr0, mem_load_flds_f f1 stcs' fl addr0 dm m =
                                   mem_load_flds_f f2 stcs' fl addr0 dm m)
      by (rewrite Efl; reflexivity).
    intros fl; induction fl as [|[fld sh] fl IHf]; intros addr0; [reflexivity|].
    cbn [mem_load_flds_f]. rewrite (IH f2) by lia. rewrite IHf. reflexivity.
Qed.

Lemma mem_load_flds_f_fuel f1 f2 (stcs : list (stcname * struct_info)) fl (addr : word a) dm m :
  (List.length stcs < f1)%nat -> (List.length stcs < f2)%nat ->
  mem_load_flds_f f1 stcs fl addr dm m = mem_load_flds_f f2 stcs fl addr dm m.
Proof.
  intros H1 H2; revert addr; induction fl as [|[fld sh] fl IH]; intros addr; [reflexivity|].
  cbn [mem_load_flds_f]. rewrite (mem_load_f_fuel f1 f2) by assumption. rewrite IH. reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_load_def" *)
Theorem mem_load_def :
  (forall sh (addr : word a) dm m stcs,
     mem_load sh addr dm m stcs =
     match sh with
     | One => if classical_dec (addr IN dm) then SOME (Val (m addr)) else NONE
     | Comb shapes =>
         match mem_loads shapes addr dm m stcs with
         | SOME vs => SOME (RStruct vs)
         | NONE => NONE
         end
     | Named nm =>
         match dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs with
         | (nm, info) :: stcs' =>
             match mem_load_flds (fields info) addr dm m stcs' with
             | SOME vflds => SOME (NStruct nm vflds)
             | NONE => NONE
             end
         | _ => NONE
         end
     end) /\
  (forall (addr : word a) dm m stcs, mem_loads [] addr dm m stcs = SOME []) /\
  (forall shape shapes (addr : word a) dm m stcs,
     mem_loads (shape :: shapes) addr dm m stcs =
     match mem_load shape addr dm m stcs,
           mem_loads shapes (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape))%w dm m stcs with
     | SOME v, SOME vs => SOME (v :: vs)
     | _, _ => NONE
     end) /\
  (forall (addr : word a) dm m stcs, mem_load_flds [] addr dm m stcs = SOME []) /\
  (forall fld shape fields (addr : word a) dm m stcs,
     mem_load_flds ((fld, shape) :: fields) addr dm m stcs =
     match mem_load shape addr dm m stcs,
           mem_load_flds fields (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape))%w dm m stcs with
     | SOME v, SOME vflds => SOME ((fld, v) :: vflds)
     | _, _ => NONE
     end).
Proof.
  repeat split; intros; try reflexivity.
  destruct sh as [| shapes | nm].
  - reflexivity.
  - unfold mem_load, mem_loads; rewrite mem_load_f_Comb; reflexivity.
  - unfold mem_load, mem_load_flds; rewrite mem_load_f_Named.
    pose proof (length_dropWhile (fun '(n, i) => negb (bool_decide (n = nm))) stcs) as Hd.
    destruct (dropWhile _ stcs) as [|[nm' info] stcs']; [reflexivity|].
    cbn [List.length] in Hd.
    rewrite (mem_load_flds_f_fuel (List.length stcs) (Datatypes.S (List.length stcs'))) by lia.
    reflexivity.
Qed.

End MemLoad.

Section Eval.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "pan_op_def" *)
Definition pan_op (op : panop) (ws : list (word a)) : option (word a) :=
  match op, ws with
  | Mul, [w1; w2] => SOME (w1 * w2)
  | _, _ => NONE
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "pan_primop_def" *)
Definition pan_primop (pop : primop) (args : list (v a)) : option (v a) :=
  match pop with
  | AddCarry =>
      if andb (LENGTH args =? 3)%N (EVERY isValWord args) then
        let l := theValWord (EL 0 args) in
        let r := theValWord (EL 1 args) in
        let ci := theValWord (EL 2 args) in
        let '(res, co) := backend_common.word_add_carry l r ci in
        SOME (RStruct [ValWord res; ValWord co])
      else NONE
  end.

(** [eval] recurses structurally on expressions; in the [NStruct] case HOL
    evaluates [SND (UNZIP eflds)], computed here by mapping over the pairs
    ([eval_def] is HOL's equation). *)
Fixpoint eval (s : state a ffi_t) (e : exp a) {struct e} : option (v a) :=
  match e with
  | Const w => SOME (ValWord w)
  | Var Local v => FLOOKUP (locals s) v
  | Var Global v => FLOOKUP (globals s) v
  | panLang.RStruct es =>
      match OPT_MMAP (eval s) es with SOME vs => SOME (RStruct vs) | NONE => NONE end
  | RField index e =>
      match eval s e with
      | SOME (RStruct vs) => if (index <? LENGTH vs)%N then SOME (EL index vs) else NONE
      | _ => NONE
      end
  | panLang.NStruct nm eflds =>
      let field_names := MAP fst eflds in
      match ALOOKUP (structs s) nm with
      | SOME info =>
          let '(field_names', field_shapes) := UNZIP (fields info) in
          if bool_decide (field_names' = field_names) then
            match OPT_MMAP (fun p => eval s (snd p)) eflds with
            | SOME field_vals =>
                if EVERY (fun '(s, v) => bool_decide (s = shape_of v)) (ZIP (field_shapes, field_vals))
                then SOME (NStruct nm (ZIP (field_names, field_vals)))
                else NONE
            | NONE => NONE
            end
          else NONE
      | NONE => NONE
      end
  | NField fld e =>
      match eval s e with
      | SOME (NStruct nm vflds) =>
          if negb (bool_decide (ALOOKUP (structs s) nm = NONE)) then ALOOKUP vflds fld else NONE
      | _ => NONE
      end
  | Load shape addr =>
      if is_wf_shape (structs s) shape then
        match eval s addr with
        | SOME (Val (Word w)) => mem_load shape w (memaddrs s) (memory s) (structs s)
        | _ => NONE
        end
      else NONE
  | Load32 addr =>
      match eval s addr with
      | SOME (Val (Word w)) =>
          match mem_load_32 (memory s) (memaddrs s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (ValWord (w2w w))
          end
      | _ => NONE
      end
  | LoadByte addr =>
      match eval s addr with
      | SOME (Val (Word w)) =>
          match mem_load_byte (memory s) (memaddrs s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (ValWord (w2w w))
          end
      | _ => NONE
      end
  | Op op es =>
      match OPT_MMAP (eval s) es with
      | SOME ws =>
          if EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws
          then OPTION_MAP ValWord
                 (wordLang.word_op op (MAP (fun w => match w with Val (Word n) => n | _ => ARB end) ws))
          else NONE
      | _ => NONE
      end
  | Panop op es =>
      match OPT_MMAP (eval s) es with
      | SOME ws =>
          if EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws
          then OPTION_MAP ValWord
                 (pan_op op (MAP (fun w => match w with Val (Word n) => n | _ => ARB end) ws))
          else NONE
      | _ => NONE
      end
  | Cmp cmp e1 e2 =>
      match eval s e1, eval s e2 with
      | SOME (Val (Word w1)), SOME (Val (Word w2)) =>
          SOME (ValWord (if word_cmp cmp w1 w2 then n2w 1 else n2w 0))
      | _, _ => NONE
      end
  | Shift sh e1 e2 =>
      match eval s e1, eval s e2 with
      | SOME (Val (Word w1)), SOME (Val (Word w2)) =>
          OPTION_MAP ValWord (wordLang.word_sh sh w1 (w2n w2))
      | _, _ => NONE
      end
  | BaseAddr => SOME (ValWord (base_addr s))
  | TopAddr => SOME (ValWord (top_addr s))
  | BytesInWord => SOME (ValWord bytes_in_word)
  end.

End Eval.

Lemma UNZIP_MAP {A B} (l : list (A * B)) : UNZIP l = (MAP fst l, MAP snd l).
Proof. induction l as [|[x y] l IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

Lemma OPT_MMAP_MAP {A B C} (f : B -> option C) (g : A -> B) l :
  OPT_MMAP f (MAP g l) = OPT_MMAP (fun x => f (g x)) l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH; reflexivity. Qed.

Section EvalDef.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "eval_def" *)
Theorem eval_def :
  (forall (s : state a ffi_t) w,
     eval s (Const w) = SOME (ValWord w)) /\
  (forall (s : state a ffi_t) v,
     eval s (Var Local v) = FLOOKUP (locals s) v) /\
  (forall (s : state a ffi_t) v,
     eval s (Var Global v) = FLOOKUP (globals s) v) /\
  (forall (s : state a ffi_t) es,
     eval s (panLang.RStruct es) =
      match OPT_MMAP (eval s) es with SOME vs => SOME (RStruct vs) | NONE => NONE end) /\
  (forall (s : state a ffi_t) index e,
     eval s (RField index e) =
      match eval s e with
      | SOME (RStruct vs) => if (index <? LENGTH vs)%N then SOME (EL index vs) else NONE
      | _ => NONE
      end) /\
  (forall (s : state a ffi_t) nm eflds,
     eval s (panLang.NStruct nm eflds) =
      let '(field_names, field_exps) := UNZIP eflds in
      match ALOOKUP (structs s) nm with
      | SOME info =>
          let '(field_names', field_shapes) := UNZIP (fields info) in
          if bool_decide (field_names' = field_names) then
            match OPT_MMAP (eval s) field_exps with
            | SOME field_vals =>
                if EVERY (fun '(s, v) => bool_decide (s = shape_of v)) (ZIP (field_shapes, field_vals))
                then SOME (NStruct nm (ZIP (field_names, field_vals)))
                else NONE
            | NONE => NONE
            end
          else NONE
      | NONE => NONE
      end) /\
  (forall (s : state a ffi_t) fld e,
     eval s (NField fld e) =
      match eval s e with
      | SOME (NStruct nm vflds) =>
          if negb (bool_decide (ALOOKUP (structs s) nm = NONE)) then ALOOKUP vflds fld else NONE
      | _ => NONE
      end) /\
  (forall (s : state a ffi_t) shape addr,
     eval s (Load shape addr) =
      if is_wf_shape (structs s) shape then
        match eval s addr with
        | SOME (Val (Word w)) => mem_load shape w (memaddrs s) (memory s) (structs s)
        | _ => NONE
        end
      else NONE) /\
  (forall (s : state a ffi_t) addr,
     eval s (Load32 addr) =
      match eval s addr with
      | SOME (Val (Word w)) =>
          match mem_load_32 (memory s) (memaddrs s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (ValWord (w2w w))
          end
      | _ => NONE
      end) /\
  (forall (s : state a ffi_t) addr,
     eval s (LoadByte addr) =
      match eval s addr with
      | SOME (Val (Word w)) =>
          match mem_load_byte (memory s) (memaddrs s) (be s) w with
          | NONE => NONE
          | SOME w => SOME (ValWord (w2w w))
          end
      | _ => NONE
      end) /\
  (forall (s : state a ffi_t) op es,
     eval s (Op op es) =
      match OPT_MMAP (eval s) es with
      | SOME ws =>
          if EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws
          then OPTION_MAP ValWord
                 (wordLang.word_op op (MAP (fun w => match w with Val (Word n) => n | _ => ARB end) ws))
          else NONE
      | _ => NONE
      end) /\
  (forall (s : state a ffi_t) op es,
     eval s (Panop op es) =
      match OPT_MMAP (eval s) es with
      | SOME ws =>
          if EVERY (fun w => match w with Val (Word _) => true | _ => false end) ws
          then OPTION_MAP ValWord
                 (pan_op op (MAP (fun w => match w with Val (Word n) => n | _ => ARB end) ws))
          else NONE
      | _ => NONE
      end) /\
  (forall (s : state a ffi_t) cmp e1 e2,
     eval s (Cmp cmp e1 e2) =
      match eval s e1, eval s e2 with
      | SOME (Val (Word w1)), SOME (Val (Word w2)) =>
          SOME (ValWord (if word_cmp cmp w1 w2 then n2w 1 else n2w 0))
      | _, _ => NONE
      end) /\
  (forall (s : state a ffi_t) sh e1 e2,
     eval s (Shift sh e1 e2) =
      match eval s e1, eval s e2 with
      | SOME (Val (Word w1)), SOME (Val (Word w2)) =>
          OPTION_MAP ValWord (wordLang.word_sh sh w1 (w2n w2))
      | _, _ => NONE
      end) /\
  (forall (s : state a ffi_t) ,
     eval s (BaseAddr) = SOME (ValWord (base_addr s))) /\
  (forall (s : state a ffi_t) ,
     eval s (TopAddr) = SOME (ValWord (top_addr s))) /\
  (forall (s : state a ffi_t) ,
     eval s (BytesInWord) = SOME (ValWord bytes_in_word)).
Proof.
  repeat split; intros; try reflexivity.
  cbn [eval]; rewrite UNZIP_MAP, OPT_MMAP_MAP; reflexivity.
Qed.

End EvalDef.

Section Store.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_store_byte_def" *)
Definition mem_store_byte (m : word a -> word_lab a) (dm : word a -> Prop) (be : bool)
    (w : word a) (b : word8) : option (word a -> word_lab a) :=
  match m (byte_align w) with
  | Word v =>
      if classical_dec (byte_align w IN dm)
      then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
      else NONE
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "write_bytearray_def" *)
Fixpoint write_bytearray (a0 : word a) (bs : list word8) (m : word a -> word_lab a)
    (dm : word a -> Prop) (be : bool) : word a -> word_lab a :=
  match bs with
  | [] => m
  | b :: bs =>
      match mem_store_byte (write_bytearray (a0 + n2w 1) bs m dm be) dm be a0 b with
      | SOME m => m
      | NONE => m
      end
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_store_32_def" *)
Definition mem_store_32 (m : word a -> word_lab a) (dm : word a -> Prop) (be : bool)
    (w : word a) (hw : word32) : option (word a -> word_lab a) :=
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm) then
          let v0 := set_byte w (get_byte (n2w 0 : word32) hw be) v be in
          let v1 := set_byte (w + n2w 1) (get_byte (n2w 1) hw be) v0 be in
          let v2 := set_byte (w + n2w 2) (get_byte (n2w 2) hw be) v1 be in
          let v3 := set_byte (w + n2w 3) (get_byte (n2w 3) hw be) v2 be in
          SOME ((byte_align w =+ Word v3) m)
        else NONE
    end
  else NONE.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_store_def" *)
Definition mem_store (addr : word a) (w : word_lab a) (dm : word a -> Prop)
    (m : word a -> word_lab a) : option (word a -> word_lab a) :=
  if classical_dec (addr IN dm) then SOME ((addr =+ w) m) else NONE.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_stores_def" *)
Fixpoint mem_stores (a0 : word a) (ws : list (word_lab a)) (dm : word a -> Prop)
    (m : word a -> word_lab a) : option (word a -> word_lab a) :=
  match ws with
  | [] => SOME m
  | w :: ws =>
      match mem_store a0 w dm m with
      | SOME m' => mem_stores (a0 + bytes_in_word) ws dm m'
      | NONE => NONE
      end
  end.

(** HOL [flatten] (well-founded on [v_size]; structural here). *)
Fixpoint flatten (x : v a) : list (word_lab a) :=
  match x with
  | Val w => [w]
  | RStruct vs => FLAT (MAP flatten vs)
  | NStruct nm flds => FLAT (MAP (fun p => flatten (snd p)) flds)
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "flatten_def" *)
Theorem flatten_def :
  (forall w, flatten (Val w) = [w]) /\
  (forall vs, flatten (RStruct vs) = FLAT (MAP flatten vs)) /\
  (forall nm flds, flatten (NStruct nm flds) = FLAT (MAP flatten (MAP SND flds))).
Proof.
  repeat split; intros; try reflexivity.
  cbn [flatten]; f_equal; rewrite map_map; reflexivity.
Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "set_var_def" *)
Definition set_var (v0 : varname) (value : v a) (s : state a ffi_t) : state a ffi_t :=
  set_locals (locals s |+ (v0, value)) s.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "set_global_def" *)
Definition set_global (v0 : varname) (value : v a) (s : state a ffi_t) : state a ffi_t :=
  set_globals (globals s |+ (v0, value)) s.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "set_kvar_def" *)
Definition set_kvar (vk : varkind) (v0 : varname) (value : v a) (s : state a ffi_t)
    : state a ffi_t :=
  match vk with Local => set_var v0 value s | Global => set_global v0 value s end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "lookup_kvar_def" *)
Definition lookup_kvar (vk : varkind) (v0 : varname) (s : state a ffi_t) : option (v a) :=
  match vk with Local => FLOOKUP (locals s) v0 | Global => FLOOKUP (globals s) v0 end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "upd_locals_def" *)
Definition upd_locals (varargs : list (varname * v a)) (s : state a ffi_t) : state a ffi_t :=
  set_locals (FEMPTY |++ varargs) s.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "empty_locals_def" *)
Definition empty_locals (s : state a ffi_t) : state a ffi_t := set_locals FEMPTY s.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "dec_clock_def" *)
Definition dec_clock (s : state a ffi_t) : state a ffi_t := set_clock (clock s - 1) s.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_def" *)
Definition fix_clock {R} (old_s : state a ffi_t) (p : R * state a ffi_t) : R * state a ffi_t :=
  let '(res, new_s) := p in
  (res, set_clock (if clock old_s <? clock new_s then clock old_s else clock new_s) new_s).

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_IMP_LESS_EQ" *)
Theorem fix_clock_IMP_LESS_EQ : forall {R} (s : state a ffi_t) (x : R * state a ffi_t) res s1,
  fix_clock s x = (res, s1) -> (clock s1 <= clock s)%N.
Proof.
  intros R s [r s'] res s1 H; cbn in H; inversion H; subst; cbn.
  destruct (N.ltb_spec (clock s) (clock s')); lia.
Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "lookup_code_def" *)
Definition lookup_code
    (code0 : fmap funname (list (varname * shape) * (prog a * shape)))
    (fname : funname) (args : list (v a))
    : option (prog a * (fmap varname (v a) * shape)) :=
  match FLOOKUP code0 fname with
  | SOME (vshapes, (prog0, rshape)) =>
      if andb (ALL_DISTINCT (MAP fst vshapes))
              ⌜LIST_REL (fun vshape arg => snd vshape = shape_of arg) vshapes args⌝
      then SOME (prog0, (FEMPTY |++ ZIP (MAP fst vshapes, args), rshape))
      else NONE
  | _ => NONE
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "is_valid_value_def" *)
Definition is_valid_value (s : state a ffi_t) (vk : varkind) (v0 : varname) (value : v a) : bool :=
  match lookup_kvar vk v0 s with
  | SOME w => bool_decide (shape_of value = shape_of w)
  | NONE => false
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "res_var_def" *)
Definition res_var (lc : fmap varname (v a)) (p : varname * option (v a)) : fmap varname (v a) :=
  match p with
  | (n, NONE) => lc \\ n
  | (n, SOME v0) => lc |+ (n, v0)
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "nb_op_def" *)
Definition nb_op (op : opsize) : N :=
  match op with Op8 => 1 | Op16 => 2 | OpW => 0 | Op32 => 4 end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "sh_mem_load_def" *)
Definition sh_mem_load (vk : varkind) (v0 : varname) (addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  if (nb =? 0)%N then
    (if classical_dec (addr IN sh_memaddrs s) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_kvar vk v0 (ValWord (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s))
  else
    (if classical_dec (byte_align addr IN sh_memaddrs s) then
       match call_FFI (ffi s) (SharedMem MappedRead) [n2w nb] (word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
       | FFI_return new_ffi new_bytes =>
           (NONE, set_ffi new_ffi (set_kvar vk v0 (ValWord (word_of_bytes false (n2w 0) new_bytes)) s))
       end
     else (SOME Error, s)).

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "sh_mem_store_def" *)
Definition sh_mem_store (w addr : word a) (nb : N) (s : state a ffi_t)
    : option (result a) * state a ffi_t :=
  if (nb =? 0)%N then
    (if classical_dec (addr IN sh_memaddrs s) then
       match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
               (word_to_bytes w false ++ word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), s)
       | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
       end
     else (SOME Error, s))
  else
    (if classical_dec (byte_align addr IN sh_memaddrs s) then
       match call_FFI (ffi s) (SharedMem MappedWrite) [n2w nb]
               (TAKE nb (word_to_bytes w false) ++ word_to_bytes addr false) with
       | FFI_final outcome => (SOME (FinalFFI outcome), s)
       | FFI_return new_ffi new_bytes => (NONE, set_ffi new_ffi s)
       end
     else (SOME Error, s)).

End Store.

(** ** HOL's [mem_load_32_alt] and [mem_store_32_alt]

    HOL proves these by evaluation and bit-blasting; here via the byte
    identities of [byte/word_of_bytes4.v]. *)
Section Alt.
Context {a : N}.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_load_32_alt" *)
Theorem mem_load_32_alt : forall m dm be (w : word a),
  mem_load_32 m dm be w =
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm) then
          let b0 := get_byte w v be in
          let b1 := get_byte (w + n2w 1)%w v be in
          let b2 := get_byte (w + n2w 2)%w v be in
          let b3 := get_byte (w + n2w 3)%w v be in
          let v' := (if be
                     then (w2w b0 << 24 || w2w b1 << 16 || w2w b2 << 8 || w2w b3)%w
                     else (w2w b0 || w2w b1 << 8 || w2w b2 << 16 || w2w b3 << 24)%w) in
          SOME (v' : word32)
        else NONE
    end
  else NONE.
Proof.
  intros m dm be w; unfold mem_load_32.
  destruct (aligned 2 w); [|reflexivity].
  destruct (m (byte_align w)) as [v]; destruct (classical_dec _); [|reflexivity].
  cbv zeta; f_equal; destruct be; [apply word_of_bytes_4_be|apply word_of_bytes_4_le].
Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "mem_store_32_alt" *)
Theorem mem_store_32_alt : forall m dm be (w : word a) (hw : word32),
  mem_store_32 m dm be w hw =
  if aligned 2 w then
    match m (byte_align w) with
    | Word v =>
        if classical_dec (byte_align w IN dm) then
          if be then
            let v0 := set_byte w (w2w (hw >>> 24)%w) v be in
            let v1 := set_byte (w + n2w 1)%w (w2w (hw >>> 16)%w) v0 be in
            let v2 := set_byte (w + n2w 2)%w (w2w (hw >>> 8)%w) v1 be in
            let v3 := set_byte (w + n2w 3)%w (w2w hw) v2 be in
            SOME ((byte_align w =+ Word v3) m)
          else
            let v0 := set_byte w (w2w hw) v be in
            let v1 := set_byte (w + n2w 1)%w (w2w (hw >>> 8)%w) v0 be in
            let v2 := set_byte (w + n2w 2)%w (w2w (hw >>> 16)%w) v1 be in
            let v3 := set_byte (w + n2w 3)%w (w2w (hw >>> 24)%w) v2 be in
            SOME ((byte_align w =+ Word v3) m)
        else NONE
    end
  else NONE.
Proof.
  intros m dm be w hw; unfold mem_store_32.
  destruct (aligned 2 w); [|reflexivity].
  destruct (m (byte_align w)) as [v]; destruct (classical_dec _); [|reflexivity].
  destruct be; cbv zeta; unfold get_byte; f_equal.
  all: repeat f_equal.
  all: first [ apply word_eq_w2n; reflexivity
             | apply word_testbit_eq; intros j Hj; rewrite testbit_lsr;
               f_equal; unfold byte_index; cbn; lia ].
Qed.

End Alt.


Section Evaluate.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(** One step of HOL's [evaluate]: [go] evaluates at the same clock bound
    (structurally smaller programs), [lower] at a smaller clock. *)
Definition evaluate_body
    (go lower : prog a -> state a ffi_t -> option (result a) * state a ffi_t)
    (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
  match p with
  | Skip => (NONE, s)
  | Dec v0 sh e prog0 =>
      match eval s e with
      | SOME value =>
          if bool_decide (sh = shape_of value) then
            let '(res, st) := go prog0 (set_locals (locals s |+ (v0, value)) s) in
            (res, set_locals (res_var (locals st) (v0, FLOOKUP (locals s) v0)) st)
          else (SOME Error, s)
      | NONE => (SOME Error, s)
      end
  | Assign vk v0 src =>
      match eval s src with
      | SOME value =>
          if is_valid_value s vk v0 value then (NONE, set_kvar vk v0 value s)
          else (SOME Error, s)
      | NONE => (SOME Error, s)
      end
  | Primitive v0 pop es =>
      match OPT_MMAP (eval s) es with
      | SOME vs =>
          match pan_primop pop vs with
          | SOME value =>
              if is_valid_value s Local v0 value then (NONE, set_var v0 value s)
              else (SOME Error, s)
          | NONE => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | Store dst src =>
      match eval s dst, eval s src with
      | SOME (Val (Word addr)), SOME value =>
          match mem_stores addr (flatten value) (memaddrs s) (memory s) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | Store32 dst src =>
      match eval s dst, eval s src with
      | SOME (Val (Word adr)), SOME (Val (Word w)) =>
          match mem_store_32 (memory s) (memaddrs s) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | StoreByte dst src =>
      match eval s dst, eval s src with
      | SOME (Val (Word adr)), SOME (Val (Word w)) =>
          match mem_store_byte (memory s) (memaddrs s) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end
  | ShMemLoad op vk v0 ad =>
      match eval s ad with
      | SOME (Val (Word addr)) =>
          match lookup_kvar vk v0 s with
          | SOME (Val (Word _)) => sh_mem_load vk v0 addr (nb_op op) s
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | ShMemStore op ad e =>
      match eval s ad, eval s e with
      | SOME (Val (Word addr)), SOME (Val (Word bytes)) => sh_mem_store bytes addr (nb_op op) s
      | _, _ => (SOME Error, s)
      end
  | Seq c1 c2 =>
      let '(res, s1) := fix_clock s (go c1 s) in
      match res with NONE => go c2 s1 | _ => (res, s1) end
  | If e c1 c2 =>
      match eval s e with
      | SOME (Val (Word w)) =>
          if negb (bool_decide (w = n2w 0)) then go c1 s else go c2 s
      | _ => (SOME Error, s)
      end
  | panLang.Break => (SOME Break, s)
  | panLang.Continue => (SOME Continue, s)
  | While e c =>
      match eval s e with
      | SOME (Val (Word w)) =>
          if negb (bool_decide (w = n2w 0)) then
            if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
            else
              let '(res, s1) := fix_clock (dec_clock s) (go c (dec_clock s)) in
              match res with
              | SOME Continue => lower (While e c) s1
              | NONE => lower (While e c) s1
              | SOME Break => (NONE, s1)
              | _ => (res, s1)
              end
          else (NONE, s)
      | _ => (SOME Error, s)
      end
  | panLang.Return e =>
      match eval s e with
      | SOME value =>
          if (size_of_sh_with_ctxt (structs s) (shape_of value) <=? 32)%N
          then (SOME (Return value), empty_locals s)
          else (SOME Error, s)
      | _ => (SOME Error, s)
      end
  | Raise eid e =>
      match FLOOKUP (eshapes s) eid, eval s e with
      | SOME sh, SOME value =>
          if andb (bool_decide (shape_of value = sh))
                  (size_of_sh_with_ctxt (structs s) (shape_of value) <=? 32)%N
          then (SOME (Exception eid value), empty_locals s)
          else (SOME Error, s)
      | _, _ => (SOME Error, s)
      end
  | Tick =>
      if (clock s =? 0)%N then (SOME TimeOut, empty_locals s) else (NONE, dec_clock s)
  | Annot _ _ => (NONE, s)
  | Call caltyp fname argexps =>
      match OPT_MMAP (eval s) argexps with
      | SOME args =>
          match lookup_code (code s) fname args with
          | SOME (prog0, (newlocals, return_sh)) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
              else
                match fix_clock (set_locals newlocals (dec_clock s))
                        (lower prog0 (set_locals newlocals (dec_clock s))) with
                | (NONE, st) => (SOME Error, st)
                | (SOME Break, st) => (SOME Error, st)
                | (SOME Continue, st) => (SOME Error, st)
                | (SOME (Return retv), st) =>
                    if negb (bool_decide (shape_of retv = return_sh)) then (SOME Error, st)
                    else
                      match caltyp with
                      | NONE => (SOME (Return retv), empty_locals st)
                      | SOME (NONE, _) => (NONE, set_locals (locals s) st)
                      | SOME (SOME (rk, rt), _) =>
                          if is_valid_value s rk rt retv
                          then (NONE, set_kvar rk rt retv (set_locals (locals s) st))
                          else (SOME Error, st)
                      end
                | (SOME (Exception eid exn), st) =>
                    match caltyp with
                    | NONE => (SOME (Exception eid exn), empty_locals st)
                    | SOME (_, NONE) => (SOME (Exception eid exn), empty_locals st)
                    | SOME (_, SOME (eid', (evar, p))) =>
                        if bool_decide (eid = eid') then
                          match FLOOKUP (eshapes s) eid with
                          | SOME sh =>
                              if andb (bool_decide (shape_of exn = sh))
                                      (is_valid_value s Local evar exn)
                              then lower p (set_var evar exn (set_locals (locals s) st))
                              else (SOME Error, st)
                          | NONE => (SOME Error, st)
                          end
                        else (SOME (Exception eid exn), empty_locals st)
                    end
                | (res, st) => (res, empty_locals st)
                end
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | DecCall rt shape fname argexps prog1 =>
      match OPT_MMAP (eval s) argexps with
      | SOME args =>
          match lookup_code (code s) fname args with
          | SOME (prog0, (newlocals, return_sh)) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
              else
                match fix_clock (set_locals newlocals (dec_clock s))
                        (lower prog0 (set_locals newlocals (dec_clock s))) with
                | (NONE, st) => (SOME Error, st)
                | (SOME Break, st) => (SOME Error, st)
                | (SOME Continue, st) => (SOME Error, st)
                | (SOME (Return retv), st) =>
                    if andb (bool_decide (shape_of retv = shape))
                            (bool_decide (shape_of retv = return_sh)) then
                      let '(res', st') :=
                        lower prog1 (set_var rt retv (set_locals (locals s) st)) in
                      (res', set_locals (res_var (locals st') (rt, FLOOKUP (locals s) rt)) st')
                    else (SOME Error, st)
                | (res, st) => (res, empty_locals st)
                end
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end
  | ExtCall ffi_index ptr1 len1 ptr2 len2 =>
      match eval s ptr1, eval s len1, eval s ptr2, eval s len2 with
      | SOME (Val (Word sz1)), SOME (Val (Word ad1)), SOME (Val (Word sz2)), SOME (Val (Word ad2)) =>
          match read_bytearray sz1 (w2n ad1) (mem_load_byte (memory s) (memaddrs s) (be s)),
                read_bytearray sz2 (w2n ad2) (mem_load_byte (memory s) (memaddrs s) (be s)) with
          | SOME bytes, SOME bytes2 =>
              match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
              | FFI_return new_ffi new_bytes =>
                  let nmem := write_bytearray sz2 new_bytes (memory s) (memaddrs s) (be s) in
                  (NONE, set_ffi new_ffi (set_memory nmem s))
              end
          | _, _ => (SOME Error, s)
          end
      | _, _, _, _ => (SOME Error, s)
      end
  end.

Fixpoint evaluate_c (cf : nat) (p0 : prog a) (s0 : state a ffi_t) {struct cf}
    : option (result a) * state a ffi_t :=
  let lower (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
    match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c cf' p s end in
  let fix go (p : prog a) (s : state a ffi_t) {struct p} : option (result a) * state a ffi_t :=
    evaluate_body go lower p s in
  go p0 s0.

(** HOL [evaluate]: run with a clock fuel above the state's clock. *)
Definition evaluate (x : prog a * state a ffi_t) : option (result a) * state a ffi_t :=
  let '(p, s) := x in evaluate_c (Datatypes.S (N.to_nat (clock s))) p s.

End Evaluate.

(** ** HOL's [evaluate_def]

    Termination measure, as in HOL: the clock, then the program size
    (Galette counts constructors; only the existence of a decreasing measure
    matters). *)
Section EvaluateEqns.
Context {a : N} {ffi_t : Type}.

Fixpoint psize (p : prog a) : nat :=
  match p with
  | Dec _ _ _ p => Datatypes.S (psize p)
  | Seq c1 c2 => Datatypes.S (psize c1 + psize c2)
  | If _ c1 c2 => Datatypes.S (psize c1 + psize c2)
  | While _ c => Datatypes.S (psize c)
  | DecCall _ _ _ _ p => Datatypes.S (psize p)
  | _ => 1
  end.

Definition eval_lt (x y : prog a * state a ffi_t) : Prop :=
  (clock (snd x) < clock (snd y))%N \/
  (clock (snd x) = clock (snd y) /\ (psize (fst x) < psize (fst y))%nat).

Lemma eval_lt_wf : well_founded eval_lt.
Proof.
  intros [p s].
  remember (N.to_nat (clock s)) as c eqn:Hc. revert p s Hc.
  induction c as [c IHc] using (well_founded_induction lt_wf).
  intros p s Hc.
  remember (psize p) as n eqn:Hn. revert p s Hc Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros p s Hc Hn; constructor; intros [p' s'] [Hlt|[Heq Hlt]]; cbn in *.
  - eapply IHc; [|reflexivity]. lia.
  - eapply IHn; [| |reflexivity]; [lia|]. lia.
Qed.

Definition lowerF (cf : nat) (p : prog a) (s : state a ffi_t) : option (result a) * state a ffi_t :=
  match cf with O => (SOME Error, s) | Datatypes.S cf' => evaluate_c cf' p s end.

Lemma evaluate_c_unfold cf p s :
  evaluate_c cf p s = evaluate_body (evaluate_c cf) (lowerF cf) p s.
Proof. destruct cf, p; reflexivity. Qed.

(** Every recursive call of [evaluate_body] is smaller in [eval_lt]; so two
    instances that agree on smaller arguments compute the same step. *)
Ltac clock_facts :=
  repeat match goal with
         | H : fix_clock _ _ = (_, _) |- _ =>
             let Hle := fresh "Hle" in
             pose proof (fix_clock_IMP_LESS_EQ _ _ _ _ H) as Hle; clear H
         | H : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in H
         end;
  repeat match goal with |- context [set_kvar ?vk _ _ _] => is_var vk; destruct vk end;
  cbn [clock set_locals set_globals set_structs set_var set_global set_kvar set_memory set_ffi set_clock
       dec_clock empty_locals psize] in *.

Ltac prove_eval_lt := unfold eval_lt; cbn [fst snd]; clock_facts; lia.
Ltac prove_clock_lt := clock_facts; lia.

Lemma evaluate_body_ext
    (go1 go2 lo1 lo2 : prog a -> state a ffi_t -> option (result a) * state a ffi_t) p s :
  (forall p' s', eval_lt (p', s') (p, s) -> go1 p' s' = go2 p' s') ->
  (forall p' s', (clock s' < clock s)%N -> lo1 p' s' = lo2 p' s') ->
  evaluate_body go1 lo1 p s = evaluate_body go2 lo2 p s.
Proof.
  intros Hgo Hlo.
  destruct p; cbn [evaluate_body];
  repeat first
    [ reflexivity
    | match goal with
      | |- context [go1 ?p' ?s'] => rewrite (Hgo p' s') by prove_eval_lt
      | |- context [lo1 ?p' ?s'] => rewrite (Hlo p' s') by prove_clock_lt
      end
    | match goal with
      | |- context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E
      end ].
Qed.

Lemma evaluate_c_fuel : forall (x : prog a * state a ffi_t) cf1 cf2,
  (N.to_nat (clock (snd x)) < cf1)%nat -> (N.to_nat (clock (snd x)) < cf2)%nat ->
  evaluate_c cf1 (fst x) (snd x) = evaluate_c cf2 (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros cf1 cf2 H1 H2; cbn [fst snd] in *.
  rewrite !evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Hlt. apply (IH (p', s') Hlt); cbn;
      destruct Hlt as [Hlt|[Heq _]]; cbn in *; lia.
  - intros p' s' Hlt. destruct cf1 as [|cf1]; [lia|]. destruct cf2 as [|cf2]; [lia|].
    cbn [lowerF]. apply (IH (p', s')); [left; exact Hlt| |]; cbn; lia.
Qed.

Lemma evaluate_eq_c cf (p : prog a) (s : state a ffi_t) :
  (N.to_nat (clock s) < cf)%nat -> evaluate (p, s) = evaluate_c cf p s.
Proof.
  intros H; unfold evaluate.
  apply (evaluate_c_fuel (p, s)); cbn; lia.
Qed.

(** [evaluate] is a fixed point of its one-step body. *)
Lemma evaluate_eqn (p : prog a) (s : state a ffi_t) :
  evaluate (p, s) =
  evaluate_body (fun p' s' => evaluate (p', s')) (fun p' s' => evaluate (p', s')) p s.
Proof.
  rewrite (evaluate_eq_c (Datatypes.S (N.to_nat (clock s)))) by lia.
  rewrite evaluate_c_unfold. apply evaluate_body_ext.
  - intros p' s' Hlt. symmetry; apply evaluate_eq_c.
    destruct Hlt as [Hlt|[Heq _]]; cbn in *; lia.
  - intros p' s' Hlt. cbn [lowerF]. symmetry; apply evaluate_eq_c. lia.
Qed.


Ltac clock_step IH H :=
  repeat first
    [ match type of H with
      | evaluate (?p', ?s'') = (?r', ?t) =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t H));
          clear H; clock_facts; lia
      | (_, _) = (_, _) => injection H as <- <-; clock_facts; lia
      end
    | match goal with
      | E : evaluate (?p', ?s'') = (?r', ?t) |- _ =>
          let Hc := fresh "Hc" in
          assert (Hc : (clock t <= clock s'')%N)
            by (apply (IH (p', s'') ltac:(prove_eval_lt) r' t E));
          clear E
      | E : fix_clock _ _ = (_, _) |- _ =>
          let Hle := fresh "Hle" in
          pose proof (fix_clock_IMP_LESS_EQ _ _ _ _ E) as Hle; clear E
      | E : (clock _ =? 0)%N = false |- _ => apply N.eqb_neq in E
      end
    | match type of H with
      | context [match ?x with _ => _ end] =>
          let E := fresh "E" in destruct x eqn:E; cbn beta iota zeta in H
      end ].

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "evaluate_clock" *)
Theorem evaluate_clock : forall (prog0 : prog a) (s : state a ffi_t) r s',
  evaluate (prog0, s) = (r, s') -> (clock s' <= clock s)%N.
Proof.
  enough (G : forall x : prog a * state a ffi_t, forall r s',
            evaluate x = (r, s') -> (clock s' <= clock (snd x))%N)
    by (intros p s r s' H; exact (G (p, s) r s' H)).
  intros x; induction x as [[p s] IH] using (well_founded_induction eval_lt_wf).
  intros r s' H; cbn [snd].
  rewrite evaluate_eqn in H.
  destruct p; cbn [evaluate_body] in H; unfold sh_mem_load, sh_mem_store in H;
    clock_step IH H.
Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "fix_clock_evaluate" *)
Theorem fix_clock_evaluate : forall (prog0 : prog a) (s : state a ffi_t),
  fix_clock s (evaluate (prog0, s)) = evaluate (prog0, s).
Proof.
  intros p s; destruct (evaluate (p, s)) as [r s'] eqn:E.
  pose proof (evaluate_clock p s r s' E) as Hc.
  unfold fix_clock; f_equal.
  destruct (N.ltb_spec (clock s) (clock s')); [lia|].
  destruct s'; reflexivity.
Qed.

End EvaluateEqns.

Section EvaluateDef.
Context {a : N} {ffi_t : Type}.
Local Open Scope word_scope.

(** HOL's [evaluate_def] as rebound after [fix_clock_evaluate] (the
    [compute] form CakeML's proofs use). *)
(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "evaluate_def" 780 *)
Theorem evaluate_def :
  (forall (s : state a ffi_t),
     evaluate (Skip, s) =
 (NONE, s)) /\
  (forall v0 sh e prog0 (s : state a ffi_t),
     evaluate (Dec v0 sh e prog0, s) =
      match eval s e with
      | SOME value =>
          if bool_decide (sh = shape_of value) then
            let '(res, st) := evaluate (prog0, (set_locals (locals s |+ (v0, value)) s)) in
            (res, set_locals (res_var (locals st) (v0, FLOOKUP (locals s) v0)) st)
          else (SOME Error, s)
      | NONE => (SOME Error, s)
      end) /\
  (forall vk v0 src (s : state a ffi_t),
     evaluate (Assign vk v0 src, s) =
      match eval s src with
      | SOME value =>
          if is_valid_value s vk v0 value then (NONE, set_kvar vk v0 value s)
          else (SOME Error, s)
      | NONE => (SOME Error, s)
      end) /\
  (forall v0 pop es (s : state a ffi_t),
     evaluate (Primitive v0 pop es, s) =
      match OPT_MMAP (eval s) es with
      | SOME vs =>
          match pan_primop pop vs with
          | SOME value =>
              if is_valid_value s Local v0 value then (NONE, set_var v0 value s)
              else (SOME Error, s)
          | NONE => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (Store dst src, s) =
      match eval s dst, eval s src with
      | SOME (Val (Word addr)), SOME value =>
          match mem_stores addr (flatten value) (memaddrs s) (memory s) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (Store32 dst src, s) =
      match eval s dst, eval s src with
      | SOME (Val (Word adr)), SOME (Val (Word w)) =>
          match mem_store_32 (memory s) (memaddrs s) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall dst src (s : state a ffi_t),
     evaluate (StoreByte dst src, s) =
      match eval s dst, eval s src with
      | SOME (Val (Word adr)), SOME (Val (Word w)) =>
          match mem_store_byte (memory s) (memaddrs s) (be s) adr (w2w w) with
          | SOME m => (NONE, set_memory m s)
          | NONE => (SOME Error, s)
          end
      | _, _ => (SOME Error, s)
      end) /\
  (forall op vk v0 ad (s : state a ffi_t),
     evaluate (ShMemLoad op vk v0 ad, s) =
      match eval s ad with
      | SOME (Val (Word addr)) =>
          match lookup_kvar vk v0 s with
          | SOME (Val (Word _)) => sh_mem_load vk v0 addr (nb_op op) s
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end) /\
  (forall op ad e (s : state a ffi_t),
     evaluate (ShMemStore op ad e, s) =
      match eval s ad, eval s e with
      | SOME (Val (Word addr)), SOME (Val (Word bytes)) => sh_mem_store bytes addr (nb_op op) s
      | _, _ => (SOME Error, s)
      end) /\
  (forall c1 c2 (s : state a ffi_t),
     evaluate (Seq c1 c2, s) =
      let '(res, s1) := evaluate (c1, s) in
      if ⌜res = NONE⌝ then evaluate (c2, s1) else (res, s1)) /\
  (forall e c1 c2 (s : state a ffi_t),
     evaluate (If e c1 c2, s) =
      match eval s e with
      | SOME (Val (Word w)) =>
          evaluate (if negb (bool_decide (w = n2w 0)) then c1 else c2, s)
      | _ => (SOME Error, s)
      end) /\
  (forall (s : state a ffi_t),
     evaluate (panLang.Break, s) =
 (SOME Break, s)) /\
  (forall (s : state a ffi_t),
     evaluate (panLang.Continue, s) =
 (SOME Continue, s)) /\
  (forall e c (s : state a ffi_t),
     evaluate (While e c, s) =
      match eval s e with
      | SOME (Val (Word w)) =>
          if negb (bool_decide (w = n2w 0)) then
            if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
            else
              let '(res, s1) := fix_clock (dec_clock s) (evaluate (c, (dec_clock s))) in
              match res with
              | SOME Continue => evaluate ((While e c), s1)
              | NONE => evaluate ((While e c), s1)
              | SOME Break => (NONE, s1)
              | _ => (res, s1)
              end
          else (NONE, s)
      | _ => (SOME Error, s)
      end) /\
  (forall e (s : state a ffi_t),
     evaluate (panLang.Return e, s) =
      match eval s e with
      | SOME value =>
          if (size_of_sh_with_ctxt (structs s) (shape_of value) <=? 32)%N
          then (SOME (Return value), empty_locals s)
          else (SOME Error, s)
      | _ => (SOME Error, s)
      end) /\
  (forall eid e (s : state a ffi_t),
     evaluate (Raise eid e, s) =
      match FLOOKUP (eshapes s) eid, eval s e with
      | SOME sh, SOME value =>
          if andb (bool_decide (shape_of value = sh))
                  (size_of_sh_with_ctxt (structs s) (shape_of value) <=? 32)%N
          then (SOME (Exception eid value), empty_locals s)
          else (SOME Error, s)
      | _, _ => (SOME Error, s)
      end) /\
  (forall (s : state a ffi_t),
     evaluate (Tick, s) =
      if (clock s =? 0)%N then (SOME TimeOut, empty_locals s) else (NONE, dec_clock s)) /\
  (forall s1 s2 (s : state a ffi_t),
     evaluate (Annot s1 s2, s) =
 (NONE, s)) /\
  (forall caltyp fname argexps (s : state a ffi_t),
     evaluate (Call caltyp fname argexps, s) =
      match OPT_MMAP (eval s) argexps with
      | SOME args =>
          match lookup_code (code s) fname args with
          | SOME (prog0, (newlocals, return_sh)) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
              else
                match fix_clock (set_locals newlocals (dec_clock s))
                        (evaluate (prog0, (set_locals newlocals (dec_clock s)))) with
                | (NONE, st) => (SOME Error, st)
                | (SOME Break, st) => (SOME Error, st)
                | (SOME Continue, st) => (SOME Error, st)
                | (SOME (Return retv), st) =>
                    if negb (bool_decide (shape_of retv = return_sh)) then (SOME Error, st)
                    else
                      match caltyp with
                      | NONE => (SOME (Return retv), empty_locals st)
                      | SOME (NONE, _) => (NONE, set_locals (locals s) st)
                      | SOME (SOME (rk, rt), _) =>
                          if is_valid_value s rk rt retv
                          then (NONE, set_kvar rk rt retv (set_locals (locals s) st))
                          else (SOME Error, st)
                      end
                | (SOME (Exception eid exn), st) =>
                    match caltyp with
                    | NONE => (SOME (Exception eid exn), empty_locals st)
                    | SOME (_, NONE) => (SOME (Exception eid exn), empty_locals st)
                    | SOME (_, SOME (eid', (evar, p))) =>
                        if bool_decide (eid = eid') then
                          match FLOOKUP (eshapes s) eid with
                          | SOME sh =>
                              if andb (bool_decide (shape_of exn = sh))
                                      (is_valid_value s Local evar exn)
                              then evaluate (p, (set_var evar exn (set_locals (locals s) st)))
                              else (SOME Error, st)
                          | NONE => (SOME Error, st)
                          end
                        else (SOME (Exception eid exn), empty_locals st)
                    end
                | (res, st) => (res, empty_locals st)
                end
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end) /\
  (forall rt shape fname argexps prog1 (s : state a ffi_t),
     evaluate (DecCall rt shape fname argexps prog1, s) =
      match OPT_MMAP (eval s) argexps with
      | SOME args =>
          match lookup_code (code s) fname args with
          | SOME (prog0, (newlocals, return_sh)) =>
              if (clock s =? 0)%N then (SOME TimeOut, empty_locals s)
              else
                match fix_clock (set_locals newlocals (dec_clock s))
                        (evaluate (prog0, (set_locals newlocals (dec_clock s)))) with
                | (NONE, st) => (SOME Error, st)
                | (SOME Break, st) => (SOME Error, st)
                | (SOME Continue, st) => (SOME Error, st)
                | (SOME (Return retv), st) =>
                    if andb (bool_decide (shape_of retv = shape))
                            (bool_decide (shape_of retv = return_sh)) then
                      let '(res', st') :=
                        evaluate (prog1, (set_var rt retv (set_locals (locals s) st))) in
                      (res', set_locals (res_var (locals st') (rt, FLOOKUP (locals s) rt)) st')
                    else (SOME Error, st)
                | (res, st) => (res, empty_locals st)
                end
          | _ => (SOME Error, s)
          end
      | _ => (SOME Error, s)
      end) /\
  (forall ffi_index ptr1 len1 ptr2 len2 (s : state a ffi_t),
     evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s) =
      match eval s ptr1, eval s len1, eval s ptr2, eval s len2 with
      | SOME (Val (Word sz1)), SOME (Val (Word ad1)), SOME (Val (Word sz2)), SOME (Val (Word ad2)) =>
          match read_bytearray sz1 (w2n ad1) (mem_load_byte (memory s) (memaddrs s) (be s)),
                read_bytearray sz2 (w2n ad2) (mem_load_byte (memory s) (memaddrs s) (be s)) with
          | SOME bytes, SOME bytes2 =>
              match call_FFI (ffi s) (ffi.ExtCall ffi_index) bytes bytes2 with
              | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
              | FFI_return new_ffi new_bytes =>
                  let nmem := write_bytearray sz2 new_bytes (memory s) (memaddrs s) (be s) in
                  (NONE, set_ffi new_ffi (set_memory nmem s))
              end
          | _, _ => (SOME Error, s)
          end
      | _, _, _, _ => (SOME Error, s)
      end).
Proof.
  repeat split; intros; rewrite evaluate_eqn; cbn [evaluate_body];
    rewrite ?fix_clock_evaluate; try reflexivity.
  all: try (destruct (evaluate (c1, s)) as [[res|] s1]; cbn beta iota;
            unfold bool_decide; destruct (decide _) as [Hd|Hd];
            solve [reflexivity | discriminate | exfalso; apply Hd; reflexivity]).
  all: try (destruct (eval s e) as [[[w]| |]|]; try reflexivity;
            destruct (negb _); reflexivity).
Qed.

End EvaluateDef.

(** ** Observable semantics and declarations *)
Section Semantics.
Context {a : N} {ffi_t : Type}.

#[local] Instance behaviour_inhabited : Inhabited behaviour := Fail.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "semantics_def" *)
Definition semantics (s : state a ffi_t) (start : funname) : behaviour :=
  let prog0 := @panLang.Call a NONE start [] in
  if classical_dec (exists k,
       match fst (evaluate (prog0, set_clock k s)) with
       | SOME TimeOut => False
       | SOME (FinalFFI _) => False
       | SOME (Return _) => False
       | _ => True
       end)
  then Fail
  else
    match some (fun res => exists k t r outcome,
             evaluate (prog0, set_clock k s) = (r, t) /\
             match r with
             | SOME (FinalFFI e) => outcome = FFI_outcome e
             | SOME (Return _) => outcome = Success
             | _ => False
             end /\
             res = Terminate outcome (io_events (ffi t))) with
    | SOME res => res
    | NONE =>
        Diverge (build_lprefix_lub
                   (IMAGE (fun k => fromList (io_events (ffi (snd (evaluate (prog0, set_clock k s))))))
                          UNIV))
    end.

(** HOL [s with code := s.code |+ ...] etc. *)
Definition set_code x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) x s.(eshapes) s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).
Definition set_eshapes x (s : state a ffi_t) := mk_state s.(locals) s.(globals) s.(structs) s.(code) x s.(memory) s.(memaddrs) s.(sh_memaddrs) s.(clock) s.(be) s.(ffi) s.(base_addr) s.(top_addr).

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "evaluate_decls_def" *)
Fixpoint evaluate_decls (s : state a ffi_t) (ds : list (decl a)) : option (state a ffi_t) :=
  match ds with
  | [] => SOME s
  | Name nm flds :: ds => evaluate_decls s ds
  | Decl sh v0 e :: ds =>
      match eval (set_locals FEMPTY s) e with
      | SOME res =>
          if bool_decide (sh = shape_of res)
          then evaluate_decls (set_globals (globals s |+ (v0, res)) s) ds
          else NONE
      | NONE => NONE
      end
  | Function fi :: ds =>
      if andb (EVERY (is_wf_shape (structs s) ∘ snd) (params fi))
              (is_wf_shape (structs s) (fun_decl_return fi))
      then evaluate_decls
             (set_code (code s |+ (name fi, (params fi, (body fi, fun_decl_return fi)))) s) ds
      else NONE
  | ExnDecl eid sh :: ds =>
      if andb (bool_decide (FLOOKUP (eshapes s) eid = NONE)) (is_wf_shape (structs s) sh)
      then evaluate_decls (set_eshapes (eshapes s |+ (eid, sh)) s) ds
      else NONE
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "decs_stcnames_def" *)
Fixpoint decs_stcnames (st_ctxt : list (stcname * struct_info)) (ds : list (decl a))
    : option (list (stcname * struct_info)) :=
  match ds with
  | [] => SOME st_ctxt
  | Name nm flds :: ds =>
      match ALOOKUP st_ctxt nm with
      | SOME info => NONE
      | NONE =>
          if ALL_DISTINCT (MAP fst flds) then
            let shs := MAP snd flds in
            if EVERY (is_wf_shape st_ctxt) shs then
              let info := {| fields := flds; size := size_of_sh_with_ctxt st_ctxt (Comb shs) |} in
              decs_stcnames ((nm, info) :: st_ctxt) ds
            else NONE
          else NONE
      end
  | Decl sh v0 e :: ds => decs_stcnames st_ctxt ds
  | Function fi :: ds => decs_stcnames st_ctxt ds
  | ExnDecl eid sh :: ds => decs_stcnames st_ctxt ds
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "semantics_decls_def" *)
Definition semantics_decls (s : state a ffi_t) (start : funname) (decls : list (decl a)) : behaviour :=
  match decs_stcnames [] decls with
  | NONE => Fail
  | SOME st_ctxt =>
      match evaluate_decls (set_structs st_ctxt s) decls with
      | NONE => Fail
      | SOME s' => semantics s' start
      end
  end.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "kvar_simps" *)
Theorem kvar_simps : forall v0 value (s : state a ffi_t),
  set_kvar Local v0 value s = set_var v0 value s /\
  set_kvar Global v0 value s = set_global v0 value s /\
  lookup_kvar Local v0 s = FLOOKUP (locals s) v0 /\
  lookup_kvar Global v0 s = FLOOKUP (globals s) v0.
Proof. repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "is_valid_value_simps" *)
Theorem is_valid_value_simps : forall (s : state a ffi_t) v0 value,
  is_valid_value s Local v0 value =
    match FLOOKUP (locals s) v0 with
    | SOME w => bool_decide (shape_of value = shape_of w)
    | NONE => false
    end /\
  is_valid_value s Global v0 value =
    match FLOOKUP (globals s) v0 with
    | SOME w => bool_decide (shape_of value = shape_of w)
    | NONE => false
    end.
Proof. repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "is_valid_value_simps2" *)
Theorem is_valid_value_simps2 : forall (s : state a ffi_t) k ffi0 cd m vk v0 vl,
  is_valid_value (set_clock k s) vk v0 vl = is_valid_value s vk v0 vl /\
  is_valid_value (set_ffi ffi0 s) vk v0 vl = is_valid_value s vk v0 vl /\
  is_valid_value (set_code cd s) vk v0 vl = is_valid_value s vk v0 vl /\
  is_valid_value (set_memory m s) vk v0 vl = is_valid_value s vk v0 vl /\
  lookup_kvar vk v0 (set_clock k s) = lookup_kvar vk v0 s /\
  lookup_kvar vk v0 (set_ffi ffi0 s) = lookup_kvar vk v0 s /\
  lookup_kvar vk v0 (set_code cd s) = lookup_kvar vk v0 s /\
  lookup_kvar vk v0 (set_memory m s) = lookup_kvar vk v0 s.
Proof. intros; destruct vk; repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "kvar_defs" *)
Theorem kvar_defs :
  (forall v0 value (s : state a ffi_t), set_var v0 value s = set_locals (locals s |+ (v0, value)) s) /\
  (forall v0 value (s : state a ffi_t), set_global v0 value s = set_globals (globals s |+ (v0, value)) s) /\
  (forall vk v0 value (s : state a ffi_t),
     set_kvar vk v0 value s = match vk with Local => set_var v0 value s | Global => set_global v0 value s end) /\
  (forall (s : state a ffi_t) vk v0 value,
     is_valid_value s vk v0 value =
     match lookup_kvar vk v0 s with
     | SOME w => bool_decide (shape_of value = shape_of w)
     | NONE => false
     end) /\
  (forall vk v0 (s : state a ffi_t),
     lookup_kvar vk v0 s = match vk with Local => FLOOKUP (locals s) v0 | Global => FLOOKUP (globals s) v0 end).
Proof. repeat split. Qed.

(*! HOL "cakeml/pancake/semantics/panSemScript.sml" "vshapes_args_rel_imp_eq_len_MAP" *)
Theorem vshapes_args_rel_imp_eq_len_MAP : forall (vshapes : list (varname * shape)) (args : list (v a)),
  LIST_REL (fun vshape arg => snd vshape = shape_of arg) vshapes args ->
  LENGTH vshapes = LENGTH args /\ MAP snd vshapes = MAP shape_of args.
Proof.
  intros vshapes args H; induction H as [|x y l1 l2 Hxy Hl IH]; [split; reflexivity|].
  destruct IH as [IH1 IH2]; cbn [LENGTH MAP List.map]; rewrite IH1, Hxy, IH2; split; reflexivity.
Qed.

End Semantics.
