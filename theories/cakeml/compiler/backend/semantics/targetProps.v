(** * CakeML [targetProps]: properties of the target semantics

    Port of [cakeml/compiler/backend/semantics/targetPropsScript.sml].

    - As in [targetSem], HOL's [mc with f := v] is [set_<f> v mc] and HOL
      tuples are right-nested ([(app, (mc, ffi))]).
    - [find_next_interference] recurses on the clock ([num_rec]) like
      [targetSem]'s [evaluate]; HOL's equation is [find_next_interference_def].
      [interference_app_seq] and [interference_count] use [num_rec] too.
    - [next_interference] is HOL's [some res. ...]; Rocq's [some] needs an
      inhabitant of the result type, which is built from the arguments
      (the choice is irrelevant: the result is unique,
      [find_next_interference_unique]).
    - HOL's predicates [P] on applications are [bool]-valued (as in HOL,
      where [P app] is also used in [if P app then 1 else 0]).
    - Untagged Galette helpers: [some_SOME], [some_NONE], [some_unique],
      [interference_pos_SOME], [find_next_interference_body_mono],
      [evaluate_body_rel], [evaluate_clock_le], [call_FFI_prefix],
      [DROP_LENGTH_self], [bytes_in_memory_DROP], [evaluate_one_step],
      [encoded_bytes_in_mem_intro].
    - Not yet ported: [encoder_correct_asm_step_target_state_rel] and
      [encoder_correct_RTC_asm_step_target_state_rel], which need HOL's
      [FUNPOW] (with [FOLDR_FUNPOW], [FUNPOW_refl_trans_chain]) and
      [asmProps]' [asserts2_every]; [lab_to_targetProof] does not use them. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require lemmas.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.list.src Require Import rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.relation Require Import relation.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require lab_to_target.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem.
Open Scope N_scope.

Section Shift.
Context {a : N} {B C : Type}.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "shift_interfer_def" *)
Definition shift_interfer (k : N) (s : machine_config a B C) : machine_config a B C :=
  set_next_interfer (shift_seq k s.(next_interfer)) s.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "shift_interfer_intro" *)
Theorem shift_interfer_intro : forall k1 k2 c,
  shift_interfer k1 (shift_interfer k2 c) = shift_interfer (k1 + k2) c.
Proof.
  intros k1 k2 c. unfold shift_interfer, set_next_interfer, shift_seq; cbn.
  do 2 f_equal. apply functional_extensionality; intros i. f_equal. lia.
Qed.

End Shift.

Section Bytes.
Context {a : N}.
Local Open Scope word_scope.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "bytes_in_memory_SUBSET" *)
Theorem bytes_in_memory_SUBSET : forall (dm dm2 : word a -> Prop) xs (m : word a -> word8)
    (p : word a),
  dm SUBSET dm2 /\ bytes_in_memory p xs m dm ->
  bytes_in_memory p xs m dm2.
Proof.
  intros dm dm2 xs; revert dm dm2.
  induction xs as [|x xs IH]; intros dm dm2 m p [Hs H]; cbn in *; [exact Logic.I|].
  destruct H as (H1 & H2 & H3). split; [exact H1|split; [apply Hs, H2|]].
  apply (IH dm dm2 m); split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "bytes_in_memory_DIFF" *)
Theorem bytes_in_memory_DIFF : forall (dm dm2 pcs : word a -> Prop) xs (m : word a -> word8)
    (p : word a),
  (dm = dm2 DIFF pcs /\ bytes_in_memory p xs m dm2 /\
   DISJOINT pcs (fun x => exists i, x = p + n2w i /\ (i < LENGTH xs)%N)) ->
  bytes_in_memory p xs m dm.
Proof.
  intros dm dm2 pcs xs m p (-> & H & Hd). rewrite DISJOINT_ALT in Hd.
  apply (bytes_in_memory_change_domain p xs m dm2). split; [exact H|].
  intros n [Hn Hi]. split; [exact Hi|]. intros Hp.
  apply (Hd (p + n2w n) Hp). exists n. split; [reflexivity|exact Hn].
Qed.

End Bytes.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "ffi_entry_pcs_disjoint_def" *)
Definition ffi_entry_pcs_disjoint {a B C} (mc : machine_config a B C) (s1 : asm_state a)
    (len : N) : Prop :=
  DISJOINT (set mc.(ffi_entry_pcs)) (fun x => exists a0, x = (s1.(pc) + n2w a0)%w /\ a0 < len).

(** ** The interference-application trace of a machine run *)

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_app" *)
Inductive interference_app (a : N) (state : Type) : Type :=
| FfiApp : N -> list word8 -> state -> state -> interference_app a state
| CcApp : word a -> word a -> state -> state -> interference_app a state.
Arguments FfiApp {a state} _ _ _ _.
Arguments CcApp {a state} _ _ _ _.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "is_ffi_app_def" *)
Definition is_ffi_app {a state} (x : interference_app a state) : bool :=
  match x with
  | FfiApp index new_bytes ms_pre ms_post => true
  | CcApp a1 a2 ms_pre ms_post => false
  end.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "app_post_def" *)
Definition app_post {a state} (x : interference_app a state) : state :=
  match x with
  | FfiApp index new_bytes ms_pre ms_post => ms_post
  | CcApp a1 a2 ms_pre ms_post => ms_post
  end.

Section Find.
Context {a : N} {B C Ffi : Type}.

Local Abbreviation fresult :=
  (option (interference_app a B * (machine_config a B C * ffi_state Ffi)))%type.

(** One step of [find_next_interference] at a positive clock, with [rec]
    for the recursive call at clock [k - 1]. *)
Definition find_next_interference_body
    (rec : machine_config a B C -> ffi_state Ffi -> B -> fresult)
    (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B) : fresult :=
      if classical_dec ((get_pc mc.(target) ms) IN (mc.(prog_addresses) DIFF (set mc.(ffi_entry_pcs)))) then
        if classical_dec (encoded_bytes_in_mem
            (config mc.(target)) (get_pc mc.(target) ms)
            (get_byte mc.(target) ms) mc.(prog_addresses)) then
          let ms1 := next mc.(target) ms in
          let '(ms2, new_oracle) := apply_oracle mc.(next_interfer) ms1 in
          let mc := set_next_interfer new_oracle mc in
            if classical_dec (EVERY (state_ok mc.(target)) [ms; ms1; ms2] /\
               (forall x, x NOTIN mc.(prog_addresses) ->
                   get_byte mc.(target) ms1 x =
                   get_byte mc.(target) ms x))
            then
              rec mc ffi ms2
            else NONE
        else NONE
      else if decide (get_pc mc.(target) ms = mc.(halt_pc)) then NONE
      else if decide (get_pc mc.(target) ms = mc.(ccache_pc)) then
        let '(ms1, new_oracle) :=
          apply_oracle mc.(ccache_interfer)
            (get_reg mc.(target) ms mc.(ptr_reg),
             (get_reg mc.(target) ms mc.(len_reg),
              ms)) in
          SOME (CcApp (get_reg mc.(target) ms mc.(ptr_reg))
                      (get_reg mc.(target) ms mc.(len_reg)) ms ms1,
                (set_ccache_interfer new_oracle mc, ffi))
      else
        match find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 with
        | NONE => NONE
        | SOME ffi_index =>
            match EL ffi_index mc.(ffi_names) with
            | SharedMem op =>
                match ALOOKUP mc.(mmio_info) ffi_index with
                | NONE => NONE
                | SOME (nb, (a0, (reg, pc'))) =>
                    match op with
                    | MappedRead =>
                        match a0 with
                        | Addr r off =>
                            let ad := (get_reg mc.(target) ms r + off)%w in
                              (if classical_dec ((if decide (nb = n2w 0)
                                   then (w2n ad MOD (dimindex a DIV 8)) = 0 else True) /\
                                  (ad IN mc.(shared_addresses)) /\
                                  is_valid_mapped_read (get_pc mc.(target) ms) nb a0 reg pc'
                                                       mc.(target) ms mc.(prog_addresses))
                               then
                                 match call_FFI ffi (EL ffi_index mc.(ffi_names)) [nb]
                                                (word_to_bytes ad false) with
                                 | FFI_final outcome => NONE
                                 | FFI_return new_ffi new_bytes =>
                                     let '(ms1, new_oracle)
                                         := apply_oracle mc.(ffi_interfer)
                                                         (ffi_index, (new_bytes, ms)) in
                                       SOME (FfiApp ffi_index new_bytes ms ms1,
                                             (set_ffi_interfer new_oracle mc,
                                              new_ffi))
                                 end
                               else NONE)
                        end
                    | MappedWrite =>
                        match a0 with
                        | Addr r off =>
                            let ad := (get_reg mc.(target) ms r + off)%w in
                              (if classical_dec ((if decide (nb = n2w 0)
                                   then (w2n ad MOD (dimindex a DIV 8)) = 0 else True) /\
                                  (ad IN mc.(shared_addresses)) /\
                                  is_valid_mapped_write (get_pc mc.(target) ms) nb a0 reg pc'
                                                        mc.(target) ms mc.(prog_addresses))
                               then
                                 match call_FFI ffi (EL ffi_index mc.(ffi_names)) [nb]
                                                ((let w := get_reg mc.(target) ms reg in
                                                    if decide (nb = n2w 0) then word_to_bytes w false
                                                    else word_to_bytes_aux (w2n nb) w false)
                                                 ++ (word_to_bytes ad false)) with
                                 | FFI_final outcome => NONE
                                 | FFI_return new_ffi new_bytes =>
                                     let '(ms1, new_oracle)
                                         := apply_oracle mc.(ffi_interfer)
                                                         (ffi_index, (new_bytes, ms)) in
                                       SOME (FfiApp ffi_index new_bytes ms ms1,
                                             (set_ffi_interfer new_oracle mc,
                                              new_ffi))
                                 end
                               else NONE)
                        end
                    end
                end
            | ExtCall _ =>
                match ALOOKUP mc.(mmio_info) ffi_index with
                | SOME _ => NONE
                | NONE =>
                    match read_ffi_bytearrays mc ms with
                    | (SOME bytes, SOME bytes2) =>
                        match call_FFI ffi (EL ffi_index mc.(ffi_names)) bytes bytes2 with
                        | FFI_final outcome => NONE
                        | FFI_return new_ffi new_bytes =>
                            let '(ms1, new_oracle)
                                := apply_oracle mc.(ffi_interfer)
                                                (ffi_index, (new_bytes, ms)) in
                              SOME (FfiApp ffi_index new_bytes ms ms1,
                                    (set_ffi_interfer new_oracle mc,
                                     new_ffi))
                        end
                    | _ => NONE
                    end
                end
            end
        end.

(** clocked clone of [evaluate] that stops at the first interference
    application (FFI, shared-memory or cache-clear) and returns its data
    together with the continuation configuration and ffi state *)
Definition find_next_interference (mc : machine_config a B C) (ffi : ffi_state Ffi) (k : N)
    (ms : B) : fresult :=
  num_rec (fun (_ : machine_config a B C) (_ : ffi_state Ffi) (_ : B) => NONE)
    (fun _ rec mc ffi ms => find_next_interference_body rec mc ffi ms) k mc ffi ms.

Lemma find_next_interference_eqn : forall mc ffi k ms,
  find_next_interference mc ffi k ms =
  if k =? 0 then NONE
  else find_next_interference_body (fun mc ffi ms => find_next_interference mc ffi (k - 1) ms)
         mc ffi ms.
Proof.
  intros mc ffi k ms; destruct k as [|p] using N.peano_ind; [reflexivity|].
  unfold find_next_interference at 1; rewrite num_rec_SUC.
  replace (N.succ p =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  replace (N.succ p - 1) with p by lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "find_next_interference_def" *)
Theorem find_next_interference_def : forall (mc : machine_config a B C) (ffi : ffi_state Ffi) k
    (ms : B),
  find_next_interference mc ffi k ms =
    if k =? 0 then NONE
    else
        if classical_dec ((get_pc mc.(target) ms) IN (mc.(prog_addresses) DIFF (set mc.(ffi_entry_pcs)))) then
          if classical_dec (encoded_bytes_in_mem
              (config mc.(target)) (get_pc mc.(target) ms)
              (get_byte mc.(target) ms) mc.(prog_addresses)) then
            let ms1 := next mc.(target) ms in
            let '(ms2, new_oracle) := apply_oracle mc.(next_interfer) ms1 in
            let mc := set_next_interfer new_oracle mc in
              if classical_dec (EVERY (state_ok mc.(target)) [ms; ms1; ms2] /\
                 (forall x, x NOTIN mc.(prog_addresses) ->
                     get_byte mc.(target) ms1 x =
                     get_byte mc.(target) ms x))
              then
                find_next_interference mc ffi (k - 1) ms2
              else NONE
          else NONE
        else if decide (get_pc mc.(target) ms = mc.(halt_pc)) then NONE
        else if decide (get_pc mc.(target) ms = mc.(ccache_pc)) then
          let '(ms1, new_oracle) :=
            apply_oracle mc.(ccache_interfer)
              (get_reg mc.(target) ms mc.(ptr_reg),
               (get_reg mc.(target) ms mc.(len_reg),
                ms)) in
            SOME (CcApp (get_reg mc.(target) ms mc.(ptr_reg))
                        (get_reg mc.(target) ms mc.(len_reg)) ms ms1,
                  (set_ccache_interfer new_oracle mc, ffi))
        else
          match find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 with
          | NONE => NONE
          | SOME ffi_index =>
              match EL ffi_index mc.(ffi_names) with
              | SharedMem op =>
                  match ALOOKUP mc.(mmio_info) ffi_index with
                  | NONE => NONE
                  | SOME (nb, (a0, (reg, pc'))) =>
                      match op with
                      | MappedRead =>
                          match a0 with
                          | Addr r off =>
                              let ad := (get_reg mc.(target) ms r + off)%w in
                                (if classical_dec ((if decide (nb = n2w 0)
                                     then (w2n ad MOD (dimindex a DIV 8)) = 0 else True) /\
                                    (ad IN mc.(shared_addresses)) /\
                                    is_valid_mapped_read (get_pc mc.(target) ms) nb a0 reg pc'
                                                         mc.(target) ms mc.(prog_addresses))
                                 then
                                   match call_FFI ffi (EL ffi_index mc.(ffi_names)) [nb]
                                                  (word_to_bytes ad false) with
                                   | FFI_final outcome => NONE
                                   | FFI_return new_ffi new_bytes =>
                                       let '(ms1, new_oracle)
                                           := apply_oracle mc.(ffi_interfer)
                                                           (ffi_index, (new_bytes, ms)) in
                                         SOME (FfiApp ffi_index new_bytes ms ms1,
                                               (set_ffi_interfer new_oracle mc,
                                                new_ffi))
                                   end
                                 else NONE)
                          end
                      | MappedWrite =>
                          match a0 with
                          | Addr r off =>
                              let ad := (get_reg mc.(target) ms r + off)%w in
                                (if classical_dec ((if decide (nb = n2w 0)
                                     then (w2n ad MOD (dimindex a DIV 8)) = 0 else True) /\
                                    (ad IN mc.(shared_addresses)) /\
                                    is_valid_mapped_write (get_pc mc.(target) ms) nb a0 reg pc'
                                                          mc.(target) ms mc.(prog_addresses))
                                 then
                                   match call_FFI ffi (EL ffi_index mc.(ffi_names)) [nb]
                                                  ((let w := get_reg mc.(target) ms reg in
                                                      if decide (nb = n2w 0) then word_to_bytes w false
                                                      else word_to_bytes_aux (w2n nb) w false)
                                                   ++ (word_to_bytes ad false)) with
                                   | FFI_final outcome => NONE
                                   | FFI_return new_ffi new_bytes =>
                                       let '(ms1, new_oracle)
                                           := apply_oracle mc.(ffi_interfer)
                                                           (ffi_index, (new_bytes, ms)) in
                                         SOME (FfiApp ffi_index new_bytes ms ms1,
                                               (set_ffi_interfer new_oracle mc,
                                                new_ffi))
                                   end
                                 else NONE)
                          end
                      end
                  end
              | ExtCall _ =>
                  match ALOOKUP mc.(mmio_info) ffi_index with
                  | SOME _ => NONE
                  | NONE =>
                      match read_ffi_bytearrays mc ms with
                      | (SOME bytes, SOME bytes2) =>
                          match call_FFI ffi (EL ffi_index mc.(ffi_names)) bytes bytes2 with
                          | FFI_final outcome => NONE
                          | FFI_return new_ffi new_bytes =>
                              let '(ms1, new_oracle)
                                  := apply_oracle mc.(ffi_interfer)
                                                  (ffi_index, (new_bytes, ms)) in
                                SOME (FfiApp ffi_index new_bytes ms ms1,
                                      (set_ffi_interfer new_oracle mc,
                                       new_ffi))
                          end
                      | _ => NONE
                      end
                  end
              end
          end.
Proof. intros mc ffi k ms; rewrite find_next_interference_eqn; reflexivity. Qed.

End Find.

Lemma some_SOME {A} `{Inhabited A} (P : A -> Prop) x : some P = SOME x -> P x.
Proof.
  unfold some. destruct (classical_dec _) as [Ex|_]; [|discriminate].
  intros E; injection E as <-. apply select_spec, Ex.
Qed.

Lemma some_NONE {A} `{Inhabited A} (P : A -> Prop) : some P = NONE -> forall x, ~ P x.
Proof.
  unfold some. destruct (classical_dec _) as [Ex|Hn]; [discriminate|].
  intros _ x Hx. apply Hn. exists x. exact Hx.
Qed.

(** [some P] is the unique [x] with [P x]. *)
Lemma some_unique {A} `{Inhabited A} (P : A -> Prop) x :
  P x -> (forall y, P y -> y = x) -> some P = SOME x.
Proof.
  intros Hx Hu. unfold some. destruct (classical_dec _) as [Ex|Hn].
  - f_equal. apply Hu, select_spec, Ex.
  - exfalso. apply Hn. exists x. exact Hx.
Qed.

Section Interference.
Context {a : N} {B C Ffi : Type}.
Implicit Types (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B)
  (app : interference_app a B).

Local Abbreviation fresult :=
  (option (interference_app a B * (machine_config a B C * ffi_state Ffi)))%type.

(** the limit of [find_next_interference] over all clocks *)
(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_def" *)
Definition next_interference (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B)
    : fresult :=
  @some _ (FfiApp 0 [] ms ms, (mc, ffi))
    (fun res => exists k, find_next_interference mc ffi k ms = SOME res).

Definition interference_app_seq (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B)
    (n : N) : fresult :=
  num_rec (fun mc ffi ms => next_interference mc ffi ms)
    (fun _ r mc ffi ms =>
       match next_interference mc ffi ms with
       | NONE => NONE
       | SOME (app, (mc', ffi')) => r mc' ffi' (app_post app)
       end) n mc ffi ms.

(** the sequence of interference applications of a run *)
(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_app_seq_def" *)
Theorem interference_app_seq_def :
  (forall mc ffi ms, interference_app_seq mc ffi ms 0 = next_interference mc ffi ms) /\
  (forall mc ffi ms n,
     interference_app_seq mc ffi ms (SUC n) =
     match next_interference mc ffi ms with
     | NONE => NONE
     | SOME (app, (mc', ffi')) => interference_app_seq mc' ffi' (app_post app) n
     end).
Proof.
  split; [reflexivity|]. intros mc ffi ms n.
  unfold interference_app_seq at 1. rewrite num_rec_SUC. reflexivity.
Qed.

Definition interference_count (P : interference_app a B -> bool) (mc : machine_config a B C)
    (ffi : ffi_state Ffi) (ms : B) (n : N) : N :=
  num_rec 0
    (fun n r => r +
       match interference_app_seq mc ffi ms n with
       | SOME (app, (mc', ffi')) => if P app then 1 else 0
       | NONE => 0
       end) n.

(** number of applications satisfying [P] among the first [n] applications *)
(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_count_def" *)
Theorem interference_count_def :
  (forall P mc ffi ms, interference_count P mc ffi ms 0 = 0) /\
  (forall P mc ffi ms n,
     interference_count P mc ffi ms (SUC n) =
     interference_count P mc ffi ms n +
     match interference_app_seq mc ffi ms n with
     | SOME (app, (mc', ffi')) => if P app then 1 else 0
     | NONE => 0
     end).
Proof.
  split; [reflexivity|]. intros P mc ffi ms n.
  unfold interference_count at 1. rewrite num_rec_SUC. reflexivity.
Qed.

(** position in the application sequence of the [k]-th application
    satisfying [P] *)
(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_pos_def" *)
Definition interference_pos (P : interference_app a B -> bool) (mc : machine_config a B C)
    (ffi : ffi_state Ffi) (ms : B) (k : N) : option N :=
  some (fun n => interference_count P mc ffi ms n = k /\
                 exists app mc' ffi',
                   interference_app_seq mc ffi ms n = SOME (app, (mc', ffi')) /\
                   P app).

(** the lab-level oracle sequences, constructed from the machine run:
    caller-saved register and FP-register residues are read off each
    application's post state; callee-saved (and avoid / out-of-range)
    registers are marked [NONE], i.e. preserved *)
(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_io_regs_def" *)
Definition target_io_regs (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B) (k : N)
    (name : ffiname) (r : N) : option (word a) :=
  match interference_pos is_ffi_app mc ffi ms k with
  | NONE => NONE
  | SOME n =>
    match interference_app_seq mc ffi ms n with
    | SOME (FfiApp index new_bytes ms_pre ms_post, (mc', ffi')) =>
        if MEM r mc.(callee_saved_regs) ||
           negb (r <? reg_count (config mc.(target))) ||
           MEM r (avoid_regs (config mc.(target)))
        then NONE
        else SOME (get_reg mc.(target) ms_post r)
    | _ => NONE
    end
  end.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_io_fp_regs_def" *)
Definition target_io_fp_regs (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B) (k : N)
    (i : N) : word64 :=
  match interference_pos is_ffi_app mc ffi ms k with
  | NONE => n2w 0
  | SOME n =>
    match interference_app_seq mc ffi ms n with
    | SOME (FfiApp index new_bytes ms_pre ms_post, (mc', ffi')) =>
        get_fp_reg mc.(target) ms_post i
    | _ => n2w 0
    end
  end.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_cc_regs_def" *)
Definition target_cc_regs (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B) (k : N)
    (r : N) : option (word a) :=
  match interference_pos (fun app => negb (is_ffi_app app)) mc ffi ms k with
  | NONE => NONE
  | SOME n =>
    match interference_app_seq mc ffi ms n with
    | SOME (CcApp a1 a2 ms_pre ms_post, (mc', ffi')) =>
        if MEM r mc.(callee_saved_regs) || bool_decide (r = mc.(ptr_reg)) ||
           negb (r <? reg_count (config mc.(target))) ||
           MEM r (avoid_regs (config mc.(target)))
        then NONE
        else SOME (get_reg mc.(target) ms_post r)
    | _ => NONE
    end
  end.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_cc_fp_regs_def" *)
Definition target_cc_fp_regs (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B) (k : N)
    (i : N) : word64 :=
  match interference_pos (fun app => negb (is_ffi_app app)) mc ffi ms k with
  | NONE => n2w 0
  | SOME n =>
    match interference_app_seq mc ffi ms n with
    | SOME (CcApp a1 a2 ms_pre ms_post, (mc', ffi')) =>
        get_fp_reg mc.(target) ms_post i
    | _ => n2w 0
    end
  end.

Lemma find_next_interference_body_mono
    (rec1 rec2 : machine_config a B C -> ffi_state Ffi -> B -> fresult) mc ffi ms res :
  (forall mc ffi ms res, rec1 mc ffi ms = SOME res -> rec2 mc ffi ms = SOME res) ->
  find_next_interference_body rec1 mc ffi ms = SOME res ->
  find_next_interference_body rec2 mc ffi ms = SOME res.
Proof.
  intros Hrec H. unfold find_next_interference_body, apply_oracle in *.
  destruct (classical_dec (_ IN _)); [|exact H].
  destruct (classical_dec (encoded_bytes_in_mem _ _ _ _)); [|discriminate].
  destruct (classical_dec (_ /\ _)); [|discriminate].
  apply Hrec, H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "find_next_interference_mono" *)
Theorem find_next_interference_mono : forall k mc ffi ms res i,
  find_next_interference mc ffi k ms = SOME res ->
  find_next_interference mc ffi (k + i) ms = SOME res.
Proof.
  intros k; induction k as [|k IH] using N.peano_ind; intros mc ffi ms res i H.
  { rewrite find_next_interference_eqn in H. discriminate. }
  rewrite find_next_interference_eqn in H |- *.
  rewrite (proj2 (N.eqb_neq (N.succ k) 0)) in H by lia.
  rewrite (proj2 (N.eqb_neq (N.succ k + i) 0)) by lia.
  replace (N.succ k - 1) with k in H by lia.
  replace (N.succ k + i - 1) with (k + i) by lia.
  revert H. apply find_next_interference_body_mono. intros; apply IH; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "find_next_interference_unique" *)
Theorem find_next_interference_unique : forall mc ffi k1 ms res1 k2 res2,
  find_next_interference mc ffi k1 ms = SOME res1 /\
  find_next_interference mc ffi k2 ms = SOME res2 ->
  res1 = res2.
Proof.
  intros mc ffi k1 ms res1 k2 res2 [H1 H2].
  apply (find_next_interference_mono _ _ _ _ _ k2) in H1.
  apply (find_next_interference_mono _ _ _ _ _ k1) in H2.
  rewrite N.add_comm, H2 in H1. injection H1 as ->. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_intro" *)
Theorem next_interference_intro : forall mc ffi k ms res,
  find_next_interference mc ffi k ms = SOME res ->
  next_interference mc ffi ms = SOME res.
Proof.
  intros mc ffi k ms res H. unfold next_interference. apply some_unique; [exists k; exact H|].
  intros y [k' Hy]. eapply find_next_interference_unique. split; [exact Hy|exact H].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_shift" *)
Theorem next_interference_shift : forall mc1 ffi1 l ms1 mc2 ffi2 ms2,
  (forall k, find_next_interference mc1 ffi1 (k + l) ms1 =
             find_next_interference mc2 ffi2 k ms2) ->
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2.
Proof.
  intros mc1 ffi1 l ms1 mc2 ffi2 ms2 H.
  destruct (classical_dec (exists k res, find_next_interference mc2 ffi2 k ms2 = SOME res))
    as [(k & res & Hk)|Hn].
  - rewrite (next_interference_intro _ _ _ _ _ Hk).
    rewrite <- H in Hk. apply (next_interference_intro _ _ _ _ _ Hk).
  - unfold next_interference, some.
    destruct (classical_dec (exists x, exists k, find_next_interference mc1 ffi1 k ms1 = SOME x))
      as [(x & k & Hk)|_].
    + exfalso. apply Hn. exists k, x.
      rewrite <- H. apply (find_next_interference_mono _ _ _ _ _ l) in Hk. exact Hk.
    + destruct (classical_dec _) as [(x & k & Hk)|_]; [|reflexivity].
      exfalso. apply Hn. exists k, x. exact Hk.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "find_next_interference_const" *)
Theorem find_next_interference_const : forall k mc ffi ms app mc' ffi',
  find_next_interference mc ffi k ms = SOME (app, (mc', ffi')) ->
  mc'.(target) = mc.(target) /\
  mc'.(callee_saved_regs) = mc.(callee_saved_regs) /\
  mc'.(ptr_reg) = mc.(ptr_reg).
Proof.
  intros k; induction k as [|k IH] using N.peano_ind; intros mc ffi ms app mc' ffi' H.
  { rewrite find_next_interference_eqn in H. discriminate. }
  rewrite find_next_interference_eqn in H. rewrite (proj2 (N.eqb_neq _ 0)) in H by lia.
  replace (N.succ k - 1) with k in H by lia.
  unfold find_next_interference_body, apply_oracle in H.
  repeat match type of H with
         | context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E
             end
         | context [if classical_dec ?p then _ else _] =>
             destruct (classical_dec p)
         end; cbn beta iota zeta in H; try discriminate;
    try (injection H as <- <- <-; repeat split; reflexivity).
  apply IH in H. exact H.
Qed.
(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_const" *)
Theorem next_interference_const : forall mc ffi ms app mc' ffi',
  next_interference mc ffi ms = SOME (app, (mc', ffi')) ->
  mc'.(target) = mc.(target) /\
  mc'.(callee_saved_regs) = mc.(callee_saved_regs) /\
  mc'.(ptr_reg) = mc.(ptr_reg).
Proof.
  intros mc ffi ms app mc' ffi' H. apply some_SOME in H as [k H].
  eapply find_next_interference_const; exact H.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_app_seq_EQ" *)
Theorem interference_app_seq_EQ : forall mc1 ffi1 ms1 mc2 ffi2 ms2,
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ->
  forall n, interference_app_seq mc1 ffi1 ms1 n = interference_app_seq mc2 ffi2 ms2 n.
Proof.
  intros mc1 ffi1 ms1 mc2 ffi2 ms2 H n. destruct n as [|n] using N.peano_ind.
  - rewrite !(proj1 interference_app_seq_def). exact H.
  - rewrite !(proj2 interference_app_seq_def), H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_app_seq_tail" *)
Theorem interference_app_seq_tail : forall mc ffi ms app mc' ffi',
  next_interference mc ffi ms = SOME (app, (mc', ffi')) ->
  forall n, interference_app_seq mc ffi ms (SUC n) =
            interference_app_seq mc' ffi' (app_post app) n.
Proof. intros mc ffi ms app mc' ffi' H n. rewrite (proj2 interference_app_seq_def), H. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_count_mono" *)
Theorem interference_count_mono : forall P mc ffi ms i m,
  interference_count P mc ffi ms m <= interference_count P mc ffi ms (m + i).
Proof.
  intros P mc ffi ms i; induction i as [|i IH] using N.peano_ind; intros m.
  - rewrite N.add_0_r. lia.
  - rewrite N.add_succ_r, (proj2 interference_count_def). specialize (IH m). lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_count_lt" *)
Theorem interference_count_lt : forall mc ffi ms n app mc' ffi' (P : interference_app a B -> bool)
    n2,
  interference_app_seq mc ffi ms n = SOME (app, (mc', ffi')) /\ P app /\ n < n2 ->
  interference_count P mc ffi ms n < interference_count P mc ffi ms n2.
Proof.
  intros mc ffi ms n app mc' ffi' P n2 (H & HP & Hn).
  assert (E : interference_count P mc ffi ms (SUC n) = interference_count P mc ffi ms n + 1).
  { rewrite (proj2 interference_count_def), H. unfold is_true in HP. rewrite HP. reflexivity. }
  pose proof (interference_count_mono P mc ffi ms (n2 - SUC n) (SUC n)) as M.
  replace (SUC n + (n2 - SUC n)) with n2 in M by lia. lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_pos_unique" *)
Theorem interference_pos_unique : forall mc ffi ms n1 app1 mc1' ffi1' (P : interference_app a B -> bool)
    n2 app2 mc2' ffi2',
  interference_app_seq mc ffi ms n1 = SOME (app1, (mc1', ffi1')) /\ P app1 /\
  interference_app_seq mc ffi ms n2 = SOME (app2, (mc2', ffi2')) /\ P app2 /\
  interference_count P mc ffi ms n1 = interference_count P mc ffi ms n2 ->
  n1 = n2.
Proof.
  intros mc ffi ms n1 app1 mc1' ffi1' P n2 app2 mc2' ffi2' (H1 & P1 & H2 & P2 & E).
  destruct (N.lt_trichotomy n1 n2) as [L|[L|L]]; [|exact L|].
  - pose proof (interference_count_lt mc ffi ms n1 app1 mc1' ffi1' P n2 (conj H1 (conj P1 L))). lia.
  - pose proof (interference_count_lt mc ffi ms n2 app2 mc2' ffi2' P n1 (conj H2 (conj P2 L))). lia.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_count_tail" *)
Theorem interference_count_tail : forall mc ffi ms app0 mcc ffic P,
  next_interference mc ffi ms = SOME (app0, (mcc, ffic)) ->
  forall n, interference_count P mc ffi ms (SUC n) =
            (if P app0 then 1 else 0) + interference_count P mcc ffic (app_post app0) n.
Proof.
  intros mc ffi ms app0 mcc ffic P H n. induction n as [|n IH] using N.peano_ind.
  - rewrite !(proj2 interference_count_def), !(proj1 interference_count_def),
      (proj1 interference_app_seq_def), H. lia.
  - rewrite (proj2 interference_count_def (P) mc ffi ms (SUC n)), IH.
    rewrite (proj2 interference_count_def P mcc ffic (app_post app0) n).
    rewrite (interference_app_seq_tail _ _ _ _ _ _ H). lia.
Qed.

(** [interference_pos] as a relation (Galette helper). *)
Lemma interference_pos_SOME P mc ffi ms k n :
  interference_pos P mc ffi ms k = SOME n <->
  (interference_count P mc ffi ms n = k /\
   exists app mc' ffi', interference_app_seq mc ffi ms n = SOME (app, (mc', ffi')) /\ P app).
Proof.
  split; [intros E; exact (some_SOME _ _ E)|]. intros Hn. unfold interference_pos. apply some_unique; [exact Hn|].
  intros y (Ey & app & mc' & ffi' & Hy & Py). destruct Hn as (En & app2 & mc2 & ffi2 & Hn & Pn).
  eapply interference_pos_unique. repeat split; [exact Hy|exact Py|exact Hn|exact Pn|congruence].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_pos_head" *)
Theorem interference_pos_head : forall mc ffi ms app0 mcc ffic (P : interference_app a B -> bool),
  next_interference mc ffi ms = SOME (app0, (mcc, ffic)) /\ P app0 ->
  interference_pos P mc ffi ms 0 = SOME 0.
Proof.
  intros mc ffi ms app0 mcc ffic P [H HP]. apply interference_pos_SOME.
  split; [apply (proj1 interference_count_def)|].
  exists app0, mcc, ffic. rewrite (proj1 interference_app_seq_def). split; [exact H|exact HP].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_pos_tail_hit" *)
Theorem interference_pos_tail_hit : forall mc ffi ms app0 mcc ffic (P : interference_app a B -> bool)
    k,
  next_interference mc ffi ms = SOME (app0, (mcc, ffic)) /\ P app0 ->
  interference_pos P mc ffi ms (SUC k) =
  OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k).
Proof.
  intros mc ffi ms app0 mcc ffic P k [H HP]. unfold is_true in HP.
  pose proof (interference_app_seq_tail _ _ _ _ _ _ H) as ES.
  pose proof (interference_count_tail _ _ _ _ _ _ P H) as EC. rewrite HP in EC.
  destruct (interference_pos P mcc ffic (app_post app0) k) as [m|] eqn:E; cbn [option_map].
  - apply interference_pos_SOME in E as (Ec & app & mc' & ffi' & Hs & Hp).
    apply interference_pos_SOME. rewrite EC, ES, Ec. split; [lia|eauto].
  - destruct (interference_pos P mc ffi ms (SUC k)) as [n|] eqn:E2; [|reflexivity].
    apply interference_pos_SOME in E2 as (Ec & app & mc' & ffi' & Hs & Hp).
    destruct n as [|m] using N.peano_ind.
    + rewrite (proj1 interference_count_def) in Ec. lia.
    + rewrite EC in Ec. rewrite ES in Hs.
      assert (E3 : interference_pos P mcc ffic (app_post app0) k = SOME m).
      { apply interference_pos_SOME. split; [lia|eauto]. }
      congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_pos_tail_miss" *)
Theorem interference_pos_tail_miss : forall mc ffi ms app0 mcc ffic (P : interference_app a B -> bool)
    k,
  next_interference mc ffi ms = SOME (app0, (mcc, ffic)) /\ ~ P app0 ->
  interference_pos P mc ffi ms k =
  OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k).
Proof.
  intros mc ffi ms app0 mcc ffic P k [H HP]. apply not_true_is_false in HP.
  pose proof (interference_app_seq_tail _ _ _ _ _ _ H) as ES.
  pose proof (interference_count_tail _ _ _ _ _ _ P H) as EC. rewrite HP in EC.
  destruct (interference_pos P mcc ffic (app_post app0) k) as [m|] eqn:E; cbn [option_map].
  - apply interference_pos_SOME in E as (Ec & app & mc' & ffi' & Hs & Hp).
    apply interference_pos_SOME. rewrite EC, ES, Ec. split; [lia|eauto].
  - destruct (interference_pos P mc ffi ms k) as [n|] eqn:E2; [|reflexivity].
    apply interference_pos_SOME in E2 as (Ec & app & mc' & ffi' & Hs & Hp).
    destruct n as [|m] using N.peano_ind.
    + rewrite (proj1 interference_app_seq_def), H in Hs. injection Hs as <- _ _.
      unfold is_true in Hp. congruence.
    + rewrite EC in Ec. rewrite ES in Hs.
      assert (E3 : interference_pos P mcc ffic (app_post app0) k = SOME m).
      { apply interference_pos_SOME. split; [lia|eauto]. }
      congruence.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "constructed_oracles_ffi_step" *)
Theorem constructed_oracles_ffi_step : forall mc ffi ms index new_bytes ms_pre ms_post mc' ffi'
    name r i k,
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms_pre ms_post, (mc', ffi')) ->
  target_io_regs mc ffi ms 0 name r =
    (if MEM r mc.(callee_saved_regs) ||
        negb (r <? reg_count (config mc.(target))) ||
        MEM r (avoid_regs (config mc.(target)))
     then NONE else SOME (get_reg mc.(target) ms_post r)) /\
  target_io_fp_regs mc ffi ms 0 i = get_fp_reg mc.(target) ms_post i /\
  target_io_regs mc ffi ms (SUC k) name r =
    target_io_regs mc' ffi' ms_post k name r /\
  target_io_fp_regs mc ffi ms (SUC k) i =
    target_io_fp_regs mc' ffi' ms_post k i /\
  target_cc_regs mc ffi ms k r = target_cc_regs mc' ffi' ms_post k r /\
  target_cc_fp_regs mc ffi ms k i = target_cc_fp_regs mc' ffi' ms_post k i.
Proof.
  intros mc ffi ms index new_bytes ms_pre ms_post mc' ffi' name r i k H.
  destruct (next_interference_const _ _ _ _ _ _ H) as (Et & Ecs & Ep).
  assert (H0 : interference_pos is_ffi_app mc ffi ms 0 = SOME 0)
    by (apply (interference_pos_head mc ffi ms (FfiApp index new_bytes ms_pre ms_post) mc' ffi' is_ffi_app); split; [exact H|reflexivity]).
  assert (Hhit : forall k, interference_pos is_ffi_app mc ffi ms (SUC k) =
            OPTION_MAP SUC (interference_pos is_ffi_app mc' ffi' ms_post k))
    by (intros k0; apply (interference_pos_tail_hit mc ffi ms (FfiApp index new_bytes ms_pre ms_post) mc' ffi' is_ffi_app k0); split; [exact H|reflexivity]).
  assert (Hmiss : forall k, interference_pos (fun app => negb (is_ffi_app app)) mc ffi ms k =
            OPTION_MAP SUC (interference_pos (fun app => negb (is_ffi_app app)) mc' ffi' ms_post k))
    by (intros k0; apply (interference_pos_tail_miss mc ffi ms (FfiApp index new_bytes ms_pre ms_post) mc' ffi' (fun app => negb (is_ffi_app app)) k0); split; [exact H|discriminate]).
  pose proof (interference_app_seq_tail _ _ _ _ _ _ H) as ES. cbn [app_post] in ES.
  assert (S0 : interference_app_seq mc ffi ms 0 =
               SOME (FfiApp index new_bytes ms_pre ms_post, (mc', ffi')))
    by (rewrite (proj1 interference_app_seq_def); exact H).
  unfold target_io_regs, target_io_fp_regs, target_cc_regs, target_cc_fp_regs.
  rewrite H0, Hhit, Hmiss, S0, Et, Ecs, Ep.
  repeat match goal with |- _ /\ _ => split end.
  all: try reflexivity.
  all: lazymatch goal with
       | |- context [option_map _ (interference_pos ?P ?m ?f ?p ?kk)] =>
           destruct (interference_pos P m f p kk); cbn [option_map]; rewrite ?ES;
           reflexivity
       end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "constructed_oracles_cc_step" *)
Theorem constructed_oracles_cc_step : forall mc ffi ms a1 a2 ms_pre ms_post mc' ffi' r i k name,
  next_interference mc ffi ms =
    SOME (CcApp a1 a2 ms_pre ms_post, (mc', ffi')) ->
  target_cc_regs mc ffi ms 0 r =
    (if MEM r mc.(callee_saved_regs) || bool_decide (r = mc.(ptr_reg)) ||
        negb (r <? reg_count (config mc.(target))) ||
        MEM r (avoid_regs (config mc.(target)))
     then NONE else SOME (get_reg mc.(target) ms_post r)) /\
  target_cc_fp_regs mc ffi ms 0 i = get_fp_reg mc.(target) ms_post i /\
  target_cc_regs mc ffi ms (SUC k) r = target_cc_regs mc' ffi' ms_post k r /\
  target_cc_fp_regs mc ffi ms (SUC k) i =
    target_cc_fp_regs mc' ffi' ms_post k i /\
  target_io_regs mc ffi ms k name r =
    target_io_regs mc' ffi' ms_post k name r /\
  target_io_fp_regs mc ffi ms k i = target_io_fp_regs mc' ffi' ms_post k i.
Proof.
  intros mc ffi ms a1 a2 ms_pre ms_post mc' ffi' r i k name H.
  destruct (next_interference_const _ _ _ _ _ _ H) as (Et & Ecs & Ep).
  assert (H0 : interference_pos (fun app => negb (is_ffi_app app)) mc ffi ms 0 = SOME 0)
    by (apply (interference_pos_head mc ffi ms (CcApp a1 a2 ms_pre ms_post) mc' ffi' (fun app => negb (is_ffi_app app))); split; [exact H|reflexivity]).
  assert (Hhit : forall k, interference_pos (fun app => negb (is_ffi_app app)) mc ffi ms (SUC k) =
            OPTION_MAP SUC (interference_pos (fun app => negb (is_ffi_app app)) mc' ffi' ms_post k))
    by (intros k0; apply (interference_pos_tail_hit mc ffi ms (CcApp a1 a2 ms_pre ms_post) mc' ffi' (fun app => negb (is_ffi_app app)) k0); split; [exact H|reflexivity]).
  assert (Hmiss : forall k, interference_pos is_ffi_app mc ffi ms k =
            OPTION_MAP SUC (interference_pos is_ffi_app mc' ffi' ms_post k))
    by (intros k0; apply (interference_pos_tail_miss mc ffi ms (CcApp a1 a2 ms_pre ms_post) mc' ffi' is_ffi_app k0); split; [exact H|discriminate]).
  pose proof (interference_app_seq_tail _ _ _ _ _ _ H) as ES. cbn [app_post] in ES.
  assert (S0 : interference_app_seq mc ffi ms 0 =
               SOME (CcApp a1 a2 ms_pre ms_post, (mc', ffi')))
    by (rewrite (proj1 interference_app_seq_def); exact H).
  unfold target_io_regs, target_io_fp_regs, target_cc_regs, target_cc_fp_regs.
  rewrite H0, Hhit, Hmiss, S0, Et, Ecs, Ep.
  repeat match goal with |- _ /\ _ => split end.
  all: try reflexivity.
  all: lazymatch goal with
       | |- context [option_map _ (interference_pos ?P ?m ?f ?p ?kk)] =>
           destruct (interference_pos P m f p kk); cbn [option_map]; rewrite ?ES;
           reflexivity
       end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_count_EQ" *)
Theorem interference_count_EQ : forall mc1 ffi1 ms1 mc2 ffi2 ms2 P,
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ->
  forall n, interference_count P mc1 ffi1 ms1 n = interference_count P mc2 ffi2 ms2 n.
Proof.
  intros mc1 ffi1 ms1 mc2 ffi2 ms2 P H n. induction n as [|n IH] using N.peano_ind.
  - rewrite !(proj1 interference_count_def). reflexivity.
  - rewrite !(proj2 interference_count_def), IH, (interference_app_seq_EQ _ _ _ _ _ _ H n).
    reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "constructed_oracles_EQ" *)
Theorem constructed_oracles_EQ : forall mc1 ffi1 ms1 mc2 ffi2 ms2,
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 /\
  mc1.(target) = mc2.(target) /\
  mc1.(callee_saved_regs) = mc2.(callee_saved_regs) /\
  mc1.(ptr_reg) = mc2.(ptr_reg) ->
  target_io_regs mc1 ffi1 ms1 = target_io_regs mc2 ffi2 ms2 /\
  target_io_fp_regs mc1 ffi1 ms1 = target_io_fp_regs mc2 ffi2 ms2 /\
  target_cc_regs mc1 ffi1 ms1 = target_cc_regs mc2 ffi2 ms2 /\
  target_cc_fp_regs mc1 ffi1 ms1 = target_cc_fp_regs mc2 ffi2 ms2.
Proof.
  intros mc1 ffi1 ms1 mc2 ffi2 ms2 (H & Et & Ecs & Ep).
  pose proof (interference_app_seq_EQ _ _ _ _ _ _ H) as ES.
  assert (EP : forall P k, interference_pos P mc1 ffi1 ms1 k = interference_pos P mc2 ffi2 ms2 k).
  { intros P k. unfold interference_pos. f_equal.
    apply functional_extensionality; intros n.
    rewrite (interference_count_EQ _ _ _ _ _ _ P H n), ES. reflexivity. }
  unfold target_io_regs, target_io_fp_regs, target_cc_regs, target_cc_fp_regs.
  repeat match goal with |- _ /\ _ => split end;
    repeat (apply functional_extensionality; intros); rewrite EP;
    match goal with
    | |- context [interference_pos ?P mc2 ffi2 ms2 ?k] =>
        destruct (interference_pos P mc2 ffi2 ms2 k); rewrite ?ES, ?Et, ?Ecs, ?Ep; reflexivity
    end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_io_regs_callee_saved" *)
Theorem target_io_regs_callee_saved : forall r mc ffi ms k name,
  MEM r mc.(callee_saved_regs) -> target_io_regs mc ffi ms k name r = NONE.
Proof.
  intros r mc ffi ms k name H. unfold is_true in H. unfold target_io_regs.
  destruct (interference_pos _ _ _ _ _); [|reflexivity].
  destruct (interference_app_seq _ _ _ _) as [[[] [? ?]]|]; try reflexivity.
  rewrite H. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_cc_regs_callee_saved" *)
Theorem target_cc_regs_callee_saved : forall r mc ffi ms k,
  MEM r mc.(callee_saved_regs) -> target_cc_regs mc ffi ms k r = NONE.
Proof.
  intros r mc ffi ms k H. unfold is_true in H. unfold target_cc_regs.
  destruct (interference_pos _ _ _ _ _); [|reflexivity].
  destruct (interference_app_seq _ _ _ _) as [[[] [? ?]]|]; try reflexivity.
  rewrite H. reflexivity.
Qed.

Ltac next_step_tac :=
  apply (next_interference_intro _ _ 1);
  rewrite find_next_interference_eqn; cbn [N.eqb Pos.eqb];
  unfold find_next_interference_body, apply_oracle;
  repeat match goal with
         | H : ?p NOTIN ?s |- context [classical_dec (?p IN ?s)] =>
             destruct (classical_dec (p IN s)) as [?|_]; [contradiction|]
         | H : ?x <> ?y |- context [decide (?x = ?y)] =>
             destruct (decide (x = y)) as [?|_]; [contradiction|]
         | H : ?x = ?y |- context [decide (?x = ?y)] =>
             destruct (decide (x = y)) as [_|?]; [|contradiction]
         | H : ?x = _ |- context [match ?x with _ => _ end] => rewrite H
         end; cbn beta iota zeta.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_ExtCall" *)
Theorem next_interference_ExtCall : forall mc ms index name bytes bytes2 ffi new_ffi new_bytes,
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) DIFF set mc.(ffi_entry_pcs) /\
  get_pc mc.(target) ms <> mc.(halt_pc) /\
  get_pc mc.(target) ms <> mc.(ccache_pc) /\
  find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 = SOME index /\
  EL index mc.(ffi_names) = ExtCall name /\
  ALOOKUP mc.(mmio_info) index = NONE /\
  read_ffi_bytearrays mc ms = (SOME bytes, SOME bytes2) /\
  call_FFI ffi (ExtCall name) bytes bytes2 = FFI_return new_ffi new_bytes ->
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms (mc.(ffi_interfer) 0 (index, (new_bytes, ms))),
          (set_ffi_interfer (shift_seq 1 mc.(ffi_interfer)) mc,
           new_ffi)).
Proof.
  intros mc ms index name bytes bytes2 ffi new_ffi new_bytes
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  next_step_tac. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_ccache" *)
Theorem next_interference_ccache : forall mc ms ffi,
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) DIFF set mc.(ffi_entry_pcs) /\
  get_pc mc.(target) ms <> mc.(halt_pc) /\
  get_pc mc.(target) ms = mc.(ccache_pc) ->
  next_interference mc ffi ms =
    SOME (CcApp (get_reg mc.(target) ms mc.(ptr_reg))
                (get_reg mc.(target) ms mc.(len_reg)) ms
                (mc.(ccache_interfer) 0
                   (get_reg mc.(target) ms mc.(ptr_reg),
                    (get_reg mc.(target) ms mc.(len_reg), ms))),
          (set_ccache_interfer (shift_seq 1 mc.(ccache_interfer)) mc,
           ffi)).
Proof.
  intros mc ms ffi (H1 & H2 & H3). next_step_tac. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_MappedRead" *)
Theorem next_interference_MappedRead : forall mc ms index nb r off reg pc' ffi new_ffi new_bytes,
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) DIFF set mc.(ffi_entry_pcs) /\
  get_pc mc.(target) ms <> mc.(halt_pc) /\
  get_pc mc.(target) ms <> mc.(ccache_pc) /\
  find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 = SOME index /\
  EL index mc.(ffi_names) = SharedMem MappedRead /\
  ALOOKUP mc.(mmio_info) index = SOME (nb, (Addr r off, (reg, pc'))) /\
  (nb = n2w 0 ->
   w2n (get_reg mc.(target) ms r + off)%w MOD (dimindex a DIV 8) = 0) /\
  (get_reg mc.(target) ms r + off)%w IN mc.(shared_addresses) /\
  is_valid_mapped_read (get_pc mc.(target) ms) nb (Addr r off) reg pc'
    mc.(target) ms mc.(prog_addresses) /\
  call_FFI ffi (EL index mc.(ffi_names)) [nb]
    (word_to_bytes (get_reg mc.(target) ms r + off)%w false) =
    FFI_return new_ffi new_bytes ->
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms (mc.(ffi_interfer) 0 (index, (new_bytes, ms))),
          (set_ffi_interfer (shift_seq 1 mc.(ffi_interfer)) mc,
           new_ffi)).
Proof.
  intros mc ms index nb r off reg pc' ffi new_ffi new_bytes
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  rewrite H5 in H10. cbv zeta in H10. next_step_tac.
  destruct (classical_dec _) as [_|Hn].
  - rewrite ?H10. reflexivity.
  - exfalso. apply Hn. split; [|split; [exact H8|exact H9]].
    destruct (decide (nb = n2w 0)); [apply H7; assumption|exact Logic.I].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_MappedWrite" *)
Theorem next_interference_MappedWrite : forall mc ms index nb r off reg pc' ffi new_ffi new_bytes,
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) DIFF set mc.(ffi_entry_pcs) /\
  get_pc mc.(target) ms <> mc.(halt_pc) /\
  get_pc mc.(target) ms <> mc.(ccache_pc) /\
  find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 = SOME index /\
  EL index mc.(ffi_names) = SharedMem MappedWrite /\
  ALOOKUP mc.(mmio_info) index = SOME (nb, (Addr r off, (reg, pc'))) /\
  (nb = n2w 0 ->
   w2n (get_reg mc.(target) ms r + off)%w MOD (dimindex a DIV 8) = 0) /\
  (get_reg mc.(target) ms r + off)%w IN mc.(shared_addresses) /\
  is_valid_mapped_write (get_pc mc.(target) ms) nb (Addr r off) reg pc'
    mc.(target) ms mc.(prog_addresses) /\
  call_FFI ffi (EL index mc.(ffi_names)) [nb]
    ((let w := get_reg mc.(target) ms reg in
        if decide (nb = n2w 0) then word_to_bytes w false
        else word_to_bytes_aux (w2n nb) w false) ++
     word_to_bytes (get_reg mc.(target) ms r + off)%w false) =
    FFI_return new_ffi new_bytes ->
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms (mc.(ffi_interfer) 0 (index, (new_bytes, ms))),
          (set_ffi_interfer (shift_seq 1 mc.(ffi_interfer)) mc,
           new_ffi)).
Proof.
  intros mc ms index nb r off reg pc' ffi new_ffi new_bytes
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  rewrite H5 in H10. cbv zeta in H10. next_step_tac.
  destruct (classical_dec _) as [_|Hn].
  - rewrite ?H10. reflexivity.
  - exfalso. apply Hn. split; [|split; [exact H8|exact H9]].
    destruct (decide (nb = n2w 0)); [apply H7; assumption|exact Logic.I].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_SharedMem" *)
Theorem next_interference_SharedMem : forall mc ms index op nb r off reg pc' ffi new_ffi new_bytes,
  get_pc mc.(target) ms NOTIN mc.(prog_addresses) DIFF set mc.(ffi_entry_pcs) /\
  get_pc mc.(target) ms <> mc.(halt_pc) /\
  get_pc mc.(target) ms <> mc.(ccache_pc) /\
  find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 = SOME index /\
  EL index mc.(ffi_names) = SharedMem op /\
  ALOOKUP mc.(mmio_info) index = SOME (nb, (Addr r off, (reg, pc'))) /\
  (nb = n2w 0 ->
   w2n (get_reg mc.(target) ms r + off)%w MOD (dimindex a DIV 8) = 0) /\
  (get_reg mc.(target) ms r + off)%w IN mc.(shared_addresses) /\
  (op = MappedRead ->
     is_valid_mapped_read (get_pc mc.(target) ms) nb (Addr r off) reg pc'
       mc.(target) ms mc.(prog_addresses) /\
     call_FFI ffi (EL index mc.(ffi_names)) [nb]
       (word_to_bytes (get_reg mc.(target) ms r + off)%w false) =
       FFI_return new_ffi new_bytes) /\
  (op = MappedWrite ->
     is_valid_mapped_write (get_pc mc.(target) ms) nb (Addr r off) reg pc'
       mc.(target) ms mc.(prog_addresses) /\
     call_FFI ffi (EL index mc.(ffi_names)) [nb]
       ((let w := get_reg mc.(target) ms reg in
           if decide (nb = n2w 0) then word_to_bytes w false
           else word_to_bytes_aux (w2n nb) w false) ++
        word_to_bytes (get_reg mc.(target) ms r + off)%w false) =
       FFI_return new_ffi new_bytes) ->
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms (mc.(ffi_interfer) 0 (index, (new_bytes, ms))),
          (set_ffi_interfer (shift_seq 1 mc.(ffi_interfer)) mc,
           new_ffi)).
Proof.
  intros mc ms index op nb r off reg pc' ffi new_ffi new_bytes
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HR & HW).
  destruct op.
  - destruct (HR eq_refl) as [H9 H10].
    apply (next_interference_MappedRead mc ms index nb r off reg pc').
    repeat split; assumption.
  - destruct (HW eq_refl) as [H9 H10].
    apply (next_interference_MappedWrite mc ms index nb r off reg pc').
    repeat split; assumption.
Qed.

End Interference.

(** ** Basic properties of [evaluate] *)

Section Basic.
Context {a : N} {B C Ffi : Type}.
Implicit Types (mc : machine_config a B C) (ffi st : ffi_state Ffi) (ms : B).

Local Abbreviation result := (machine_result * (B * ffi_state Ffi))%type.

Ltac split_goal :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] =>
             lazymatch x with
             | context [match _ with _ => _ end] => fail
             | _ => let E := fresh "E" in destruct x eqn:E
             end
         | |- context [if classical_dec ?p then _ else _] =>
             let E := fresh "E" in destruct (classical_dec p) as [E|E]
         end; cbn beta iota zeta.

(** Two unfoldings of [evaluate_body] are related when the recursive calls
    are (Galette helper). *)
Lemma evaluate_body_rel (R : result -> result -> Prop)
    (rec1 rec2 : machine_config a B C -> ffi_state Ffi -> B -> result) mc ffi ms :
  (forall x, R x x) -> (forall mc ffi ms, R (rec1 mc ffi ms) (rec2 mc ffi ms)) ->
  R (evaluate_body rec1 mc ffi ms) (evaluate_body rec2 mc ffi ms).
Proof.
  intros Hr Hrec. unfold evaluate_body, apply_oracle. split_goal; auto.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "evaluate_add_clock" *)
Theorem evaluate_add_clock : forall mc ffi k ms k1 r ms1 st1,
  evaluate mc ffi k ms = (r, (ms1, st1)) /\ r <> TimeOut ->
  evaluate mc ffi (k + k1) ms = (r, (ms1, st1)).
Proof.
  intros mc ffi k; revert mc ffi.
  induction k as [|k IH] using N.peano_ind; intros mc ffi ms k1 r ms1 st1 [H Hr].
  { rewrite evaluate_eqn in H. injection H as <- _ _. contradiction. }
  rewrite evaluate_eqn in H |- *.
  rewrite (proj2 (N.eqb_neq (N.succ k) 0)) in H by lia.
  rewrite (proj2 (N.eqb_neq (N.succ k + k1) 0)) by lia.
  replace (N.succ k - 1) with k in H by lia.
  replace (N.succ k + k1 - 1) with (k + k1) by lia.
  pose proof (evaluate_body_rel (fun x y => FST x <> TimeOut -> y = x)
    (fun mc ffi ms => evaluate mc ffi k ms) (fun mc ffi ms => evaluate mc ffi (k + k1) ms)
    mc ffi ms) as R.
  rewrite H in R. apply R; [intros x _; reflexivity| |exact Hr].
  intros mc' ffi' ms'. destruct (evaluate mc' ffi' k ms') as [r' [ms'' st']] eqn:E.
  intros Hr'. apply IH. split; [exact E|exact Hr'].
Qed.

Lemma call_FFI_prefix {F} (st st' : ffi_state F) n conf bytes bytes' :
  call_FFI st n conf bytes = FFI_return st' bytes' ->
  isPREFIX (io_events st) (io_events st').
Proof.
  unfold call_FFI. intros H.
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x; try discriminate
         | context [if ?x then _ else _] => destruct x; try discriminate
         end;
  injection H as <- <-; cbn; [|apply isPREFIX_REFL].
  clear. induction (io_events st) as [|x0 l0 IH]; cbn; [reflexivity|].
  unfold is_true; rewrite Bool.andb_true_iff; split; [apply bool_decide_spec; reflexivity|exact IH].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "evaluate_io_events_mono" *)
Theorem evaluate_io_events_mono : forall mc ffi k ms,
  isPREFIX (io_events ffi) (io_events (SND (SND (evaluate mc ffi k ms)))).
Proof.
  intros mc ffi k; revert mc ffi.
  induction k as [|k IH] using N.peano_ind; intros mc ffi ms.
  { rewrite evaluate_eqn. apply isPREFIX_REFL. }
  rewrite evaluate_eqn, (proj2 (N.eqb_neq (N.succ k) 0)) by lia.
  replace (N.succ k - 1) with k by lia.
  unfold evaluate_body, apply_oracle. split_goal; try apply isPREFIX_REFL; try apply IH;
    match goal with
    | E : call_FFI _ _ _ _ = FFI_return _ _ |- _ =>
        eapply isPREFIX_TRANS; split; [eapply call_FFI_prefix; exact E|apply IH]
    end.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "evaluate_add_clock_io_events_mono" *)
Theorem evaluate_add_clock_io_events_mono : forall mc ffi k ms k',
  k <= k' ->
  isPREFIX (io_events (SND (SND (evaluate mc ffi k ms))))
           (io_events (SND (SND (evaluate mc ffi k' ms)))).
Proof.
  intros mc ffi k; revert mc ffi.
  induction k as [|k IH] using N.peano_ind; intros mc ffi ms k' Hk.
  { rewrite (evaluate_eqn mc ffi 0). apply evaluate_io_events_mono. }
  rewrite !evaluate_eqn, (proj2 (N.eqb_neq (N.succ k) 0)), (proj2 (N.eqb_neq k' 0)) by lia.
  replace (N.succ k - 1) with k by lia.
  apply (evaluate_body_rel (fun x y => isPREFIX (io_events (SND (SND x)))
                                                (io_events (SND (SND y))))).
  - intros; apply isPREFIX_REFL.
  - intros; apply IH; lia.
Qed.

(** The machine run at clock [k1] determines the run at any larger
    clock, unless it timed out (Galette helper). *)
Lemma evaluate_clock_le mc ffi k1 k2 ms r ms1 st1 :
  evaluate mc ffi k1 ms = (r, (ms1, st1)) -> r <> TimeOut -> k1 <= k2 ->
  evaluate mc ffi k2 ms = (r, (ms1, st1)).
Proof.
  intros H Hr Hk. replace k2 with (k1 + (k2 - k1)) by lia.
  apply evaluate_add_clock. split; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "machine_sem_total" *)
Theorem machine_sem_total : forall mc st ms, exists b, machine_sem mc st ms b.
Proof.
  intros mc st ms.
  destruct (classical_dec (exists k t, FST (evaluate mc st k ms) = Halt t)) as [(k & t & Hk)|Hh].
  { destruct (evaluate mc st k ms) as [r [ms' st']] eqn:E. cbn in Hk. subst r.
    exists (Terminate t (io_events st')). cbn. exists k, ms', st'. split; [exact E|reflexivity]. }
  destruct (classical_dec (exists k, FST (evaluate mc st k ms) = Error)) as [He|He].
  { exists Fail. exact He. }
  eexists (Diverge (build_lprefix_lub _)). cbn. split.
  - intros k. destruct (evaluate mc st k ms) as [r [ms' st']] eqn:E.
    destruct r as [t| |].
    + exfalso. apply Hh. exists k, t. rewrite E. reflexivity.
    + exfalso. apply He. exists k. rewrite E. reflexivity.
    + exists ms', st'. reflexivity.
  - apply build_lprefix_lub_thm.
    assert (EI : IMAGE (fun k => fromList (io_events (snd (snd (evaluate mc st k ms))))) UNIV =
                 IMAGE fromList (IMAGE (fun k => io_events (snd (snd (evaluate mc st k ms)))) UNIV)).
    { apply functional_extensionality; intros y; apply propositional_extensionality.
      unfold IMAGE, UNIV. split.
      - intros (k & -> & _). eexists; split; [reflexivity|]. exists k. split; [reflexivity|exact Logic.I].
      - intros (l & -> & (k & -> & _)). exists k. split; [reflexivity|exact Logic.I]. }
    rewrite EI. apply prefix_chain_lprefix_chain.
    intros l1 l2 [(k1 & -> & _) (k2 & -> & _)].
    destruct (N.le_ge_cases k1 k2); [left|right]; apply evaluate_add_clock_io_events_mono; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "machine_sem_unique" *)
Theorem machine_sem_unique : forall mc ffi ms b1 b2,
  machine_sem mc ffi ms b1 /\ machine_sem mc ffi ms b2 -> b1 = b2.
Proof.
  intros mc ffi ms b1 b2 [H1 H2].
  destruct b1 as [l1|t1 io1|], b2 as [l2|t2 io2|]; cbn in H1, H2.
  - f_equal. eapply unique_lprefix_lub. split; [exact (proj2 H1)|exact (proj2 H2)].
  - destruct H1 as [H1 _]. destruct H2 as (k & ms' & st' & E & _).
    destruct (H1 k) as (ms'' & st'' & E'). congruence.
  - destruct H1 as [H1 _]. destruct H2 as [k E]. destruct (H1 k) as (ms'' & st'' & E'').
    rewrite E'' in E. discriminate.
  - destruct H2 as [H2 _]. destruct H1 as (k & ms' & st' & E & _).
    destruct (H2 k) as (ms'' & st'' & E'). congruence.
  - destruct H1 as (k1 & ms1 & st1 & E1 & <-), H2 as (k2 & ms2 & st2 & E2 & <-).
    pose proof (evaluate_clock_le _ _ _ (k1 + k2) _ _ _ _ E1 ltac:(discriminate) ltac:(lia)) as F1.
    pose proof (evaluate_clock_le _ _ _ (k1 + k2) _ _ _ _ E2 ltac:(discriminate) ltac:(lia)) as F2.
    rewrite F1 in F2. injection F2 as -> _ ->. reflexivity.
  - destruct H1 as (k1 & ms1 & st1 & E1 & _), H2 as [k2 E2].
    destruct (evaluate mc ffi k2 ms) as [r [ms2 st2]] eqn:E. cbn in E2. subst r.
    pose proof (evaluate_clock_le _ _ _ (k1 + k2) _ _ _ _ E1 ltac:(discriminate) ltac:(lia)) as F1.
    pose proof (evaluate_clock_le _ _ _ (k1 + k2) _ _ _ _ E ltac:(discriminate) ltac:(lia)) as F2.
    congruence.
  - destruct H2 as [H2 _]. destruct H1 as [k E]. destruct (H2 k) as (ms'' & st'' & E'').
    rewrite E'' in E. discriminate.
  - destruct H2 as (k1 & ms1 & st1 & E1 & _), H1 as [k2 E2].
    destruct (evaluate mc ffi k2 ms) as [r [ms2 st2]] eqn:E. cbn in E2. subst r.
    pose proof (evaluate_clock_le _ _ _ (k1 + k2) _ _ _ _ E1 ltac:(discriminate) ltac:(lia)) as F1.
    pose proof (evaluate_clock_le _ _ _ (k1 + k2) _ _ _ _ E ltac:(discriminate) ltac:(lia)) as F2.
    congruence.
  - reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "read_ffi_bytearray_IMP_SUBSET_prog_addresses" *)
Theorem read_ffi_bytearray_IMP_SUBSET_prog_addresses : forall mc a0 l ms bytes,
  read_ffi_bytearray mc a0 l ms = SOME bytes ->
  all_words (get_reg mc.(target) ms a0) (LENGTH bytes) SUBSET mc.(prog_addresses).
Proof.
  intros mc a0 l ms. unfold read_ffi_bytearray.
  generalize (get_reg mc.(target) ms a0) as x. generalize (w2n (get_reg mc.(target) ms l)) as n.
  intros n; induction n as [|n IH] using N.peano_ind; intros x res H.
  - rewrite (proj1 (read_bytearray_def _ _ 0)) in H. injection H as <-. cbn [LENGTH].
    rewrite (proj1 (all_words_def x 0)). intros y Hy. destruct Hy.
  - rewrite (proj2 (read_bytearray_def _ _ n)) in H.
    destruct (classical_dec (x IN prog_addresses mc)) as [Hx|]; [|discriminate].
    destruct (read_bytearray _ n _) as [bs|] eqn:Eb; [|discriminate].
    injection H as <-. cbn [LENGTH]. rewrite (proj2 (all_words_def x (LENGTH bs))).
    intros y [->|Hy]; [exact Hx|]. exact (IH _ _ Eb y Hy).
Qed.

End Basic.

(** ** Interface lemmas for the interference contracts *)

Section Contracts.
Context {a : N} {B C : Type}.
Local Abbreviation ffi_offset := lab_to_target.ffi_offset.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "ffi_interfer_ok_post_ffi_asm" *)
Theorem ffi_interfer_ok_post_ffi_asm : forall pc0 (mc_conf : machine_config a B C) index i
    (t1 : asm_state a) ms2 bytes bytes2 new_bytes k,
  ffi_interfer_ok pc0 mc_conf /\
  index < LENGTH mc_conf.(ffi_names) /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  index < i /\
  mc_conf.(prog_addresses) = t1.(mem_domain) /\
  read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) /\
  LENGTH new_bytes = LENGTH bytes2 /\
  (EL index mc_conf.(ffi_names) = ExtCall (strlit []) -> new_bytes = bytes2) /\
  target_state_rel mc_conf.(target)
    (set_pc (- n2w ((3 + index) * ffi_offset) + pc0)%w t1) ms2 /\
  aligned (code_alignment (config mc_conf.(target)))
    (t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0 | Some n => n end)) ->
  target_state_rel mc_conf.(target)
    (post_ffi_asm mc_conf t1 new_bytes
       (mc_conf.(ffi_interfer) k (index, (new_bytes, ms2))))
    (mc_conf.(ffi_interfer) k (index, (new_bytes, ms2))).
Proof.
  intros pc0 mc_conf index i t1 ms2 bytes bytes2 new_bytes k
    (Hok & Hl & Hi & Hlt & Hd & Hr & Hlen & Hext & Hrel & Hal).
  destruct (Hok ms2 k index new_bytes t1 bytes bytes2 i (conj Hl (conj Hi Hd))) as [Hlow _].
  destruct (Hlow Hlt (conj Hr (conj Hlen (conj Hext (conj Hrel Hal))))) as (S1 & S2 & S3 & S4).
  unfold post_ffi_asm, target_state_rel. cbn [asmSem.set_pc asmSem.set_mem asmSem.set_fp_regs
    asmSem.set_regs asmSem.regs asmSem.fp_regs asmSem.mem asmSem.mem_domain asmSem.pc].
  split; [exact S1|split; [exact S2|split; [exact S3|split]]].
  - intros r [Hr1 Hr2]. destruct (MEM r (callee_saved_regs mc_conf)) eqn:Ec.
    + cbn [orb]. apply S4. split; [exact Ec|split; assumption].
    + cbn [orb]. rewrite (proj2 (N.ltb_lt _ _) Hr1). cbn [negb orb].
      apply not_true_is_false in Hr2. rewrite Hr2. reflexivity.
  - intros j _. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "ccache_interfer_ok_post_ccache_asm" *)
Theorem ccache_interfer_ok_post_ccache_asm : forall pc0 (mc_conf : machine_config a B C)
    (t1 : asm_state a) ms2 k a1 a2,
  ccache_interfer_ok pc0 mc_conf /\
  target_state_rel mc_conf.(target)
    (set_pc (- n2w (2 * ffi_offset) + pc0)%w t1) ms2 /\
  aligned (code_alignment (config mc_conf.(target)))
    (t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0 | Some n => n end)) ->
  target_state_rel mc_conf.(target)
    (post_ccache_asm mc_conf t1 (mc_conf.(ccache_interfer) k (a1, (a2, ms2))))
    (mc_conf.(ccache_interfer) k (a1, (a2, ms2))).
Proof.
  intros pc0 mc_conf t1 ms2 k a1 a2 (Hok & Hrel & Hal).
  destruct (Hok ms2 t1 k a1 a2 (conj Hrel Hal)) as (S1 & S2 & S3 & S4).
  unfold post_ccache_asm, target_state_rel. cbn [asmSem.set_pc asmSem.set_fp_regs
    asmSem.set_regs asmSem.regs asmSem.fp_regs asmSem.mem asmSem.mem_domain asmSem.pc].
  split; [exact S1|split; [exact S2|split; [exact S3|split]]].
  - intros r [Hr1 Hr2].
    destruct (MEM r (callee_saved_regs mc_conf) || bool_decide (r = ptr_reg mc_conf)) eqn:Ec.
    + cbn [orb]. apply S4. split; [|split; assumption].
      apply Bool.orb_true_iff in Ec as [Ec|Ec]; [left; exact Ec|right; exact (proj1 (bool_decide_spec _) Ec)].
    + cbn [orb]. rewrite (proj2 (N.ltb_lt _ _) Hr1). cbn [negb orb].
      apply not_true_is_false in Hr2. rewrite Hr2. reflexivity.
  - intros j _. reflexivity.
Qed.

End Contracts.

(** ** Executing the encoding of an instruction *)

Section Step.
Context {a : N} {B C Ffi : Type}.
Implicit Types (c : machine_config a B C) (io : ffi_state Ffi) (ms : B).

Lemma DROP_LENGTH_self {X} (l : list X) : DROP (LENGTH l) l = [].
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [LENGTH DROP].
  rewrite (proj2 (N.eqb_neq (N.succ (LENGTH l)) 0)) by lia.
  replace (N.succ (LENGTH l) - 1) with (LENGTH l) by lia. exact IH.
Qed.

Lemma bytes_in_memory_DROP (m : word a -> word8) d : forall l (p : word a) j,
  bytes_in_memory p l m d -> j < LENGTH l ->
  bytes_in_memory (p + n2w j)%w (DROP j l) m d.
Proof.
  intros l; induction l as [|x l IH]; intros p j H Hj; cbn [LENGTH] in Hj; [lia|].
  cbn [DROP]. destruct (N.eqb_spec j 0) as [->|Hj0].
  - rewrite (proj1 lemmas.WORD_ADD_0). exact H.
  - destruct H as (_ & _ & H).
    replace (p + n2w j)%w with ((p + n2w 1) + n2w (j - 1))%w.
    + destruct (N.eqb_spec (j - 1) (LENGTH l)) as [E|E].
      * rewrite E, DROP_LENGTH_self. exact Logic.I.
      * apply IH; [exact H|lia].
    + rewrite <- lemmas.WORD_ADD_ASSOC, lemmas.word_add_n2w. do 2 f_equal. lia.
Qed.

(** One machine step at a program address (Galette helper). *)
Lemma evaluate_one_step c io k ms1 :
  k <> 0 ->
  get_pc c.(target) ms1 IN (c.(prog_addresses) DIFF set c.(ffi_entry_pcs)) ->
  encoded_bytes_in_mem (config c.(target)) (get_pc c.(target) ms1)
    (get_byte c.(target) ms1) c.(prog_addresses) ->
  state_ok c.(target) ms1 -> state_ok c.(target) (next c.(target) ms1) ->
  state_ok c.(target) (c.(next_interfer) 0 (next c.(target) ms1)) ->
  (forall x, x NOTIN c.(prog_addresses) ->
     get_byte c.(target) (next c.(target) ms1) x = get_byte c.(target) ms1 x) ->
  evaluate c io k ms1 =
    evaluate (shift_interfer 1 c) io (k - 1) (c.(next_interfer) 0 (next c.(target) ms1)) /\
  find_next_interference c io k ms1 =
    find_next_interference (shift_interfer 1 c) io (k - 1)
      (c.(next_interfer) 0 (next c.(target) ms1)).
Proof.
  intros Hk Hpc Henc S1 S2 S3 Hb.
  rewrite evaluate_eqn, find_next_interference_eqn, (proj2 (N.eqb_neq k 0) Hk).
  unfold evaluate_body, find_next_interference_body, apply_oracle.
  destruct (classical_dec (_ IN _)) as [_|]; [|contradiction].
  destruct (classical_dec (encoded_bytes_in_mem _ _ _ _)) as [_|]; [|contradiction].
  cbv zeta. cbn [set_next_interfer target prog_addresses].
  destruct (classical_dec _) as [_|Hn]; [split; reflexivity|].
  exfalso. apply Hn. split; [|exact Hb].
  cbn [EVERY]. unfold is_true in *. rewrite S1, S2, S3. reflexivity.
Qed.

(** The start of an encoded instruction is an encoded instruction. *)
Lemma encoded_bytes_in_mem_intro (cfg : asm_config a) (i : asm.asm a) init_pc j
    (m : word a -> word8) (md dm : word a -> Prop) :
  j * 2 ** code_alignment cfg < LENGTH (encode cfg i) ->
  bytes_in_memory init_pc (encode cfg i) m md -> md SUBSET dm ->
  encoded_bytes_in_mem cfg (init_pc + n2w (j * 2 ** code_alignment cfg))%w m dm.
Proof.
  intros Hj Hb Hs. exists i, j. split; [exact Hj|].
  apply (bytes_in_memory_SUBSET md dm). split; [exact Hs|].
  apply bytes_in_memory_DROP; assumption.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "evaluate_EQ_evaluate_lemma" *)
Theorem evaluate_EQ_evaluate_lemma : forall n ms1 c dm (i : asm.asm a) (init_pc : word a)
    (s2 : asm_state a) io,
  get_pc c.(target) ms1 IN (c.(prog_addresses) DIFF set c.(ffi_entry_pcs)) /\
  state_ok c.(target) ms1 /\
  c.(prog_addresses) = dm /\
  interference_ok c.(next_interfer) (proj c.(target) dm) /\
  (forall s ms, target_state_rel c.(target) s ms -> state_ok c.(target) ms) /\
  (forall ms1 ms2, proj c.(target) dm ms1 = proj c.(target) dm ms2 ->
     state_ok c.(target) ms1 = state_ok c.(target) ms2 /\
     get_pc c.(target) ms1 = get_pc c.(target) ms2 /\
     (forall a0, a0 IN dm -> get_byte c.(target) ms1 a0 = get_byte c.(target) ms2 a0)) /\
  (forall env,
     interference_ok env (proj c.(target) dm) ->
     asserts n (fun k s => env k (next c.(target) s)) ms1
       (fun ms' => state_ok c.(target) ms' /\
          (forall pc0, pc0 IN all_pcs (LENGTH (encode (config c.(target)) i)) init_pc 0 ->
             get_byte c.(target) ms' pc0 = get_byte c.(target) ms1 pc0) /\
          get_pc c.(target) ms' IN
            all_pcs (LENGTH (encode (config c.(target)) i)) init_pc
              (code_alignment (config c.(target))))
       (fun ms' => target_state_rel c.(target) s2 ms')) /\
  asserts2 (n + 1) (fun k => c.(next_interfer) (n + 1 - k)) (next c.(target)) ms1
    (fun ms1 ms2 => forall x, x NOTIN dm ->
       get_byte c.(target) ms1 x = get_byte c.(target) ms2 x) /\
  (exists k,
     get_pc c.(target) ms1 = (init_pc + n2w (k * 2 ** code_alignment (config c.(target))))%w /\
     k * 2 ** code_alignment (config c.(target)) < LENGTH (encode (config c.(target)) i) /\
     bytes_in_memory init_pc (encode (config c.(target)) i)
       (get_byte c.(target) ms1) (c.(prog_addresses) DIFF set c.(ffi_entry_pcs))) ->
  exists ms2, forall k,
    evaluate c io (k + (n + 1)) ms1 = evaluate (shift_interfer (n + 1) c) io k ms2 /\
    find_next_interference c io (k + (n + 1)) ms1 =
      find_next_interference (shift_interfer (n + 1) c) io k ms2 /\
    target_state_rel c.(target) s2 ms2.
Proof.
  intros n; induction n as [|n IH] using N.peano_ind;
    intros ms1 c dm i init_pc s2 io (Hpc & S1 & Hdm & Hint & Hsok & Hproj & Has & Has2 & Hk);
    subst dm.
  all: assert (Hint0 : interference_ok (fun _ : N => c.(next_interfer) 0)
                         (proj c.(target) c.(prog_addresses)))
         by (intros j ms; apply Hint).
  all: pose proof (Has _ Hint0) as Has0.
  all: assert (Hb1 : forall x, x NOTIN c.(prog_addresses) ->
                 get_byte c.(target) (next c.(target) ms1) x = get_byte c.(target) ms1 x)
         by (intros x Hx; symmetry;
             refine (asserts2_first _ _ _ _ _ (conj _ Has2) x Hx); lia).
  all: assert (Henc : encoded_bytes_in_mem (config c.(target)) (get_pc c.(target) ms1)
                        (get_byte c.(target) ms1) c.(prog_addresses))
         by (destruct Hk as (j & -> & Hj & Hb);
             eapply encoded_bytes_in_mem_intro; [exact Hj|exact Hb|apply DIFF_SUBSET]).
  all: assert (Snext : state_ok c.(target) (next c.(target) ms1) =
                       state_ok c.(target) (c.(next_interfer) 0 (next c.(target) ms1)))
         by (symmetry; apply (Hproj _ _ (Hint 0 _))).
  - (* n = 0 *)
    rewrite (proj1 (asserts_def 0 _ _ _ _)) in Has0. cbn beta in Has0.
    exists (c.(next_interfer) 0 (next c.(target) ms1)). intros k.
    assert (S3 := Hsok _ _ Has0).
    destruct (evaluate_one_step c io (k + (0 + 1)) ms1 ltac:(lia) Hpc Henc S1
                ltac:(rewrite Snext; exact S3) S3 Hb1) as [E1 E2].
    replace (k + (0 + 1) - 1) with k in E1, E2 by lia.
    split; [exact E1|split; [exact E2|exact Has0]].
  - (* SUC n *)
    rewrite (proj2 (asserts_def n _ _ _ _)) in Has0. cbv zeta in Has0. cbn beta in Has0.
    destruct Has0 as [(P1 & P2 & P3) _].
    set (ms1' := c.(next_interfer) 0 (next c.(target) ms1)) in *.
    destruct (IH ms1' (shift_interfer 1 c) c.(prog_addresses) i init_pc s2 io) as [ms2 Hms2].
    { cbn [shift_interfer set_next_interfer target prog_addresses ffi_entry_pcs next_interfer].
      split; [|split; [exact P1|split; [reflexivity|split; [|split; [exact Hsok|split; [exact Hproj|split; [|split]]]]]]].
      - destruct Hk as (j0 & _ & _ & Hb).
        exact (bytes_in_memory_all_pcs _ _ _ _ _ Hb _ P3).
      - intros j ms. unfold shift_seq. apply Hint.
      - intros env Henv.
        set (env' := fun k => if k =? SUC n then c.(next_interfer) 0 else env k).
        assert (Henv' : interference_ok env' (proj c.(target) c.(prog_addresses))).
        { intros j ms. unfold env'. destruct (j =? SUC n); [apply Hint|apply Henv]. }
        pose proof (Has _ Henv') as H'.
        rewrite (proj2 (asserts_def n _ _ _ _)) in H'. cbv zeta in H'. cbn beta in H'.
        destruct H' as [_ H']. unfold env' at 2 in H'. rewrite N.eqb_refl in H'. fold ms1' in H'.
        revert H'. apply asserts_WEAKEN. intros j Hj. split.
        + apply functional_extensionality; intros s. unfold env'.
          rewrite (proj2 (N.eqb_neq j (SUC n))) by lia. reflexivity.
        + intros (Q1 & Q2 & Q3). split; [exact Q1|split; [|exact Q3]].
          intros pc0 Hpc0. rewrite (Q2 pc0 Hpc0), (P2 pc0 Hpc0). reflexivity.
      - rewrite (asserts2_def (SUC n + 1)) in Has2.
        destruct (bool_decide (SUC n + 1 = 0)) eqn:Ez;
          [apply bool_decide_spec in Ez; lia|].
        destruct Has2 as [_ Has2].
        replace (SUC n + 1 - (SUC n + 1)) with 0 in Has2 by lia. fold ms1' in Has2.
        replace (SUC n + 1 - 1) with (n + 1) in Has2 by lia.
        refine (asserts2_change_interfer _ _ _ _ _ _ (conj Has2 _)).
        intros j Hj. apply functional_extensionality; intros x. unfold shift_seq.
        cbn beta. f_equal. lia.
      - destruct P3 as (j & Ej & Hj). exists j. split; [exact Ej|split; [exact Hj|]].
        destruct Hk as (j0 & _ & _ & Hb).
        apply (bytes_in_memory_change_mem _ _ (get_byte c.(target) ms1)). split; [exact Hb|].
        intros m Hm. symmetry. apply P2. exists m. split; [|lia].
        rewrite N.pow_0_r, N.mul_1_r. reflexivity. }
    exists ms2. intros k. destruct (Hms2 k) as (E1 & E2 & Hrel).
    destruct (evaluate_one_step c io (k + (SUC n + 1)) ms1 ltac:(lia) Hpc Henc S1
                ltac:(rewrite Snext; exact P1) P1 Hb1) as [F1 F2].
    replace (k + (SUC n + 1) - 1) with (k + (n + 1)) in F1, F2 by lia. fold ms1' in F1, F2.
    rewrite shift_interfer_intro in E1, E2.
    replace (n + 1 + 1) with (SUC n + 1) in E1, E2 by lia.
    split; [congruence|split; [congruence|exact Hrel]].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "enc_ok_not_empty" *)
Theorem enc_ok_not_empty : forall (cfg : asm_config a) (w : asm.asm a),
  enc_ok cfg /\ asm_ok w cfg -> encode cfg w <> [].
Proof.
  intros cfg w [[_ [H _]] _] E. destruct (H w) as [_ H2]. rewrite E in H2. apply H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "asm_step_IMP_evaluate_step_find_next" *)
Theorem asm_step_IMP_evaluate_step_find_next : forall c (s1 : asm_state a) ms1 io (i : asm.asm a),
  encoder_correct c.(target) /\
  c.(prog_addresses) = s1.(mem_domain) /\
  ffi_entry_pcs_disjoint c s1 (LENGTH (encode (config c.(target)) i)) /\
  interference_ok c.(next_interfer) (proj c.(target) s1.(mem_domain)) /\
  asm_step (config c.(target)) s1 i
    (asm i (s1.(pc) + n2w (LENGTH (encode (config c.(target)) i)))%w s1) /\
  target_state_rel c.(target) s1 ms1 ->
  exists l ms2, forall k,
    evaluate c io (k + l) ms1 = evaluate (shift_interfer l c) io k ms2 /\
    find_next_interference c io (k + l) ms1 =
      find_next_interference (shift_interfer l c) io k ms2 /\
    target_state_rel c.(target)
      (asm i (s1.(pc) + n2w (LENGTH (encode (config c.(target)) i)))%w s1) ms2 /\
    l <> 0.
Proof.
  intros c s1 ms1 io i ((Hok & Henc) & Hdm & Hdis & Hint & Hstep & Hrel).
  set (s2 := asm i (s1.(pc) + n2w (LENGTH (encode (config c.(target)) i)))%w s1) in *.
  destruct (Henc s1 i s2 ms1 (conj Hstep Hrel)) as [n Hn]. cbv zeta in Hn.
  pose proof Hstep as (Hb & _ & _ & _ & _ & _ & Hasm_ok).
  assert (Hne : encode (config c.(target)) i <> []).
  { apply enc_ok_not_empty. split; [exact (proj1 Hok)|exact Hasm_ok]. }
  assert (Hlen : 0 < LENGTH (encode (config c.(target)) i)).
  { destruct (encode (config c.(target)) i); [contradiction|cbn [LENGTH]; lia]. }
  destruct Hrel as (Rok & Rpc & Rmem & Rregs & Rfp).
  destruct (evaluate_EQ_evaluate_lemma n ms1 c s1.(mem_domain) i s1.(pc) s2 io) as [ms2 H].
  { split; [|split; [exact Rok|split; [exact Hdm|split; [exact Hint|split; [|split; [|split; [|split]]]]]]].
    - rewrite Rpc, Hdm. split.
      + pose proof (bytes_in_memory_in_domain _ _ _ _ 0 (conj Hb Hlen)) as Hd.
        rewrite (proj1 lemmas.WORD_ADD_0) in Hd. exact Hd.
      + intros Hm. unfold ffi_entry_pcs_disjoint in Hdis. rewrite DISJOINT_ALT in Hdis.
        apply (Hdis _ Hm). exists 0. rewrite (proj1 lemmas.WORD_ADD_0). split; [reflexivity|exact Hlen].
    - intros s ms (H1 & _). exact H1.
    - intros m1 m2 E. destruct (proj2 Hok m1 m2 s1 E) as (_ & E1 & E2 & E3).
      split; [exact E1|split; [exact E2|exact E3]].
    - intros env Henv.
      destruct (Hn (fun k => env (n - k))) as [Ha _].
      { intros j ms. apply Henv. }
      revert Ha. apply asserts_WEAKEN. intros j Hj. split; [|intros P; exact P].
      apply functional_extensionality; intros x. cbn beta. f_equal. lia.
    - destruct (Hn c.(next_interfer)) as [_ Ha2]; [exact Hint|].
      exact Ha2.
    - exists 0. rewrite N.mul_0_l, (proj1 lemmas.WORD_ADD_0). split; [exact Rpc|split; [exact Hlen|]].
      apply (bytes_in_memory_DIFF _ c.(prog_addresses) (set c.(ffi_entry_pcs))).
      split; [reflexivity|split; [|exact Hdis]].
      apply (bytes_in_memory_change_mem _ _ s1.(mem)). split; [rewrite Hdm; exact Hb|].
      intros m Hm. symmetry. apply Rmem.
      exact (bytes_in_memory_in_domain _ _ _ _ m (conj Hb Hm)). }
  exists (n + 1), ms2. intros k. destruct (H k) as (E1 & E2 & E3).
  split; [exact E1|split; [exact E2|split; [exact E3|lia]]].
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetPropsScript.sml" "asm_step_IMP_evaluate_step" *)
Theorem asm_step_IMP_evaluate_step : forall c (s1 : asm_state a) ms1 io (i : asm.asm a),
  encoder_correct c.(target) /\
  c.(prog_addresses) = s1.(mem_domain) /\
  ffi_entry_pcs_disjoint c s1 (LENGTH (encode (config c.(target)) i)) /\
  interference_ok c.(next_interfer) (proj c.(target) s1.(mem_domain)) /\
  asm_step (config c.(target)) s1 i
    (asm i (s1.(pc) + n2w (LENGTH (encode (config c.(target)) i)))%w s1) /\
  target_state_rel c.(target) s1 ms1 ->
  exists l ms2,
    (forall k, evaluate c io (k + l) ms1 = evaluate (shift_interfer l c) io k ms2) /\
    target_state_rel c.(target)
      (asm i (s1.(pc) + n2w (LENGTH (encode (config c.(target)) i)))%w s1) ms2 /\
    l <> 0.
Proof.
  intros c s1 ms1 io i H.
  destruct (asm_step_IMP_evaluate_step_find_next c s1 ms1 io i H) as (l & ms2 & H').
  exists l, ms2. split; [intros k; apply (H' k)|]. destruct (H' 0) as (_ & _ & H1 & H2).
  split; assumption.
Qed.

End Step.
