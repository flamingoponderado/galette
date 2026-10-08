(** * CakeML [targetSem]: semantics of the target machine

    Port of [cakeml/compiler/backend/semantics/targetSemScript.sml]: the
    target machine run with interference from the environment
    ([evaluate], [machine_sem]) and the installation predicates.

    - HOL's [('a,'b,'c) machine_config] is [machine_config a B C] (width
      index [a], machine state [B], projection type [C]); its fields carry
      HOL's names ([target] is the field; the type of targets is
      [asmProps.target]).  [mc with f := v] is [set_<f> v mc].
    - HOL tuples [x # y # z] are right-nested, so they are written
      [x * (y * z)] here (and [evaluate] returns [(res, (ms, ffi))]),
      keeping [SND (SND (evaluate ...))] etc. as in HOL.
    - Conditions over arbitrary sets ([IN] an address set, [∀x. ...]) are
      decided classically ([classical_dec]).
    - [evaluate] recurses on the clock [k] ([num_rec]); HOL's equation is
      [evaluate_def].
    - Not ported: [installed_def], which needs [misc]'s [word_list] and
      [word_list_exists] (not yet in [misc.v]). *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require lab_to_target wordLang.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "machine_result" *)
Inductive machine_result : Type :=
| Halt : outcome -> machine_result
| Error : machine_result
| TimeOut : machine_result.

#[global] Instance machine_result_inhabited : Inhabited machine_result := Error.

(** ** Machine configurations *)

(** HOL's record [machine_config], fields in HOL's order. *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "machine_config" *)
Record machine_config (a : N) (B C : Type) : Type := mk_machine_config {
  prog_addresses : word a -> Prop;
  shared_addresses : word a -> Prop;
  (* FFI-specific configurations *)
  ffi_entry_pcs : list (word a);
  ffi_names : list ffiname;
  ptr_reg : N;
  len_reg : N;
  ptr2_reg : N;
  len2_reg : N;
  (* major interference by FFI calls *)
  ffi_interfer : N -> N * (list word8 * B) -> B;
  callee_saved_regs : list N;
  (* minor interference during execution *)
  next_interfer : N -> B -> B;
  (* program exits successfully at halt_pc *)
  halt_pc : word a;
  (* entry point for calling clear_cache *)
  ccache_pc : word a;
  (* major interference by calling clear_cache *)
  ccache_interfer : N -> word a * (word a * B) -> B;
  (* target next-state function etc. *)
  target : asmProps.target a B C;
  (* ffi_index -> byte_size, address, register to be updated/ stored, new pc value *)
  mmio_info : list (N * (word8 * (asm.addr a * (N * word a))))
}.
Arguments mk_machine_config {a B C} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Arguments prog_addresses {a B C} _ _.
Arguments shared_addresses {a B C} _ _.
Arguments ffi_entry_pcs {a B C} _.
Arguments ffi_names {a B C} _.
Arguments ptr_reg {a B C} _.
Arguments len_reg {a B C} _.
Arguments ptr2_reg {a B C} _.
Arguments len2_reg {a B C} _.
Arguments ffi_interfer {a B C} _ _ _.
Arguments callee_saved_regs {a B C} _.
Arguments next_interfer {a B C} _ _ _.
Arguments halt_pc {a B C} _.
Arguments ccache_pc {a B C} _.
Arguments ccache_interfer {a B C} _ _ _.
Arguments target {a B C} _.
Arguments mmio_info {a B C} _.

Section Config.
Context {a : N} {B C : Type}.
Implicit Types (mc : machine_config a B C).

Definition set_ffi_interfer x mc :=
  mk_machine_config mc.(prog_addresses) mc.(shared_addresses) mc.(ffi_entry_pcs)
    mc.(ffi_names) mc.(ptr_reg) mc.(len_reg) mc.(ptr2_reg) mc.(len2_reg) x
    mc.(callee_saved_regs) mc.(next_interfer) mc.(halt_pc) mc.(ccache_pc)
    mc.(ccache_interfer) mc.(target) mc.(mmio_info).
Definition set_next_interfer x mc :=
  mk_machine_config mc.(prog_addresses) mc.(shared_addresses) mc.(ffi_entry_pcs)
    mc.(ffi_names) mc.(ptr_reg) mc.(len_reg) mc.(ptr2_reg) mc.(len2_reg)
    mc.(ffi_interfer) mc.(callee_saved_regs) x mc.(halt_pc) mc.(ccache_pc)
    mc.(ccache_interfer) mc.(target) mc.(mmio_info).
Definition set_ccache_interfer x mc :=
  mk_machine_config mc.(prog_addresses) mc.(shared_addresses) mc.(ffi_entry_pcs)
    mc.(ffi_names) mc.(ptr_reg) mc.(len_reg) mc.(ptr2_reg) mc.(len2_reg)
    mc.(ffi_interfer) mc.(callee_saved_regs) mc.(next_interfer) mc.(halt_pc)
    mc.(ccache_pc) x mc.(target) mc.(mmio_info).

End Config.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "apply_oracle_def" *)
Definition apply_oracle {X Y : Type} (oracle : N -> X -> Y) (x : X) : Y * (N -> X -> Y) :=
  (oracle 0 x, shift_seq 1 oracle).

Section Sem.
Context {a : N} {B C : Type}.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "encoded_bytes_in_mem_def" *)
Definition encoded_bytes_in_mem (c : asm_config a) (pc0 : word a) (m : word a -> word8)
    (md : word a -> Prop) : Prop :=
  exists i k, k * (2 ** code_alignment c) < LENGTH (encode c i) /\
    bytes_in_memory pc0
      (DROP (k * (2 ** code_alignment c)) (encode c i))
      m md.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "read_ffi_bytearray_def" *)
Definition read_ffi_bytearray (mc : machine_config a B C) (ptr_reg0 len_reg0 : N) (ms : B)
    : option (list word8) :=
  read_bytearray (get_reg mc.(target) ms ptr_reg0)
    (w2n (get_reg mc.(target) ms len_reg0))
    (fun ad =>
       if classical_dec (ad IN mc.(prog_addresses)) then
         SOME (get_byte mc.(target) ms ad)
       else NONE).

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "read_ffi_bytearrays_def" *)
Definition read_ffi_bytearrays (mc : machine_config a B C) (ms : B)
    : option (list word8) * option (list word8) :=
  (read_ffi_bytearray mc mc.(ptr_reg) mc.(len_reg) ms,
   read_ffi_bytearray mc mc.(ptr2_reg) mc.(len2_reg) ms).

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "is_valid_mapped_read_def" *)
Definition is_valid_mapped_read (pc0 : word a) (nb : word8) (ad : asm.addr a) (r : N)
    (pc' : word a) (t : asmProps.target a B C) (ms : B) (md : word a -> Prop) : Prop :=
  if decide (nb = n2w 1)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Load8 r ad)))
      (get_byte t ms) md)
  else if decide (nb = n2w 0)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Load r ad)))
      (get_byte t ms) md)
  else if decide (nb = n2w 2)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Load16 r ad)))
      (get_byte t ms) md)
  else if decide (nb = n2w 4)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Load32 r ad)))
      (get_byte t ms) md)
  else False.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "is_valid_mapped_write_def" *)
Definition is_valid_mapped_write (pc0 : word a) (nb : word8) (ad : asm.addr a) (r : N)
    (pc' : word a) (t : asmProps.target a B C) (ms : B) (md : word a -> Prop) : Prop :=
  if decide (nb = n2w 1)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Store8 r ad)))
      (get_byte t ms) md)
  else if decide (nb = n2w 0)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Store r ad)))
      (get_byte t ms) md)
  else if decide (nb = n2w 2)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Store16 r ad)))
      (get_byte t ms) md)
  else if decide (nb = n2w 4)
  then
    (bytes_in_memory pc0 (encode (config t) (Inst (Mem Store32 r ad)))
      (get_byte t ms) md)
  else False.

Context {Ffi : Type}.

Local Abbreviation result := (machine_result * (B * ffi_state Ffi))%type.

(** One step of [evaluate] at a positive clock, with [rec] for the
    recursive calls at clock [k - 1]. *)
Definition evaluate_body
    (rec : machine_config a B C -> ffi_state Ffi -> B -> result)
    (mc : machine_config a B C) (ffi : ffi_state Ffi) (ms : B) : result :=
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
            else
              (Error, (ms, ffi))
        else (Error, (ms, ffi))
      else if decide (get_pc mc.(target) ms = mc.(halt_pc)) then
        (if decide (get_reg mc.(target) ms mc.(ptr_reg) = n2w 0)
         then Halt Success else Halt Resource_limit_hit, (ms, ffi))
      else if decide (get_pc mc.(target) ms = mc.(ccache_pc)) then
        let '(ms1, new_oracle) :=
          apply_oracle mc.(ccache_interfer)
            (get_reg mc.(target) ms mc.(ptr_reg),
             (get_reg mc.(target) ms mc.(len_reg),
              ms)) in
        let mc := set_ccache_interfer new_oracle mc in
          rec mc ffi ms1
      else
        match find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 with
        | NONE => (Error, (ms, ffi))
        | SOME ffi_index =>
            match EL ffi_index mc.(ffi_names) with
            | SharedMem op =>
                match ALOOKUP mc.(mmio_info) ffi_index with
                | NONE => (Error, (ms, ffi))
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
                                 | FFI_final outcome =>
                                     (Halt (FFI_outcome outcome), (ms, ffi))
                                 | FFI_return new_ffi new_bytes =>
                                     let '(ms1, new_oracle)
                                         := apply_oracle mc.(ffi_interfer)
                                                         (ffi_index, (new_bytes, ms)) in
                                       let mc := set_ffi_interfer new_oracle mc in
                                         rec mc new_ffi ms1
                                 end
                               else (Error, (ms, ffi)))
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
                                 | FFI_final outcome =>
                                     (Halt (FFI_outcome outcome), (ms, ffi))
                                 | FFI_return new_ffi new_bytes =>
                                     let '(ms1, new_oracle)
                                         := apply_oracle mc.(ffi_interfer)
                                                         (ffi_index, (new_bytes, ms)) in
                                       let mc := set_ffi_interfer new_oracle mc in
                                         rec mc new_ffi ms1
                                 end
                               else (Error, (ms, ffi)))
                        end
                    end
                end
            | ExtCall _ =>
                match ALOOKUP mc.(mmio_info) ffi_index with
                | SOME _ => (Error, (ms, ffi))
                | NONE =>
                    match read_ffi_bytearrays mc ms with
                    | (SOME bytes, SOME bytes2) =>
                        match call_FFI ffi (EL ffi_index mc.(ffi_names)) bytes bytes2 with
                        | FFI_final outcome => (Halt (FFI_outcome outcome), (ms, ffi))
                        | FFI_return new_ffi new_bytes =>
                            let '(ms1, new_oracle)
                                := apply_oracle mc.(ffi_interfer)
                                                (ffi_index, (new_bytes, ms)) in
                              let mc := set_ffi_interfer new_oracle mc in
                                rec mc new_ffi ms1
                        end
                    | _ => (Error, (ms, ffi))
                    end
                end
            end
        end.

(** [evaluate mc ffi k ms], by primitive recursion on the clock [k];
    HOL's defining equation is [evaluate_def]. *)
Definition evaluate (mc : machine_config a B C) (ffi : ffi_state Ffi) (k : N) (ms : B)
    : result :=
  num_rec (fun (_ : machine_config a B C) ffi ms => (TimeOut, (ms, ffi)))
    (fun _ rec mc ffi ms => evaluate_body rec mc ffi ms) k mc ffi ms.

Lemma evaluate_eqn : forall mc ffi k ms,
  evaluate mc ffi k ms =
  if k =? 0 then (TimeOut, (ms, ffi))
  else evaluate_body (fun mc ffi ms => evaluate mc ffi (k - 1) ms) mc ffi ms.
Proof.
  intros mc ffi k ms; destruct k as [|p] using N.peano_ind; [reflexivity|].
  unfold evaluate at 1; rewrite num_rec_SUC.
  replace (N.succ p =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  replace (N.succ p - 1) with p by lia; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "evaluate_def" *)
Theorem evaluate_def : forall (mc : machine_config a B C) (ffi : ffi_state Ffi) k (ms : B),
  evaluate mc ffi k ms =
    if k =? 0 then (TimeOut, (ms, ffi))
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
              evaluate mc ffi (k - 1) ms2
            else
              (Error, (ms, ffi))
        else (Error, (ms, ffi))
      else if decide (get_pc mc.(target) ms = mc.(halt_pc)) then
        (if decide (get_reg mc.(target) ms mc.(ptr_reg) = n2w 0)
         then Halt Success else Halt Resource_limit_hit, (ms, ffi))
      else if decide (get_pc mc.(target) ms = mc.(ccache_pc)) then
        let '(ms1, new_oracle) :=
          apply_oracle mc.(ccache_interfer)
            (get_reg mc.(target) ms mc.(ptr_reg),
             (get_reg mc.(target) ms mc.(len_reg),
              ms)) in
        let mc := set_ccache_interfer new_oracle mc in
          evaluate mc ffi (k - 1) ms1
      else
        match find_index (get_pc mc.(target) ms) mc.(ffi_entry_pcs) 0 with
        | NONE => (Error, (ms, ffi))
        | SOME ffi_index =>
            match EL ffi_index mc.(ffi_names) with
            | SharedMem op =>
                match ALOOKUP mc.(mmio_info) ffi_index with
                | NONE => (Error, (ms, ffi))
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
                                 | FFI_final outcome =>
                                     (Halt (FFI_outcome outcome), (ms, ffi))
                                 | FFI_return new_ffi new_bytes =>
                                     let '(ms1, new_oracle)
                                         := apply_oracle mc.(ffi_interfer)
                                                         (ffi_index, (new_bytes, ms)) in
                                       let mc := set_ffi_interfer new_oracle mc in
                                         evaluate mc new_ffi (k - 1) ms1
                                 end
                               else (Error, (ms, ffi)))
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
                                 | FFI_final outcome =>
                                     (Halt (FFI_outcome outcome), (ms, ffi))
                                 | FFI_return new_ffi new_bytes =>
                                     let '(ms1, new_oracle)
                                         := apply_oracle mc.(ffi_interfer)
                                                         (ffi_index, (new_bytes, ms)) in
                                       let mc := set_ffi_interfer new_oracle mc in
                                         evaluate mc new_ffi (k - 1) ms1
                                 end
                               else (Error, (ms, ffi)))
                        end
                    end
                end
            | ExtCall _ =>
                match ALOOKUP mc.(mmio_info) ffi_index with
                | SOME _ => (Error, (ms, ffi))
                | NONE =>
                    match read_ffi_bytearrays mc ms with
                    | (SOME bytes, SOME bytes2) =>
                        match call_FFI ffi (EL ffi_index mc.(ffi_names)) bytes bytes2 with
                        | FFI_final outcome => (Halt (FFI_outcome outcome), (ms, ffi))
                        | FFI_return new_ffi new_bytes =>
                            let '(ms1, new_oracle)
                                := apply_oracle mc.(ffi_interfer)
                                                (ffi_index, (new_bytes, ms)) in
                              let mc := set_ffi_interfer new_oracle mc in
                                evaluate mc new_ffi (k - 1) ms1
                        end
                    | _ => (Error, (ms, ffi))
                    end
                end
            end
        end.
Proof. intros mc ffi k ms; rewrite evaluate_eqn; reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "machine_sem_def" *)
Definition machine_sem (mc : machine_config a B C) (st : ffi_state Ffi) (ms : B)
    (b : behaviour) : Prop :=
  match b with
  | Terminate t io_list =>
      exists k ms' st',
        evaluate mc st k ms = (Halt t, (ms', st')) /\
        io_events st' = io_list
  | Diverge io_trace =>
      (forall k, exists ms' st', evaluate mc st k ms = (TimeOut, (ms', st'))) /\
      lprefix_lub
        (IMAGE
          (fun k => fromList (io_events (snd (snd (evaluate mc st k ms))))) UNIV)
        io_trace
  | Fail =>
      exists k, fst (evaluate mc st k ms) = Error
  end.

End Sem.

(** ** Code installation *)

Section Install.
Context {a : N} {B C : Type}.

(** define what it means for code to be loaded and ready to run *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "code_loaded_def" *)
Definition code_loaded (bytes : list word8) (mc : machine_config a B C) (ms : B) : Prop :=
  read_bytearray (get_pc mc.(target) ms) (LENGTH bytes)
    (fun ad => if classical_dec (ad IN mc.(prog_addresses))
              then SOME (get_byte mc.(target) ms ad) else NONE) = SOME bytes.

(** target_configured: target and mc_conf are compatible *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "target_configured_def" *)
Definition target_configured (t : asm_state a) (mc_conf : machine_config a B C) : Prop :=
  ~ t.(failed) /\
  t.(be) = big_endian (config mc_conf.(target)) /\
  t.(align) = code_alignment (config mc_conf.(target)) /\
  t.(mem_domain) = mc_conf.(prog_addresses) /\
  (match link_reg (config mc_conf.(target)) with None => True | Some r => t.(lr) = r end).

End Install.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "get_reg_value_def" *)
Definition get_reg_value {A B} (o_ : option A) (w : B) (f : A -> B) : B :=
  match o_ with
  | NONE => w
  | SOME v => f v
  end.

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "mmio_pcs_min_index_def" *)
Definition mmio_pcs_min_index (ffi_names0 : list ffiname) : option N :=
  some (fun x =>
    (x <= LENGTH ffi_names0) /\
    (forall j, j < x -> exists s, EL j ffi_names0 = ExtCall s) /\
    (forall j, x <= j /\ j < LENGTH ffi_names0 ->
         exists op, EL j ffi_names0 = SharedMem op)).

Section Ok.
Context {a : N} {B C : Type}.
Local Abbreviation ffi_offset := lab_to_target.ffi_offset.

(** start_pc_ok: machine configuration's saved pcs and initial pc are ok *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "start_pc_ok_def" *)
Definition start_pc_ok (mc_conf : machine_config a B C) (pc0 : word a) : Prop :=
  mc_conf.(halt_pc) NOTIN mc_conf.(prog_addresses) /\
  mc_conf.(ccache_pc) NOTIN mc_conf.(prog_addresses) /\
  mc_conf.(halt_pc) NOTIN mc_conf.(shared_addresses) /\
  mc_conf.(ccache_pc) NOTIN mc_conf.(shared_addresses) /\
  (pc0 - n2w ffi_offset = mc_conf.(halt_pc))%w /\
  (pc0 - n2w (2 * ffi_offset) = mc_conf.(ccache_pc))%w /\
  (n2w 1 && pc0 = n2w 0)%w /\
  exists i, mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  (forall index,
     index < i ->
     (pc0 - n2w ((3 + index) * ffi_offset))%w NOTIN
     mc_conf.(prog_addresses) /\
     (pc0 - n2w ((3 + index) * ffi_offset))%w NOTIN
     mc_conf.(shared_addresses) /\
     (pc0 - n2w ((3 + index) * ffi_offset))%w <>
     mc_conf.(halt_pc) /\
     (pc0 - n2w ((3 + index) * ffi_offset))%w <>
     mc_conf.(ccache_pc) /\
     find_index
       (pc0 - n2w ((3 + index) * ffi_offset))%w
       mc_conf.(ffi_entry_pcs) 0 = SOME index) /\
  (forall index,
    index < LENGTH mc_conf.(ffi_names) /\ i <= index ->
    mc_conf.(halt_pc) <> (EL index mc_conf.(ffi_entry_pcs)) /\
    mc_conf.(ccache_pc) <> (EL index mc_conf.(ffi_entry_pcs))) /\
  LENGTH mc_conf.(ffi_names) = LENGTH mc_conf.(ffi_entry_pcs).

(** ffi_interfer_ok: the FFI interference oracle is ok (see HOL's
    comment: per-call promises of the calling convention). *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "ffi_interfer_ok_def" *)
Definition ffi_interfer_ok (pc0 : word a) (mc_conf : machine_config a B C) : Prop :=
  forall ms2 k index new_bytes (t1 : asm_state a) bytes bytes2 i,
     index < LENGTH mc_conf.(ffi_names) /\
     mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
     mc_conf.(prog_addresses) = t1.(mem_domain) ->
       (index < i ->
         read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) /\
         LENGTH new_bytes = LENGTH bytes2 /\
         (EL index mc_conf.(ffi_names) = ExtCall (strlit []) -> new_bytes = bytes2) /\
         target_state_rel mc_conf.(target)
           (set_pc (- n2w ((3 + index) * ffi_offset) + pc0)%w t1) ms2 /\
         aligned (code_alignment (config mc_conf.(target)))
          (t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0 | Some n => n end))
      ->
      (let ms' := mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)) in
         state_ok mc_conf.(target) ms' /\
         get_pc mc_conf.(target) ms' =
           t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0
                      | Some n => n end) /\
         (forall ad, ad IN t1.(mem_domain) ->
              get_byte mc_conf.(target) ms' ad =
              asm_write_bytearray (t1.(regs) mc_conf.(ptr2_reg)) new_bytes t1.(mem) ad) /\
         (forall r, MEM r mc_conf.(callee_saved_regs) /\
              r < reg_count (config mc_conf.(target)) /\
              ~ MEM r (avoid_regs (config mc_conf.(target))) ->
              get_reg mc_conf.(target) ms' r = t1.(regs) r))) /\
       (i <= index /\
         target_state_rel mc_conf.(target)
          (set_pc (EL index mc_conf.(ffi_entry_pcs)) t1) ms2 ->
            (exists info, ALOOKUP mc_conf.(mmio_info) index = SOME info /\
             (EL index mc_conf.(ffi_names) = SharedMem MappedRead ->
             forall new_bytes,
             target_state_rel mc_conf.(target)
               (set_regs (fun n => if decide (n = fst (snd (snd info))) then
                    (word_of_bytes false (n2w 0) new_bytes) else t1.(regs) n)
                 (set_pc (snd (snd (snd info))) t1))
                (mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)))) /\
             (EL index mc_conf.(ffi_names) = SharedMem MappedWrite ->
             target_state_rel mc_conf.(target)
               (set_pc (snd (snd (snd info))) t1)
               (mc_conf.(ffi_interfer) k (index, (new_bytes, ms2)))))).

(** ccache_interfer_ok: a cache-clear transition must satisfy the same
    per-call promises, additionally preserving ptr_reg and leaving all
    program memory unchanged *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "ccache_interfer_ok_def" *)
Definition ccache_interfer_ok (pc0 : word a) (mc_conf : machine_config a B C) : Prop :=
  forall ms2 (t1 : asm_state a) k a1 a2,
     target_state_rel mc_conf.(target)
       (set_pc (- n2w (2 * ffi_offset) + pc0)%w t1)
     ms2 /\
     aligned (code_alignment (config mc_conf.(target)))
       (t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0 | Some n => n end)) ->
     (let ms' := mc_conf.(ccache_interfer) k (a1, (a2, ms2)) in
        state_ok mc_conf.(target) ms' /\
        get_pc mc_conf.(target) ms' =
          t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0
                     | Some n => n end) /\
        (forall ad, ad IN t1.(mem_domain) ->
             get_byte mc_conf.(target) ms' ad = t1.(mem) ad) /\
        (forall r, (MEM r mc_conf.(callee_saved_regs) \/ r = mc_conf.(ptr_reg)) /\
             r < reg_count (config mc_conf.(target)) /\
             ~ MEM r (avoid_regs (config mc_conf.(target))) ->
             get_reg mc_conf.(target) ms' r = t1.(regs) r)).

(** post_ffi_asm / post_ccache_asm: the canonical asm-level successor
    state after an FFI / cache-clear transition *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "post_ffi_asm_def" *)
Definition post_ffi_asm (mc_conf : machine_config a B C) (t1 : asm_state a)
    (new_bytes : list word8) (ms' : B) : asm_state a :=
  set_pc (t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0
                     | Some n => n end))
  (set_mem (asm_write_bytearray (t1.(regs) mc_conf.(ptr2_reg)) new_bytes t1.(mem))
  (set_fp_regs (fun i => get_fp_reg mc_conf.(target) ms' i)
  (set_regs (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                         negb (a0 <? reg_count (config mc_conf.(target))) ||
                         MEM a0 (avoid_regs (config mc_conf.(target)))
                      then t1.(regs) a0
                      else get_reg mc_conf.(target) ms' a0) t1))).

(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "post_ccache_asm_def" *)
Definition post_ccache_asm (mc_conf : machine_config a B C) (t1 : asm_state a)
    (ms' : B) : asm_state a :=
  set_pc (t1.(regs) (match link_reg (config mc_conf.(target)) with None => 0
                     | Some n => n end))
  (set_fp_regs (fun i => get_fp_reg mc_conf.(target) ms' i)
  (set_regs (fun a0 => if MEM a0 mc_conf.(callee_saved_regs) ||
                         bool_decide (a0 = mc_conf.(ptr_reg)) ||
                         negb (a0 <? reg_count (config mc_conf.(target))) ||
                         MEM a0 (avoid_regs (config mc_conf.(target)))
                      then t1.(regs) a0
                      else get_reg mc_conf.(target) ms' a0) t1)).

(** good_init_state: how code (bytes) and ffi is installed in the machine
    (mc_conf, ms), using labLang (m, dm, cbspace) and target semantics (t)
    information as an intermediary. *)
(*! HOL "cakeml/compiler/backend/semantics/targetSemScript.sml" "good_init_state_def" *)
Definition good_init_state
    (mc_conf : machine_config a B C) (ms : B) (bytes : list word8)
    (cbspace : N)
    (t : asm_state a) (m : word a -> wordLang.word_loc a) (dm sdm : word a -> Prop) : Prop :=
    target_state_rel mc_conf.(target) t ms /\
    target_configured t mc_conf /\

    (* starting pc assumptions *)
    t.(pc) = get_pc mc_conf.(target) ms /\
    start_pc_ok mc_conf t.(pc) /\
    (n2w (2 ** t.(align) - 1) && t.(pc) = n2w 0)%w /\

    interference_ok mc_conf.(next_interfer) (proj mc_conf.(target) mc_conf.(prog_addresses)) /\
    ffi_interfer_ok t.(pc) mc_conf /\
    ccache_interfer_ok t.(pc) mc_conf /\

    (* code memory relation *)
    code_loaded bytes mc_conf ms /\
    bytes_in_mem t.(pc) bytes t.(mem) t.(mem_domain) dm /\
    (* data memory relation -- note that this implies m contains no labels *)
    dm SUBSET t.(mem_domain) /\
    (forall ad, byte_align ad IN dm -> ad IN dm) /\
    sdm = mc_conf.(shared_addresses) /\
    (forall ad, byte_align ad IN sdm -> ad IN sdm) /\
    DISJOINT mc_conf.(prog_addresses) mc_conf.(shared_addresses) /\
    (forall ad, exists w,
      t.(mem) ad = byte.get_byte ad w (big_endian (config mc_conf.(target))) /\
      m (byte_align ad) = wordLang.Word w) /\
    (* code buffer constraints *)
    (forall n, n < cbspace ->
      (n2w (n + LENGTH bytes) + t.(pc))%w IN t.(mem_domain) /\
      (n2w (n + LENGTH bytes) + t.(pc))%w NOTIN dm) /\
    cbspace + LENGTH bytes < dimword a.

End Ok.
