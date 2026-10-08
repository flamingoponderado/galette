(** * CakeML [asmProps]: properties of the asm language (partial)

    Partial port of [cakeml/compiler/encoders/asm/asmPropsScript.sml]: the
    definitions up to [interference_ok] (the [target] record and the
    state relation used by [targetSem]) and [asm_deterministic].  The rest
    of the script (the [encoder_correct] machinery and its lemmas) is not
    ported yet.

    HOL's [('a,'b,'c) target] is [target a B C] (width index [a], machine
    state [B], projection type [C]); its fields carry HOL's names.  As in
    [asmSem], the short names [asm], [inst] denote [asmSem]'s functions;
    the types are [asm.asm], [asm.inst]. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem.
Open Scope N_scope.

(** ** Semantics is deterministic *)

(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asm_deterministic" *)
Theorem asm_deterministic : forall {a} (c : asm_config a) i (s1 s2 s3 : asm_state a),
  asm_step c s1 i s2 /\ asm_step c s1 i s3 -> s2 = s3.
Proof.
  intros a c i s1 s2 s3 [(_ & _ & _ & _ & H2 & _) (_ & _ & _ & _ & H3 & _)].
  rewrite <- H2, <- H3; reflexivity.
Qed.

(** ** Well-formedness of encoding *)

Section Enc.
Context {a : N}.

(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "offset_monotonic_def" *)
Definition offset_monotonic (enc : asm.asm a -> list word8) (c : asm_config a)
    (a1 a2 : word a) (i1 i2 : asm.asm a) : Prop :=
  asm_ok i1 c /\ asm_ok i2 c ->
  ((n2w 0 <= a1)%w /\ (n2w 0 <= a2)%w /\ (a1 <= a2)%w -> LENGTH (enc i1) <= LENGTH (enc i2)) /\
  ((a1 < n2w 0)%w /\ (a2 < n2w 0)%w /\ (a2 <= a1)%w -> LENGTH (enc i1) <= LENGTH (enc i2)).

(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "enc_ok_def" *)
Definition enc_ok (c : asm_config a) : Prop :=
  (* code alignment and length *)
  (2 ** code_alignment c = LENGTH (encode c (Inst Skip))) /\
  (forall w, (LENGTH (encode c w) MOD 2 ** code_alignment c = 0) /\
             LENGTH (encode c w) <> 0) /\
  (* label instantiation predictably affects length of code *)
  (forall w1 w2, offset_monotonic (encode c) c w1 w2 (Jump w1) (Jump w2)) /\
  (forall cmp r ri w1 w2,
     offset_monotonic (encode c) c w1 w2
       (JumpCmp cmp r ri w1) (JumpCmp cmp r ri w2)) /\
  (forall w1 w2, offset_monotonic (encode c) c w1 w2 (Call w1) (Call w2)) /\
  (forall w1 w2 r, offset_monotonic (encode c) c w1 w2 (Loc r w1) (Loc r w2)).

End Enc.

(** ** Targets *)

(** HOL's record [target], fields in HOL's order. *)
(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "target" *)
Record target (a : N) (B C : Type) : Type := mk_target {
  config : asm_config a;
  next : B -> B;
  get_pc : B -> word a;
  get_reg : B -> N -> word a;
  get_fp_reg : B -> N -> word64;
  get_byte : B -> word a -> word8;
  state_ok : B -> bool;
  proj : (word a -> Prop) -> B -> C
}.
Arguments mk_target {a B C} _ _ _ _ _ _ _ _.
Arguments config {a B C} _.
Arguments next {a B C} _ _.
Arguments get_pc {a B C} _ _.
Arguments get_reg {a B C} _ _ _.
Arguments get_fp_reg {a B C} _ _ _.
Arguments get_byte {a B C} _ _ _.
Arguments state_ok {a B C} _ _.
Arguments proj {a B C} _ _ _.

Section Targets.
Context {a : N} {B C : Type}.

(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "target_state_rel_def" *)
Definition target_state_rel (t : target a B C) (s : asm_state a) (ms : B) : Prop :=
  state_ok t ms /\ (get_pc t ms = s.(pc)) /\
  (forall ad, ad IN s.(mem_domain) -> get_byte t ms ad = s.(mem) ad) /\
  (forall i, i < reg_count (config t) /\ ~ MEM i (avoid_regs (config t)) ->
     get_reg t ms i = s.(regs) i) /\
  (forall i, i < fp_reg_count (config t) -> get_fp_reg t ms i = s.(fp_regs) i).

(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "target_ok_def" *)
Definition target_ok (t : target a B C) : Prop :=
  enc_ok (config t) /\
  forall ms1 ms2 (s : asm_state a),
    proj t s.(mem_domain) ms1 = proj t s.(mem_domain) ms2 ->
    (target_state_rel t s ms1 <-> target_state_rel t s ms2) /\
    (state_ok t ms1 = state_ok t ms2) /\
    (get_pc t ms1 = get_pc t ms2) /\
    (forall ad, ad IN s.(mem_domain) -> get_byte t ms1 ad = get_byte t ms2 ad).

End Targets.

(*! HOL "cakeml/compiler/encoders/asm/asmPropsScript.sml" "interference_ok_def" *)
Definition interference_ok {B C : Type} (env : N -> B -> B) (proj : B -> C) : Prop :=
  forall (i : N) ms, proj (env i ms) = proj ms.
