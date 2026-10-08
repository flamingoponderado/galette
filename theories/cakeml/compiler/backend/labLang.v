(** * CakeML [labLang]: the target-neutral labelled assembly language

    Port of [cakeml/compiler/backend/labLangScript.sml].  HOL's constructor
    [Section] is [Section_] ([Section] is a Rocq keyword).  The constructors
    [Jump], [JumpCmp], [Call], [Halt] shadow ASM's (and stackLang's);
    the others are written qualified where needed. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
Open Scope N_scope.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "reg" *)
Abbreviation reg := N.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "lab" *)
Inductive lab : Type := Lab : N -> N -> lab.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "asm_with_lab" *)
Inductive asm_with_lab (a : N) : Type :=
| Jump : lab -> asm_with_lab a
| JumpCmp : cmp -> reg -> reg_imm a -> lab -> asm_with_lab a
| Call : lab -> asm_with_lab a
| LocValue : reg -> lab -> asm_with_lab a
| CallFFI : mlstring -> asm_with_lab a
| Install : asm_with_lab a
| Halt : asm_with_lab a.
Arguments Jump {a} _.
Arguments JumpCmp {a} _ _ _ _.
Arguments Call {a} _.
Arguments LocValue {a} _ _.
Arguments CallFFI {a} _.
Arguments Install {a}.
Arguments Halt {a}.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "asm_or_cbw" *)
Inductive asm_or_cbw (a : N) : Type :=
| Asmi : asm a -> asm_or_cbw a
| Cbw : reg -> reg -> asm_or_cbw a
| ShareMem : memop -> reg -> addr a -> asm_or_cbw a.
Arguments Asmi {a} _.
Arguments Cbw {a} _ _.
Arguments ShareMem {a} _ _ _.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "line" *)
Inductive line (a : N) : Type :=
| Label : N -> N -> N -> line a
| Asm : asm_or_cbw a -> list word8 -> N -> line a
| LabAsm : asm_with_lab a -> word a -> list word8 -> N -> line a.
Arguments Label {a} _ _ _.
Arguments Asm {a} _ _ _.
Arguments LabAsm {a} _ _ _ _.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "sec" *)
Inductive sec (a : N) : Type := Section_ : N -> list (line a) -> sec a.
Arguments Section_ {a} _ _.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "Section_num_def" *)
Definition Section_num {a} (s : sec a) : N := match s with Section_ k _ => k end.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "Section_lines_def" *)
Definition Section_lines {a} (s : sec a) : list (line a) :=
  match s with Section_ _ lines => lines end.

(*! HOL "cakeml/compiler/backend/labLangScript.sml" "prog" *)
Abbreviation prog a := (list (sec a)).

(** ** Decidable equality and inhabitants (Galette infrastructure) *)

#[global] Instance lab_eq_dec : EqDecision lab.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance lab_inhabited : Inhabited lab := Lab 0 0.

Section EqDec.
Context {a : N}.
#[global] Instance asm_with_lab_eq_dec : EqDecision (asm_with_lab a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance asm_or_cbw_eq_dec : EqDecision (asm_or_cbw a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance line_eq_dec : EqDecision (line a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
#[global] Instance sec_eq_dec : EqDecision (sec a).
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.
End EqDec.

#[global] Instance asm_with_lab_inhabited {a} : Inhabited (asm_with_lab a) := Halt.
#[global] Instance asm_or_cbw_inhabited {a} : Inhabited (asm_or_cbw a) := Cbw 0 0.
#[global] Instance line_inhabited {a} : Inhabited (line a) := Label 0 0 0.
#[global] Instance sec_inhabited {a} : Inhabited (sec a) := Section_ 0 [].
