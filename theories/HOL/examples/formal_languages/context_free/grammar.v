(** * HOL4 [grammar]: context-free grammars and parse trees

    Port of [HOL/examples/formal-languages/context-free/grammarScript.sml],
    restricted to what the PEG machinery and the Pancake parser use: the
    [inf] type abbreviation, symbols, parse trees and their executable
    location/fringe functions.

    Not ported: the [grammar] record and everything about derivations and
    languages ([valid_ptree], [complete_ptree], [language], [derive], ...
    and their theorems).  The [grammar] record has fields [start]/[rules],
    which [peg]'s record reuses; it is not needed by the parser. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.examples.formal_languages.context_free Require Import location.
Open Scope N_scope.
#[local] Set Warnings "-register-all".

(** HOL [type_abbrev("inf", ``:'a + num``)]. *)
Definition inf (B : Type) : Type := (B + N)%type.

#[global] Instance inf_eq_dec {B} `{EqDecision B} : EqDecision (inf B) := sum_eq_dec.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "symbol" *)
Inductive symbol (A B : Type) : Type :=
| TOK : A -> symbol A B
| NT : inf B -> symbol A B.
Arguments TOK {A B} _.
Arguments NT {A B} _.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "isTOK_def" *)
Definition isTOK {A B} (s : symbol A B) : bool :=
  match s with TOK _ => true | NT _ => false end.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "destTOK_def" *)
Definition destTOK {A B L} (p : symbol A B * L) : option A :=
  match p with (TOK tk, _) => Some tk | _ => None end.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "parsetree" *)
Inductive parsetree (A B L : Type) : Type :=
| Lf : symbol A B * L -> parsetree A B L
| Nd : inf B * L -> list (parsetree A B L) -> parsetree A B L.
Arguments Lf {A B L} _.
Arguments Nd {A B L} _ _.

(** Every HOL type is inhabited; HOL's partial list functions on parse trees
    ([HD], [EL], ...) need this. *)
#[global] Instance parsetree_inhabited {A B L} `{Inhabited L} : Inhabited (parsetree A B L) :=
  Nd (inr 0%N, inhabitant L) [].


Section Ptree.
Context {A B L : Type}.

(** Induction principle for the nested datatype. *)
Lemma parsetree_ind' (P : parsetree A B L -> Prop) :
  (forall p, P (Lf p)) ->
  (forall n ts, Forall P ts -> P (Nd n ts)) ->
  forall t, P t.
Proof.
  intros hl hn; fix IH 1; intros [p|n ts]; [apply hl|apply hn].
  induction ts as [|t ts IHts]; constructor; [apply IH|apply IHts].
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_loc_def" *)
Definition ptree_loc (t : parsetree A B L) : L :=
  match t with Lf (_, l) => l | Nd (_, l) _ => l end.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_head_def" *)
Definition ptree_head (t : parsetree A B L) : symbol A B :=
  match t with Lf (tok, l) => tok | Nd (nt, l) children => NT nt end.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_fringe_def" 57 *)
Fixpoint ptree_fringe (t : parsetree A B L) : list (symbol A B) :=
  match t with
  | Lf (t, _) => [t]
  | Nd _ children => FLAT (MAP ptree_fringe children)
  end.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "real_fringe_def" *)
Fixpoint real_fringe (t : parsetree A B L) : list (symbol A B * L) :=
  match t with
  | Lf t => [t]
  | Nd n ptl => FLAT (MAP real_fringe ptl)
  end.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_fringe_real_fringe" *)
Theorem ptree_fringe_real_fringe : forall pt, ptree_fringe pt = MAP FST (real_fringe pt).
Proof.
  intros pt; induction pt as [[s l]|n ts IH] using parsetree_ind'; [reflexivity|].
  cbn; induction IH as [|t ts h _ IH']; [reflexivity|].
  cbn in *; rewrite List.map_app; congruence.
Qed.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "LENGTH_real_fringe" *)
Theorem LENGTH_real_fringe : forall pt, LENGTH (real_fringe pt) = LENGTH (ptree_fringe pt).
Proof.
  intros pt; rewrite ptree_fringe_real_fringe, !LENGTH_length, length_map; reflexivity.
Qed.

End Ptree.

(*! HOL "HOL/examples/formal-languages/context-free/grammarScript.sml" "ptree_list_loc_def" *)
Definition ptree_list_loc {A B} (l : list (parsetree A B locs)) : locs :=
  merge_list_locs (MAP ptree_loc l).
