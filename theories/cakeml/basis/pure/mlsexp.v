(** * CakeML [mlsexp]: mlstring-based S-expressions

    Port of [cakeml/basis/pure/mlsexpScript.sml], restricted to the pretty
    printing of [str_tree]s ([str_tree] ... [str_tree_to_strs]), which the
    compiler's [--explore] output uses (through [displayLang]).

    The constructors of [pretty] are HOL's: [String] shadows Rocq's
    [String.String] and [Append] shadows [misc]'s [app_list] constructor in
    any module importing this one, so clients [Require] this module without
    importing it (or import it before [misc]).

    Not ported: the [sexp] and [token] datatypes, lexing and parsing
    ([read_string], [lex], [parse], [fromString]), the [sexp] printers
    ([is_safe_char], [str_every], [make_str_safe], [sexp2tree],
    [sexp_to_app_list], [sexp_to_string], [sexp_to_pretty_string]) and
    their theorems. *)

From Galette Require Import Base.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
Open Scope N_scope.
Open Scope hol_string_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "str_tree" *)
Inductive str_tree : Type :=
| Str : mlstring -> str_tree
| Trees : list str_tree -> str_tree
| GrabLine : str_tree -> str_tree.

#[global] Instance str_tree_inhabited : Inhabited str_tree := Str (strlit "").

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "pretty" *)
Inductive pretty : Type :=
| Parenthesis : pretty -> pretty
| String : mlstring -> pretty
| Append : pretty -> bool -> pretty -> pretty
| Size : N -> pretty -> pretty.

#[global] Instance pretty_inhabited : Inhabited pretty := String (strlit "").

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "newlines_def" *)
Fixpoint newlines (l : list pretty) : pretty :=
  match l with
  | [] => String (strlit "")
  | [x] => x
  | x :: ((_ :: _) as xs) => Append x true (newlines xs)
  end.

(** HOL's [v2pretty]/[vs2pretty] are mutually recursive on [str_tree] and
    [str_tree list]; here [vs2pretty] is the nested [fix] and both are
    characterised by the tagged [v2pretty_def]. *)
Fixpoint v2pretty (v : str_tree) : pretty :=
  match v with
  | Str s => String s
  | GrabLine w => Size 100000 (v2pretty w)
  | Trees l =>
      Parenthesis (newlines ((fix vs2pretty (vs : list str_tree) : list pretty :=
                                match vs with
                                | [] => []
                                | v :: vs => v2pretty v :: vs2pretty vs
                                end) l))
  end.

Fixpoint vs2pretty (vs : list str_tree) : list pretty :=
  match vs with
  | [] => []
  | v :: vs => v2pretty v :: vs2pretty vs
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "v2pretty_def" *)
Theorem v2pretty_def :
  (forall v, v2pretty v =
     match v with
     | Str s => String s
     | GrabLine w => Size 100000 (v2pretty w)
     | Trees l => Parenthesis (newlines (vs2pretty l))
     end) /\
  (forall vs, vs2pretty vs =
     match vs with
     | [] => []
     | v :: vs => v2pretty v :: vs2pretty vs
     end).
Proof.
  split; intros []; reflexivity. Qed.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "get_size_def" *)
Fixpoint get_size (p : pretty) : N :=
  match p with
  | Size n x => n
  | Append x _ y => get_size x + get_size y + 1
  | Parenthesis x => get_size x + 2
  | _ => 0
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "get_next_size_def" *)
Fixpoint get_next_size (p : pretty) : N :=
  match p with
  | Size n x => n
  | Append x _ y => get_next_size x
  | Parenthesis x => get_next_size x + 2
  | _ => 0
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "annotate_def" *)
Fixpoint annotate (p : pretty) : pretty :=
  match p with
  | String s => Size (strlen s) (String s)
  | Parenthesis b =>
      let b := annotate b in
      Size (get_size b + 2) (Parenthesis b)
  | Append b1 n b2 =>
      let b1 := annotate b1 in
      let b2 := annotate b2 in
      Append b1 n b2
  | Size n b => Size n (annotate b)
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "remove_all_def" *)
Fixpoint remove_all (p : pretty) : pretty :=
  match p with
  | Parenthesis v => Parenthesis (remove_all v)
  | String v1 => String v1
  | Append v2 _ v3 => Append (remove_all v2) false (remove_all v3)
  | Size v4 v5 => remove_all v5
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "smart_remove_def" *)
Fixpoint smart_remove (i k : N) (p : pretty) : pretty :=
  match p with
  | Size n b => if k + n <? 70 then remove_all b else smart_remove i k b
  | Parenthesis v => Parenthesis (smart_remove (i + 1) (k + 1) v)
  | String v1 => String v1
  | Append v2 b v3 =>
      let n2 := get_size v2 in
      let n3 := get_next_size v3 in
      if k + n2 + n3 <? 50 then
        Append (smart_remove i k v2) false (smart_remove i (k + n2) v3)
      else
        Append (smart_remove i k v2) true (smart_remove i i v3)
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "flatten_def" *)
Fixpoint flatten (indent : mlstring) (p : pretty) (s : list mlstring) : list mlstring :=
  match p with
  | Size n p => flatten indent p s
  | Parenthesis p =>
      strlit "(" :: flatten (concat [indent; strlit "   "]) p (strlit ")" :: s)
  | String t => t :: s
  | Append p1 b p2 =>
      flatten indent p1 ((if b then indent else strlit " ") :: flatten indent p2 s)
  end.

(*! HOL "cakeml/basis/pure/mlsexpScript.sml" "str_tree_to_strs_def" *)
Definition str_tree_to_strs (end_ : mlstring) (v : str_tree) : list mlstring :=
  flatten (strlit ["010"%char]) (smart_remove 0 0 (annotate (v2pretty v))) [end_].

(** HOL's local sanity checks [test1_str_tree_to_strs] and
    [test2_str_tree_to_strs]. *)
Example test1_str_tree_to_strs :
  concat (str_tree_to_strs (strlit "") (Trees [Str (strlit "hello"); Str (strlit "there")])) =
  strlit "(hello there)".
Proof. reflexivity. Qed.

Example test2_str_tree_to_strs :
  concat (str_tree_to_strs (strlit "")
            (Trees [Str (strlit "test"); GrabLine (Str (strlit "hi"));
                    GrabLine (Str (strlit "there"))])) =
  strlit ("(test" ++ ["010"%char] ++ "   hi" ++ ["010"%char] ++ "   there)").
Proof. reflexivity. Qed.
