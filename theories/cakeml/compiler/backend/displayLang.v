(** * CakeML [displayLang]: a simple language for displaying programs

    Port of [cakeml/compiler/backend/displayLangScript.sml]: the [sExp]
    datatype and its conversion [display_to_str_tree] to [mlsexp]'s
    [str_tree].

    The constructors [String] and [List] of [sExp] are HOL's; they shadow
    Rocq's [String.String] and [misc]'s [app_list] constructor [List] in
    modules importing this one ([misc.List] then names the latter).
    [mlsexp] is required, not imported (its [pretty] constructors [String]
    and [Append] would clash too).

    Not ported: [trace_to_json], [display_to_json] (JSON output, not used by
    the [--explore] text output; [jsonLang] is ported only as far as
    [num_to_hex_digit]) and [MEM_sExp_size] (about HOL's generated size
    function, for termination only). *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.basis.pure Require mlsexp.
From Galette.cakeml.compiler.backend Require Import backend_common.
Open Scope N_scope.
Open Scope hol_string_scope.
Local Set Warnings "-register-all".

(*! HOL "cakeml/compiler/backend/displayLangScript.sml" "sExp" *)
Inductive sExp : Type :=
| Item : option tra -> mlstring -> list sExp -> sExp
| String : mlstring -> sExp
| Tuple : list sExp -> sExp
| List : list sExp -> sExp.

#[global] Instance sExp_inhabited : Inhabited sExp := String (strlit "").

(** HOL's [display_to_str_tree] and [display_to_str_tree_list] are mutually
    recursive on [sExp] and [sExp list]; here the list function is a nested
    [fix] (and a separate [Fixpoint]), and HOL's equations are the tagged
    [display_to_str_tree_def]. *)
Fixpoint display_to_str_tree (e : sExp) : mlsexp.str_tree :=
  let display_to_str_tree_list :=
    fix display_to_str_tree_list (l : list sExp) : list mlsexp.str_tree :=
      match l with
      | [] => []
      | x :: xs => display_to_str_tree x :: display_to_str_tree_list xs
      end in
  match e with
  | Item tra name es =>
      mlsexp.Trees (mlsexp.Str name :: display_to_str_tree_list es)
  | String s => mlsexp.Str s
  | Tuple es =>
      if NULL es then mlsexp.Str (strlit "()")
      else mlsexp.Trees (display_to_str_tree_list es)
  | List es =>
      if NULL es then mlsexp.Str (strlit "()")
      else mlsexp.Trees (MAP mlsexp.GrabLine (display_to_str_tree_list es))
  end.

Fixpoint display_to_str_tree_list (l : list sExp) : list mlsexp.str_tree :=
  match l with
  | [] => []
  | x :: xs => display_to_str_tree x :: display_to_str_tree_list xs
  end.

(*! HOL "cakeml/compiler/backend/displayLangScript.sml" "display_to_str_tree_def" *)
Theorem display_to_str_tree_def :
  (forall tra name es, display_to_str_tree (Item tra name es) =
     mlsexp.Trees (mlsexp.Str name :: display_to_str_tree_list es)) /\
  (forall s, display_to_str_tree (String s) = mlsexp.Str s) /\
  (forall es, display_to_str_tree (Tuple es) =
     if NULL es then mlsexp.Str (strlit "()")
     else mlsexp.Trees (display_to_str_tree_list es)) /\
  (forall es, display_to_str_tree (List es) =
     if NULL es then mlsexp.Str (strlit "()")
     else mlsexp.Trees (MAP mlsexp.GrabLine (display_to_str_tree_list es))) /\
  (display_to_str_tree_list [] = []) /\
  (forall x xs, display_to_str_tree_list (x :: xs) =
     display_to_str_tree x :: display_to_str_tree_list xs).
Proof. repeat split. Qed.
