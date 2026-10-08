(** * CakeML [namespace]: nested namespaces

    Partial port of [cakeml/semantics/namespaceScript.sml]: the [alist]
    abbreviation, the datatypes [id] and [namespace], and [nsEmpty].  The
    lookup/update/append operations and their theorems are not ported.

    HOL orders type variables alphabetically: [('m,'n) id] and
    [('m,'n,'v) namespace]; the Rocq parameters follow that order. *)

From Galette Require Import Base.
Local Set Warnings "-register-all".

(*! HOL "cakeml/semantics/namespaceScript.sml" "alist" *)
Abbreviation alist k v := (list (k * v)).

(** Identifiers. *)
(*! HOL "cakeml/semantics/namespaceScript.sml" "id" *)
Inductive id (m n : Type) : Type :=
| Short : n -> id m n
| Long : m -> id m n -> id m n.
Arguments Short {m n} _.
Arguments Long {m n} _ _.

#[global] Instance id_inhabited {m n} `{Inhabited n} : Inhabited (id m n) :=
  Short (inhabitant n).

(*! HOL "cakeml/semantics/namespaceScript.sml" "namespace" *)
Inductive namespace (m n v : Type) : Type :=
| Bind : alist n v -> alist m (namespace m n v) -> namespace m n v.
Arguments Bind {m n v} _ _.

(*! HOL "cakeml/semantics/namespaceScript.sml" "nsEmpty_def" *)
Definition nsEmpty {m n v : Type} : namespace m n v := Bind [] [].

#[global] Instance namespace_inhabited {m n v} : Inhabited (namespace m n v) :=
  nsEmpty.
