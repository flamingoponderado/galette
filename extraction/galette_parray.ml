(* Persistent arrays (Baker's rerooting; Conchon & Filliatre, "A persistent
   union-find data structure", 2007).

   Galette realises HOL's monadic arrays (lists in the logic, see
   ml_monadBase.v [marray]) with this module.  Every operation has the
   purely functional meaning of the corresponding list operation: [set]
   returns a new array and leaves the old one unchanged, so the realisation
   is correct whether or not the program uses arrays linearly; when it does
   (as the CakeML allocator's state monad does), [get] and [set] are O(1).
   This file is part of the trusted base of the executable. *)

type 'a t = 'a data ref
and 'a data =
  | Arr of 'a array
  | Diff of int * 'a * 'a t

let make n x = ref (Arr (Array.make n x))

let init n f = ref (Arr (Array.init n f))

(* Make [t] the version that owns the underlying array. *)
let rec reroot t =
  match !t with
  | Arr _ -> ()
  | Diff (i, v, t') ->
      reroot t';
      (match !t' with
       | Arr a as n ->
           let v' = a.(i) in
           a.(i) <- v;
           t := n;
           t' := Diff (i, v', t)
       | Diff _ -> assert false)

let rec get t i =
  match !t with
  | Arr a -> a.(i)
  | Diff _ ->
      reroot t;
      (match !t with Arr a -> a.(i) | Diff _ -> assert false)

let set t i v =
  reroot t;
  match !t with
  | Arr a as n ->
      let old = a.(i) in
      if old == v then t
      else begin
        a.(i) <- v;
        let res = ref n in
        t := Diff (i, old, res);
        res
      end
  | Diff _ -> assert false

let length t =
  reroot t;
  match !t with Arr a -> Array.length a | Diff _ -> assert false
