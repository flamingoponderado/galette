(** * Pancake [pan_structs]: convert named structs to raw structs

    Port of [cakeml/pancake/pan_structsScript.sml].

    [compile_shape]/[compile_shapes] are mutually recursive in HOL and
    terminate lexicographically (length of the struct context, then shape
    size): the [Named] case recurses on the field shapes of the struct
    found by [dropWhile] in a strictly shorter context.  Here they are
    computed by [compile_shape_f], structural on the shape and on a fuel
    bounding the context length ([LENGTH sctxt + 1] is sufficient); HOL's
    equations are the tagged [compile_shape_def] theorem.  The mutual
    [old_exp_shape]/[old_exp_shapes] and
    [compile_exp]/[compile_exps]/[compile_fields] are nested [fix]es, with
    top-level copies of the list functions and HOL's equations proved.

    HOL record updates ([ctxt with locals := ...], [fi with <| params
    updated_by ... |>]) are written as record constructions.

    [dropWhile] and [oEL] (HOL [LLOOKUP l n] is [oEL n l]; [listScript])
    are Galette-local copies until ported in [list.v]. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.pancake Require Import panLang.
Open Scope N_scope.


(** HOL [dropWhile] (from [listScript]; Galette-local until ported there). *)
#[local] Fixpoint dropWhile {A} (P : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => if P h then dropWhile P t else h :: t
  end.

(** HOL [oEL] (from [listScript]; Galette-local until ported there). *)
#[local] Fixpoint oEL {A} (n : N) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if decide (n = 0) then Some x else oEL (n - 1) xs
  end.

Lemma dropWhile_cons_length {A} (P : A -> bool) l x l' :
  dropWhile P l = x :: l' -> (length l' < length l)%nat.
Proof.
  induction l as [|h t IH]; cbn; [discriminate|].
  destruct (P h); [intros H; apply IH in H; lia|intros H; injection H as -> ->; lia].
Qed.

(** HOL [context]. *)
(*! HOL "cakeml/pancake/pan_structsScript.sml" "context" *)
Record context : Type := {
  structs : list (stcname * list (fldname * shape));
  locals : list (varname * shape);
  globals : list (varname * shape)
}.

(*! HOL "cakeml/pancake/pan_structsScript.sml" "afindi_def" *)
Fixpoint afindi {K V} `{EqDecision K} (x : K) (l : list (K * V)) : option N :=
  match l with
  | [] => None
  | (k, v) :: t =>
      if decide (x = k) then Some 0
      else match afindi x t with
           | None => None
           | Some i => Some (1 + i)
           end
  end.

(** ** Shapes *)

Abbreviation sctxt_ty := (list (stcname * list (fldname * shape))).

(** [compile_shape] with a fuel bounding the length of the struct
    context. *)
Fixpoint compile_shape_f (fuel : nat) (sctxt : sctxt_ty) (sh : shape) {struct fuel} : shape :=
  match fuel with
  | O => One
  | S fuel' =>
      (fix cs (sh : shape) : shape :=
         match sh with
         | One => One
         | Comb shapes =>
             Comb ((fix css (l : list shape) : list shape :=
                      match l with [] => [] | sh :: shs => cs sh :: css shs end) shapes)
         | Named nm =>
             match dropWhile (fun '(n, fs) => negb (bool_decide (n = nm))) sctxt with
             | (nm, flds) :: sctxt' => Comb (MAP (compile_shape_f fuel' sctxt') (MAP SND flds))
             | _ => One
             end
         end) sh
  end.

Definition compile_shape (sctxt : sctxt_ty) (sh : shape) : shape :=
  compile_shape_f (S (length sctxt)) sctxt sh.

Fixpoint compile_shapes (sctxt : sctxt_ty) (l : list shape) : list shape :=
  match l with
  | [] => []
  | sh :: shs => compile_shape sctxt sh :: compile_shapes sctxt shs
  end.

Lemma compile_shape_f_fuel : forall f1 f2 sctxt sh,
  (length sctxt < f1)%nat -> (length sctxt < f2)%nat ->
  compile_shape_f f1 sctxt sh = compile_shape_f f2 sctxt sh.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] sctxt sh H1 H2; try lia.
  revert sh; fix IHsh 1; intros [|shapes|nm]; cbn [compile_shape_f]; [reflexivity| |].
  - f_equal; induction shapes as [|sh shs IHl]; [reflexivity|].
    cbn; f_equal; [apply IHsh|apply IHl].
  - destruct (dropWhile _ sctxt) as [|[nm' flds] sctxt'] eqn:E; [reflexivity|].
    apply dropWhile_cons_length in E.
    f_equal; apply map_ext; intros sh; apply IH; lia.
Qed.

Lemma compile_shape_f_eq : forall f sctxt sh,
  (length sctxt < f)%nat -> compile_shape_f f sctxt sh = compile_shape sctxt sh.
Proof. intros; apply compile_shape_f_fuel; [assumption|lia]. Qed.

(*! HOL "cakeml/pancake/pan_structsScript.sml" "compile_shape_def" *)
Theorem compile_shape_def :
  (forall sctxt, compile_shape sctxt One = One) /\
  (forall sctxt shapes, compile_shape sctxt (Comb shapes) = Comb (compile_shapes sctxt shapes)) /\
  (forall sctxt nm, compile_shape sctxt (Named nm) =
     match dropWhile (fun '(n, fs) => negb (bool_decide (n = nm))) sctxt with
     | (nm, flds) :: sctxt' => Comb (compile_shapes sctxt' (MAP SND flds))
     | _ => One
     end) /\
  (forall sctxt, compile_shapes sctxt [] = []) /\
  (forall sctxt sh shs,
     compile_shapes sctxt (sh :: shs) = compile_shape sctxt sh :: compile_shapes sctxt shs).
Proof.
  repeat split; try reflexivity.
  - intros sctxt shapes; unfold compile_shape at 1; cbn [compile_shape_f]; f_equal.
    induction shapes as [|sh shs IH]; [reflexivity|]; cbn; f_equal; exact IH.
  - intros sctxt nm; unfold compile_shape at 1; cbn [compile_shape_f].
    destruct (dropWhile _ sctxt) as [|[nm' flds] sctxt'] eqn:E; [reflexivity|].
    apply dropWhile_cons_length in E.
    f_equal; induction (MAP SND flds) as [|sh shs IH]; [reflexivity|].
    cbn; f_equal; [apply compile_shape_f_eq; lia|exact IH].
Qed.

(** ** Expressions *)

Section Defs.
Context {a : N}.

Fixpoint old_exp_shape (ctxt : context) (e : exp a) : shape :=
  match e with
  | Var Local v =>
      match ALOOKUP (locals ctxt) v with
      | None => One
      | Some sh => sh
      end
  | Var Global v =>
      match ALOOKUP (globals ctxt) v with
      | None => One
      | Some sh => sh
      end
  | RStruct es =>
      Comb ((fix old_exp_shapes (l : list (exp a)) : list shape :=
               match l with
               | [] => []
               | e :: es => old_exp_shape ctxt e :: old_exp_shapes es
               end) es)
  | RField index e =>
      match old_exp_shape ctxt e with
      | Comb shs =>
          match oEL index shs with
          | Some sh => sh
          | None => One
          end
      | _ => One
      end
  | NStruct nm eflds => Named nm
  | NField fld e =>
      match old_exp_shape ctxt e with
      | Named nm =>
          match ALOOKUP (structs ctxt) nm with
          | Some flds =>
              match ALOOKUP flds fld with
              | Some sh => sh
              | None => One
              end
          | None => One
          end
      | _ => One
      end
  | Load sh e => sh
  | _ => One
  end.

Fixpoint old_exp_shapes (ctxt : context) (l : list (exp a)) : list shape :=
  match l with
  | [] => []
  | e :: es => old_exp_shape ctxt e :: old_exp_shapes ctxt es
  end.

Lemma old_exp_shape_RStruct ctxt es :
  old_exp_shape ctxt (RStruct es) = Comb (old_exp_shapes ctxt es).
Proof. cbn; f_equal; induction es as [|e es IH]; cbn; congruence. Qed.

(** HOL [old_exp_shape_def] with [old_exp_shapes] the top-level function. *)
(*! HOL "cakeml/pancake/pan_structsScript.sml" "old_exp_shape_def" *)
Theorem old_exp_shape_def :
  (forall ctxt v, old_exp_shape ctxt (Var Local v) =
     match ALOOKUP (locals ctxt) v with None => One | Some sh => sh end) /\
  (forall ctxt v, old_exp_shape ctxt (Var Global v) =
     match ALOOKUP (globals ctxt) v with None => One | Some sh => sh end) /\
  (forall ctxt es, old_exp_shape ctxt (RStruct es) = Comb (old_exp_shapes ctxt es)) /\
  (forall ctxt index e, old_exp_shape ctxt (RField index e) =
     match old_exp_shape ctxt e with
     | Comb shs => match oEL index shs with Some sh => sh | None => One end
     | _ => One
     end) /\
  (forall ctxt nm eflds, old_exp_shape ctxt (NStruct nm eflds) = Named nm) /\
  (forall ctxt fld e, old_exp_shape ctxt (NField fld e) =
     match old_exp_shape ctxt e with
     | Named nm =>
         match ALOOKUP (structs ctxt) nm with
         | Some flds => match ALOOKUP flds fld with Some sh => sh | None => One end
         | None => One
         end
     | _ => One
     end) /\
  (forall ctxt sh e, old_exp_shape ctxt (Load sh e) = sh) /\
  (forall ctxt w, old_exp_shape ctxt (Const w) = One) /\
  (forall ctxt e, old_exp_shape ctxt (Load32 e) = One) /\
  (forall ctxt e, old_exp_shape ctxt (LoadByte e) = One) /\
  (forall ctxt bop es, old_exp_shape ctxt (Op bop es) = One) /\
  (forall ctxt op es, old_exp_shape ctxt (Panop op es) = One) /\
  (forall ctxt c e1 e2, old_exp_shape ctxt (Cmp c e1 e2) = One) /\
  (forall ctxt sh e1 e2, old_exp_shape ctxt (Shift sh e1 e2) = One) /\
  (forall ctxt, old_exp_shape ctxt BaseAddr = One) /\
  (forall ctxt, old_exp_shape ctxt TopAddr = One) /\
  (forall ctxt, old_exp_shape ctxt BytesInWord = One) /\
  (forall ctxt, old_exp_shapes ctxt [] = []) /\
  (forall ctxt e es, old_exp_shapes ctxt (e :: es) = old_exp_shape ctxt e :: old_exp_shapes ctxt es).
Proof.
  repeat split; try (intros; reflexivity).
  intros; apply old_exp_shape_RStruct.
Qed.

Fixpoint compile_exp (ctxt : context) (e : exp a) : exp a :=
  let compile_exps := fix compile_exps (l : list (exp a)) : list (exp a) :=
    match l with
    | [] => []
    | e :: es => compile_exp ctxt e :: compile_exps es
    end in
  match e with
  | RStruct es => RStruct (compile_exps es)
  | RField index e => RField index (compile_exp ctxt e)
  | NStruct nm eflds =>
      let eflds' := (fix compile_fields (l : list (fldname * exp a)) : list (fldname * exp a) :=
                       match l with
                       | [] => []
                       | (fld, exp) :: eflds => (fld, compile_exp ctxt exp) :: compile_fields eflds
                       end) eflds in
      let es' := match ALOOKUP (structs ctxt) nm with
                 | Some flds =>
                     FLAT (MAP (fun '(nm', sh) =>
                                  match ALOOKUP eflds' nm' with
                                  | None => []
                                  | Some e => [e]
                                  end) flds)
                 | None => []
                 end in
      RStruct es'
  | NField fld e =>
      let e' := compile_exp ctxt e in
      let index :=
        match old_exp_shape ctxt e with
        | Named nm =>
            match ALOOKUP (structs ctxt) nm with
            | Some flds =>
                match afindi fld flds with
                | Some i => i
                | None => 0
                end
            | None => 0
            end
        | _ => 0
        end in
      RField index e'
  | Load sh e => Load (compile_shape (structs ctxt) sh) (compile_exp ctxt e)
  | LoadByte e => LoadByte (compile_exp ctxt e)
  | Load32 e => Load32 (compile_exp ctxt e)
  | Op bop es => Op bop (compile_exps es)
  | Panop pop es => Panop pop (compile_exps es)
  | Cmp cmp e1 e2 => Cmp cmp (compile_exp ctxt e1) (compile_exp ctxt e2)
  | Shift sh e e' => Shift sh (compile_exp ctxt e) (compile_exp ctxt e')
  | e => e
  end.

Fixpoint compile_exps (ctxt : context) (l : list (exp a)) : list (exp a) :=
  match l with
  | [] => []
  | e :: es => compile_exp ctxt e :: compile_exps ctxt es
  end.

Fixpoint compile_fields (ctxt : context) (l : list (fldname * exp a)) : list (fldname * exp a) :=
  match l with
  | [] => []
  | (fld, exp) :: eflds => (fld, compile_exp ctxt exp) :: compile_fields ctxt eflds
  end.

Lemma compile_exps_nested ctxt l :
  (fix compile_exps (l : list (exp a)) : list (exp a) :=
     match l with
     | [] => []
     | e :: es => compile_exp ctxt e :: compile_exps es
     end) l = compile_exps ctxt l.
Proof. induction l as [|e es IH]; cbn; congruence. Qed.

Lemma compile_fields_nested ctxt l :
  (fix compile_fields (l : list (fldname * exp a)) : list (fldname * exp a) :=
     match l with
     | [] => []
     | (fld, exp) :: eflds => (fld, compile_exp ctxt exp) :: compile_fields eflds
     end) l = compile_fields ctxt l.
Proof. induction l as [|[f e] es IH]; cbn; congruence. Qed.

(** HOL [compile_exp_def] with [compile_exps]/[compile_fields] the
    top-level functions. *)
(*! HOL "cakeml/pancake/pan_structsScript.sml" "compile_exp_def" *)
Theorem compile_exp_def :
  (forall ctxt es, compile_exp ctxt (RStruct es) = RStruct (compile_exps ctxt es)) /\
  (forall ctxt index e, compile_exp ctxt (RField index e) = RField index (compile_exp ctxt e)) /\
  (forall ctxt nm eflds, compile_exp ctxt (NStruct nm eflds) =
     let eflds' := compile_fields ctxt eflds in
     let es' := match ALOOKUP (structs ctxt) nm with
                | Some flds =>
                    FLAT (MAP (fun '(nm', sh) =>
                                 match ALOOKUP eflds' nm' with
                                 | None => []
                                 | Some e => [e]
                                 end) flds)
                | None => []
                end in
     RStruct es') /\
  (forall ctxt fld e, compile_exp ctxt (NField fld e) =
     let e' := compile_exp ctxt e in
     let index :=
       match old_exp_shape ctxt e with
       | Named nm =>
           match ALOOKUP (structs ctxt) nm with
           | Some flds => match afindi fld flds with Some i => i | None => 0 end
           | None => 0
           end
       | _ => 0
       end in
     RField index e') /\
  (forall ctxt sh e, compile_exp ctxt (Load sh e) =
     Load (compile_shape (structs ctxt) sh) (compile_exp ctxt e)) /\
  (forall ctxt e, compile_exp ctxt (LoadByte e) = LoadByte (compile_exp ctxt e)) /\
  (forall ctxt e, compile_exp ctxt (Load32 e) = Load32 (compile_exp ctxt e)) /\
  (forall ctxt bop es, compile_exp ctxt (Op bop es) = Op bop (compile_exps ctxt es)) /\
  (forall ctxt pop es, compile_exp ctxt (Panop pop es) = Panop pop (compile_exps ctxt es)) /\
  (forall ctxt cmp e1 e2, compile_exp ctxt (Cmp cmp e1 e2) =
     Cmp cmp (compile_exp ctxt e1) (compile_exp ctxt e2)) /\
  (forall ctxt sh e e', compile_exp ctxt (Shift sh e e') =
     Shift sh (compile_exp ctxt e) (compile_exp ctxt e')) /\
  (forall ctxt w, compile_exp ctxt (Const w) = Const w) /\
  (forall ctxt vk v, compile_exp ctxt (Var vk v) = Var vk v) /\
  (forall ctxt, compile_exp ctxt BaseAddr = BaseAddr) /\
  (forall ctxt, compile_exp ctxt TopAddr = TopAddr) /\
  (forall ctxt, compile_exp ctxt BytesInWord = BytesInWord) /\
  (forall ctxt, compile_exps ctxt [] = []) /\
  (forall ctxt e es, compile_exps ctxt (e :: es) = compile_exp ctxt e :: compile_exps ctxt es) /\
  (forall ctxt, compile_fields ctxt [] = []) /\
  (forall ctxt fld exp eflds, compile_fields ctxt ((fld, exp) :: eflds) =
     (fld, compile_exp ctxt exp) :: compile_fields ctxt eflds).
Proof.
  repeat split; try (intros; reflexivity);
    intros; cbn [compile_exp]; rewrite ?compile_exps_nested, ?compile_fields_nested;
    reflexivity.
Qed.

(** ** Programs *)

(*! HOL "cakeml/pancake/pan_structsScript.sml" "compile_def" *)
Fixpoint compile (ctxt : context) (p : prog a) : prog a :=
  match p with
  | Dec v s e p =>
      Dec v (compile_shape (structs ctxt) s) (compile_exp ctxt e)
        (compile {| structs := structs ctxt; locals := (v, s) :: locals ctxt;
                    globals := globals ctxt |} p)
  | Assign vk v e => Assign vk v (compile_exp ctxt e)
  | Primitive v pop es => Primitive v pop (compile_exps ctxt es)
  | Store ad v => Store (compile_exp ctxt ad) (compile_exp ctxt v)
  | Store32 ad v => Store32 (compile_exp ctxt ad) (compile_exp ctxt v)
  | StoreByte dest src => StoreByte (compile_exp ctxt dest) (compile_exp ctxt src)
  | Seq p p' => Seq (compile ctxt p) (compile ctxt p')
  | If e p p' => If (compile_exp ctxt e) (compile ctxt p) (compile ctxt p')
  | While e p => While (compile_exp ctxt e) (compile ctxt p)
  | Call rtyp f es =>
      let cexps := compile_exps ctxt es in
      match rtyp with
      | None => Call None f cexps
      | Some (tl, hdl) =>
          Call (Some (tl, match hdl with
                          | None => None
                          | Some (eid, (evar, p)) => Some (eid, (evar, compile ctxt p))
                          end))
            f cexps
      end
  | DecCall v s f es p =>
      DecCall v (compile_shape (structs ctxt) s) f (compile_exps ctxt es)
        (compile {| structs := structs ctxt; locals := (v, s) :: locals ctxt;
                    globals := globals ctxt |} p)
  | ExtCall f ptr1 len1 ptr2 len2 =>
      ExtCall f (compile_exp ctxt ptr1) (compile_exp ctxt len1)
        (compile_exp ctxt ptr2) (compile_exp ctxt len2)
  | Return rt => Return (compile_exp ctxt rt)
  | Raise eid excp => Raise eid (compile_exp ctxt excp)
  | ShMemStore op r ad => ShMemStore op (compile_exp ctxt r) (compile_exp ctxt ad)
  | ShMemLoad op vk r ad => ShMemLoad op vk r (compile_exp ctxt ad)
  | p => p
  end.

(*! HOL "cakeml/pancake/pan_structsScript.sml" "compile_decs_def" *)
Fixpoint compile_decs (ctxt : context) (l : list (decl a)) : list (decl a) * context :=
  match l with
  | [] => ([], ctxt)
  | Decl sh v e :: ds =>
      let (ds', ctxt') := compile_decs {| structs := structs ctxt; locals := locals ctxt;
                                          globals := (v, sh) :: globals ctxt |} ds in
      (Decl (compile_shape (structs ctxt) sh) v (compile_exp ctxt e) :: ds', ctxt')
  | Function fi :: ds =>
      let (ds', ctxt') := compile_decs ctxt ds in
      let params := params fi in
      let fi' := {| name := name fi; inline := inline fi; export := export fi;
                    panLang.params :=
                      MAP (fun '(p, s) => (p, compile_shape (structs ctxt) s)) (panLang.params fi);
                    body := compile {| structs := structs ctxt'; locals := params;
                                       globals := globals ctxt' |} (body fi);
                    fun_decl_return := compile_shape (structs ctxt) (fun_decl_return fi) |} in
      (Function fi' :: ds', ctxt')
  | Name nm flds :: ds => compile_decs ctxt ds
  | ExnDecl nm sh :: ds =>
      let (ds', ctxt') := compile_decs ctxt ds in
      (ExnDecl nm (compile_shape (structs ctxt) sh) :: ds', ctxt')
  end.

(*! HOL "cakeml/pancake/pan_structsScript.sml" "get_names_def" *)
Fixpoint get_names (ctxt : context) (l : list (decl a)) : context :=
  match l with
  | [] => ctxt
  | Name nm flds :: ds =>
      get_names {| structs := (nm, flds) :: structs ctxt; locals := locals ctxt;
                   globals := globals ctxt |} ds
  | _ :: ds => get_names ctxt ds
  end.

(*! HOL "cakeml/pancake/pan_structsScript.sml" "compile_top_def" *)
Definition compile_top (decs : list (decl a)) : list (decl a) :=
  let ctxt := {| structs := []; locals := []; globals := [] |} in
  FST (compile_decs (get_names ctxt decs) decs).

End Defs.
