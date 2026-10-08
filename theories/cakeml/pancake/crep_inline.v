(** * Pancake [crep_inline]: function inlining in crepLang

    Port of [cakeml/pancake/crep_inlineScript.sml].

    [inline_prog] terminates in HOL lexicographically on
    [(CARD (FDOM inlineable_fs), prog_size p)]: inlining a callee removes
    it from the map.  Here it is a well-founded [Fix] on
    [FCARD inlineable_fs] whose body is structural on the program (the
    proofs, and [FCARD], are erased on extraction; the well-foundedness
    proof is wrapped in [Acc_intro_generator] so that [inline_prog] also
    reduces in the kernel).  HOL's equations are the tagged
    [inline_prog_def] theorem.

    The [finite_map] notations clash with the [words] notation [w ' i];
    [finite_map] is imported without its notations. *)

From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.finite_maps Require Import alist.
From Galette.HOL.src.finite_maps Require finite_map.
Import -(notations) finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.pancake Require Import crepLang.
Open Scope N_scope.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "var_prog_def" *)
Fixpoint var_prog (p : prog a) : list varname :=
  match p with
  | Dec v e p => [v] ++ var_cexp e ++ var_prog p
  | Assign v e => [v] ++ var_cexp e
  | Store e1 e2 => var_cexp e1 ++ var_cexp e2
  | Store32 e1 e2 => var_cexp e1 ++ var_cexp e2
  | StoreByte e1 e2 => var_cexp e1 ++ var_cexp e2
  | StoreGlob w e => var_cexp e
  | Seq p1 p2 => var_prog p1 ++ var_prog p2
  | If e p1 p2 => var_cexp e ++ var_prog p1 ++ var_prog p2
  | While e p => var_cexp e ++ var_prog p
  | Call ctyp e es =>
      let var_ctyp :=
        match ctyp with
        | None => []
        | Some (vs, None) => vs
        | Some (vs, Some (w, hdl)) => vs ++ var_prog hdl
        end in
      FLAT (MAP var_cexp es) ++ var_ctyp
  | ExtCall f v1 v2 v3 v4 => [v1; v2; v3; v4]
  | Return es => FLAT (MAP var_cexp es)
  | ShMem mop v e => [v] ++ var_cexp e
  | Primitive lhss pop rhss => lhss ++ rhss
  | _ => []
  end.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "vmax_prog_def" *)
Definition vmax_prog (p : prog a) : N := MAX_LIST (var_prog p).

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "has_return_def" *)
Fixpoint has_return (p : prog a) : bool :=
  match p with
  | Dec v e p => has_return p
  | Seq p1 p2 => has_return p1 || has_return p2
  | If e p1 p2 => has_return p1 || has_return p2
  | While e p => has_return p
  | Call ctyp e args =>
      match ctyp with
      | None => true
      | Some (_, None) => false
      | Some (_, Some (w, hdl)) => has_return hdl
      end
  | Return e => true
  | _ => false
  end.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "arg_load_def" *)
Definition arg_load (tmp_vars : list varname) (args : list (exp a)) (args_vname : list varname)
    (p : prog a) : prog a :=
  nested_decs tmp_vars args (nested_decs args_vname (MAP Var tmp_vars) p).

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "not_branch_ret_def" *)
Fixpoint not_branch_ret (p : prog a) : bool :=
  match p with
  | Dec v e p => not_branch_ret p
  | Seq p1 p2 => not_branch_ret p1 && not_branch_ret p2
  | If e p1 p2 => negb (has_return p1) && negb (has_return p2)
  | While e p => negb (has_return p)
  | Call ctyp e args =>
      match ctyp with
      | None => true
      | Some (_, None) => true
      | Some (_, Some (w, hdl)) => negb (has_return hdl)
      end
  | _ => true
  end.

End Defs.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "early_exit" *)
Inductive early_exit : Type := Exn | Ret | Loop_exit.

#[global] Instance early_exit_eq_dec : EqDecision early_exit.
Proof. intros x y; unfold Decision; decide equality. Defined.

Section Defs2.
Context {a : N}.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "unreach_elim_def" *)
Fixpoint unreach_elim (p : prog a) : prog a * option early_exit :=
  match p with
  | Return e => (Return e, Some Ret)
  | Raise eid => (Raise eid, Some Exn)
  | Break n => (Break n, Some Loop_exit)
  | Continue n => (Continue n, Some Loop_exit)
  | Seq p1 p2 =>
      let (p1', r1) := unreach_elim p1 in
      if decide (r1 <> None) then (p1', r1) else
        let (p2', r2) := unreach_elim p2 in (Seq p1' p2', r2)
  | Dec v e p =>
      let (p', r) := unreach_elim p in (Dec v e p', r)
  | If e p1 p2 =>
      let (p1', r1) := unreach_elim p1 in
      let (p2', r2) := unreach_elim p2 in
      let r3 := match r1, r2 with
                | Some Ret, e => e
                | e, Some Ret => e
                | Some Exn, e => e
                | e, Some Exn => e
                | Some Loop_exit, e => e
                | e, Some Loop_exit => e
                | None, None => None
                end in
      (If e p1' p2', r3)
  | While e p =>
      let (p', r) := unreach_elim p in (While e p', None)
  | Call ctyp e args =>
      match ctyp with
      | None => (Call None e args, Some Ret)
      | Some (rt, None) => (Call (Some (rt, None)) e args, None)
      | Some (rt, Some (w, hdl)) =>
          let (hdl', rhdl) := unreach_elim hdl in
          (Call (Some (rt, Some (w, hdl'))) e args, None)
      end
  | p => (p, None)
  end.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "transform_eoc_def" *)
Fixpoint transform_eoc (rets : list varname) (p : prog a) : prog a :=
  match p with
  | Return es => nested_seq (MAP2 Assign rets es)
  | Call ctyp e args =>
      match ctyp with
      | None => Call (Some (rets, None)) e args
      | Some (rs, None) => Call (Some (rs, None)) e args
      | Some (rs, Some (w, hdl)) => Call (Some (rs, Some (w, transform_eoc rets hdl))) e args
      end
  | Dec v e p => Dec v e (transform_eoc rets p)
  | While e p => While e (transform_eoc rets p)
  | Seq p1 p2 => Seq (transform_eoc rets p1) (transform_eoc rets p2)
  | If e p1 p2 => If e (transform_eoc rets p1) (transform_eoc rets p2)
  | p => p
  end.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "transform_branch_def" *)
Fixpoint transform_branch (ld : N) (rets : list varname) (p : prog a) : prog a :=
  match p with
  | Return es => Seq (nested_seq (MAP2 Assign rets es)) (Break ld)
  | Call ctyp e args =>
      match ctyp with
      | None => Seq (Call (Some (rets, None)) e args) (Break ld)
      | Some (rs, None) => Call (Some (rs, None)) e args
      | Some (rs, Some (w, hdl)) =>
          Call (Some (rs, Some (w, transform_branch ld rets hdl))) e args
      end
  | Dec v e p => Dec v e (transform_branch ld rets p)
  | While e p => While e (transform_branch (ld + 1) rets p)
  | Seq p1 p2 => Seq (transform_branch ld rets p1) (transform_branch ld rets p2)
  | If e p1 p2 => If e (transform_branch ld rets p1) (transform_branch ld rets p2)
  | p => p
  end.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "inline_tail_def" *)
Definition inline_tail (p : prog a) : prog a := Seq Tick p.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "inline_nontail_def" *)
Definition inline_nontail (p : prog a) (rts temp_rets tmp_vars : list varname)
    (args : list (exp a)) (args_vname : list varname) : prog a :=
  nested_decs temp_rets (REPLICATE (LENGTH temp_rets) (Const (n2w 0)))
    (Seq (arg_load tmp_vars args args_vname p)
         (nested_seq (MAP2 Assign rts (MAP Var temp_rets)))).

(** ** Inlining *)

Abbreviation inl_map := (fmap funname (list varname * prog a)).

Lemma FCARD_fdomsub_lt (fs : inl_map) e v :
  FLOOKUP fs e = Some v -> (N.to_nat (FCARD (fdomsub fs e)) < N.to_nat (FCARD fs))%nat.
Proof.
  intros H; unfold FCARD; rewrite FDOM_DOMSUB, CARD_DELETE by apply FDOM_FINITE.
  destruct (classical_dec _) as [Hin|Hin].
  - assert (CARD (FDOM fs) <> 0).
    { rewrite (CARD_EQ_0 _ (FDOM_FINITE fs)); intros E; rewrite E in Hin; exact Hin. }
    lia.
  - exfalso; apply Hin; hnf; unfold FDOM; rewrite H; discriminate.
Qed.

(** The body of [inline_prog] for a fixed map [fs], given [inline_prog] on
    the maps with fewer entries. *)
Definition inline_prog_F (fs : inl_map)
    (rec : forall fs' : inl_map, (N.to_nat (FCARD fs') < N.to_nat (FCARD fs))%nat -> prog a -> prog a)
    : prog a -> prog a :=
  fix go (p : prog a) : prog a :=
  match p with
  | Call ctyp e args =>
      let ctyp_inl :=
        match ctyp with
        | None => None
        | Some (x, None) => Some (x, None)
        | Some (x, Some (w, hdl)) => Some (x, Some (w, go hdl))
        end in
      if match ctyp_inl with None => false | Some (rts, _) => negb (ALL_DISTINCT rts) end
      then Call ctyp_inl e args
      else
        match FLOOKUP fs e as o return FLOOKUP fs e = o -> prog a with
        | None => fun _ => Call ctyp_inl e args
        | Some (args_vname, p) => fun H =>
            let n_inlineable_fs := fdomsub fs e in
            let inlined_callee_unnormalised :=
              rec n_inlineable_fs (FCARD_fdomsub_lt fs e _ H) p in
            let (inlined_callee, exit_type) := unreach_elim inlined_callee_unnormalised in
            let max_args := MAX_LIST (FLAT (MAP var_cexp args)) in
            let max_args_vname := MAX_LIST args_vname in
            let tmp_vars := GENLIST (fun x => SUC x + MAX max_args max_args_vname)
                              (LENGTH args_vname) in
            match ctyp_inl with
            | None => inline_tail (arg_load tmp_vars args args_vname inlined_callee)
            | Some (rts, hdl) =>
                match hdl with
                | None =>
                    let ret_max := MAX_LIST [MAX_LIST rts; vmax_prog inlined_callee;
                                             MAX_LIST tmp_vars] in
                    let temp_rets := GENLIST (fun x => SUC x + ret_max) (LENGTH rts) in
                    let n_br := not_branch_ret inlined_callee in
                    let transformed_callee :=
                      if n_br then Seq Tick (transform_eoc temp_rets inlined_callee)
                      else While (Const (n2w 1)) (transform_branch 0 temp_rets inlined_callee) in
                    inline_nontail transformed_callee rts temp_rets tmp_vars args args_vname
                | Some w_hdl => Call ctyp_inl e args
                end
            end
        end eq_refl
  | Dec v e p => Dec v e (go p)
  | Seq p1 p2 =>
      let inline_p1 := go p1 in
      let inline_p2 := go p2 in
      Seq inline_p1 inline_p2
  | If e p1 p2 =>
      let inline_p1 := go p1 in
      let inline_p2 := go p2 in
      If e inline_p1 inline_p2
  | While e p => While e (go p)
  | p => p
  end.

(** The well-foundedness proof is wrapped in [Acc_intro_generator] so that
    [inline_prog] also reduces in the kernel ([vm_compute]); it is erased on
    extraction. *)
Definition inline_prog_wf : well_founded (ltof inl_map (fun fs => N.to_nat (FCARD fs))) :=
  Acc_intro_generator 32 (well_founded_ltof _ (fun fs : inl_map => N.to_nat (FCARD fs))).

Definition inline_prog : inl_map -> prog a -> prog a :=
  Fix inline_prog_wf (fun _ => prog a -> prog a) inline_prog_F.

Lemma inline_prog_eq fs : inline_prog fs = inline_prog_F fs (fun fs' _ => inline_prog fs').
Proof.
  unfold inline_prog.
  refine (Fix_eq inline_prog_wf (fun _ => prog a -> prog a) inline_prog_F _ fs).
  intros x f g Hfg; f_equal.
  apply functional_extensionality_dep; intros y; apply functional_extensionality_dep; intros H.
  apply Hfg.
Qed.

Lemma inline_prog_unfold fs p :
  inline_prog fs p = inline_prog_F fs (fun fs' _ => inline_prog fs') p.
Proof. exact (f_equal (fun g => g p) (inline_prog_eq fs)). Qed.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "inline_prog_def" *)
Theorem inline_prog_def :
  (forall inlineable_fs ctyp e args, inline_prog inlineable_fs (Call ctyp e args) =
     let ctyp_inl :=
       match ctyp with
       | None => None
       | Some (x, None) => Some (x, None)
       | Some (x, Some (w, hdl)) => Some (x, Some (w, inline_prog inlineable_fs hdl))
       end in
     if match ctyp_inl with None => false | Some (rts, _) => negb (ALL_DISTINCT rts) end
     then Call ctyp_inl e args
     else
       match FLOOKUP inlineable_fs e with
       | None => Call ctyp_inl e args
       | Some (args_vname, p) =>
           let n_inlineable_fs := fdomsub inlineable_fs e in
           let inlined_callee_unnormalised := inline_prog n_inlineable_fs p in
           let (inlined_callee, exit_type) := unreach_elim inlined_callee_unnormalised in
           let max_args := MAX_LIST (FLAT (MAP var_cexp args)) in
           let max_args_vname := MAX_LIST args_vname in
           let tmp_vars := GENLIST (fun x => SUC x + MAX max_args max_args_vname)
                             (LENGTH args_vname) in
           match ctyp_inl with
           | None => inline_tail (arg_load tmp_vars args args_vname inlined_callee)
           | Some (rts, hdl) =>
               match hdl with
               | None =>
                   let ret_max := MAX_LIST [MAX_LIST rts; vmax_prog inlined_callee;
                                            MAX_LIST tmp_vars] in
                   let temp_rets := GENLIST (fun x => SUC x + ret_max) (LENGTH rts) in
                   let n_br := not_branch_ret inlined_callee in
                   let transformed_callee :=
                     if n_br then Seq Tick (transform_eoc temp_rets inlined_callee)
                     else While (Const (n2w 1)) (transform_branch 0 temp_rets inlined_callee) in
                   inline_nontail transformed_callee rts temp_rets tmp_vars args args_vname
               | Some w_hdl => Call ctyp_inl e args
               end
           end
       end) /\
  (forall inlineable_fs v e p,
     inline_prog inlineable_fs (Dec v e p) = Dec v e (inline_prog inlineable_fs p)) /\
  (forall inlineable_fs p1 p2, inline_prog inlineable_fs (Seq p1 p2) =
     let inline_p1 := inline_prog inlineable_fs p1 in
     let inline_p2 := inline_prog inlineable_fs p2 in
     Seq inline_p1 inline_p2) /\
  (forall inlineable_fs e p1 p2, inline_prog inlineable_fs (If e p1 p2) =
     let inline_p1 := inline_prog inlineable_fs p1 in
     let inline_p2 := inline_prog inlineable_fs p2 in
     If e inline_p1 inline_p2) /\
  (forall inlineable_fs e p,
     inline_prog inlineable_fs (While e p) = While e (inline_prog inlineable_fs p)) /\
  (forall inlineable_fs, inline_prog inlineable_fs Skip = Skip) /\
  (forall inlineable_fs v e, inline_prog inlineable_fs (Assign v e) = Assign v e) /\
  (forall inlineable_fs lhss pop rhss,
     inline_prog inlineable_fs (Primitive lhss pop rhss) = Primitive lhss pop rhss) /\
  (forall inlineable_fs e1 e2, inline_prog inlineable_fs (Store e1 e2) = Store e1 e2) /\
  (forall inlineable_fs e1 e2, inline_prog inlineable_fs (Store32 e1 e2) = Store32 e1 e2) /\
  (forall inlineable_fs e1 e2, inline_prog inlineable_fs (StoreByte e1 e2) = StoreByte e1 e2) /\
  (forall inlineable_fs w e, inline_prog inlineable_fs (StoreGlob w e) = StoreGlob w e) /\
  (forall inlineable_fs n, inline_prog inlineable_fs (Break n) = Break n) /\
  (forall inlineable_fs n, inline_prog inlineable_fs (Continue n) = Continue n) /\
  (forall inlineable_fs f v1 v2 v3 v4,
     inline_prog inlineable_fs (ExtCall f v1 v2 v3 v4) = ExtCall f v1 v2 v3 v4) /\
  (forall inlineable_fs w, inline_prog inlineable_fs (Raise w) = Raise w) /\
  (forall inlineable_fs es, inline_prog inlineable_fs (Return es) = Return es) /\
  (forall inlineable_fs op v e, inline_prog inlineable_fs (ShMem op v e) = ShMem op v e) /\
  (forall inlineable_fs, inline_prog inlineable_fs Tick = Tick).
Proof.
  repeat match goal with |- _ /\ _ => split end.
  6-19: intros; apply inline_prog_unfold.
  - intros fs ctyp e args; rewrite (inline_prog_unfold fs (Call ctyp e args)).
    destruct ctyp as [[x [[w hdl]|]]|]; [rewrite (inline_prog_unfold fs hdl)| |];
      cbn [inline_prog_F];
      destruct (FLOOKUP fs e) as [[args_vname p]|]; reflexivity.
  - intros fs v e p; rewrite (inline_prog_unfold fs (Dec v e p)), (inline_prog_unfold fs p).
    try reflexivity.
  - intros fs p1 p2; rewrite (inline_prog_unfold fs (Seq p1 p2)), (inline_prog_unfold fs p1),
      (inline_prog_unfold fs p2); try reflexivity.
  - intros fs e p1 p2; rewrite (inline_prog_unfold fs (If e p1 p2)), (inline_prog_unfold fs p1),
      (inline_prog_unfold fs p2); try reflexivity.
  - intros fs e p; rewrite (inline_prog_unfold fs (While e p)), (inline_prog_unfold fs p).
    try reflexivity.
Qed.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "compile_inl_prog_def" *)
Definition compile_inl_prog (inl_fs : inl_map) (prog : list (funname * (list varname * crepLang.prog a)))
    : list (funname * (list varname * crepLang.prog a)) :=
  MAP (fun '(name, (params, body)) => (name, (params, inline_prog (fdomsub inl_fs name) body))) prog.

(*! HOL "cakeml/pancake/crep_inlineScript.sml" "compile_inl_top_def" *)
Definition compile_inl_top (inl_fname : list funname)
    (prog : list (funname * (list varname * crepLang.prog a)))
    : list (funname * (list varname * crepLang.prog a)) :=
  let inl_fs_alist := FILTER (fun '(x, y) => MEM x inl_fname) prog in
  let inl_fs := alist_to_fmap inl_fs_alist in
  compile_inl_prog inl_fs prog.

End Defs2.
