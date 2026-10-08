(** * Pancake [pan_simp]: simplification of panLang

    Port of [cakeml/pancake/pan_simpScript.sml].

    HOL's test [p = Skip] in [SmartSeq] is decided by the local instance
    [prog_Skip_dec] (a match on [p]; it needs no equality on programs).
    HOL's [fi with body := compile fi.body] is the record rebuilt.

    The [_pmatch] theorems restate the definitions with HOL's [pmatch]
    syntax (first-match case expressions); here they are [match]es. *)

From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.pancake Require Import panLang.
Open Scope N_scope.

(** A decision procedure for [p = Skip] (HOL's [if p = Skip]). *)
#[local] Instance prog_Skip_dec {a : N} (p : prog a) : Decision (p = Skip).
Proof. destruct p; (left; reflexivity) || (right; discriminate). Defined.

Section Defs.
Context {a : N}.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "SmartSeq_def" *)
Definition SmartSeq (p q : prog a) : prog a :=
  if decide (p = Skip) then q else Seq p q.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "seq_assoc_def" *)
Fixpoint seq_assoc (p : prog a) (q0 : prog a) {struct q0} : prog a :=
  match q0 with
  | Skip => p
  | Dec v s e q => SmartSeq p (Dec v s e (seq_assoc Skip q))
  | Seq q r => seq_assoc (seq_assoc p q) r
  | If e q r => SmartSeq p (If e (seq_assoc Skip q) (seq_assoc Skip r))
  | While e q => SmartSeq p (While e (seq_assoc Skip q))
  | Call None name args => SmartSeq p (Call None name args)
  | Call (Some (rv, exp)) name args =>
      SmartSeq p (Call
                    (match exp with
                     | None => Some (rv, None)
                     | Some (eid, (ev, ep)) => Some (rv, Some (eid, (ev, seq_assoc Skip ep)))
                     end)
                    name args)
  | DecCall v s e es q => SmartSeq p (DecCall v s e es (seq_assoc Skip q))
  | Annot _ _ => p
  | q => SmartSeq p q
  end.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "seq_call_ret_def" *)
Definition seq_call_ret (prog : prog a) : panLang.prog a :=
  match prog with
  | Seq (Call (Some (Some (Local, rv1), None)) trgt args) (Return (Var Local rv2)) =>
      if decide (rv1 = rv2) then TailCall trgt args else prog
  | other => other
  end.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "ret_to_tail_def" *)
Fixpoint ret_to_tail (p0 : prog a) : prog a :=
  match p0 with
  | Skip => Skip
  | Dec v s e q => Dec v s e (ret_to_tail q)
  | Seq p q => seq_call_ret (Seq (ret_to_tail p) (ret_to_tail q))
  | If e p q => If e (ret_to_tail p) (ret_to_tail q)
  | While e p => While e (ret_to_tail p)
  | Call None name args => Call None name args
  | Call (Some (rv, exp)) name args =>
      Call (Some (rv, match exp with
                      | None => None
                      | Some (eid, (ev, ep)) => Some (eid, (ev, ret_to_tail ep))
                      end))
           name args
  | DecCall v s e es q => DecCall v s e es (ret_to_tail q)
  | p => p
  end.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "compile_def" *)
Definition compile (p : prog a) : prog a :=
  let p := seq_assoc Skip p in
  ret_to_tail p.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "compile_prog_def" *)
Definition compile_prog (prog : list (decl a)) : list (decl a) :=
  MAP (fun decl =>
         match decl with
         | Function fi =>
             Function {| name := name fi; inline := inline fi; export := export fi;
                         params := params fi; body := compile (body fi);
                         fun_decl_return := fun_decl_return fi |}
         | _ => decl
         end) prog.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "seq_assoc_pmatch" *)
Theorem seq_assoc_pmatch : forall (p prog : prog a),
  seq_assoc p prog =
  match prog with
  | Skip => p
  | Dec v s e q => SmartSeq p (Dec v s e (seq_assoc Skip q))
  | Seq q r => seq_assoc (seq_assoc p q) r
  | If e q r => SmartSeq p (If e (seq_assoc Skip q) (seq_assoc Skip r))
  | While e q => SmartSeq p (While e (seq_assoc Skip q))
  | Call rtyp name args =>
      SmartSeq p (Call
                    (match rtyp with
                     | None => None
                     | Some (rv, None) => Some (rv, None)
                     | Some (rv, Some (eid, (ev, ep))) => Some (rv, Some (eid, (ev, seq_assoc Skip ep)))
                     end)
                    name args)
  | DecCall v s e es q => SmartSeq p (DecCall v s e es (seq_assoc Skip q))
  | Annot _ _ => p
  | q => SmartSeq p q
  end.
Proof.
  intros p prog; destruct prog as [| | | | | | | | | | | | [[rv [[eid [ev ep]]|]]|] | | | | | | | |];
    reflexivity.
Qed.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "ret_to_tail_pmatch" *)
Theorem ret_to_tail_pmatch : forall p : prog a,
  ret_to_tail p =
  match p with
  | Skip => Skip
  | Dec v s e q => Dec v s e (ret_to_tail q)
  | Seq q r => seq_call_ret (Seq (ret_to_tail q) (ret_to_tail r))
  | If e q r => If e (ret_to_tail q) (ret_to_tail r)
  | While e q => While e (ret_to_tail q)
  | Call rtyp name args =>
      Call (match rtyp with
            | None => None
            | Some (rv, None) => Some (rv, None)
            | Some (rv, Some (eid, (ev, ep))) => Some (rv, Some (eid, (ev, ret_to_tail ep)))
            end)
           name args
  | DecCall v s e es q => DecCall v s e es (ret_to_tail q)
  | p => p
  end.
Proof.
  intros p; destruct p as [| | | | | | | | | | | | [[rv [[eid [ev ep]]|]]|] | | | | | | | |];
    reflexivity.
Qed.

(*! HOL "cakeml/pancake/pan_simpScript.sml" "compile_prog_pmatch" *)
Theorem compile_prog_pmatch : forall prog : list (decl a),
  compile_prog prog =
  MAP (fun decl =>
         match decl with
         | Function fi =>
             Function {| name := name fi; inline := inline fi; export := export fi;
                         params := params fi; body := compile (body fi);
                         fun_decl_return := fun_decl_return fi |}
         | _ => decl
         end) prog.
Proof. reflexivity. Qed.

End Defs.
