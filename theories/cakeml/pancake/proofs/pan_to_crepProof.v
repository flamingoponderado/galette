(** * Pancake [pan_to_crepProof]: correctness of [pan_to_crep]

    Port of [cakeml/pancake/proofs/pan_to_crepProofScript.sml].

    Naming: [crepLang] and [crepSem] are imported (after [panLang]), so
    unqualified program constructors, [state], [eval], [evaluate], ... are
    crepLang's and crepSem's; panLang's constructors and panSem's
    definitions are written [panLang.X], [panSem.X].  HOL's
    [t with clock := k] is [set_clock k t].

    Method.  HOL proves [pc_compile_correct] by [recInduct evaluate_ind]
    with one [Resume] block per case; here each case is a Galette-only
    lemma [pc_X] about the predicate [pc_P], and [pc_all] combines them by
    well-founded induction on [panSem.eval_lt].  [pc_post] is HOL's
    post-condition strengthened with the shape well-formedness of a
    returned or raised value; this replaces HOL's
    [evaluate_shape_invariant_ret_inst(2)], which rest on panProps'
    [evaluate_is_wf_shape_invariant] (not ported).  The callee context of
    a call is handled by the Galette-only [call_setup] / [call_locals_rel]
    (callee parameters are numbered by [GENLIST I]) instead of HOL's
    [call_preserve_state_code_locals_rel].  The observable-semantics
    theorems use [crep_to_loopProof.semantics_wrapper]: by
    [pc_compile_correct] the Pancake and CrepLang runs agree for every
    clock, so the two wrapped functions are equal.  [state_rel_imp_semantics]
    composes [state_rel_imp_semantics_to_crep] (on the target state with the
    un-inlined code) with [crep_inlineProof.state_rel_imp_semantics].

    Not ported:
    - [evaluate_shape_invariant_ret_inst], [evaluate_shape_invariant_ret_inst2],
      [call_preserve_state_code_locals_rel]: see above.
    - [compile_exp_not_mem_load_glob], [load_shape_el_rel], [mem_comp_field],
      [eval_map_var_cexp_present_ctxt], [evaluate_nested_decs_load_globals],
      [locals_rel_extend_new_var], [MAP_SOME_MEM_lemma]: not needed by the
      proofs here.
    ([size_of_eids_eq] is commented out in the HOL script.) *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte bitstring.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.pancake Require Import panLang pan_common crepLang pan_to_crep.
From Galette.cakeml.pancake.semantics Require panSem panProps.
From Galette.cakeml.pancake.semantics Require Import pan_commonProps crepSem crepProps.
From Galette.cakeml.pancake.proofs Require crep_to_loopProof crep_inlineProof.
Import crep_to_loopProof(semantics_run_res(..)).
Import panSem(word_lab(..), shape_of, flatten).
Open Scope N_scope.
Local Open Scope fmap_scope.

(** ** Relations *)

Section Rel.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "excp_rel_def" *)
Definition excp_rel (ceids : fmap eid (word a)) (seids : fmap eid shape) : Prop :=
  FDOM seids = FDOM ceids /\
  forall e e' n n',
    FLOOKUP ceids e = SOME n /\ FLOOKUP ceids e' = SOME n' /\ n = n' -> e = e'.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_def" *)
Definition ctxt_fc (cvs : fmap funname (list (panLang.varname * shape) * shape))
    (em : fmap eid (word a)) (vs : list panLang.varname) (shs : list shape) (ns : list N)
    : context a :=
  {| vars := FEMPTY |++ ZIP (vs, ZIP (shs, with_shape shs ns));
     funcs := cvs; eids := em; vmax := MAX_LIST ns |}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_def" *)
Definition code_rel (ctxt : context a)
    (s_code : fmap funname (list (panLang.varname * shape) * (panLang.prog a * shape)))
    (t_code : fmap funname (list N * prog a)) : Prop :=
  forall f vshs prog rsh,
    FLOOKUP s_code f = SOME (vshs, (prog, rsh)) ->
    panProps.localised_prog prog /\
    FLOOKUP (funcs ctxt) f = SOME (vshs, rsh) /\
    let vs := MAP FST vshs in
    let shs := MAP SND vshs in
    let ns := GENLIST I (size_of_shape (Comb shs)) in
    let nctxt := ctxt_fc (funcs ctxt) (eids ctxt) vs shs ns in
    FLOOKUP t_code f = SOME (ns, compile nctxt prog).

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def" *)
Definition state_rel (s : panSem.state a ffi_t) (t : state a ffi_t) : Prop :=
  panSem.memory s = memory t /\
  panSem.memaddrs s = memaddrs t /\
  panSem.sh_memaddrs s = sh_memaddrs t /\
  panSem.structs s = [] /\
  panSem.globals s = FEMPTY /\
  panSem.clock s = clock t /\
  panSem.be s = be t /\
  panSem.ffi s = ffi t /\
  panSem.base_addr s = base_addr t /\
  panSem.top_addr s = top_addr t.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_structs" *)
Local Theorem state_rel_structs : forall s t, state_rel s t -> panSem.structs s = [].
Proof. intros s t H; apply H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_globals" *)
Local Theorem state_rel_globals : forall s t, state_rel s t -> panSem.globals s = FEMPTY.
Proof. intros s t H; apply H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_def" *)
Definition locals_rel (ctxt : context a) (s_locals : fmap mlstring (panSem.v a))
    (t_locals : fmap varname (word_lab a)) : Prop :=
  no_overlap (vars ctxt) /\ ctxt_max (vmax ctxt) (vars ctxt) /\
  forall vname v,
    FLOOKUP s_locals vname = SOME v ->
    exists ns vs, FLOOKUP (vars ctxt) vname = SOME (shape_of v, ns) /\
      OPT_MMAP (FLOOKUP t_locals) ns = SOME vs /\ flatten v = vs /\
      panProps.is_wf_shape_nil (shape_of v).

End Rel.

Section Basic.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_imp" *)
Theorem code_rel_imp : forall (ctxt : context a) s_code t_code rsh,
  code_rel ctxt s_code t_code ->
  forall f vshs prog,
    FLOOKUP s_code f = SOME (vshs, (prog, rsh)) ->
    panProps.localised_prog prog /\
    FLOOKUP (funcs ctxt) f = SOME (vshs, rsh) /\
    let vs := MAP FST vshs in
    let shs := MAP SND vshs in
    let ns := GENLIST I (size_of_shape (Comb shs)) in
    let nctxt := ctxt_fc (funcs ctxt) (eids ctxt) vs shs ns in
    FLOOKUP t_code f = SOME (ns, compile nctxt prog).
Proof. intros ctxt s_code t_code rsh H f vshs prog Hf. exact (H f vshs prog rsh Hf). Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "code_rel_empty_locals" *)
Theorem code_rel_empty_locals : forall (ctxt : context a) (s : panSem.state a ffi_t) (t : state a ffi_t),
  code_rel ctxt (panSem.code s) (code t) ->
  code_rel ctxt (panSem.code (panSem.empty_locals s)) (code (empty_locals t)).
Proof. intros ctxt s t H. exact H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "cexp_heads_eq" *)
Theorem cexp_heads_eq : forall es : list (list (exp a)),
  cexp_heads es = cexp_heads_simp es.
Proof.
  induction es as [|e es IH]; [reflexivity|]. cbn [cexp_heads]. rewrite IH.
  unfold cexp_heads_simp. cbn [MEM]. destruct e as [|x xs].
  - rewrite (proj2 (bool_decide_spec ([] = []))) by reflexivity. reflexivity.
  - destruct (bool_decide ([] = x :: xs)) eqn:E; [apply bool_decide_spec in E; discriminate|].
    cbn [orb]. destruct (MEM [] es); reflexivity.
Qed.

End Basic.

(** ** Expressions *)

Ltac csplit := repeat match goal with |- _ /\ _ => split end.

Section Exp.
Context {a : N} {ffi_t : Type}.

Lemma In_firstn' {A} (x : A) n l : In x (TAKE n l) -> In x l.
Proof. rewrite TAKE_firstn. intros H; rewrite <- (firstn_skipn (N.to_nat n) l); apply in_or_app; left; exact H. Qed.

Lemma In_skipn' {A} (x : A) n l : In x (DROP n l) -> In x l.
Proof. rewrite DROP_skipn. intros H; rewrite <- (firstn_skipn (N.to_nat n) l); apply in_or_app; right; exact H. Qed.

Lemma MAP_TAKE' {A B} (f : A -> B) n l : MAP f (TAKE n l) = TAKE n (MAP f l).
Proof. rewrite !TAKE_firstn. symmetry; apply firstn_map. Qed.

Lemma MAP_DROP' {A B} (f : A -> B) n l : MAP f (DROP n l) = DROP n (MAP f l).
Proof. rewrite !DROP_skipn. symmetry; apply skipn_map. Qed.

Lemma TAKE_app_exact {A} (l1 l2 : list A) n : n = LENGTH l1 -> TAKE n (l1 ++ l2) = l1.
Proof.
  intros ->. rewrite TAKE_firstn, LENGTH_length, Nat2N.id, firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma DROP_app_exact {A} (l1 l2 : list A) n : n = LENGTH l1 -> DROP n (l1 ++ l2) = l2.
Proof.
  intros ->. rewrite DROP_skipn, LENGTH_length, Nat2N.id, skipn_app, skipn_all, Nat.sub_diag.
  reflexivity.
Qed.

Lemma LENGTH_MAP' {A B} (f : A -> B) l : LENGTH (MAP f l) = LENGTH l.
Proof. rewrite !LENGTH_length, length_map. reflexivity. Qed.

Lemma LENGTH_app' {A} (x y : list A) : LENGTH (x ++ y) = LENGTH x + LENGTH y.
Proof. rewrite !LENGTH_length, length_app. lia. Qed.

Lemma LENGTH_GENLIST' {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, LENGTH_app', IH. cbn. lia.
Qed.

Lemma MAP_eq_LENGTH {A B C} (f : A -> B) (g : C -> B) l1 l2 :
  MAP f l1 = MAP g l2 -> LENGTH l1 = LENGTH l2.
Proof. intros H. rewrite <- (LENGTH_MAP' f), <- (LENGTH_MAP' g l2), H. reflexivity. Qed.

Lemma MAP_eq_EL {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) : forall (l1 : list A) (l2 : list B),
  LENGTH l1 = LENGTH l2 -> (forall n, n < LENGTH l1 -> f (EL n l1) = EL n l2) -> MAP f l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] Hl He; cbn [LENGTH] in Hl; try lia; [reflexivity|].
  cbn [MAP List.map]. f_equal.
  - exact (He 0 ltac:(cbn [LENGTH]; lia)).
  - apply IH; [lia|]. intros n Hn. specialize (He (SUC n) ltac:(cbn [LENGTH]; lia)).
    rewrite !EL_SUC in He. exact He.
Qed.

Lemma EL_MAP' {A B} `{Inhabited A} `{Inhabited B} (f : A -> B) : forall (l : list A) n,
  n < LENGTH l -> EL n (MAP f l) = f (EL n l).
Proof.
  induction l as [|x l IH]; intros n Hn; cbn [LENGTH] in Hn; [lia|].
  destruct (N.eq_dec n 0) as [->|Hn0]; [reflexivity|].
  replace n with (SUC (n - 1)) by lia. rewrite !EL_SUC. cbn [TL MAP List.map]. apply IH. lia.
Qed.

Lemma comp_field_rel (t : state a ffi_t) : forall (vs : list (panSem.v a)) i cexp es sh,
  i < LENGTH vs ->
  MAP (eval t) cexp = MAP SOME (FLAT (MAP flatten vs)) ->
  EVERY panProps.is_wf_shape_nil (MAP shape_of vs) ->
  comp_field i (MAP shape_of vs) cexp = (es, sh) ->
  MAP (eval t) es = MAP SOME (flatten (EL i vs)) /\ LENGTH es = size_of_shape sh /\
  shape_of (EL i vs) = sh /\ panProps.is_wf_shape_nil sh.
Proof.
  induction vs as [|x vs IH]; intros i cexp es sh Hi Hm Hw Hc; cbn [LENGTH] in Hi; [lia|].
  cbn [MAP List.map comp_field EVERY FLAT List.concat] in *.
  apply andb_prop in Hw as [Hwx Hw].
  assert (Hlx : LENGTH (flatten x) = size_of_shape (shape_of x))
    by (apply panProps.length_flatten_eq_size_of_shape, Hwx).
  destruct (decide (i = 0)) as [->|Hi0].
  - injection Hc as <- <-. change (EL 0 (x :: vs)) with x.
    rewrite MAP_TAKE', Hm, map_app, TAKE_app_exact by (rewrite LENGTH_MAP'; congruence).
    split; [reflexivity|]. split; [|split; [reflexivity|exact Hwx]].
    rewrite <- (LENGTH_MAP' (eval t)), MAP_TAKE', Hm, map_app, TAKE_app_exact
      by (rewrite LENGTH_MAP'; congruence).
    rewrite LENGTH_MAP'. exact Hlx.
  - replace (EL i (x :: vs)) with (EL (i - 1) vs)
      by (replace i with (SUC (i - 1)) at 2 by lia; rewrite EL_SUC; reflexivity).
    apply (IH (i - 1) (DROP (size_of_shape (shape_of x)) cexp)); [lia| |exact Hw|exact Hc].
    rewrite MAP_DROP', Hm, map_app, DROP_app_exact by (rewrite LENGTH_MAP'; congruence).
    reflexivity.
Qed.

Lemma eval_Op_Add_Const (t : state a ffi_t) e (w c : word a) :
  eval t e = SOME (Word w) ->
  eval t (Op Add [e; Const c]) = SOME (Word (w + c)%w).
Proof.
  intros H. cbn [eval OPT_MMAP]. rewrite H. cbn. f_equal. f_equal. word_ring.
Qed.

Lemma eval_Load_Op_Const (t : state a ffi_t) e (w c : word a) :
  eval t e = SOME (Word w) ->
  eval t (Load (Op Add [e; Const c])) = mem_load (w + c)%w t.
Proof.
  intros H. cbn [eval OPT_MMAP]. rewrite H. cbn. f_equal. word_ring.
Qed.

Definition val_word (w : panSem.v a) : word a :=
  match w with panSem.Val (Word n) => n | _ => ARB end.

Lemma EVERY_MAP_Word (ws : list (panSem.v a)) :
  EVERY (fun w => match w with Word _ => true end) (MAP (fun w => Word (val_word w)) ws) = true.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn. exact IH. Qed.

Lemma MAP_MAP_Word (ws : list (panSem.v a)) :
  MAP (fun w => match w with Word n => n end) (MAP (fun w => Word (val_word w)) ws) =
  MAP (fun w => match w with panSem.Val (Word n) => n | _ => ARB end) ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma heads_rel (s : panSem.state a ffi_t) (t : state a ffi_t) ct : forall es0,
  Forall (fun e => forall v es sh, panSem.eval s e = SOME v -> panProps.localised_exp e = true ->
            compile_exp ct e = (es, sh) ->
            MAP (eval t) es = MAP SOME (flatten v) /\ LENGTH es = size_of_shape sh /\
            shape_of v = sh /\ panProps.is_wf_shape_nil sh) es0 ->
  forall ws, OPT_MMAP (panSem.eval s) es0 = SOME ws ->
  EVERY (fun w => match w with panSem.Val (Word _) => true | _ => false end) ws = true ->
  EVERY panProps.localised_exp es0 = true ->
  exists hs, cexp_heads (MAP FST (MAP (compile_exp ct) es0)) = SOME hs /\
    OPT_MMAP (eval t) hs = SOME (MAP (fun w => Word (val_word w)) ws).
Proof.
  intros es0 IH. induction IH as [|x xs Hx Hxs IHl]; intros ws Eo Ew Hloc.
  - injection Eo as <-. exists []. split; reflexivity.
  - cbn [OPT_MMAP] in Eo. destruct (panSem.eval s x) as [vx|] eqn:Ex; [|discriminate].
    destruct (OPT_MMAP (panSem.eval s) xs) as [vs'|] eqn:Exs; [|discriminate]. injection Eo as <-.
    cbn [EVERY] in Ew, Hloc. apply andb_prop in Ew as [Ewx Ews]. apply andb_prop in Hloc as [Hlx Hlxs].
    destruct (IHl vs' eq_refl Ews Hlxs) as (hs & Hh & Hhe).
    destruct (compile_exp ct x) as [ex shx] eqn:Ecx.
    destruct (Hx vx ex shx eq_refl Hlx eq_refl) as (A1 & _).
    destruct vx as [[n]|vs|nm fl]; try discriminate Ewx.
    destruct ex as [|h ex]; [discriminate A1|]. cbn [MAP List.map flatten] in A1. injection A1 as A1 _.
    exists (h :: hs). cbn [MAP List.map cexp_heads]. rewrite Ecx. cbn [FST fst]. rewrite Hh.
    split; [reflexivity|]. cbn [OPT_MMAP]. rewrite A1, Hhe. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_exp_val_rel" *)
Theorem compile_exp_val_rel : forall (s : panSem.state a ffi_t) e v (t : state a ffi_t) ct es sh,
  panSem.eval s e = SOME v /\
  state_rel s t /\
  code_rel ct (panSem.code s) (code t) /\
  locals_rel ct (panSem.locals s) (locals t) /\
  panProps.localised_exp e /\
  compile_exp ct e = (es, sh) ->
  MAP (eval t) es = MAP SOME (flatten v) /\
  LENGTH es = size_of_shape sh /\
  shape_of v = sh /\
  panProps.is_wf_shape_nil sh.
Proof.
  intros s e v t ct es sh (Hev & Hs & Hc & Hl & Hloc & Hce). revert v es sh Hev Hloc Hce.
  pose proof Hs as (Hm & Hma & Hsh & Hst & Hgl & Hck & Hbe & Hff & Hba & Hta).
  induction e as [w|vk vn|es0 IH|i e IH|nm es0 IH|f e IH|sh0 e IH|e IH|e IH|bop es0 IH|op es0 IH
                  |c e1 e2 IH1 IH2|sh0 e1 e2 IH1 IH2| | |] using panProps.exp_nested_ind;
    intros v es sh Hev Hloc Hce; cbn [panSem.eval compile_exp] in Hev, Hce;
    unfold panProps.localised_exp in Hloc; cbn [panProps.every_exp] in Hloc.
  - (* Const *)
    injection Hev as <-. injection Hce as <- <-. cbn. csplit; reflexivity.
  - (* Var *)
    destruct vk; [|discriminate Hloc].
    destruct Hl as (_ & _ & Hl). destruct (Hl _ _ Hev) as (ns & vs & Hv & Ho & Hf & Hw).
    rewrite Hv in Hce. injection Hce as <- <-.
    rewrite lookup_locals_eq_map_vars in Ho. apply opt_mmap_eq_some in Ho.
    split; [rewrite Ho, Hf; reflexivity|]. split; [|split; [reflexivity|exact Hw]].
    rewrite (MAP_eq_LENGTH _ _ _ _ Ho), <- Hf. apply panProps.length_flatten_eq_size_of_shape, Hw.
  - (* RStruct *)
    destruct (OPT_MMAP (panSem.eval s) es0) as [vs|] eqn:Eo; [|discriminate]. injection Hev as <-.
    injection Hce as <- <-. cbn [flatten shape_of size_of_shape is_wf_shape].
    apply andb_prop in Hloc as [_ Hloc]. revert vs Eo Hloc.
    induction IH as [|x xs Hx Hxs IHl]; intros vs Eo Hloc.
    + injection Eo as <-. cbn. csplit; reflexivity.
    + cbn [OPT_MMAP] in Eo. destruct (panSem.eval s x) as [vx|] eqn:Ex; [|discriminate].
      destruct (OPT_MMAP (panSem.eval s) xs) as [vs'|] eqn:Exs; [|discriminate].
      injection Eo as <-. cbn [EVERY] in Hloc. apply andb_prop in Hloc as [Hlx Hlxs].
      destruct (compile_exp ct x) as [ex shx] eqn:Ecx.
      destruct (Hx vx ex shx eq_refl Hlx eq_refl) as (A1 & B1 & C1 & D1).
      destruct (IHl vs' eq_refl Hlxs) as (A2 & B2 & C2 & D2).
      cbn [MAP List.map FLAT List.concat SUM EVERY]. rewrite Ecx. cbn [FST SND fst snd].
      split; [rewrite !map_app, A1, A2; reflexivity|].
      split; [rewrite LENGTH_app', B1, B2; reflexivity|].
      split; [rewrite C1; first [injection C2 as C2'; rewrite C2'; reflexivity | rewrite C2; reflexivity]|].
      rewrite D1. exact D2.
  - (* RField *)
    destruct (panSem.eval s e) as [[w|vs|nm fl]|] eqn:Ee; try discriminate.
    destruct (i <? LENGTH vs) eqn:Ei; [|discriminate]. injection Hev as <-. apply N.ltb_lt in Ei.
    apply andb_prop in Hloc as [_ Hloc].
    destruct (compile_exp ct e) as [cexp shp] eqn:Ece.
    destruct (IH _ _ _ eq_refl Hloc eq_refl) as (A & B & C & D).
    cbn [shape_of] in C. subst shp. cbn [is_wf_shape] in D.
    exact (comp_field_rel t vs i cexp es sh Ei A D Hce).
  - (* NStruct *)
    rewrite Hst in Hev. cbn in Hev. discriminate Hev.
  - (* NField *)
    destruct (panSem.eval s e) as [[w|vs|nm fl]|]; try discriminate.
    rewrite Hst in Hev. cbn in Hev.
    match type of Hev with context [bool_decide (?x = ?x)] =>
      rewrite (proj2 (bool_decide_spec (x = x)) eq_refl) in Hev end.
    discriminate Hev.
  - (* Load *)
    rewrite Hst in Hev.
    destruct (is_wf_shape [] sh0) eqn:Ew; [|discriminate].
    destruct (panSem.eval s e) as [[[w]|vs|nm fl]|] eqn:Ee; try discriminate.
    apply andb_prop in Hloc as [_ Hloc].
    destruct (compile_exp ct e) as [cexp shp] eqn:Ece.
    destruct (IH _ _ _ eq_refl Hloc eq_refl) as (A & B & C & D).
    destruct cexp as [|e' cexp]; [discriminate A|].
    cbn [MAP List.map flatten] in A. injection A as A1 A2.
    destruct cexp; [|discriminate A2].
    injection Hce as <- <-.
    pose proof (panProps.mem_load_some_shape_eq _ _ _ _ _ _ Hev) as Hshv.
    assert (Hlen : LENGTH (flatten v) = size_of_shape sh0)
      by (rewrite <- Hshv; apply panProps.length_flatten_eq_size_of_shape; rewrite Hshv; exact Ew).
    split; [|split; [apply length_load_shape_eq_shape|split; [exact Hshv|exact Ew]]].
    apply MAP_eq_EL; [rewrite length_load_shape_eq_shape, LENGTH_MAP', Hlen; reflexivity|].
    intros k Hk. rewrite length_load_shape_eq_shape in Hk.
    rewrite eval_load_shape_el_rel by exact Hk. rewrite EL_MAP' by lia.
    rewrite (eval_Load_Op_Const t e' w _ A1).
    replace (w + (n2w 0 + bytes_in_word * n2w k))%w with (w + bytes_in_word * n2w k)%w by word_ring.
    apply (proj1 mem_loads_flat_rel sh0 w (panSem.memaddrs s) (panSem.memory s) [] v
             (conj Hev Ew) t k ltac:(lia) Hma Hm).
  - (* Load32 *)
    destruct (panSem.eval s e) as [[[w]|vs|nm fl]|] eqn:Ee; try discriminate.
    destruct (panSem.mem_load_32 _ _ _ _) as [w32|] eqn:Em32; [|discriminate]. injection Hev as <-.
    apply andb_prop in Hloc as [_ Hloc].
    destruct (compile_exp ct e) as [cexp shp] eqn:Ece.
    destruct (IH _ _ _ eq_refl Hloc eq_refl) as (A & B & C & D).
    cbn [shape_of] in C. subst shp.
    destruct cexp as [|e' cexp]; [discriminate A|]. cbn [MAP List.map flatten] in A. injection A as A1 _.
    injection Hce as <- <-. cbn [MAP List.map flatten eval]. rewrite A1.
    rewrite <- Hm, <- Hma, <- Hbe, Em32. csplit; reflexivity.
  - (* LoadByte *)
    destruct (panSem.eval s e) as [[[w]|vs|nm fl]|] eqn:Ee; try discriminate.
    destruct (panSem.mem_load_byte _ _ _ _) as [w8|] eqn:Em8; [|discriminate]. injection Hev as <-.
    apply andb_prop in Hloc as [_ Hloc].
    destruct (compile_exp ct e) as [cexp shp] eqn:Ece.
    destruct (IH _ _ _ eq_refl Hloc eq_refl) as (A & B & C & D).
    cbn [shape_of] in C. subst shp.
    destruct cexp as [|e' cexp]; [discriminate A|]. cbn [MAP List.map flatten] in A. injection A as A1 _.
    injection Hce as <- <-. cbn [MAP List.map flatten eval]. rewrite A1.
    rewrite <- Hm, <- Hma, <- Hbe, Em8. csplit; reflexivity.
  - (* Op *)
    destruct (OPT_MMAP (panSem.eval s) es0) as [ws|] eqn:Eo; [|discriminate].
    destruct (EVERY _ ws) eqn:Ew; [|discriminate].
    apply andb_prop in Hloc as [_ Hloc].
    destruct (heads_rel s t ct es0 IH ws Eo Ew Hloc) as (hs & Hh & Hhe). rewrite Hh in Hce.
    injection Hce as <- <-. cbn [MAP List.map eval].
    rewrite Hhe, EVERY_MAP_Word, MAP_MAP_Word.
    destruct (wordLang.word_op _ _); cbn in Hev |- *; [|discriminate].
    injection Hev as <-; cbn; csplit; reflexivity.
  - (* Panop *)
    destruct (OPT_MMAP (panSem.eval s) es0) as [ws|] eqn:Eo; [|discriminate].
    destruct (EVERY _ ws) eqn:Ew; [|discriminate].
    apply andb_prop in Hloc as [_ Hloc].
    destruct (heads_rel s t ct es0 IH ws Eo Ew Hloc) as (hs & Hh & Hhe). rewrite Hh in Hce.
    injection Hce as <- <-. cbn [MAP List.map eval].
    rewrite Hhe, EVERY_MAP_Word, MAP_MAP_Word.
    destruct op. cbn [compile_panop crep_op panSem.pan_op] in *.
    destruct (MAP _ ws) as [|w1 [|w2 [|w3 ws']]]; cbn in Hev; try discriminate Hev;
      injection Hev as <-; cbn; csplit; reflexivity.
  - (* Cmp *)
    destruct (panSem.eval s e1) as [[[w1]|vs|nm fl]|] eqn:E1; try discriminate.
    destruct (panSem.eval s e2) as [[[w2]|vs|nm fl]|] eqn:E2; try discriminate.
    injection Hev as <-. apply andb_prop in Hloc as [Hloc Hloc2]. apply andb_prop in Hloc as [_ Hloc1].
    destruct (compile_exp ct e1) as [c1 s1'] eqn:Ec1. destruct (compile_exp ct e2) as [c2 s2'] eqn:Ec2.
    destruct (IH1 _ _ _ eq_refl Hloc1 eq_refl) as (A1 & _). destruct (IH2 _ _ _ eq_refl Hloc2 eq_refl) as (A2 & _).
    destruct c1 as [|h1 c1]; [discriminate A1|]. destruct c2 as [|h2 c2]; [discriminate A2|].
    cbn [MAP List.map flatten] in A1, A2. injection A1 as A1 _. injection A2 as A2 _.
    cbn [FST fst] in Hce. injection Hce as <- <-. cbn [MAP List.map eval]. rewrite A1, A2.
    rewrite v2w_sing. cbn. csplit; reflexivity.
  - (* Shift *)
    destruct (panSem.eval s e1) as [[[w1]|vs|nm fl]|] eqn:E1; try discriminate.
    destruct (panSem.eval s e2) as [[[w2]|vs|nm fl]|] eqn:E2; try discriminate.
    apply andb_prop in Hloc as [Hloc Hloc2]. apply andb_prop in Hloc as [_ Hloc1].
    destruct (compile_exp ct e1) as [c1 s1'] eqn:Ec1. destruct (compile_exp ct e2) as [c2 s2'] eqn:Ec2.
    destruct (IH1 _ _ _ eq_refl Hloc1 eq_refl) as (A1 & _). destruct (IH2 _ _ _ eq_refl Hloc2 eq_refl) as (A2 & _).
    destruct c1 as [|h1 c1]; [discriminate A1|]. destruct c2 as [|h2 c2]; [discriminate A2|].
    cbn [MAP List.map flatten] in A1, A2. injection A1 as A1 _. injection A2 as A2 _.
    cbn [FST fst] in Hce. injection Hce as <- <-. cbn [MAP List.map eval]. rewrite A1, A2.
    destruct (wordLang.word_sh _ _ _); cbn in Hev |- *; [|discriminate].
    injection Hev as <-; cbn; csplit; reflexivity.
  - (* BaseAddr *)
    injection Hev as <-. injection Hce as <- <-. cbn. rewrite Hba. csplit; reflexivity.
  - (* TopAddr *)
    injection Hev as <-. injection Hce as <- <-. cbn. rewrite Hta. csplit; reflexivity.
  - (* BytesInWord *)
    injection Hev as <-. injection Hce as <- <-. cbn. csplit; reflexivity.
Qed.

End Exp.

(** ** Variables of compiled expressions *)

Section ExpVars.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mem_comp_field_lem" *)
Theorem mem_comp_field_lem : forall i l (es : list (exp a)) x,
  MEM x (FST (comp_field i l es)) -> MEM x es \/ x = Const (n2w 0).
Proof.
  intros i l; revert i; induction l as [|sh l IH]; intros i es x H; cbn [comp_field] in H.
  - cbn [FST fst MEM] in H. right. unfold is_true in H. apply orb_prop in H as [H|H]; [|discriminate].
    apply bool_decide_spec in H. exact H.
  - destruct (decide (i = 0)).
    + left. cbn [FST fst] in H. apply MEM_In, In_firstn' in H. apply MEM_In, H.
    + destruct (IH _ _ _ H) as [H1|H1]; [left|right; exact H1].
      apply MEM_In in H1. apply MEM_In. exact (In_skipn' _ _ _ H1).
Qed.

Lemma compile_exp_vars (ct : context a) : forall e n,
  In n (FLAT (MAP var_cexp (FST (compile_exp ct e)))) ->
  exists v shp ns, FLOOKUP (vars ct) v = SOME (shp, ns) /\ In n ns.
Proof.
  intros e. induction e as [w|vk vn|es0 IH|i e IH|nm es0 IH|f e IH|sh0 e IH|e IH|e IH|bop es0 IH|op es0 IH
                  |c e1 e2 IH1 IH2|sh0 e1 e2 IH1 IH2| | |] using panProps.exp_nested_ind;
    intros n Hn; cbn [compile_exp] in Hn.
  - cbn in Hn. destruct Hn.
  - destruct vk; [|cbn in Hn; destruct Hn].
    destruct (FLOOKUP (vars ct) vn) as [[shp ns]|] eqn:Ev; [|cbn in Hn; destruct Hn].
    cbn [FST fst] in Hn. rewrite map_var_cexp_eq_var in Hn. exists vn, shp, ns. split; assumption.
  - cbn [FST fst] in Hn. apply in_concat in Hn as (l & Hl & Hn). apply in_map_iff in Hl as (x & <- & Hx).
    apply in_concat in Hx as (l' & Hl' & Hx). apply in_map_iff in Hl' as (p & <- & Hp).
    apply in_map_iff in Hp as (e0 & <- & He0).
    rewrite Forall_forall in IH. apply (IH e0 He0 n). eapply In_FLAT_MAP; eassumption.
  - destruct (compile_exp ct e) as [cexp shp] eqn:Ece. destruct shp as [|shs|nm];
      try (cbn in Hn; destruct Hn).
    apply in_concat in Hn as (l & Hl & Hn). apply in_map_iff in Hl as (x & <- & Hx).
    destruct (mem_comp_field_lem i shs cexp x (proj2 (MEM_In _ _) Hx)) as [Hm| ->]; [|cbn in Hn; destruct Hn].
    apply IH. try rewrite Ece. cbn [FST fst]. eapply In_FLAT_MAP; [apply MEM_In, Hm|exact Hn].
  - cbn in Hn. destruct Hn.
  - cbn in Hn. destruct Hn.
  - destruct (compile_exp ct e) as [cexp shp] eqn:Ece. destruct cexp as [|e' cexp]; [cbn in Hn; destruct Hn|].
    cbn [FST fst] in Hn. apply in_concat in Hn as (l & Hl & Hn). apply in_map_iff in Hl as (x & <- & Hx).
    rewrite (var_exp_load_shape _ _ _ _ (proj2 (MEM_In _ _) Hx)) in Hn.
    apply IH. try rewrite Ece. cbn [FST fst]. eapply In_FLAT_MAP; [left; reflexivity|exact Hn].
  - destruct (compile_exp ct e) as [cexp shp] eqn:Ece. destruct cexp as [|e' cexp]; [cbn in Hn; destruct Hn|].
    destruct shp; try (cbn in Hn; destruct Hn). cbn in Hn. rewrite app_nil_r in Hn.
    apply IH. try rewrite Ece. cbn [FST fst]. eapply In_FLAT_MAP; [left; reflexivity|exact Hn].
  - destruct (compile_exp ct e) as [cexp shp] eqn:Ece. destruct cexp as [|e' cexp]; [cbn in Hn; destruct Hn|].
    destruct shp; try (cbn in Hn; destruct Hn). cbn in Hn. rewrite app_nil_r in Hn.
    apply IH. try rewrite Ece. cbn [FST fst]. eapply In_FLAT_MAP; [left; reflexivity|exact Hn].
  - destruct (cexp_heads _) as [hs|] eqn:Eh; [|cbn in Hn; destruct Hn].
    cbn in Hn. rewrite app_nil_r in Hn. rewrite cexp_heads_eq in Eh. unfold cexp_heads_simp in Eh.
    destruct (MEM [] _) eqn:Em; [discriminate|]. injection Eh as <-.
    apply in_concat in Hn as (l & Hl & Hn). apply in_map_iff in Hl as (h & <- & Hh).
    apply in_map_iff in Hh as (ces & <- & Hces). apply in_map_iff in Hces as (p & <- & Hp).
    apply in_map_iff in Hp as (e0 & <- & He0).
    rewrite Forall_forall in IH. apply (IH e0 He0 n).
    destruct (FST (compile_exp ct e0)) as [|h ces] eqn:Ef.
    + exfalso. rewrite (proj2 (MEM_In _ _)) in Em; [discriminate|].
      rewrite <- Ef. apply in_map. apply in_map. exact He0.
    + cbn [HD MAP List.map FLAT List.concat]. apply in_or_app; left; exact Hn.
  - destruct (cexp_heads _) as [hs|] eqn:Eh; [|cbn in Hn; destruct Hn].
    cbn in Hn. rewrite app_nil_r in Hn. rewrite cexp_heads_eq in Eh. unfold cexp_heads_simp in Eh.
    destruct (MEM [] _) eqn:Em; [discriminate|]. injection Eh as <-.
    apply in_concat in Hn as (l & Hl & Hn). apply in_map_iff in Hl as (h & <- & Hh).
    apply in_map_iff in Hh as (ces & <- & Hces). apply in_map_iff in Hces as (p & <- & Hp).
    apply in_map_iff in Hp as (e0 & <- & He0).
    rewrite Forall_forall in IH. apply (IH e0 He0 n).
    destruct (FST (compile_exp ct e0)) as [|h ces] eqn:Ef.
    + exfalso. rewrite (proj2 (MEM_In _ _)) in Em; [discriminate|].
      rewrite <- Ef. apply in_map. apply in_map. exact He0.
    + cbn [HD MAP List.map FLAT List.concat]. apply in_or_app; left; exact Hn.
  - destruct (FST (compile_exp ct e1)) as [|h1 c1] eqn:E1; [cbn in Hn; destruct Hn|].
    destruct (FST (compile_exp ct e2)) as [|h2 c2] eqn:E2; [cbn in Hn; destruct Hn|].
    cbn in Hn. rewrite app_nil_r in Hn. apply in_app_or in Hn as [Hn|Hn].
    + apply IH1. try rewrite E1. cbn. apply in_or_app; left; exact Hn.
    + apply IH2. try rewrite E2. cbn. apply in_or_app; left; exact Hn.
  - destruct (FST (compile_exp ct e1)) as [|h1 c1] eqn:E1; [cbn in Hn; destruct Hn|].
    destruct (FST (compile_exp ct e2)) as [|h2 c2] eqn:E2; [cbn in Hn; destruct Hn|].
    cbn in Hn. rewrite app_nil_r in Hn. apply in_app_or in Hn as [Hn|Hn].
    + apply IH1. try rewrite E1. cbn. apply in_or_app; left; exact Hn.
    + apply IH2. try rewrite E2. cbn. apply in_or_app; left; exact Hn.
  - cbn in Hn. destruct Hn.
  - cbn in Hn. destruct Hn.
  - cbn in Hn. destruct Hn.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_var_cexp_present_ctxt" *)
Theorem eval_var_cexp_present_ctxt : forall (s : panSem.state a ffi_t) e v (t : state a ffi_t) ct es sh,
  state_rel s t /\
  panSem.eval s e = SOME v /\
  code_rel ct (panSem.code s) (code t) /\
  locals_rel ct (panSem.locals s) (locals t) /\
  panProps.localised_exp e /\
  compile_exp ct e = (es, sh) ->
  forall n, MEM n (FLAT (MAP var_cexp es)) ->
    exists v shp ns, FLOOKUP (vars ct) v = SOME (shp, ns) /\ MEM n ns.
Proof.
  intros s e v t ct es sh (_ & _ & _ & _ & _ & Hce) n Hn.
  destruct (compile_exp_vars ct e n) as (v' & shp & ns & H1 & H2).
  - rewrite Hce. cbn [FST fst]. apply MEM_In, Hn.
  - exists v', shp, ns. split; [exact H1|apply MEM_In, H2].
Qed.

End ExpVars.

(** ** Tactics *)


Ltac pcbn :=
  cbn [panSem.locals panSem.globals panSem.structs panSem.code panSem.eshapes panSem.memory
       panSem.memaddrs panSem.sh_memaddrs panSem.clock panSem.be panSem.ffi panSem.base_addr
       panSem.top_addr panSem.set_locals panSem.set_globals panSem.set_structs panSem.set_memory
       panSem.set_clock panSem.set_ffi panSem.set_var panSem.empty_locals panSem.dec_clock
       panSem.set_code panSem.set_eshapes] in *.

Ltac ccbn :=
  cbn [locals globals code memory memaddrs sh_memaddrs clock be ffi base_addr top_addr
       set_locals set_memory set_clock set_ffi set_code set_globals dec_clock empty_locals
       set_var] in *.

Ltac srel H :=
  let H' := fresh "Hsr" in pose proof H as H'; unfold state_rel in *; pcbn; ccbn;
  destruct H' as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); csplit; try assumption; try congruence.

(** One step of panSem's [evaluate] in [H]. *)
Ltac pstep H :=
  rewrite panProps.evaluate_unfold in H; cbn [panSem.evaluate_body] in H;
  rewrite ?panSem.fix_clock_evaluate in H.

(** One step of crepSem's [evaluate] in the goal. *)
Ltac cstep :=
  rewrite crepProps.evaluate_unfold; cbn [evaluate_body]; unfold fcl; cbn beta;
  rewrite ?fix_clock_evaluate.


(** ** Nested assignments and declarations *)

Section Nested.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_lookup_ctxt" *)
Theorem locals_rel_lookup_ctxt : forall (ctxt : context a) lcl lcl' vr v,
  locals_rel ctxt lcl lcl' /\ FLOOKUP lcl vr = SOME v ->
  exists ns, FLOOKUP (vars ctxt) vr = SOME (shape_of v, ns) /\
    LENGTH ns = LENGTH (flatten v) /\
    OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v) /\
    panProps.is_wf_shape_nil (shape_of v).
Proof.
  intros ctxt lcl lcl' vr v [(_ & _ & H) Hv]. destruct (H _ _ Hv) as (ns & vs & H1 & H2 & <- & H4).
  exists ns. split; [exact H1|]. split; [|split; assumption].
  apply opt_mmap_eq_some in H2. exact (MAP_eq_LENGTH _ _ _ _ H2).
Qed.

Lemma eval_upd_notin_vars (t : state a ffi_t) (es : list (exp a)) ev n w :
  MAP (eval t) es = MAP SOME ev -> ~ In n (FLAT (MAP var_cexp es)) ->
  MAP (eval (set_locals (locals t |+ (n, w)) t)) es = MAP SOME ev.
Proof.
  intros H Hn. rewrite <- H. apply map_ext_in. intros e He.
  apply update_locals_not_vars_eval_eq'; [exact w|]. intros Hm. apply Hn.
  eapply In_FLAT_MAP; [exact He|apply MEM_In, Hm].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_nested_assign_distinct_eq" *)
Theorem eval_nested_assign_distinct_eq : forall (es : list (exp a)) ns (t : state a ffi_t) ev vs,
  MAP (eval t) es = MAP SOME ev /\
  OPT_MMAP (FLOOKUP (locals t)) ns = SOME vs /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns /\
  LENGTH ns = LENGTH es ->
  evaluate (nested_seq (MAP2 Assign ns es), t) =
  (NONE, set_locals (locals t |++ ZIP (ns, ev)) t).
Proof.
  induction es as [|e es IH]; intros [|n ns] t ev vs (Hm & Ho & Hd & Had & Hl);
    cbn [LENGTH] in Hl; try lia.
  - destruct ev; [|discriminate Hm]. cbn [MAP2 nested_seq]. cstep. f_equal.
    destruct t; reflexivity.
  - destruct ev as [|w ev]; [discriminate Hm|]. cbn [MAP List.map] in Hm. injection Hm as He Hm.
    cbn [OPT_MMAP] in Ho. destruct (FLOOKUP (locals t) n) as [vn|] eqn:Ev; [|discriminate].
    destruct (OPT_MMAP (FLOOKUP (locals t)) ns) as [vs'|] eqn:Evs; [|discriminate].
    cbn [ALL_DISTINCT] in Had. apply andb_prop in Had as [Hn Had].
    pose proof (proj1 (distinct_lists_iff _ _) Hd) as Hd2; clear Hd; rename Hd2 into Hd.
    cbn [MAP2 nested_seq]. cstep. cstep. rewrite He, Ev. cbn beta iota.
    rewrite (IH ns _ ev vs').
    + cbn [ZIP FUPDATE_LIST]. f_equal; destruct t; reflexivity.
    + split; [apply eval_upd_notin_vars; [exact Hm|]|].
      { intros Hin. apply (Hd n); [left; reflexivity|]. cbn [MAP List.map FLAT List.concat].
        apply in_or_app; right; exact Hin. }
      split.
      { ccbn. apply opt_mmap_flookup_update. split; [exact Evs|]. intros Hm'. rewrite Hm' in Hn. discriminate. }
      split.
      { apply distinct_lists_iff. intros x Hx Hy. apply (Hd x); [right; exact Hx|].
        cbn [MAP List.map FLAT List.concat]. apply in_or_app; right; exact Hy. }
      split; [exact Had|lia].
Qed.

Lemma res_var_FOLDL_comm (n : N) (x : option (word_lab a)) : forall ns (m : list (option (word_lab a))) l,
  ~ In n ns ->
  res_var (FOLDL res_var l (ZIP (ns, m))) (n, x) = FOLDL res_var (res_var l (n, x)) (ZIP (ns, m)).
Proof.
  induction ns as [|k ns IH]; intros [|y m] l Hn; try reflexivity.
  change (ZIP (k :: ns, y :: m)) with ((k, y) :: ZIP (ns, m)). cbn [FOLDL].
  rewrite IH by (intros H; apply Hn; right; exact H). f_equal.
  apply fmap_ext. intros z. rewrite !FLOOKUP_res_var.
  destruct (decide (z = k)), (decide (z = n)); subst; try reflexivity.
  exfalso; apply Hn; left; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_nested_decs_seq_res_var_eq" *)
Theorem eval_nested_decs_seq_res_var_eq : forall (es : list (exp a)) ns (t : state a ffi_t) ev p,
  MAP (eval t) es = MAP SOME ev /\
  LENGTH ns = LENGTH es /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns ->
  let '(q, r) := evaluate (p, set_locals (locals t |++ ZIP (ns, ev)) t) in
  evaluate (nested_decs ns es p, t) =
  (q, set_locals (FOLDL res_var (locals r) (ZIP (ns, MAP (FLOOKUP (locals t)) ns))) r).
Proof.
  induction es as [|e es IH]; intros [|n ns] t ev p (Hm & Hl & Hd & Had); cbn [LENGTH] in Hl; try lia.
  - destruct ev; [|discriminate Hm]. cbn [nested_decs ZIP FUPDATE_LIST FOLDL MAP List.map].
    replace (set_locals (locals t) t) with t by (destruct t; reflexivity).
    destruct (evaluate (p, t)) as [q r]. f_equal. destruct r; reflexivity.
  - destruct ev as [|w ev]; [discriminate Hm|]. cbn [MAP List.map] in Hm. injection Hm as He Hm.
    cbn [ALL_DISTINCT] in Had. apply andb_prop in Had as [Hn Had].
    pose proof (proj1 (distinct_lists_iff _ _) Hd) as Hd2; clear Hd; rename Hd2 into Hd.
    assert (Hm' : MAP (eval (set_locals (locals t |+ (n, w)) t)) es = MAP SOME ev).
    { apply eval_upd_notin_vars; [exact Hm|]. intros Hin. apply (Hd n); [left; reflexivity|].
      cbn [MAP List.map FLAT List.concat]. apply in_or_app; right; exact Hin. }
    assert (Hd' : distinct_lists ns (FLAT (MAP var_cexp es))).
    { apply distinct_lists_iff. intros x Hx Hy. apply (Hd x); [right; exact Hx|].
      cbn [MAP List.map FLAT List.concat]. apply in_or_app; right; exact Hy. }
    assert (Hl' : LENGTH ns = LENGTH es) by (rewrite !LENGTH_length in *; cbn [length] in Hl; lia).
    pose proof (IH ns (set_locals (locals t |+ (n, w)) t) ev p (conj Hm' (conj Hl' (conj Hd' Had)))) as IH'.
    assert (Hst : set_locals (locals (set_locals (locals t |+ (n, w)) t) |++ ZIP (ns, ev))
                     (set_locals (locals t |+ (n, w)) t) =
                   set_locals (locals t |++ ZIP (n :: ns, w :: ev)) t) by (destruct t; reflexivity).
    rewrite Hst in IH'.
    destruct (evaluate (p, set_locals (locals t |++ ZIP (n :: ns, w :: ev)) t)) as [q r] eqn:Ep.
    cbv beta iota in IH' |- *.
    cbn [nested_decs]. cstep. rewrite He. cbv zeta. rewrite IH'. ccbn.
    f_equal.
    assert (Hmap : MAP (FLOOKUP (locals t |+ (n, w))) ns = MAP (FLOOKUP (locals t)) ns).
    { apply map_ext_in. intros k Hk. rewrite FLOOKUP_UPDATE. destruct (decide (n = k)) as [->|]; [|reflexivity].
      exfalso. apply MEM_In in Hk. rewrite Hk in Hn. discriminate. }
    rewrite Hmap. cbn [MAP List.map]. change (ZIP (n :: ns, FLOOKUP (locals t) n :: MAP (FLOOKUP (locals t)) ns))
      with ((n, FLOOKUP (locals t) n) :: ZIP (ns, MAP (FLOOKUP (locals t)) ns)). cbn [FOLDL].
    rewrite res_var_FOLDL_comm by (intros Hin; apply MEM_In in Hin; rewrite Hin in Hn; discriminate).
    destruct r; reflexivity.
Qed.

End Nested.

(** ** Assigned variables of compiled programs *)

Section Assigned.
Context {a : N}.

(** Induction on panLang programs with an induction hypothesis for the
    handler program of [Call] (Galette-only). *)
Lemma pan_prog_ind (P : panLang.prog a -> Prop)
    (Hskip : P panLang.Skip)
    (Hdec : forall v sh e p, P p -> P (panLang.Dec v sh e p))
    (Hassign : forall vk v e, P (panLang.Assign vk v e))
    (Hprim : forall v pop es, P (panLang.Primitive v pop es))
    (Hstore : forall e1 e2, P (panLang.Store e1 e2))
    (Hs32 : forall e1 e2, P (panLang.Store32 e1 e2))
    (Hsb : forall e1 e2, P (panLang.StoreByte e1 e2))
    (Hseq : forall p q, P p -> P q -> P (panLang.Seq p q))
    (Hif : forall e p q, P p -> P q -> P (panLang.If e p q))
    (Hwhile : forall e p, P p -> P (panLang.While e p))
    (Hbrk : P panLang.Break) (Hcont : P panLang.Continue)
    (Hcall : forall rt f es,
        match rt with SOME (_, SOME (_, (_, p))) => P p | _ => True end ->
        P (panLang.Call rt f es))
    (Hdcall : forall v sh f es p, P p -> P (panLang.DecCall v sh f es p))
    (Hext : forall f e1 e2 e3 e4, P (panLang.ExtCall f e1 e2 e3 e4))
    (Hraise : forall eid e, P (panLang.Raise eid e))
    (Hret : forall e, P (panLang.Return e))
    (Hshl : forall op vk v e, P (panLang.ShMemLoad op vk v e))
    (Hshs : forall op e1 e2, P (panLang.ShMemStore op e1 e2))
    (Htick : P panLang.Tick)
    (Hannot : forall m1 m2, P (panLang.Annot m1 m2)) : forall p, P p.
Proof.
  fix rec 1. intros p. destruct p.
  - apply Hskip.
  - apply Hdec, rec.
  - apply Hassign.
  - apply Hprim.
  - apply Hstore.
  - apply Hs32.
  - apply Hsb.
  - apply Hseq; apply rec.
  - apply Hif; apply rec.
  - apply Hwhile, rec.
  - apply Hbrk.
  - apply Hcont.
  - apply Hcall. destruct o as [[r [[e0 [v0 p0]]|]]|]; [apply rec|exact Logic.I|exact Logic.I].
  - apply Hdcall, rec.
  - apply Hext.
  - apply Hraise.
  - apply Hret.
  - apply Hshl.
  - apply Hshs.
  - apply Htick.
  - apply Hannot.
Qed.

Lemma In_FILTER_negb_MEM (x : N) ns l : In x (FILTER (fun y => negb (MEM y ns)) l) -> In x l /\ ~ In x ns.
Proof.
  intros H. apply filter_In in H as [H1 H2]. split; [exact H1|]. intros Hn.
  apply MEM_In in Hn. rewrite Hn in H2. discriminate.
Qed.

Lemma ctxt_upd_ok (ctxt : context a) v sh x k :
  ctxt_max (vmax ctxt) (vars ctxt) ->
  (forall v' sh' ns', FLOOKUP (vars ctxt) v' = SOME (sh', ns') -> ~ MEM x ns') ->
  x <= vmax ctxt ->
  let nvars := GENLIST (fun y => vmax ctxt + SUC y) k in
  let nctxt := {| vars := FUPDATE (vars ctxt) (v, (sh, nvars)); funcs := funcs ctxt;
                  eids := eids ctxt; vmax := vmax ctxt + k |} in
  ctxt_max (vmax nctxt) (vars nctxt) /\
  (forall v' sh' ns', FLOOKUP (vars nctxt) v' = SOME (sh', ns') -> ~ MEM x ns') /\
  x <= vmax nctxt.
Proof.
  intros Hm Hx Hle nvars nctxt. cbn [vars vmax nctxt]. split; [|split; [|lia]].
  - split; [lia|]. intros v' a0 xs Hv y Hy. rewrite FLOOKUP_UPDATE in Hv.
    destruct (decide (v = v')) as [<-|].
    + injection Hv as <- <-. apply MEM_In, In_GENLIST_iff in Hy as (i & Hi & ->). lia.
    + destruct Hm as [_ Hm]. specialize (Hm _ _ _ Hv _ Hy). lia.
  - intros v' sh' ns' Hv Hn. rewrite FLOOKUP_UPDATE in Hv. destruct (decide (v = v')) as [<-|].
    + injection Hv as <- <-. apply MEM_In, In_GENLIST_iff in Hn as (i & Hi & ->). lia.
    + exact (Hx _ _ _ Hv Hn).
Qed.

Lemma exp_hdl_assigned (ctxt : context a) evar x :
  In x (assigned_free_vars (exp_hdl (a := a) (vars ctxt) evar)) ->
  exists v sh ns, FLOOKUP (vars ctxt) v = SOME (sh, ns) /\ In x ns.
Proof.
  unfold exp_hdl. destruct (FLOOKUP (vars ctxt) evar) as [[sh ns]|] eqn:Ev; [|intros []].
  rewrite nested_seq_assigned_free_vars_eq by (rewrite length_load_globals_eq_read_size; reflexivity).
  intros H. exists evar, sh, ns. split; assumption.
Qed.

Lemma wrap_rt_some {A} (o : option (shape * list A)) sh ns : wrap_rt o = SOME (sh, ns) -> o = SOME (sh, ns).
Proof. destruct o as [[[| |] [|? ?]]|]; cbn; congruence. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "not_mem_context_assigned_mem_gt" *)
Theorem not_mem_context_assigned_mem_gt : forall (ctxt : context a) p x,
  ctxt_max (vmax ctxt) (vars ctxt) /\
  (forall v sh ns', FLOOKUP (vars ctxt) v = SOME (sh, ns') -> ~ MEM x ns') /\
  x <= vmax ctxt ->
  ~ MEM x (assigned_free_vars (compile ctxt p)).
Proof.
  intros ctxt p; revert ctxt. induction p using pan_prog_ind; intros ctxt x (Hm & Hx & Hle) Hmem;
    apply MEM_In in Hmem; cbn [compile] in Hmem.
  - exact Hmem.
  - (* Dec *)
    destruct (compile_exp ctxt e) as [es sh'] eqn:Ece.
    destruct (decide (size_of_shape sh' = LENGTH es)) as [Hl|]; [|exact Hmem].
    rewrite assigned_free_vars_nested_decs_append in Hmem by (rewrite LENGTH_GENLIST'; exact Hl).
    apply In_FILTER_negb_MEM in Hmem as [Hmem _].
    destruct (ctxt_upd_ok ctxt v sh' x (size_of_shape sh') Hm Hx Hle) as (A & B & C).
    exact (IHp _ x (conj A (conj B C)) (proj2 (MEM_In _ _) Hmem)).
  - (* Assign *)
    destruct vk; [|exact Hmem]. destruct (compile_exp ctxt e) as [es sh'] eqn:Ece.
    destruct (FLOOKUP (vars ctxt) v) as [[vshp ns]|] eqn:Ev; [|exact Hmem].
    destruct (decide (LENGTH ns = LENGTH es)) as [Hl|]; [|exact Hmem].
    destruct (distinct_lists ns _).
    + rewrite nested_seq_assigned_free_vars_eq in Hmem by exact Hl. exact (Hx _ _ _ Ev (proj2 (MEM_In _ _) Hmem)).
    + rewrite assigned_free_vars_nested_decs_append in Hmem by (rewrite LENGTH_GENLIST'; exact Hl).
      apply In_FILTER_negb_MEM in Hmem as [Hmem _].
      rewrite nested_seq_assigned_free_vars_eq in Hmem by (rewrite LENGTH_MAP', LENGTH_GENLIST'; reflexivity).
      exact (Hx _ _ _ Ev (proj2 (MEM_In _ _) Hmem)).
  - (* Primitive *)
    destruct (FLOOKUP (vars ctxt) v) as [[vshp ns]|] eqn:Ev; [|exact Hmem]. cbv zeta in Hmem.
    rewrite assigned_free_vars_nested_decs_append in Hmem by (rewrite LENGTH_GENLIST'; reflexivity).
    apply In_FILTER_negb_MEM in Hmem as [Hmem _]. cbn [assigned_free_vars] in Hmem.
    exact (Hx _ _ _ Ev (proj2 (MEM_In _ _) Hmem)).
  - (* Store *)
    destruct (compile_exp ctxt e1) as [[|e es'] sh'] eqn:E1; [exact Hmem|].
    destruct (compile_exp ctxt e2) as [es sh] eqn:E2.
    destruct (decide (size_of_shape sh = LENGTH es)) as [Hl|]; [|exact Hmem].
    rewrite assigned_free_vars_nested_decs_append in Hmem by (cbn [LENGTH]; rewrite LENGTH_GENLIST'; lia).
    apply In_FILTER_negb_MEM in Hmem as [Hmem _]. rewrite assigned_free_vars_seq_store_empty in Hmem. exact Hmem.
  - destruct (compile_exp ctxt e1) as [[|? ?] ?], (compile_exp ctxt e2) as [[|? ?] ?]; exact Hmem.
  - destruct (compile_exp ctxt e1) as [[|? ?] ?], (compile_exp ctxt e2) as [[|? ?] ?]; exact Hmem.
  - cbn [assigned_free_vars] in Hmem. apply in_app_or in Hmem as [H1|H1].
    + exact (IHp1 _ x (conj Hm (conj Hx Hle)) (proj2 (MEM_In _ _) H1)).
    + exact (IHp2 _ x (conj Hm (conj Hx Hle)) (proj2 (MEM_In _ _) H1)).
  - destruct (compile_exp ctxt e) as [[|ce ces] sh] eqn:Ece; [exact Hmem|].
    cbn [assigned_free_vars] in Hmem. apply in_app_or in Hmem as [H1|H1].
    + exact (IHp1 _ x (conj Hm (conj Hx Hle)) (proj2 (MEM_In _ _) H1)).
    + exact (IHp2 _ x (conj Hm (conj Hx Hle)) (proj2 (MEM_In _ _) H1)).
  - destruct (compile_exp ctxt e) as [[|ce ces] sh] eqn:Ece; [exact Hmem|].
    cbn [assigned_free_vars] in Hmem. exact (IHp _ x (conj Hm (conj Hx Hle)) (proj2 (MEM_In _ _) Hmem)).
  - exact Hmem.
  - exact Hmem.
  - (* Call *)
    cbv zeta in Hmem. set (args := FLAT (MAP FST (MAP (compile_exp ctxt) es))) in Hmem.
    destruct rt as [[ret hdl]|]; [|exact Hmem].
    assert (Hh : forall eid evar p0, hdl = SOME (eid, (evar, p0)) ->
                 ~ In x (assigned_free_vars (Seq (exp_hdl (vars ctxt) evar) (compile ctxt p0)))).
    { intros eid evar p0 -> Hin. cbn [assigned_free_vars] in Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (exp_hdl_assigned ctxt evar x Hin) as (v' & sh' & ns' & Hv' & Hn').
        exact (Hx _ _ _ Hv' (proj2 (MEM_In _ _) Hn')).
      - exact (H ctxt x (conj Hm (conj Hx Hle)) (proj2 (MEM_In _ _) Hin)). }
    destruct ret as [[rk rt]|].
    + destruct (wrap_rt (FLOOKUP (vars ctxt) rt)) as [[sh ns]|] eqn:Ew.
      * apply wrap_rt_some in Ew.
        assert (Hns : ~ In x ns) by (intros Hin; exact (Hx _ _ _ Ew (proj2 (MEM_In _ _) Hin))).
        destruct hdl as [[eid [evar p0]]|].
        -- destruct (FLOOKUP (eids ctxt) eid); cbn [assigned_free_vars] in Hmem;
             [apply in_app_or in Hmem as [Hmem|Hmem]; [exact (Hns Hmem)|exact (Hh _ _ _ eq_refl Hmem)]|exact (Hns Hmem)].
        -- cbn [assigned_free_vars] in Hmem. exact (Hns Hmem).
      * destruct hdl as [[eid [evar p0]]|]; [|exact Hmem].
        destruct (FLOOKUP (eids ctxt) eid); [|exact Hmem].
        cbn [assigned_free_vars app] in Hmem. exact (Hh _ _ _ eq_refl Hmem).
    + set (rts := match FLOOKUP (funcs ctxt) f with
                  | NONE => [] | SOME (_, rshape) => GENLIST (fun y => vmax ctxt + SUC y) (size_of_shape rshape) end)
        in Hmem.
      assert (Hl : LENGTH rts = LENGTH (REPLICATE (LENGTH rts) (@Const a (n2w 0))))
        by (rewrite LENGTH_REPLICATE; reflexivity).
      destruct hdl as [[eid [evar p0]]|].
      * destruct (FLOOKUP (eids ctxt) eid);
          rewrite assigned_free_vars_nested_decs_append in Hmem by exact Hl;
          apply In_FILTER_negb_MEM in Hmem as [Hmem Hnr]; cbn [assigned_free_vars] in Hmem;
          [apply in_app_or in Hmem as [Hmem|Hmem]; [exact (Hnr Hmem)|exact (Hh _ _ _ eq_refl Hmem)]|exact (Hnr Hmem)].
      * rewrite assigned_free_vars_nested_decs_append in Hmem by exact Hl.
        apply In_FILTER_negb_MEM in Hmem as [Hmem Hnr]. cbn [assigned_free_vars] in Hmem. exact (Hnr Hmem).
  - (* DecCall *)
    cbv zeta in Hmem.
    rewrite assigned_free_vars_nested_decs_append in Hmem
      by (rewrite LENGTH_REPLICATE, LENGTH_GENLIST'; reflexivity).
    apply In_FILTER_negb_MEM in Hmem as [Hmem Hnv]. cbn [assigned_free_vars] in Hmem.
    apply in_app_or in Hmem as [H1|H1]; [contradiction|].
    destruct (ctxt_upd_ok ctxt v sh x (size_of_shape sh) Hm Hx Hle) as (A & B & C).
    exact (IHp _ x (conj A (conj B C)) (proj2 (MEM_In _ _) H1)).
  - (* ExtCall *)
    cbv zeta in Hmem. repeat match type of Hmem with context [match ?y with _ => _ end] =>
      destruct y; cbn [assigned_free_vars] in Hmem; try exact Hmem end.
  - (* Raise *)
    destruct (FLOOKUP (eids ctxt) eid); [|exact Hmem].
    destruct (compile_exp ctxt e) as [ces sh] eqn:Ece. destruct (decide _) as [Hl|]; [|exact Hmem].
    cbn [assigned_free_vars] in Hmem. rewrite app_nil_r in Hmem.
    rewrite assigned_free_vars_nested_decs_append in Hmem by (rewrite LENGTH_GENLIST'; exact Hl).
    apply In_FILTER_negb_MEM in Hmem as [Hmem _]. rewrite assigned_free_vars_store_globals_empty in Hmem.
    exact Hmem.
  - destruct (compile_exp ctxt e) as [ces sh]. destruct (decide _); exact Hmem.
  - (* ShMemLoad *)
    destruct vk; [|exact Hmem]. destruct (compile_exp ctxt e) as [[|a0 ?] ?]; [exact Hmem|].
    destruct (FLOOKUP (vars ctxt) v) as [[? [|r' ?]]|] eqn:Ev; try exact Hmem.
    cbn [assigned_free_vars] in Hmem. destruct Hmem as [<-|[]].
    apply (Hx _ _ _ Ev). apply MEM_In. left; reflexivity.
  - (* ShMemStore *)
    destruct (compile_exp ctxt e1) as [[|e' ?] ?], (compile_exp ctxt e2) as [[|a0 ?] ?]; try exact Hmem.
    cbn [assigned_free_vars FILTER List.filter] in Hmem.
    destruct (bool_decide _) eqn:Eb; [apply bool_decide_spec in Eb; contradiction Eb|exact Hmem].
    destruct Hmem as [<-|[]]. reflexivity.
  - exact Hmem.
  - exact Hmem.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "rewritten_context_unassigned" *)
Theorem rewritten_context_unassigned : forall p (nctxt : context a) v ctxt ns nvars sh sh',
  nctxt = {| vars := FUPDATE (vars ctxt) (v, (sh, nvars)); funcs := funcs ctxt; eids := eids ctxt;
             vmax := vmax ctxt + size_of_shape sh |} /\
  FLOOKUP (vars ctxt) v = SOME (sh', ns) /\
  no_overlap (vars ctxt) /\
  ctxt_max (vmax ctxt) (vars ctxt) /\
  no_overlap (vars nctxt) /\
  ctxt_max (vmax nctxt) (vars nctxt) /\
  distinct_lists nvars ns ->
  distinct_lists ns (assigned_free_vars (compile nctxt p)).
Proof.
  intros p nctxt v ctxt ns nvars sh sh' (-> & Hv & Hno & Hmx & Hno' & Hmx' & Hd).
  apply distinct_lists_iff. intros k Hk Hin.
  refine (not_mem_context_assigned_mem_gt _ p k _ (proj2 (MEM_In _ _) Hin)).
  split; [exact Hmx'|]. split.
  - intros v'' sh'' ns' Hv'' Hm. cbn [vars] in Hv''. rewrite FLOOKUP_UPDATE in Hv''.
    destruct (decide (v = v'')) as [<-|Hne].
    + injection Hv'' as _ <-. apply MEM_In in Hm. exact (proj1 (distinct_lists_iff _ _) Hd k Hm Hk).
    + apply Hne. destruct Hno as [_ Hno]. apply (Hno v v'' sh' sh'' ns ns'). split; [exact Hv|]. split; [exact Hv''|].
      intros Hdj. exact (proj1 (DISJOINT_set_iff ns ns') Hdj k Hk (proj1 (MEM_In _ _) Hm)).
  - cbn [vmax]. destruct Hmx as [_ Hmx]. specialize (Hmx _ _ _ Hv k (proj2 (MEM_In _ _) Hk)). lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_max_el_leq" *)
Theorem ctxt_max_el_leq : forall (ctxt : context a) v sh ns n,
  ctxt_max (vmax ctxt) (vars ctxt) /\ FLOOKUP (vars ctxt) v = SOME (sh, ns) /\ n < LENGTH ns ->
  EL n ns <= vmax ctxt.
Proof.
  intros ctxt v sh ns n ([_ Hmx] & Hv & Hn). apply (Hmx _ _ _ Hv). apply MEM_In.
  rewrite EL_nth by exact Hn. apply nth_In. rewrite LENGTH_length in Hn. lia.
Qed.

End Assigned.

(** ** [pc_compile_correct] *)

Section PC.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "globals_lookup_def" *)
Definition globals_lookup (t : state a ffi_t) (v : panSem.v a) : option (list (word_lab a)) :=
  OPT_MMAP (FLOOKUP (globals t)) (GENLIST (fun x => n2w x) (size_of_shape (shape_of v))).

Definition pc_post (res : option (panSem.result a)) (s1 : panSem.state a ffi_t)
    (t1 : state a ffi_t) (ctxt : context a) (res1 : option (result a)) : Prop :=
  match res with
  | NONE => res1 = NONE /\ locals_rel ctxt (panSem.locals s1) (locals t1)
  | SOME panSem.Error => False
  | SOME panSem.TimeOut => res1 = SOME TimeOut
  | SOME panSem.Break => res1 = SOME (Break 0) /\ locals_rel ctxt (panSem.locals s1) (locals t1)
  | SOME panSem.Continue =>
      res1 = SOME (Continue 0) /\ locals_rel ctxt (panSem.locals s1) (locals t1)
  | SOME (panSem.Return v) => res1 = SOME (Return (flatten v)) /\ panProps.is_wf_shape_nil (shape_of v)
  | SOME (panSem.Exception eid v') =>
      match FLOOKUP (eids ctxt) eid with
      | NONE => False
      | SOME n =>
          res1 = SOME (Exception n) /\ panProps.is_wf_shape_nil (shape_of v') /\
          (1 <= size_of_shape (shape_of v') ->
           globals_lookup t1 v' = SOME (flatten v') /\
           size_of_shape (shape_of v') <= 32)
      end
  | SOME (panSem.FinalFFI f) => res1 = SOME (FinalFFI f)
  end.

Definition pc_P (prog : panLang.prog a) (s : panSem.state a ffi_t) : Prop :=
  forall res s1 (t : state a ffi_t) ctxt,
    panSem.evaluate (prog, s) = (res, s1) /\ res <> SOME panSem.Error /\ state_rel s t /\
    code_rel ctxt (panSem.code s) (code t) /\ excp_rel (eids ctxt) (panSem.eshapes s) /\
    locals_rel ctxt (panSem.locals s) (locals t) /\ panProps.localised_prog prog ->
    exists res1 t1,
      evaluate (compile ctxt prog, t) = (res1, t1) /\ state_rel s1 t1 /\
      code_rel ctxt (panSem.code s1) (code t1) /\ excp_rel (eids ctxt) (panSem.eshapes s1) /\
      pc_post res s1 t1 ctxt res1.

Ltac pc_intro := intros ?res ?s1 ?t ?ctxt (?H & ?Hne & ?Hs & ?Hc & ?He & ?Hl & ?Hloc).

Lemma pc_Skip s : pc_P panLang.Skip s.
Proof.
  pc_intro. pstep H. injection H as <- <-. cbn [compile]. cstep.
  eexists _, _. split; [reflexivity|]. cbn [pc_post]. csplit; assumption || reflexivity.
Qed.

Lemma pc_Break s : pc_P panLang.Break s.
Proof.
  pc_intro. pstep H. injection H as <- <-. cbn [compile]. cstep.
  eexists _, _. split; [reflexivity|]. cbn [pc_post]. csplit; assumption || reflexivity.
Qed.

Lemma pc_Continue s : pc_P panLang.Continue s.
Proof.
  pc_intro. pstep H. injection H as <- <-. cbn [compile]. cstep.
  eexists _, _. split; [reflexivity|]. cbn [pc_post]. csplit; assumption || reflexivity.
Qed.

Lemma pc_Annot s m1 m2 : pc_P (panLang.Annot m1 m2) s.
Proof.
  pc_intro. pstep H. injection H as <- <-. cbn [compile]. cstep.
  eexists _, _. split; [reflexivity|]. cbn [pc_post]. csplit; assumption || reflexivity.
Qed.

Lemma pc_Tick s : pc_P panLang.Tick s.
Proof.
  pc_intro. pstep H. cbn [compile]. cstep.
  pose proof Hs as (_ & _ & _ & _ & _ & Hck & _). rewrite <- Hck.
  destruct (panSem.clock s =? 0); injection H as <- <-.
  - eexists _, _. split; [reflexivity|]. unfold panSem.empty_locals, empty_locals.
    split; [srel Hs|]. pcbn; ccbn. csplit; assumption || reflexivity.
  - eexists _, _. split; [reflexivity|]. unfold panSem.dec_clock, dec_clock.
    split; [srel Hs|]. pcbn; ccbn. cbn [pc_post]. csplit; assumption || reflexivity.
Qed.

Lemma pc_post_not_none r s1 t1 ctxt (res1 : option (result a)) :
  pc_post (SOME r) s1 t1 ctxt res1 -> res1 <> NONE.
Proof.
  intros Hp ->. destruct r as [| | | |v|eid v|f]; cbn [pc_post] in Hp.
  - exact Hp.
  - discriminate Hp.
  - destruct Hp as [Hp _]; discriminate Hp.
  - destruct Hp as [Hp _]; discriminate Hp.
  - destruct Hp as [Hp _]; discriminate Hp.
  - destruct (FLOOKUP (eids ctxt) eid); [destruct Hp as [Hp _]; discriminate Hp|exact Hp].
  - discriminate Hp.
Qed.

Lemma pc_Seq s p q :
  (forall p' s', panSem.eval_lt (p', s') (panLang.Seq p q, s) -> pc_P p' s') ->
  pc_P (panLang.Seq p q) s.
Proof.
  intros IH. pc_intro. pstep H. cbn [compile]. cstep. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hlp Hlq].
  destruct (panSem.evaluate (p, s)) as [r1 u1] eqn:E1.
  assert (Hr1 : r1 <> SOME panSem.Error) by (intros ->; injection H as <- <-; congruence).
  destruct (IH p s ltac:(right; split; [reflexivity|cbn [fst snd panSem.psize]; lia])
              r1 u1 t ctxt (conj E1 (conj Hr1 (conj Hs (conj Hc (conj He (conj Hl Hlp)))))))
    as (res1 & t1 & Ev1 & Hs1 & Hc1 & He1 & Hp1).
  rewrite Ev1. destruct r1 as [r1|].
  - injection H as <- <-. pose proof (pc_post_not_none _ _ _ _ _ Hp1) as Hn.
    destruct res1 as [res1|]; [|contradiction].
    exists (SOME res1), t1. split; [reflexivity|]. csplit; assumption.
  - cbn [pc_post] in Hp1. destruct Hp1 as [-> Hl1].
    pose proof (panSem.evaluate_clock _ _ _ _ E1) as Hcl.
    apply (IH q u1 ltac:(unfold panSem.eval_lt; cbn [fst snd panSem.psize];
                          destruct (N.lt_ge_cases (panSem.clock u1) (panSem.clock s)); [left; lia|right; split; lia])
             res s1 t1 ctxt). csplit; assumption.
Qed.

Lemma pc_If s e c1 c2 :
  (forall p' s', panSem.eval_lt (p', s') (panLang.If e c1 c2, s) -> pc_P p' s') ->
  pc_P (panLang.If e c1 c2) s.
Proof.
  intros IH. pc_intro. pstep H. cbn [compile]. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hloc Hl2]. apply andb_prop in Hloc as [Hle Hl1].
  destruct (panSem.eval s e) as [[[w]|vs|nm fl]|] eqn:Ee; try (injection H as <- <-; congruence).
  destruct (compile_exp ctxt e) as [ces sh] eqn:Ece.
  destruct (compile_exp_val_rel s e _ t ctxt ces sh (conj Ee (conj Hs (conj Hc (conj Hl (conj Hle Ece))))))
    as (A & _).
  destruct ces as [|ce ces]; [discriminate A|]. cbn [MAP List.map flatten] in A. injection A as A _.
  cstep. rewrite A.
  destruct (negb _).
  - apply (IH c1 s ltac:(right; split; [reflexivity|cbn [fst snd panSem.psize]; lia])). csplit; assumption.
  - apply (IH c2 s ltac:(right; split; [reflexivity|cbn [fst snd panSem.psize]; lia])). csplit; assumption.
Qed.

Lemma pc_Return s e : pc_P (panLang.Return e) s.
Proof.
  pc_intro. pstep H. cbn [compile]. cbn [panProps.localised_prog] in Hloc.
  destruct (panSem.eval s e) as [v|] eqn:Ee; [|injection H as <- <-; congruence].
  destruct (_ <=? 32) eqn:E32; [|injection H as <- <-; congruence]. injection H as <- <-.
  destruct (compile_exp ctxt e) as [ces sh] eqn:Ece.
  destruct (compile_exp_val_rel s e _ t ctxt ces sh (conj Ee (conj Hs (conj Hc (conj Hl (conj Hloc Ece))))))
    as (A & B & C & D).
  assert (Hlen : LENGTH (flatten v) = size_of_shape sh)
    by (rewrite <- C; apply panProps.length_flatten_eq_size_of_shape; rewrite C; exact D).
  destruct (decide (size_of_shape sh = 0)) as [Hz|Hz].
  - cstep. cbn [OPT_MMAP].
    assert (Hf : flatten v = []) by (destruct (flatten v); [reflexivity|cbn [LENGTH] in Hlen; lia]).
    eexists _, _. split; [reflexivity|]. unfold panSem.empty_locals, empty_locals.
    split; [srel Hs|]. pcbn; ccbn. csplit; try assumption. cbn [pc_post]. rewrite Hf.
    split; [reflexivity|rewrite C; exact D].
  - cstep. apply opt_mmap_eq_some in A. rewrite A.
    eexists _, _. split; [reflexivity|]. unfold panSem.empty_locals, empty_locals.
    split; [srel Hs|]. pcbn; ccbn. cbn [pc_post]. csplit; try assumption; try reflexivity.
    rewrite C; exact D.
Qed.

Lemma pc_Store32 s dst src : pc_P (panLang.Store32 dst src) s.
Proof.
  pc_intro. pstep H. cbn [compile]. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hl1 Hl2].
  destruct (panSem.eval s dst) as [[[adr]|vs|nm fl]|] eqn:E1; try (injection H as <- <-; congruence).
  destruct (panSem.eval s src) as [[[w]|vs|nm fl]|] eqn:E2; try (injection H as <- <-; congruence).
  destruct (panSem.mem_store_32 _ _ _ _ _) as [m|] eqn:Em; injection H as <- <-; [|congruence].
  destruct (compile_exp ctxt dst) as [c1 sh1] eqn:Ec1. destruct (compile_exp ctxt src) as [c2 sh2] eqn:Ec2.
  destruct (compile_exp_val_rel s dst _ t ctxt c1 sh1 (conj E1 (conj Hs (conj Hc (conj Hl (conj Hl1 Ec1))))))
    as (A1 & _).
  destruct (compile_exp_val_rel s src _ t ctxt c2 sh2 (conj E2 (conj Hs (conj Hc (conj Hl (conj Hl2 Ec2))))))
    as (A2 & _).
  destruct c1 as [|h1 c1]; [discriminate A1|]. destruct c2 as [|h2 c2]; [discriminate A2|].
  cbn [MAP List.map flatten] in A1, A2. injection A1 as A1 _. injection A2 as A2 _.
  cstep. rewrite A1, A2.
  pose proof Hs as (Hm & Hma & _ & _ & _ & _ & Hbe & _). rewrite <- Hm, <- Hma, <- Hbe, Em.
  eexists _, _. split; [reflexivity|]. unfold panSem.set_memory, set_memory.
  split; [srel Hs|]. pcbn; ccbn. cbn [pc_post]. csplit; try assumption; reflexivity.
Qed.

Lemma pc_StoreByte s dst src : pc_P (panLang.StoreByte dst src) s.
Proof.
  pc_intro. pstep H. cbn [compile]. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hl1 Hl2].
  destruct (panSem.eval s dst) as [[[adr]|vs|nm fl]|] eqn:E1; try (injection H as <- <-; congruence).
  destruct (panSem.eval s src) as [[[w]|vs|nm fl]|] eqn:E2; try (injection H as <- <-; congruence).
  destruct (panSem.mem_store_byte _ _ _ _ _) as [m|] eqn:Em; injection H as <- <-; [|congruence].
  destruct (compile_exp ctxt dst) as [c1 sh1] eqn:Ec1. destruct (compile_exp ctxt src) as [c2 sh2] eqn:Ec2.
  destruct (compile_exp_val_rel s dst _ t ctxt c1 sh1 (conj E1 (conj Hs (conj Hc (conj Hl (conj Hl1 Ec1))))))
    as (A1 & _).
  destruct (compile_exp_val_rel s src _ t ctxt c2 sh2 (conj E2 (conj Hs (conj Hc (conj Hl (conj Hl2 Ec2))))))
    as (A2 & _).
  destruct c1 as [|h1 c1]; [discriminate A1|]. destruct c2 as [|h2 c2]; [discriminate A2|].
  cbn [MAP List.map flatten] in A1, A2. injection A1 as A1 _. injection A2 as A2 _.
  cstep. rewrite A1, A2.
  pose proof Hs as (Hm & Hma & _ & _ & _ & _ & Hbe & _). rewrite <- Hm, <- Hma, <- Hbe, Em.
  eexists _, _. split; [reflexivity|]. unfold panSem.set_memory, set_memory.
  split; [srel Hs|]. pcbn; ccbn. cbn [pc_post]. csplit; try assumption; reflexivity.
Qed.

Lemma pc_While s e c :
  (forall p' s', panSem.eval_lt (p', s') (panLang.While e c, s) -> pc_P p' s') ->
  pc_P (panLang.While e c) s.
Proof.
  intros IH. pc_intro. assert (Hrec := H). pstep H. cbn [compile]. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hle Hlc].
  destruct (panSem.eval s e) as [[[w]|vs|nm fl]|] eqn:Ee; try (injection H as <- <-; congruence).
  destruct (compile_exp ctxt e) as [ces sh] eqn:Ece.
  destruct (compile_exp_val_rel s e _ t ctxt ces sh (conj Ee (conj Hs (conj Hc (conj Hl (conj Hle Ece))))))
    as (A & _).
  destruct ces as [|ce ces]; [discriminate A|]. cbn [MAP List.map flatten] in A. injection A as A _.
  cstep. rewrite A.
  destruct (negb _) eqn:Ew.
  2:{ injection H as <- <-. eexists _, _. split; [reflexivity|]. cbn [pc_post]. csplit; assumption || reflexivity. }
  pose proof Hs as (_ & _ & _ & _ & _ & Hck & _). rewrite <- Hck.
  destruct (panSem.clock s =? 0) eqn:Ec0.
  { injection H as <- <-. eexists _, _. split; [reflexivity|]. unfold panSem.empty_locals, empty_locals.
    split; [srel Hs|]. pcbn; ccbn. cbn [pc_post]. csplit; assumption || reflexivity. }
  apply N.eqb_neq in Ec0.
  destruct (panSem.evaluate (c, panSem.dec_clock s)) as [r1 u1] eqn:E1.
  assert (Hr1 : r1 <> SOME panSem.Error) by (intros ->; injection H as <- <-; congruence).
  assert (Hsd : state_rel (panSem.dec_clock s) (dec_clock t))
    by (unfold panSem.dec_clock, dec_clock; srel Hs).
  destruct (IH c (panSem.dec_clock s) ltac:(left; cbn [fst snd]; unfold panSem.dec_clock; pcbn; lia)
              r1 u1 (dec_clock t) ctxt (conj E1 (conj Hr1 (conj Hsd (conj Hc (conj He (conj Hl Hlc)))))))
    as (res1 & t1 & Ev1 & Hs1 & Hc1 & He1 & Hp1).
  rewrite Ev1. pose proof (panSem.evaluate_clock _ _ _ _ E1) as Hcl.
  assert (Rec : panSem.evaluate (panLang.While e c, u1) = (res, s1) ->
                locals_rel ctxt (panSem.locals u1) (locals t1) ->
                exists res2 t2, evaluate (While ce (compile ctxt c), t1) = (res2, t2) /\ state_rel s1 t2 /\
                  code_rel ctxt (panSem.code s1) (code t2) /\ excp_rel (eids ctxt) (panSem.eshapes s1) /\
                  pc_post res s1 t2 ctxt res2).
  { intros Hw Hl1.
    pose proof (IH (panLang.While e c) u1 ltac:(left; cbn [fst snd]; unfold panSem.dec_clock in Hcl; pcbn; lia)
                  res s1 t1 ctxt) as IH2.
    cbn [compile] in IH2. rewrite Ece in IH2. apply IH2. csplit; try assumption.
    cbn [panProps.localised_prog]. rewrite Hle, Hlc. reflexivity. }
  destruct r1 as [[| | | |v|eid v|f]|]; cbn [pc_post] in Hp1; try congruence.
  - subst res1. injection H as <- <-. eexists _, _. split; [reflexivity|]. csplit; assumption || reflexivity.
  - destruct Hp1 as [-> Hl1]. injection H as <- <-. eexists _, _. split; [reflexivity|]. cbn [pc_post].
    csplit; assumption || reflexivity.
  - destruct Hp1 as [-> Hl1]. exact (Rec H Hl1).
  - destruct Hp1 as [-> Hw1]. injection H as <- <-. eexists _, _. split; [reflexivity|].
    cbn [pc_post]. csplit; assumption || reflexivity.
  - injection H as <- <-. destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En; [|contradiction].
    destruct Hp1 as [-> [Hw1 Hg1]]. eexists _, _. split; [reflexivity|]. cbn [pc_post]. rewrite En.
    csplit; assumption || reflexivity.
  - subst res1. injection H as <- <-. eexists _, _. split; [reflexivity|]. csplit; assumption || reflexivity.
  - destruct Hp1 as [-> Hl1]. exact (Rec H Hl1).
Qed.

Lemma locals_rel_agree ctxt (lcl : fmap mlstring (panSem.v a)) (L1 L2 : fmap varname (word_lab a)) :
  locals_rel ctxt lcl L1 -> (forall k, k <= vmax ctxt -> FLOOKUP L2 k = FLOOKUP L1 k) ->
  locals_rel ctxt lcl L2.
Proof.
  intros (Hno & Hmx & Hl) Hk. split; [exact Hno|]. split; [exact Hmx|].
  intros vn v Hv. destruct (Hl _ _ Hv) as (ns & vs & H1 & H2 & H3 & H4). exists ns, vs.
  split; [exact H1|]. split; [|split; assumption].
  rewrite <- H2. apply OPT_MMAP_ext_In''. intros k Hin. apply Hk.
  destruct Hmx as [_ Hmx]. apply (Hmx vn _ ns H1), MEM_In, Hin.
Qed.

Lemma locals_rel_assign ctxt (lcl : fmap mlstring (panSem.v a)) (L : fmap varname (word_lab a)) vr v value ns :
  locals_rel ctxt lcl L -> FLOOKUP lcl vr = SOME v -> FLOOKUP (vars ctxt) vr = SOME (shape_of v, ns) ->
  shape_of value = shape_of v -> panProps.is_wf_shape_nil (shape_of value) ->
  LENGTH ns = LENGTH (flatten value) ->
  locals_rel ctxt (lcl |+ (vr, value)) (L |++ ZIP (ns, flatten value)).
Proof.
  intros Hl Hv Hns Hsh Hw Hlen. pose proof Hl as (Hno & Hmx & Hl').
  split; [exact Hno|]. split; [exact Hmx|].
  intros vn v' Hv'. rewrite FLOOKUP_UPDATE in Hv'. destruct (decide (vr = vn)) as [<-|Hne].
  - injection Hv' as <-. exists ns, (flatten value). split; [rewrite Hsh; exact Hns|].
    split; [|split; [reflexivity|exact Hw]].
    apply opt_mmap_some_eq_zip_flookup. split; [|exact Hlen].
    exact (all_distinct_flookup_all_distinct (vars ctxt) vr _ ns (conj Hno Hns)).
  - destruct (Hl' _ _ Hv') as (ns' & vs & H1 & H2 & H3 & H4). exists ns', vs.
    split; [exact H1|]. split; [|split; assumption].
    rewrite opt_mmap_disj_zip_flookup; [exact H2|]. split; [|exact Hlen].
    exact (no_overlap_flookup_distinct (vars ctxt) vr vn _ _ ns ns' (conj Hno (conj Hne (conj Hns H1)))).
Qed.

Lemma compile_exp_vars_le ctxt (lcl : fmap mlstring (panSem.v a)) L e n :
  locals_rel ctxt lcl L -> In n (FLAT (MAP var_cexp (FST (compile_exp ctxt e)))) -> n <= vmax ctxt.
Proof.
  intros (_ & [_ Hmx] & _) Hn. destruct (compile_exp_vars ctxt e n Hn) as (v & shp & ns & H1 & H2).
  exact (Hmx _ _ _ H1 n (proj2 (MEM_In _ _) H2)).
Qed.

Lemma temps_eq (m k : N) : GENLIST (fun x => m + SUC x) k = GENLIST (fun x => SUC x + m) k.
Proof. apply GENLIST_ext. intros; lia. Qed.

Lemma temps_distinct (m k : N) ys : (forall y, In y ys -> y <= m) ->
  distinct_lists (GENLIST (fun x => m + SUC x) k) ys.
Proof.
  intros H. rewrite temps_eq. apply genlist_distinct_max. intros y Hy. apply H, MEM_In, Hy.
Qed.

Lemma temps_all_distinct (m k : N) : ALL_DISTINCT (GENLIST (fun x => m + SUC x) k).
Proof. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & E). lia. Qed.

Lemma temps_gt (m k x : N) : In x (GENLIST (fun x => m + SUC x) k) -> m < x.
Proof. intros H. apply In_GENLIST_iff in H as (i & _ & ->). lia. Qed.

Lemma pc_Assign s vk vr e : pc_P (panLang.Assign vk vr e) s.
Proof.
  pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc. destruct vk; [|discriminate Hloc].
  destruct (panSem.eval s e) as [value|] eqn:Ee; [|injection H as <- <-; congruence].
  unfold panSem.is_valid_value, panSem.lookup_kvar in H.
  destruct (FLOOKUP (panSem.locals s) vr) as [v|] eqn:Ev; [|injection H as <- <-; congruence].
  destruct (bool_decide (shape_of value = shape_of v)) eqn:Esh; [|injection H as <- <-; congruence].
  apply bool_decide_spec in Esh. injection H as <- <-.
  destruct (locals_rel_lookup_ctxt ctxt _ _ vr v (conj Hl Ev)) as (ns & Hns & Hlenv & Hov & Hwv).
  cbn [compile]. destruct (compile_exp ctxt e) as [es sh] eqn:Ece.
  destruct (compile_exp_val_rel s e _ t ctxt es sh (conj Ee (conj Hs (conj Hc (conj Hl (conj Hloc Ece))))))
    as (A & B & <- & D).
  assert (Hlenval : LENGTH (flatten value) = LENGTH (flatten v)).
  { rewrite !panProps.length_flatten_eq_size_of_shape; [congruence| |exact D]. rewrite <- Esh. exact D. }
  assert (Hlen : LENGTH ns = LENGTH es).
  { rewrite B, Hlenv, <- Hlenval. apply panProps.length_flatten_eq_size_of_shape, D. }
  rewrite Hns. destruct (decide (LENGTH ns = LENGTH es)) as [_|C]; [|contradiction].
  assert (Had : ALL_DISTINCT ns)
    by exact (all_distinct_flookup_all_distinct (vars ctxt) vr _ ns (conj (proj1 Hl) Hns)).
  assert (Hpost : forall L, (forall k, k <= vmax ctxt -> FLOOKUP L k = FLOOKUP (locals t |++ ZIP (ns, flatten value)) k) ->
            locals_rel ctxt (panSem.locals (panSem.set_kvar Local vr value s)) L).
  { intros L HL. apply (locals_rel_agree _ _ (locals t |++ ZIP (ns, flatten value))); [|exact HL].
    cbn [panSem.set_kvar]. unfold panSem.set_var. pcbn.
    apply (locals_rel_assign ctxt _ _ vr v); try assumption. congruence. }
  destruct (distinct_lists ns (FLAT (MAP var_cexp es))) eqn:Edl.
  - rewrite (eval_nested_assign_distinct_eq es ns t (flatten value) (flatten v)
               (conj A (conj Hov (conj Edl (conj Had Hlen))))).
    eexists _, _. split; [reflexivity|]. split; [srel Hs|]. cbn [panSem.set_kvar] in *. unfold panSem.set_var.
    pcbn. ccbn. csplit; try assumption. cbn [pc_post]. split; [reflexivity|].
    apply Hpost. intros; reflexivity.
  - set (temps := GENLIST (fun x => vmax ctxt + SUC x) (LENGTH ns)).
    assert (Hvle : forall y, In y (FLAT (MAP var_cexp es)) -> y <= vmax ctxt)
      by (intros y Hy; apply (compile_exp_vars_le ctxt _ _ e y Hl); rewrite Ece; exact Hy).
    assert (Hd1 : distinct_lists temps (FLAT (MAP var_cexp es))) by (apply temps_distinct, Hvle).
    assert (Hnsle : forall y, In y ns -> y <= vmax ctxt)
      by (intros y Hy; destruct Hl as (_ & [_ Hmx] & _); exact (Hmx _ _ _ Hns y (proj2 (MEM_In _ _) Hy))).
    assert (Hd2 : distinct_lists temps ns) by (apply temps_distinct, Hnsle).
    assert (Hadt : ALL_DISTINCT temps) by apply temps_all_distinct.
    assert (Hlt : LENGTH temps = LENGTH es) by (unfold temps; rewrite LENGTH_GENLIST'; exact Hlen).
    pose proof (eval_nested_decs_seq_res_var_eq es temps t (flatten value)
                  (nested_seq (MAP2 Assign ns (MAP Var temps))) (conj A (conj Hlt (conj Hd1 Hadt)))) as N1.
    set (t' := set_locals (locals t |++ ZIP (temps, flatten value)) t) in N1.
    assert (Hlv : LENGTH temps = LENGTH (flatten value)) by (rewrite Hlt, B; symmetry; apply panProps.length_flatten_eq_size_of_shape, D).
    assert (A2 : MAP (eval t') (MAP Var temps) = MAP SOME (flatten value)).
    { apply MAP_eq_EL; [rewrite !LENGTH_MAP'; exact Hlv|]. intros k Hk. rewrite LENGTH_MAP' in Hk.
      rewrite !EL_MAP' by (try rewrite LENGTH_MAP'; lia). cbn [eval]. unfold t'. ccbn.
      apply update_eq_zip_flookup. split; [exact Hadt|]. split; [exact Hlv|exact Hk]. }
    assert (Ho2 : OPT_MMAP (FLOOKUP (locals t')) ns = SOME (flatten v)).
    { unfold t'. ccbn. rewrite opt_mmap_disj_zip_flookup; [exact Hov|]. split; [exact Hd2|exact Hlv]. }
    assert (Hd3 : distinct_lists ns (FLAT (MAP var_cexp (MAP (@Var a) temps)))).
    { rewrite map_var_cexp_eq_var, distinct_lists_commutes. exact Hd2. }
    assert (Hl4 : LENGTH ns = LENGTH (MAP (@Var a) temps)) by (rewrite LENGTH_MAP'; lia).
    rewrite (eval_nested_assign_distinct_eq (MAP Var temps) ns t' (flatten value) (flatten v)
               (conj A2 (conj Ho2 (conj Hd3 (conj Had Hl4))))) in N1.
    cbv beta iota in N1. rewrite N1.
    eexists _, _. split; [reflexivity|]. split; [unfold t'; srel Hs|].
    cbn [panSem.set_kvar] in *. unfold panSem.set_var. pcbn. ccbn. csplit; try assumption.
    cbn [pc_post]. split; [reflexivity|]. apply Hpost. intros k Hk. ccbn.
    assert (Hkt : ~ In k temps) by (intros Hin; apply temps_gt in Hin; lia).
    rewrite FOLDL_res_var_map_lookup. destruct (in_dec _ k temps) as [Hin|_]; [contradiction|].
    unfold t'. ccbn.
    destruct (in_dec (fun x y => decide (x = y)) k (map fst (ZIP (ns, flatten value)))) as [Hin|Hnin].
    + exact (FLOOKUP_FUPDATE_LIST_in _ _ _ _ Hin).
    + rewrite (FLOOKUP_FUPDATE_LIST_notin (ZIP (ns, flatten value)) (locals t |++ ZIP (temps, flatten value)) k Hnin),
        (FLOOKUP_FUPDATE_LIST_notin (ZIP (ns, flatten value)) (locals t) k Hnin).
      apply FLOOKUP_FUPDATE_LIST_notin. intros Hin. apply Hkt. exact (In_map_fst_ZIP _ _ _ Hin).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_map_comp_exp_flat_eq" *)
Theorem eval_map_comp_exp_flat_eq : forall argexps (args : list (panSem.v a)) (s : panSem.state a ffi_t)
    (t : state a ffi_t) ctxt,
  MAP (panSem.eval s) argexps = MAP SOME args /\
  state_rel s t /\ code_rel ctxt (panSem.code s) (code t) /\
  locals_rel ctxt (panSem.locals s) (locals t) /\ EVERY panProps.localised_exp argexps ->
  MAP (eval t) (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) =
  MAP SOME (FLAT (MAP flatten args)).
Proof.
  induction argexps as [|e es IH]; intros [|v vs] s t ctxt (Hm & Hs & Hc & Hl & Hloc);
    try discriminate Hm; [reflexivity|].
  cbn [MAP List.map] in Hm. injection Hm as He Hm. cbn [EVERY] in Hloc. apply andb_prop in Hloc as [Hl1 Hl2].
  cbn [MAP List.map FLAT List.concat]. rewrite !map_app.
  destruct (compile_exp ctxt e) as [ces sh] eqn:Ece.
  destruct (compile_exp_val_rel s e v t ctxt ces sh (conj He (conj Hs (conj Hc (conj Hl (conj Hl1 Ece))))))
    as (A & _). cbn [FST fst]. rewrite A, (IH vs s t ctxt (conj Hm (conj Hs (conj Hc (conj Hl Hl2))))).
  reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pan_primop_crep_primop" *)
Theorem pan_primop_crep_primop : forall pop (vs : list (panSem.v a)) value,
  panSem.pan_primop pop vs = SOME value ->
  crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value).
Proof.
  intros [] vs value H. cbn [panSem.pan_primop] in H.
  destruct (_ && _) eqn:Eb; [|discriminate]. apply andb_prop in Eb as [El Ew]. apply N.eqb_eq in El.
  destruct vs as [|v0 [|v1 [|v2 [|v3 vs]]]]; cbn [LENGTH] in El; try lia.
  cbn [EVERY] in Ew. destruct v0 as [[w0]|? |? ?]; try discriminate Ew.
  destruct v1 as [[w1]|? |? ?]; try discriminate Ew. destruct v2 as [[w2]|? |? ?]; try discriminate Ew.
  cbn in H |- *. destruct (backend_common.word_add_carry w0 w1 w2) as [r c]. injection H as <-. reflexivity.
Qed.

Lemma pc_Primitive s vr pop es : pc_P (panLang.Primitive vr pop es) s.
Proof.
  pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc.
  destruct (OPT_MMAP (panSem.eval s) es) as [vs|] eqn:Eo; [|injection H as <- <-; congruence].
  destruct (panSem.pan_primop pop vs) as [value|] eqn:Ep; [|injection H as <- <-; congruence].
  unfold panSem.is_valid_value, panSem.lookup_kvar in H.
  destruct (FLOOKUP (panSem.locals s) vr) as [v|] eqn:Ev; [|injection H as <- <-; congruence].
  destruct (bool_decide (shape_of value = shape_of v)) eqn:Esh; [|injection H as <- <-; congruence].
  apply bool_decide_spec in Esh. injection H as <- <-.
  destruct (locals_rel_lookup_ctxt ctxt _ _ vr v (conj Hl Ev)) as (ns & Hns & Hlenv & Hov & Hwv).
  apply opt_mmap_eq_some in Eo.
  pose proof (eval_map_comp_exp_flat_eq es vs s t ctxt (conj Eo (conj Hs (conj Hc (conj Hl Hloc))))) as A.
  cbn [compile]. rewrite Hns. cbv zeta.
  set (ces := FLAT (MAP FST (MAP (compile_exp ctxt) es))) in *.
  set (fvs := FLAT (MAP flatten vs)) in *.
  set (temps := GENLIST (fun x => vmax ctxt + SUC x) (LENGTH ces)).
  assert (Hvle : forall y, In y (FLAT (MAP var_cexp ces)) -> y <= vmax ctxt).
  { intros y Hy. apply in_concat in Hy as (l & Hl1 & Hy). apply in_map_iff in Hl1 as (c & <- & Hc1).
    apply in_concat in Hc1 as (l' & Hl' & Hc1). apply in_map_iff in Hl' as (p & <- & Hp).
    apply in_map_iff in Hp as (e & <- & He1).
    apply (compile_exp_vars_le ctxt _ _ e y Hl). eapply In_FLAT_MAP; eassumption. }
  assert (Hnsle : forall y, In y ns -> y <= vmax ctxt)
    by (intros y Hy; destruct Hl as (_ & [_ Hmx] & _); exact (Hmx _ _ _ Hns y (proj2 (MEM_In _ _) Hy))).
  assert (Hd1 : distinct_lists temps (FLAT (MAP var_cexp ces))) by (apply temps_distinct, Hvle).
  assert (Hd2 : distinct_lists temps ns) by (apply temps_distinct, Hnsle).
  assert (Hadt : ALL_DISTINCT temps) by apply temps_all_distinct.
  assert (Hlt : LENGTH temps = LENGTH ces) by (unfold temps; apply LENGTH_GENLIST').
  assert (Hlv : LENGTH temps = LENGTH fvs) by (rewrite Hlt; exact (MAP_eq_LENGTH _ _ _ _ A)).
  assert (Had : ALL_DISTINCT ns)
    by exact (all_distinct_flookup_all_distinct (vars ctxt) vr _ ns (conj (proj1 Hl) Hns)).
  pose proof (pan_primop_crep_primop pop vs value Ep) as Hcp. fold fvs in Hcp.
  assert (Hwval : panProps.is_wf_shape_nil (shape_of value)) by (rewrite Esh; exact Hwv).
  assert (Hlval : LENGTH ns = LENGTH (flatten value)).
  { rewrite Hlenv, !panProps.length_flatten_eq_size_of_shape by assumption. congruence. }
  pose proof (eval_nested_decs_seq_res_var_eq ces temps t fvs (Primitive ns pop temps)
                (conj A (conj Hlt (conj Hd1 Hadt)))) as N1.
  set (t' := set_locals (locals t |++ ZIP (temps, fvs)) t) in N1.
  assert (Ep' : evaluate (Primitive ns pop temps, t') =
                (NONE, set_locals (locals t' |++ ZIP (ns, flatten value)) t')).
  { cstep. unfold t'. ccbn. rewrite opt_mmap_some_eq_zip_flookup by (split; assumption). rewrite Hcp.
    rewrite <- Hlval, N.eqb_refl, Had. cbn [andb].
    replace (EVERY _ ns) with true; [reflexivity|]. symmetry.
    apply EVERY_Forall, Forall_forall. intros k Hk.
    rewrite FLOOKUP_FUPDATE_LIST_notin.
    - apply opt_mmap_eq_some in Hov. assert (Hin : In (FLOOKUP (locals t) k) (MAP (FLOOKUP (locals t)) ns)) by (apply in_map, Hk).
      rewrite Hov in Hin. apply in_map_iff in Hin as (w & Hw & _). rewrite <- Hw. reflexivity.
    - rewrite In_ZIP_fst_iff by exact Hlv. intros Hin.
      apply (proj1 (distinct_lists_iff _ _) Hd2 k Hin Hk). }
  rewrite Ep' in N1. cbv beta iota in N1. rewrite N1.
  eexists _, _. split; [reflexivity|]. split; [unfold t'; srel Hs|].
  unfold panSem.set_var. pcbn. ccbn. csplit; try assumption. cbn [pc_post]. split; [reflexivity|].
  apply (locals_rel_agree _ _ (locals t |++ ZIP (ns, flatten value))).
  - apply (locals_rel_assign ctxt _ _ vr v); try assumption; congruence.
  - intros k Hk. unfold t'. ccbn.
    assert (Hkt : ~ In k temps) by (intros Hin; apply temps_gt in Hin; lia).
    rewrite FOLDL_res_var_map_lookup. destruct (in_dec _ k temps) as [Hin|_]; [contradiction|].
    destruct (in_dec (fun x y => decide (x = y)) k (map fst (ZIP (ns, flatten value)))) as [Hin|Hnin].
    + exact (FLOOKUP_FUPDATE_LIST_in _ _ _ _ Hin).
    + rewrite (FLOOKUP_FUPDATE_LIST_notin (ZIP (ns, flatten value)) (locals t |++ ZIP (temps, fvs)) k Hnin),
        (FLOOKUP_FUPDATE_LIST_notin (ZIP (ns, flatten value)) (locals t) k Hnin).
      apply FLOOKUP_FUPDATE_LIST_notin. intros Hin. apply Hkt. exact (In_map_fst_ZIP _ _ _ Hin).
Qed.

Lemma locals_rel_nctxt (ctxt : context a) (lcl : fmap mlstring (panSem.v a)) (L : fmap varname (word_lab a))
    v value :
  locals_rel ctxt lcl L -> panProps.is_wf_shape_nil (shape_of value) ->
  let nvars := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape (shape_of value)) in
  let nctxt := {| vars := FUPDATE (vars ctxt) (v, (shape_of value, nvars)); funcs := funcs ctxt;
                  eids := eids ctxt; vmax := vmax ctxt + size_of_shape (shape_of value) |} in
  locals_rel nctxt (lcl |+ (v, value)) (L |++ ZIP (nvars, flatten value)).
Proof.
  intros (Hno & Hmx & Hl) Hw nvars nctxt.
  assert (Hlen : LENGTH nvars = LENGTH (flatten value))
    by (unfold nvars; rewrite LENGTH_GENLIST'; symmetry; apply panProps.length_flatten_eq_size_of_shape, Hw).
  assert (Hfresh : forall v' sh' ns', FLOOKUP (vars ctxt) v' = SOME (sh', ns') -> distinct_lists nvars ns').
  { intros v' sh' ns' Hv'. apply temps_distinct. intros y Hy. destruct Hmx as [_ Hmx].
    exact (Hmx _ _ _ Hv' y (proj2 (MEM_In _ _) Hy)). }
  split; [|split].
  - split.
    + intros x a0 xs Hx. cbn [vars nctxt] in Hx. rewrite FLOOKUP_UPDATE in Hx.
      destruct (decide (v = x)); [injection Hx as _ <-; apply temps_all_distinct|].
      destruct Hno as [Hno _]. exact (Hno _ _ _ Hx).
    + intros x y a0 b xs ys (Hx & Hy & Hdj). cbn [vars nctxt] in Hx, Hy. rewrite FLOOKUP_UPDATE in Hx, Hy.
      destruct (decide (v = x)) as [<-|Hvx], (decide (v = y)) as [<-|Hvy]; [reflexivity| | |].
      * injection Hx as _ <-. exfalso. apply Hdj. apply distinct_lists_eq_disjoint. exact (Hfresh _ _ _ Hy).
      * injection Hy as _ <-. exfalso. apply Hdj. apply distinct_lists_eq_disjoint.
        rewrite distinct_lists_commutes. exact (Hfresh _ _ _ Hx).
      * destruct Hno as [_ Hno]. exact (Hno x y a0 b xs ys (conj Hx (conj Hy Hdj))).
  - split; [lia|]. intros x a0 xs Hx y Hy. cbn [vars vmax nctxt] in *. rewrite FLOOKUP_UPDATE in Hx.
    destruct (decide (v = x)).
    + injection Hx as _ <-. apply MEM_In, In_GENLIST_iff in Hy as (i & Hi & ->). lia.
    + destruct Hmx as [_ Hmx]. specialize (Hmx _ _ _ Hx _ Hy). lia.
  - intros vn v' Hv'. cbn [vars nctxt]. rewrite (FLOOKUP_UPDATE lcl) in Hv'. rewrite FLOOKUP_UPDATE. destruct (decide (v = vn)) as [<-|Hne].
    + injection Hv' as <-. exists nvars, (flatten value). split; [reflexivity|].
      split; [|split; [reflexivity|exact Hw]]. apply opt_mmap_some_eq_zip_flookup. split; [apply temps_all_distinct|exact Hlen].
    + destruct (Hl _ _ Hv') as (ns & vs & H1 & H2 & H3 & H4). exists ns, vs. split; [exact H1|].
      split; [|split; assumption]. rewrite opt_mmap_disj_zip_flookup; [exact H2|]. split; [exact (Hfresh _ _ _ H1)|exact Hlen].
Qed.

Lemma pc_Dec s v sh e prog :
  (forall p' s', panSem.eval_lt (p', s') (panLang.Dec v sh e prog, s) -> pc_P p' s') ->
  pc_P (panLang.Dec v sh e prog) s.
Proof.
  intros IH. pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc. apply andb_prop in Hloc as [Hle Hlp].
  destruct (panSem.eval s e) as [value|] eqn:Ee; [|injection H as <- <-; congruence].
  destruct (bool_decide (sh = shape_of value)) eqn:Esh; [|injection H as <- <-; congruence].
  apply bool_decide_spec in Esh. subst sh.
  cbn [compile]. destruct (compile_exp ctxt e) as [es sh'] eqn:Ece.
  destruct (compile_exp_val_rel s e _ t ctxt es sh' (conj Ee (conj Hs (conj Hc (conj Hl (conj Hle Ece))))))
    as (A & B & <- & D).
  destruct (decide (size_of_shape (shape_of value) = LENGTH es)) as [_|C]; [|congruence].
  cbv zeta.
  set (nvars := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape (shape_of value))).
  set (nctxt := {| vars := FUPDATE (vars ctxt) (v, (shape_of value, nvars)); funcs := funcs ctxt;
                   eids := eids ctxt; vmax := vmax ctxt + size_of_shape (shape_of value) |}).
  assert (Hvle : forall y, In y (FLAT (MAP var_cexp es)) -> y <= vmax ctxt)
    by (intros y Hy; apply (compile_exp_vars_le ctxt _ _ e y Hl); rewrite Ece; exact Hy).
  assert (Hd1 : distinct_lists nvars (FLAT (MAP var_cexp es))) by (apply temps_distinct, Hvle).
  assert (Hadt : ALL_DISTINCT nvars) by apply temps_all_distinct.
  assert (Hlt : LENGTH nvars = LENGTH es) by (unfold nvars; rewrite LENGTH_GENLIST'; symmetry; exact B).
  pose proof (eval_nested_decs_seq_res_var_eq es nvars t (flatten value) (compile nctxt prog)
                (conj A (conj Hlt (conj Hd1 Hadt)))) as N1.
  set (t1 := set_locals (locals t |++ ZIP (nvars, flatten value)) t) in N1.
  set (sb := panSem.set_locals (panSem.locals s |+ (v, value)) s) in H.
  destruct (panSem.evaluate (prog, sb)) as [r1 st] eqn:Ev.
  assert (Hr1 : r1 <> SOME panSem.Error) by (intros ->; injection H as <- <-; congruence).
  assert (Hs1 : state_rel sb t1) by (unfold sb, t1; srel Hs).
  assert (Hl1 : locals_rel nctxt (panSem.locals sb) (locals t1)) by (exact (locals_rel_nctxt ctxt _ _ v value Hl D)).
  destruct (IH prog sb ltac:(right; split; [reflexivity|cbn [fst snd panSem.psize]; lia])
              r1 st t1 nctxt (conj Ev (conj Hr1 (conj Hs1 (conj Hc (conj He (conj Hl1 Hlp)))))))
    as (res1 & r & Ev1 & Hsr & Hcr & Her & Hp).
  rewrite Ev1 in N1. cbv beta iota in N1. rewrite N1. injection H as <- <-.
  eexists _, _. split; [reflexivity|]. split; [srel Hsr|]. pcbn; ccbn. split; [exact Hcr|]. split; [exact Her|].
  assert (Hrest : forall res0, (res0 = NONE \/ res0 = SOME (Continue 0) \/ res0 = SOME (Break 0)) ->
            evaluate (compile nctxt prog, t1) = (res0, r) ->
            locals_rel nctxt (panSem.locals st) (locals r) ->
            locals_rel ctxt (res_var (panSem.locals st) (v, FLOOKUP (panSem.locals s) v))
              (FOLDL res_var (locals r) (ZIP (nvars, MAP (FLOOKUP (locals t)) nvars)))).
  { intros res0 Hres0 Ev0 (Hno' & Hmx' & Hlr). pose proof Hl as (Hno & Hmx & Hl0).
    split; [exact Hno|]. split; [exact Hmx|].
    intros vn w Hw. rewrite panProps.FLOOKUP_pan_res_var_thm in Hw.
    assert (Hfold : forall ns, (forall k, In k ns -> k <= vmax ctxt) ->
               OPT_MMAP (FLOOKUP (FOLDL res_var (locals r) (ZIP (nvars, MAP (FLOOKUP (locals t)) nvars)))) ns =
               OPT_MMAP (FLOOKUP (locals r)) ns).
    { intros ns Hns. apply OPT_MMAP_ext_In''. intros k Hk. rewrite FOLDL_res_var_map_lookup.
      destruct (in_dec _ k nvars) as [Hin|_]; [|reflexivity].
      exfalso. apply temps_gt in Hin. specialize (Hns k Hk). lia. }
    destruct (decide (vn = v)) as [->|Hvn].
    - destruct (Hl0 _ _ Hw) as (ns & vs & H1 & H2 & H3 & H4). exists ns, vs. split; [exact H1|].
      split; [|split; assumption].
      assert (Hnsle : forall k, In k ns -> k <= vmax ctxt)
        by (intros k Hk; destruct Hmx as [_ Hmx]; exact (Hmx _ _ _ H1 k (proj2 (MEM_In _ _) Hk))).
      rewrite Hfold by exact Hnsle. rewrite <- H2. apply OPT_MMAP_ext_In''. intros k Hk.
      assert (Hdn : distinct_lists ns (assigned_free_vars (compile nctxt prog))).
      { apply (rewritten_context_unassigned prog nctxt v ctxt ns nvars (shape_of value) (shape_of w)).
        split; [reflexivity|]. split; [exact H1|]. split; [exact Hno|]. split; [exact Hmx|].
        split; [exact Hno'|]. split; [exact Hmx'|]. apply temps_distinct. exact Hnsle. }
      assert (Hnm : ~ MEM k (assigned_free_vars (compile nctxt prog))).
      { intros Hm. apply MEM_In in Hm. exact (proj1 (distinct_lists_iff _ _) Hdn k Hk Hm). }
      rewrite (unassigned_vars_evaluate_same (compile nctxt prog) t1 res0 r k 0 (conj Ev0 (conj Hres0 Hnm))).
      unfold t1. ccbn. apply FLOOKUP_FUPDATE_LIST_notin. rewrite In_ZIP_fst_iff.
      + intros Hin. apply temps_gt in Hin. specialize (Hnsle k Hk). lia.
      + unfold nvars. rewrite LENGTH_GENLIST'. symmetry. apply panProps.length_flatten_eq_size_of_shape, D.
    - destruct (Hlr _ _ Hw) as (ns & vs & H1 & H2 & H3 & H4). cbn [vars nctxt] in H1.
      rewrite FLOOKUP_UPDATE in H1. destruct (decide (v = vn)) as [E|_]; [congruence|].
      exists ns, vs. split; [exact H1|]. split; [|split; assumption].
      rewrite Hfold; [exact H2|]. intros k Hk. destruct Hmx as [_ Hmx].
      exact (Hmx _ _ _ H1 k (proj2 (MEM_In _ _) Hk)). }
  destruct r1 as [[| | | |rv|eid ev|ff]|]; cbn [pc_post] in Hp |- *; try contradiction.
  - exact Hp.
  - destruct Hp as [-> Hlr]. split; [reflexivity|]. exact (Hrest _ (or_intror (or_intror eq_refl)) Ev1 Hlr).
  - destruct Hp as [-> Hlr]. split; [reflexivity|]. exact (Hrest _ (or_intror (or_introl eq_refl)) Ev1 Hlr).
  - exact Hp.
  - exact Hp.
  - exact Hp.
  - destruct Hp as [-> Hlr]. split; [reflexivity|]. exact (Hrest _ (or_introl eq_refl) Ev1 Hlr).
Qed.

Lemma decs_restore_agree (L M : fmap varname (word_lab a)) xs ws k :
  ~ In k xs -> FLOOKUP M k = FLOOKUP (L |++ ZIP (xs, ws)) k ->
  FLOOKUP (FOLDL res_var M (ZIP (xs, MAP (FLOOKUP L) xs))) k = FLOOKUP L k.
Proof.
  intros Hk HM. rewrite FOLDL_res_var_map_lookup. destruct (in_dec _ k xs) as [|_]; [contradiction|].
  rewrite HM. apply FLOOKUP_FUPDATE_LIST_notin. intros Hin. apply Hk. exact (In_map_fst_ZIP _ _ _ Hin).
Qed.

Lemma pc_Store s dst src : pc_P (panLang.Store dst src) s.
Proof.
  pc_intro. pstep H. cbn [compile]. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hl1 Hl2].
  destruct (panSem.eval s dst) as [[[addr]|vs|nm fl]|] eqn:E1; try (injection H as <- <-; congruence).
  destruct (panSem.eval s src) as [value|] eqn:E2; [|injection H as <- <-; congruence].
  destruct (panSem.mem_stores _ _ _ _) as [m|] eqn:Em; injection H as <- <-; [|congruence].
  destruct (compile_exp ctxt dst) as [c1 sh1] eqn:Ec1.
  destruct (compile_exp_val_rel s dst _ t ctxt c1 sh1 (conj E1 (conj Hs (conj Hc (conj Hl (conj Hl1 Ec1))))))
    as (A1 & _). destruct c1 as [|h1 c1]; [discriminate A1|]. cbn [MAP List.map flatten] in A1.
  injection A1 as A1 _.
  destruct (compile_exp ctxt src) as [es sh] eqn:Ec2.
  destruct (compile_exp_val_rel s src _ t ctxt es sh (conj E2 (conj Hs (conj Hc (conj Hl (conj Hl2 Ec2))))))
    as (A2 & B2 & <- & D2).
  destruct (decide (size_of_shape (shape_of value) = LENGTH es)) as [_|C]; [|congruence].
  set (adv := vmax ctxt + 1).
  set (temps := GENLIST (fun x => adv + SUC x) (size_of_shape (shape_of value))).
  assert (Htemps : adv :: temps = GENLIST (fun x => vmax ctxt + SUC x) (SUC (size_of_shape (shape_of value)))).
  { unfold temps, adv. rewrite GENLIST_CONS_aux. f_equal; try lia; apply GENLIST_ext; intros; lia. }
  assert (Hvle : forall y, In y (FLAT (MAP var_cexp (h1 :: es))) -> y <= vmax ctxt).
  { intros y Hy. cbn [MAP List.map FLAT List.concat] in Hy. apply in_app_or in Hy as [Hy|Hy].
    - apply (compile_exp_vars_le ctxt _ _ dst y Hl). rewrite Ec1. cbn. apply in_or_app; left; exact Hy.
    - apply (compile_exp_vars_le ctxt _ _ src y Hl). rewrite Ec2. exact Hy. }
  assert (Hd1 : distinct_lists (adv :: temps) (FLAT (MAP var_cexp (h1 :: es)))) by (rewrite Htemps; apply temps_distinct, Hvle).
  assert (Hadt : ALL_DISTINCT (adv :: temps)) by (rewrite Htemps; apply temps_all_distinct).
  assert (Hlv : LENGTH temps = LENGTH (flatten value))
    by (unfold temps; rewrite LENGTH_GENLIST'; symmetry; apply panProps.length_flatten_eq_size_of_shape, D2).
  assert (Hlt : LENGTH (adv :: temps) = LENGTH (h1 :: es)) by (cbn [LENGTH]; rewrite Hlv, (MAP_eq_LENGTH _ _ _ _ A2); reflexivity).
  assert (A : MAP (eval t) (h1 :: es) = MAP SOME (Word addr :: flatten value)) by (cbn [MAP List.map]; rewrite A1, A2; reflexivity).
  pose proof (eval_nested_decs_seq_res_var_eq (h1 :: es) (adv :: temps) t (Word addr :: flatten value)
                (nested_seq (stores (Var adv) (MAP Var temps) (n2w 0))) (conj A (conj Hlt (conj Hd1 Hadt)))) as N1.
  set (t1 := set_locals (locals t |++ ZIP (adv :: temps, Word addr :: flatten value)) t) in N1.
  destruct (evaluate (nested_seq (stores (Var adv) (MAP Var temps) (n2w 0)), t1)) as [q r] eqn:Ev.
  cbv beta iota in N1. rewrite N1.
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  assert (Hnad : ~ MEM adv temps).
  { intros Hin. apply MEM_In, In_GENLIST_iff in Hin as (i & _ & Hi). unfold adv in Hi. lia. }
  assert (Hadt' : ALL_DISTINCT temps) by (unfold temps; apply ALL_DISTINCT_GENLIST; intros m1 m2 (_ & _ & E); lia).
  assert (Hst : panSem.mem_stores (addr + n2w 0)%w (flatten value) (memaddrs t) (memory t) = SOME m)
    by (rewrite (proj1 WORD_ADD_0), <- Hm0, <- Hma; exact Em).
  destruct (evaluate_seq_stores_mem_state_rel temps (flatten value) adv (n2w 0) t q r addr m
              (conj Hlv (conj Hnad (conj Hadt' (conj Hst Ev))))) as (-> & Hmr & Hmar & Hshr & Hber & Hffr & Hcr & Hckr & Hbar & Htar).
  pose proof (evaluate_seq_stroes_locals_eq _ _ _ _ _ _ Ev) as Hlr.
  eexists _, _. split; [reflexivity|]. split.
  { unfold state_rel. pcbn; ccbn. csplit; congruence. }
  pcbn; ccbn. split; [rewrite Hcr; exact Hc|]. split; [exact He|]. cbn [pc_post]. split; [reflexivity|].
  apply (locals_rel_agree _ _ (locals t)); [exact Hl|]. intros k Hk.
  apply (decs_restore_agree _ _ _ (Word addr :: flatten value)).
  - rewrite Htemps. intros Hin. apply In_GENLIST_iff in Hin as (i & _ & ->). lia.
  - rewrite Hlr. unfold t1. reflexivity.
Qed.

Lemma n2w5_inj (m1 m2 : N) : m1 < 32 -> m2 < 32 -> (n2w m1 : word 5) = n2w m2 -> m1 = m2.
Proof.
  intros H1 H2 E. apply (f_equal w2n) in E. rewrite !w2n_n2w in E.
  change (dimword 5) with 32 in E. rewrite !N.mod_small in E by lia. exact E.
Qed.

Lemma globals_lookup_store (g : fmap (word 5) (word_lab a)) (fv : list (word_lab a)) L :
  L = LENGTH fv -> L <= 32 ->
  OPT_MMAP (FLOOKUP (g |++ ZIP (GENLIST (fun x => (n2w 0 + n2w x)%w) L, fv)))
    (GENLIST (fun x => n2w x) L) = SOME fv.
Proof.
  intros -> HL. rewrite (GENLIST_ext (fun x => (n2w 0 + n2w x)%w) (fun x => n2w x)) by (intros; word_ring).
  apply opt_mmap_some_eq_zip_flookup. split; [|apply LENGTH_GENLIST'].
  apply ALL_DISTINCT_GENLIST. intros m1 m2 (H1 & H2 & E). apply n2w5_inj; [lia|lia|exact E].
Qed.

Lemma pc_Raise s eid e : pc_P (panLang.Raise eid e) s.
Proof.
  pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc.
  destruct (FLOOKUP (panSem.eshapes s) eid) as [sh0|] eqn:Esh; [|injection H as <- <-; congruence].
  destruct (panSem.eval s e) as [value|] eqn:Ee; [|injection H as <- <-; congruence].
  destruct (_ && _) eqn:Eb; [|injection H as <- <-; congruence]. apply andb_prop in Eb as [_ E32].
  injection H as <- <-.
  destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En.
  2:{ exfalso. destruct He as [Hd _]. assert (Hin : FDOM (panSem.eshapes s) eid) by (unfold FDOM; congruence).
      rewrite Hd in Hin. unfold FDOM in Hin. congruence. }
  cbn [compile]. rewrite En. destruct (compile_exp ctxt e) as [ces sh] eqn:Ece.
  destruct (compile_exp_val_rel s e _ t ctxt ces sh (conj Ee (conj Hs (conj Hc (conj Hl (conj Hloc Ece))))))
    as (A & B & <- & D).
  destruct (decide (size_of_shape (shape_of value) = LENGTH ces)) as [_|C]; [|congruence].
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  rewrite Hstr, (panProps.size_of_sh_with_ctxt_eq _ _ D) in E32. apply N.leb_le in E32.
  set (temps := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape (shape_of value))).
  assert (Hvle : forall y, In y (FLAT (MAP var_cexp ces)) -> y <= vmax ctxt)
    by (intros y Hy; apply (compile_exp_vars_le ctxt _ _ e y Hl); rewrite Ece; exact Hy).
  assert (Hd1 : distinct_lists temps (FLAT (MAP var_cexp ces))) by (apply temps_distinct, Hvle).
  assert (Hadt : ALL_DISTINCT temps) by apply temps_all_distinct.
  assert (Hlv : LENGTH temps = LENGTH (flatten value))
    by (unfold temps; rewrite LENGTH_GENLIST'; symmetry; apply panProps.length_flatten_eq_size_of_shape, D).
  assert (Hlt : LENGTH temps = LENGTH ces) by (unfold temps; rewrite LENGTH_GENLIST'; symmetry; exact B).
  pose proof (eval_nested_decs_seq_res_var_eq ces temps t (flatten value)
                (nested_seq (store_globals (n2w 0) (MAP Var temps))) (conj A (conj Hlt (conj Hd1 Hadt)))) as N1.
  rewrite (evaluate_seq_store_globals_res temps (flatten value) t (n2w 0)) in N1.
  2:{ split; [exact Hadt|]. split; [exact Hlv|]. rewrite w2n_n2w, N.Div0.mod_0_l. lia. }
  cbv beta iota in N1. cstep. rewrite N1. cbn beta iota. cstep.
  eexists _, _. split; [reflexivity|]. unfold panSem.empty_locals, empty_locals.
  split; [unfold set_globals_field; unfold state_rel; pcbn; ccbn; csplit; assumption|].
  pcbn. unfold set_globals_field; ccbn. split; [exact Hc|]. split; [exact He|].
  cbn [pc_post]. rewrite En. split; [reflexivity|]. split; [exact D|]. intros _.
  split; [|lia]. unfold globals_lookup. unfold set_globals_field; ccbn.
  pose proof (panProps.length_flatten_eq_size_of_shape value D) as Hfl.
  rewrite <- Hfl. apply globals_lookup_store; [reflexivity|lia].
Qed.

Lemma pc_ShMemLoad (s : panSem.state a ffi_t) op vk v0 ad : pc_P (panLang.ShMemLoad op vk v0 ad) s.
Proof.
  pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc. apply andb_prop in Hloc as [Hvk Hloc].
  destruct vk; [|discriminate Hvk].
  destruct (panSem.eval s ad) as [[[addr]| |]|] eqn:Ea; try (injection H as <- <-; congruence).
  unfold panSem.lookup_kvar in H.
  destruct (FLOOKUP (panSem.locals s) v0) as [[[w]| |]|] eqn:Ev; try (injection H as <- <-; congruence).
  cbn [compile]. destruct (compile_exp ctxt ad) as [ces sh] eqn:Ece.
  destruct (compile_exp_val_rel s ad _ t ctxt ces sh (conj Ea (conj Hs (conj Hc (conj Hl (conj Hloc Ece))))))
    as (A & _ & _ & _).
  destruct ces as [|a0 ces]; [discriminate A|]. cbn [MAP List.map flatten] in A. injection A as A _.
  destruct (locals_rel_lookup_ctxt ctxt _ _ v0 _ (conj Hl Ev)) as (ns & Hns & Hlen & Hov & _).
  cbn [flatten LENGTH length] in Hlen. destruct ns as [|r' [|]]; cbn [LENGTH length] in Hlen; try lia.
  rewrite Hns. cstep. rewrite A.
  cbn [OPT_MMAP] in Hov. destruct (FLOOKUP (locals t) r') as [x|] eqn:Er; [|discriminate Hov].
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  assert (Hld : is_load (load_op op) = true) by (destruct op; reflexivity). rewrite Hld.
  assert (Hop : sh_mem_op (load_op op) r' addr t = sh_mem_load r' addr (panSem.nb_op op) t)
    by (destruct op; reflexivity). rewrite Hop.
  unfold panSem.sh_mem_load, sh_mem_load in *. rewrite <- Hsh, <- Hff.
  assert (Hpost : forall wv, locals_rel ctxt (panSem.locals s |+ (v0, panSem.ValWord wv))
                               (locals t |+ (r', Word wv))).
  { intros wv. apply (locals_rel_agree _ _ (locals t |++ ZIP ([r'], [Word wv]))).
    - apply (locals_rel_assign ctxt _ _ v0 (panSem.ValWord w)); try assumption; reflexivity.
    - intros k _. reflexivity. }
  destruct (_ =? 0);
    (destruct (classical_dec _) as [_|_]; [|injection H as <- <-; congruence]);
    (destruct (call_FFI _ _ _ _) as [nf nb|f]; injection H as <- <-);
    (eexists _, _; split; [reflexivity|]);
    unfold panSem.set_kvar, panSem.set_var, set_var, panSem.empty_locals, empty_locals;
    (split; [srel Hs|]); cbn [pc_post]; pcbn; ccbn; csplit; try assumption; try reflexivity;
    apply Hpost.
Qed.

Lemma FOLDR_MAX_ge (l : list N) x : In x l -> x <= FOLDR MAX 0 l.
Proof.
  induction l as [|y l IH]; [intros []|]. change (FOLDR MAX 0 (y :: l)) with (MAX y (FOLDR MAX 0 l)).
  cbn [In]. revert IH. generalize (FOLDR MAX 0 l) as m. intros m IH'. unfold MAX.
  intros [<-|Hx]; [|specialize (IH' Hx)]; destruct (N.ltb_spec y m); lia.
Qed.

Lemma pc_ShMemStore (s : panSem.state a ffi_t) op ad e : pc_P (panLang.ShMemStore op ad e) s.
Proof.
  pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc. apply andb_prop in Hloc as [Hl1 Hl2].
  destruct (panSem.eval s ad) as [[[addr]| |]|] eqn:E1;
    destruct (panSem.eval s e) as [[[bytes]| |]|] eqn:E2; try (injection H as <- <-; congruence).
  cbn [compile]. destruct (compile_exp ctxt ad) as [c1 sh1] eqn:Ec1.
  destruct (compile_exp_val_rel s ad _ t ctxt c1 sh1 (conj E1 (conj Hs (conj Hc (conj Hl (conj Hl1 Ec1))))))
    as (A1 & _ & _ & _).
  destruct c1 as [|h1 c1]; [discriminate A1|]. cbn [MAP List.map flatten] in A1. injection A1 as A1 _.
  destruct (compile_exp ctxt e) as [c2 sh2] eqn:Ec2.
  destruct (compile_exp_val_rel s e _ t ctxt c2 sh2 (conj E2 (conj Hs (conj Hc (conj Hl (conj Hl2 Ec2))))))
    as (A2 & _ & _ & _).
  destruct c2 as [|h2 c2]; [discriminate A2|]. cbn [MAP List.map flatten] in A2. injection A2 as A2 _.
  set (n := FOLDR MAX 0 (var_cexp h1)).
  assert (Hn : ~ MEM (n + 1) (var_cexp h1)).
  { intros Hin. apply MEM_In, FOLDR_MAX_ge in Hin. unfold n in Hin. lia. }
  cstep. rewrite A2. cbn beta iota. cstep.
  rewrite (update_locals_not_vars_eval_eq' t h1 (Word bytes) (n + 1) (Word bytes) Hn), A1.
  assert (Hld : is_load (store_op op) = false) by (destruct op; reflexivity). rewrite Hld.
  ccbn. rewrite FLOOKUP_UPDATE. destruct (decide (n + 1 = n + 1)) as [_|C]; [|congruence].
  assert (Hop : forall t' : state a ffi_t, sh_mem_op (store_op op) (n + 1) addr t' = sh_mem_store (n + 1) addr (panSem.nb_op op) t')
    by (intros; destruct op; reflexivity). rewrite Hop.
  unfold panSem.sh_mem_store, sh_mem_store in *. ccbn. rewrite FLOOKUP_UPDATE.
  destruct (decide (n + 1 = n + 1)) as [_|C]; [|congruence].
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  rewrite <- Hsh, <- Hff.
  assert (Hpost : forall L, (forall k, FLOOKUP L k = FLOOKUP (locals t) k) ->
                  locals_rel ctxt (panSem.locals s) L).
  { intros L HL. apply (locals_rel_agree _ _ (locals t)); [exact Hl|]. intros k _. apply HL. }
  assert (Hres : forall x k, FLOOKUP (res_var (locals t |+ (n + 1, x)) (n + 1, FLOOKUP (locals t) (n + 1))) k
                           = FLOOKUP (locals t) k).
  { intros x k. rewrite FLOOKUP_res_var. destruct (decide (k = n + 1)) as [->|Hk]; [reflexivity|].
    rewrite FLOOKUP_UPDATE. destruct (decide (n + 1 = k)); [congruence|reflexivity]. }
  destruct (_ =? 0);
    (destruct (classical_dec _) as [_|_]; [|injection H as <- <-; congruence]);
    (destruct (call_FFI _ _ _ _) as [nf nb|f]; injection H as <- <-);
    (eexists _, _; split; [reflexivity|]);
    (split; [srel Hs|]); cbn [pc_post]; pcbn; ccbn; csplit; try assumption; try reflexivity;
    apply Hpost; intros k; ccbn; apply Hres.
Qed.

Lemma set_locals_twice X Y (t : state a ffi_t) : set_locals X (set_locals Y t) = set_locals X t.
Proof. destruct t; reflexivity. Qed.

Lemma eval_fresh_locals (t : state a ffi_t) L h n :
  (forall x, In x (var_cexp h) -> x <= n) -> (forall x, x <= n -> FLOOKUP L x = FLOOKUP (locals t) x) ->
  eval (set_locals L t) h = eval t h.
Proof.
  intros H1 H2. rewrite (eval_locals_cong t L (locals t) h) by (intros x Hx; apply H2, H1, Hx).
  rewrite set_locals_id. reflexivity.
Qed.

Ltac fresh_dec := repeat match goal with |- context [decide (?x = ?y)] => destruct (decide (x = y)); try lia end.

Lemma pc_ExtCall (s : panSem.state a ffi_t) f ptr1 len1 ptr2 len2 :
  pc_P (panLang.ExtCall f ptr1 len1 ptr2 len2) s.
Proof.
  pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hloc Hq4]. apply andb_prop in Hloc as [Hloc Hq3].
  apply andb_prop in Hloc as [Hq1 Hq2].
  destruct (panSem.eval s ptr1) as [[[w1]| |]|] eqn:E1;
    destruct (panSem.eval s len1) as [[[w2]| |]|] eqn:E2;
    destruct (panSem.eval s ptr2) as [[[w3]| |]|] eqn:E3;
    destruct (panSem.eval s len2) as [[[w4]| |]|] eqn:E4; try (injection H as <- <-; congruence).
  cbn [compile].
  destruct (compile_exp ctxt ptr1) as [c1 sh1] eqn:Ec1.
  destruct (compile_exp_val_rel s ptr1 _ t ctxt c1 sh1 (conj E1 (conj Hs (conj Hc (conj Hl (conj Hq1 Ec1))))))
    as (A1 & _ & <- & _).
  destruct c1 as [|h1 c1]; [discriminate A1|]. cbn [MAP List.map flatten] in A1. injection A1 as A1 _.
  destruct (compile_exp ctxt len1) as [c2 sh2] eqn:Ec2.
  destruct (compile_exp_val_rel s len1 _ t ctxt c2 sh2 (conj E2 (conj Hs (conj Hc (conj Hl (conj Hq2 Ec2))))))
    as (A2 & _ & <- & _).
  destruct c2 as [|h2 c2]; [discriminate A2|]. cbn [MAP List.map flatten] in A2. injection A2 as A2 _.
  destruct (compile_exp ctxt ptr2) as [c3 sh3] eqn:Ec3.
  destruct (compile_exp_val_rel s ptr2 _ t ctxt c3 sh3 (conj E3 (conj Hs (conj Hc (conj Hl (conj Hq3 Ec3))))))
    as (A3 & _ & <- & _).
  destruct c3 as [|h3 c3]; [discriminate A3|]. cbn [MAP List.map flatten] in A3. injection A3 as A3 _.
  destruct (compile_exp ctxt len2) as [c4 sh4] eqn:Ec4.
  destruct (compile_exp_val_rel s len2 _ t ctxt c4 sh4 (conj E4 (conj Hs (conj Hc (conj Hl (conj Hq4 Ec4))))))
    as (A4 & _ & <- & _).
  destruct c4 as [|h4 c4]; [discriminate A4|]. cbn [MAP List.map flatten] in A4. injection A4 as A4 _.
  rewrite !panProps.shape_of_val.
  set (n := FOLDR MAX 0 _).
  assert (Hfr : forall h c, In (h :: c) [h1 :: c1; h2 :: c2; h3 :: c3; h4 :: c4] ->
                forall x, In x (var_cexp h) -> x <= n).
  { intros h c Hin x Hx. apply FOLDR_MAX_ge. apply in_concat. exists (var_cexp h). split; [|exact Hx].
    apply (in_map var_cexp). apply in_concat. exists (h :: c). split; [exact Hin|left; reflexivity]. }
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  cstep. rewrite A1. cbn beta iota. cstep. ccbn.
  erewrite (eval_fresh_locals t _ h2 n); [|exact (Hfr h2 c2 ltac:(cbn; tauto))|intros x Hx; rewrite FLOOKUP_UPDATE; fresh_dec; reflexivity].
  rewrite A2. cbn beta iota. cstep. ccbn. rewrite set_locals_twice.
  erewrite (eval_fresh_locals t _ h3 n); [|exact (Hfr h3 c3 ltac:(cbn; tauto))|intros x Hx; rewrite !FLOOKUP_UPDATE; fresh_dec; reflexivity].
  rewrite A3. cbn beta iota. cstep. ccbn. rewrite set_locals_twice.
  erewrite (eval_fresh_locals t _ h4 n); [|exact (Hfr h4 c4 ltac:(cbn; tauto))|intros x Hx; rewrite !FLOOKUP_UPDATE; fresh_dec; reflexivity].
  rewrite A4. cbn beta iota. cstep. ccbn. rewrite set_locals_twice. rewrite !FLOOKUP_UPDATE. fresh_dec.
  rewrite <- Hm0, <- Hma, <- Hbe, <- Hff.
  set (ld := panSem.mem_load_byte (panSem.memory s) (panSem.memaddrs s) (panSem.be s)) in *.
  destruct (read_bytearray w1 (w2n w2) ld) as [bytes|] eqn:Rb1;
    destruct (read_bytearray w3 (w2n w4) ld) as [bytes2|] eqn:Rb2;
    try (injection H as <- <-; congruence).
  destruct (call_FFI _ _ _ _) as [nf nb|o]; injection H as <- <-;
    (eexists _, _; split; [reflexivity|]); unfold panSem.empty_locals;
    (split; [srel Hs|]); cbn [pc_post]; pcbn; ccbn; csplit; try assumption; try reflexivity.
  apply (locals_rel_agree _ _ (locals t)); [exact Hl|]. intros k _.
  rewrite !FLOOKUP_res_var, !FLOOKUP_UPDATE. fresh_dec; try subst k; reflexivity.
Qed.

(** Callee contexts: [ctxt_fc] over [GENLIST I]. *)

Lemma FLOOKUP_FEMPTY_FUPDATE_LIST_distinct {K V} `{EqDecision K} (l : list (K * V)) k :
  NoDup (map fst l) -> FLOOKUP (FEMPTY |++ l) k = ALOOKUP l k.
Proof.
  intros Hd. rewrite flookup_fupdate_list, alookup_distinct_reverse.
  - destruct (ALOOKUP l k); reflexivity.
  - apply ALL_DISTINCT_iff. exact Hd.
Qed.

Lemma EL_APPEND1' {A} `{Inhabited A} (l1 l2 : list A) : forall n, n < LENGTH l1 -> EL n (l1 ++ l2) = EL n l1.
Proof.
  induction l1 as [|x l1 IH]; intros n Hn; cbn [LENGTH] in Hn; [lia|]. cbn [app].
  destruct (N.eq_dec n 0) as [->|Hn0]; [rewrite !EL_cons_0; reflexivity|].
  rewrite !EL_cons_pos by lia. apply IH. lia.
Qed.

Lemma EL_APPEND2' {A} `{Inhabited A} (l1 l2 : list A) : forall n, LENGTH l1 <= n -> EL n (l1 ++ l2) = EL (n - LENGTH l1) l2.
Proof.
  induction l1 as [|x l1 IH]; intros n Hn; cbn [LENGTH] in Hn |- *; [f_equal; lia|]. cbn [app].
  rewrite EL_cons_pos by lia. rewrite IH by lia. f_equal. lia.
Qed.

Lemma EL_GENLIST' {A} `{Inhabited A} (f : N -> A) n : forall i, i < n -> EL i (GENLIST f n) = f i.
Proof.
  induction n as [|n IH] using N.peano_ind; intros i Hi; [lia|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app.
  destruct (N.lt_ge_cases i n) as [Hl|Hl].
  - rewrite EL_APPEND1' by (rewrite LENGTH_GENLIST'; exact Hl). apply IH, Hl.
  - rewrite EL_APPEND2' by (rewrite LENGTH_GENLIST'; exact Hl). rewrite LENGTH_GENLIST'.
    replace (i - n) with 0 by lia. replace i with n by lia. apply EL_cons_0.
Qed.

Definition cvars (vshs : list (mlstring * shape)) (o : N) : list (mlstring * (shape * list N)) :=
  ZIP (MAP FST vshs, ZIP (MAP SND vshs,
    with_shape (MAP SND vshs) (GENLIST (fun x => o + x) (size_of_shape (Comb (MAP SND vshs)))))).

Lemma size_of_shape_Comb_cons sh shs :
  size_of_shape (Comb (sh :: shs)) = size_of_shape sh + size_of_shape (Comb shs).
Proof. reflexivity. Qed.

Lemma cvars_cons v sh vshs o :
  cvars ((v, sh) :: vshs) o =
  (v, (sh, GENLIST (fun x => o + x) (size_of_shape sh))) :: cvars vshs (o + size_of_shape sh).
Proof.
  unfold cvars. cbn [MAP List.map FST SND fst snd]. rewrite size_of_shape_Comb_cons, N.add_comm, GENLIST_APPEND.
  cbn [with_shape]. rewrite TAKE_app_exact, DROP_app_exact by (symmetry; apply LENGTH_GENLIST').
  cbn [ZIP]. f_equal. f_equal. f_equal. f_equal. apply GENLIST_ext. intros; lia.
Qed.

Lemma cvars_bound vshs : forall o x sh xs j,
  In (x, (sh, xs)) (cvars vshs o) -> In j xs -> o <= j /\ j < o + size_of_shape (Comb (MAP SND vshs)).
Proof.
  induction vshs as [|[v sh0] vshs IH]; intros o x sh xs j Hin Hj; [destruct Hin|].
  rewrite cvars_cons in Hin. cbn [MAP List.map SND snd]. rewrite size_of_shape_Comb_cons.
  destruct Hin as [E|Hin].
  - injection E as <- <- <-. apply In_GENLIST_iff in Hj as (i & Hi & ->). lia.
  - destruct (IH _ _ _ _ _ Hin Hj). lia.
Qed.

Lemma cvars_distinct vshs : forall o x sh xs, In (x, (sh, xs)) (cvars vshs o) -> ALL_DISTINCT xs.
Proof.
  induction vshs as [|[v sh0] vshs IH]; intros o x sh xs Hin; [destruct Hin|].
  rewrite cvars_cons in Hin. destruct Hin as [E|Hin].
  - injection E as <- <- <-. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & E). lia.
  - exact (IH _ _ _ _ Hin).
Qed.

Lemma cvars_disjoint vshs : forall o x y sa sb xs ys j,
  In (x, (sa, xs)) (cvars vshs o) -> In (y, (sb, ys)) (cvars vshs o) -> In j xs -> In j ys -> x = y.
Proof.
  induction vshs as [|[v sh0] vshs IH]; intros o x y sa sb xs ys j Hx Hy Hjx Hjy; [destruct Hx|].
  rewrite cvars_cons in Hx, Hy. destruct Hx as [Ex|Hx], Hy as [Ey|Hy].
  - injection Ex as <- _ _. injection Ey as <- _ _. reflexivity.
  - injection Ex as _ _ <-. apply In_GENLIST_iff in Hjx as (i & Hi & ->).
    destruct (cvars_bound _ _ _ _ _ _ Hy Hjy). lia.
  - injection Ey as _ _ <-. apply In_GENLIST_iff in Hjy as (i & Hi & ->).
    destruct (cvars_bound _ _ _ _ _ _ Hx Hjx). lia.
  - exact (IH _ _ _ _ _ _ _ _ Hx Hy Hjx Hjy).
Qed.

Lemma cvars_val (vshs : list (mlstring * shape)) (args : list (panSem.v a)) :
  LIST_REL (fun vsh arg => SND vsh = shape_of arg) vshs args ->
  Forall (fun arg => is_true (panProps.is_wf_shape_nil (shape_of arg))) args ->
  forall o x v, In (x, v) (ZIP (MAP FST vshs, args)) ->
  exists xs, In (x, (shape_of v, xs)) (cvars vshs o) /\
    MAP (fun j => EL (j - o) (FLAT (MAP flatten args))) xs = flatten v.
Proof.
  induction 1 as [|[v0 sh0] arg vshs args Hsh Hrel IH]; intros Hwf o x v Hin; [destruct Hin|].
  inversion Hwf as [|? ? Hw Hwf']; subst. cbn [SND snd] in Hsh. subst sh0.
  rewrite cvars_cons. cbn [MAP List.map FST fst ZIP] in Hin |- *.
  pose proof (panProps.length_flatten_eq_size_of_shape arg Hw) as Hl.
  destruct Hin as [E|Hin].
  - injection E as <- <-. exists (GENLIST (fun x => o + x) (size_of_shape (shape_of arg))).
    split; [left; reflexivity|]. cbn [FLAT List.concat].
    apply MAP_eq_EL; [rewrite LENGTH_GENLIST'; symmetry; exact Hl|]. intros n Hn.
    rewrite LENGTH_GENLIST' in Hn. rewrite EL_GENLIST' by exact Hn.
    rewrite EL_APPEND1' by lia. f_equal. lia.
  - destruct (IH Hwf' (o + size_of_shape (shape_of arg)) x v Hin) as (xs & H1 & H2).
    exists xs. split; [right; exact H1|]. rewrite <- H2. cbn [FLAT List.concat].
    apply map_ext_in. intros j Hj.
    destruct (cvars_bound _ _ _ _ _ _ H1 Hj).
    rewrite EL_APPEND2' by lia. f_equal. lia.
Qed.

Lemma cvars_fst vshs : forall o, map fst (cvars vshs o) = MAP FST vshs.
Proof.
  induction vshs as [|[v sh] vshs IH]; intros o; [reflexivity|]. rewrite cvars_cons. cbn [map MAP List.map FST fst].
  f_equal. apply IH.
Qed.

Lemma map_fst_ZIP_LIST_REL {B C} R (xs : list (mlstring * B)) (ys : list C) :
  LIST_REL R xs ys -> map fst (ZIP (MAP FST xs, ys)) = MAP FST xs.
Proof. induction 1 as [|x y xs ys _ _ IH]; [reflexivity|]. cbn [MAP List.map ZIP map fst FST]. f_equal. exact IH. Qed.

Lemma MAX_LIST_ge (l : list N) x : In x l -> x <= MAX_LIST l.
Proof.
  induction l as [|y l IH]; [intros []|]. cbn [In MAX_LIST]. revert IH. generalize (MAX_LIST l) as m.
  intros m IH. unfold MAX. intros [<-|Hx]; [|specialize (IH Hx)]; destruct (N.ltb_spec y m); lia.
Qed.

Lemma list_rel_length_flatten (vshs : list (mlstring * shape)) (args : list (panSem.v a)) :
  LIST_REL (fun vsh arg => SND vsh = shape_of arg) vshs args ->
  Forall (fun arg => is_true (panProps.is_wf_shape_nil (shape_of arg))) args ->
  size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args)).
Proof.
  induction 1 as [|[v0 sh0] arg vshs args Hsh Hrel IH]; intros Hwf; [reflexivity|].
  inversion Hwf as [|? ? Hw Hwf']; subst. cbn [SND snd] in Hsh. subst sh0.
  cbn [MAP List.map SND snd FLAT List.concat]. rewrite size_of_shape_Comb_cons, LENGTH_app', IH by exact Hwf'.
  rewrite panProps.length_flatten_eq_size_of_shape by exact Hw. reflexivity.
Qed.

Lemma In_ZIP_snd' {A B} (l1 : list A) (l2 : list B) x y : In (x, y) (ZIP (l1, l2)) -> In y l2.
Proof.
  revert l2; induction l1 as [|h l1 IH]; intros [|h2 l2] Hin; cbn [ZIP] in Hin; try destruct Hin.
  - injection H as _ ->. left; reflexivity.
  - right. exact (IH _ H).
Qed.

Lemma call_locals_rel cvs em (vshs : list (mlstring * shape)) (args : list (panSem.v a)) :
  ALL_DISTINCT (MAP FST vshs) ->
  LIST_REL (fun vsh arg => SND vsh = shape_of arg) vshs args ->
  Forall (fun arg => is_true (panProps.is_wf_shape_nil (shape_of arg))) args ->
  locals_rel (ctxt_fc cvs em (MAP FST vshs) (MAP SND vshs) (GENLIST I (size_of_shape (Comb (MAP SND vshs)))))
    (FEMPTY |++ ZIP (MAP FST vshs, args))
    (FEMPTY |++ ZIP (GENLIST I (size_of_shape (Comb (MAP SND vshs))), FLAT (MAP flatten args))).
Proof.
  intros Hd Hrel Hwf. set (n := size_of_shape (Comb (MAP SND vshs))).
  assert (Hns : GENLIST I n = GENLIST (fun x => 0 + x) n) by (apply GENLIST_ext; intros; reflexivity).
  assert (Hdn : NoDup (MAP FST vshs)) by (apply ALL_DISTINCT_iff; exact Hd).
  assert (Hv : forall k, FLOOKUP (vars (ctxt_fc cvs em (MAP FST vshs) (MAP SND vshs) (GENLIST I n))) k =
                         ALOOKUP (cvars vshs 0) k).
  { intros k. unfold ctxt_fc. cbn [vars]. rewrite Hns. fold n. change (ZIP _) with (cvars vshs 0).
    apply FLOOKUP_FEMPTY_FUPDATE_LIST_distinct. rewrite cvars_fst. exact Hdn. }
  assert (HL : LENGTH (FLAT (MAP flatten args)) = n) by (symmetry; apply list_rel_length_flatten; assumption).
  split; [split|split; [split|]].
  - intros x sh xs Hx. rewrite Hv in Hx. apply ALOOKUP_In in Hx. exact (cvars_distinct _ _ _ _ _ Hx).
  - intros x y sa sb xs ys (Hx & Hy & Hnd). rewrite Hv in Hx, Hy. apply ALOOKUP_In in Hx, Hy.
    rewrite DISJOINT_set_iff in Hnd. apply NNPP. intros Hne. apply Hnd. intros j Hj Hj'.
    apply Hne. exact (cvars_disjoint _ _ _ _ _ _ _ _ _ Hx Hy Hj Hj').
  - lia.
  - intros x sh xs Hx j Hj. rewrite Hv in Hx. apply ALOOKUP_In in Hx. apply MEM_In in Hj.
    destruct (cvars_bound _ _ _ _ _ _ Hx Hj) as [_ Hlt]. cbn [vmax ctxt_fc]. unfold ctxt_fc; cbn [vmax].
    apply MAX_LIST_ge, In_GENLIST_iff. exists j. split; [fold n in Hlt; lia|reflexivity].
  - intros vname v Hvn.
    rewrite FLOOKUP_FEMPTY_FUPDATE_LIST_distinct in Hvn by (rewrite (map_fst_ZIP_LIST_REL _ _ _ Hrel); exact Hdn).
    apply ALOOKUP_In in Hvn.
    destruct (cvars_val vshs args Hrel Hwf 0 vname v Hvn) as (xs & H1 & H2).
    exists xs, (flatten v). split.
    { rewrite Hv. apply ALOOKUP_NoDup_In; [rewrite cvars_fst; exact Hdn|exact H1]. }
    split; [|split; [reflexivity|]].
    + apply opt_mmap_eq_some. rewrite <- H2. rewrite map_map. apply map_ext_in. intros j Hj.
      destruct (cvars_bound _ _ _ _ _ _ H1 Hj) as [_ Hlt]. fold n in Hlt.
      rewrite N.sub_0_r. rewrite <- (EL_GENLIST' I n j) at 1 by lia.
      apply update_eq_zip_flookup. split; [apply ALL_DISTINCT_GENLIST; intros m1 m2 (_ & _ & E); exact E|].
      rewrite LENGTH_GENLIST'. split; [symmetry; exact HL|lia].
    + rewrite Forall_forall in Hwf. apply Hwf. apply In_ZIP_snd' in Hvn. exact Hvn.
Qed.

Lemma code_rel_ctxt_eq (c1 c2 : context a) sc (tc : fmap funname (list N * prog a)) :
  funcs c1 = funcs c2 -> eids c1 = eids c2 -> code_rel c1 sc tc -> code_rel c2 sc tc.
Proof. intros Hf He H. unfold code_rel in *. rewrite <- Hf, <- He. exact H. Qed.

Lemma args_wf (s : panSem.state a ffi_t) (t : state a ffi_t) ctxt : forall argexps args,
  OPT_MMAP (panSem.eval s) argexps = SOME args -> state_rel s t -> code_rel ctxt (panSem.code s) (code t) ->
  locals_rel ctxt (panSem.locals s) (locals t) -> EVERY panProps.localised_exp argexps ->
  Forall (fun arg => is_true (panProps.is_wf_shape_nil (shape_of arg))) args.
Proof.
  induction argexps as [|e es IH]; intros args Ha Hs Hc Hl Hloc; cbn [OPT_MMAP] in Ha.
  - injection Ha as <-. constructor.
  - destruct (panSem.eval s e) as [v|] eqn:Ee; [|discriminate].
    destruct (OPT_MMAP (panSem.eval s) es) as [vs|] eqn:Es; [|discriminate]. injection Ha as <-.
    cbn [EVERY] in Hloc. apply andb_prop in Hloc as [Hl1 Hl2].
    destruct (compile_exp ctxt e) as [ces sh] eqn:Ece.
    destruct (compile_exp_val_rel s e _ t ctxt ces sh (conj Ee (conj Hs (conj Hc (conj Hl (conj Hl1 Ece))))))
      as (_ & _ & <- & D).
    constructor; [exact D|]. exact (IH vs eq_refl Hs Hc Hl Hl2).
Qed.

Lemma call_setup (s : panSem.state a ffi_t) (t : state a ffi_t) ctxt argexps args fname prog0 newlocals rsh :
  OPT_MMAP (panSem.eval s) argexps = SOME args ->
  panSem.lookup_code (panSem.code s) fname args = SOME (prog0, (newlocals, rsh)) ->
  state_rel s t -> code_rel ctxt (panSem.code s) (code t) -> locals_rel ctxt (panSem.locals s) (locals t) ->
  EVERY panProps.localised_exp argexps ->
  exists vshs,
    FLOOKUP (funcs ctxt) fname = SOME (vshs, rsh) /\ panProps.localised_prog prog0 /\
    OPT_MMAP (eval t) (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args)) /\
    lookup_code (code t) fname (FLAT (MAP flatten args)) (LENGTH (FLAT (MAP flatten args))) =
      SOME (compile (ctxt_fc (funcs ctxt) (eids ctxt) (MAP FST vshs) (MAP SND vshs)
                       (GENLIST I (size_of_shape (Comb (MAP SND vshs))))) prog0,
            FEMPTY |++ ZIP (GENLIST I (size_of_shape (Comb (MAP SND vshs))), FLAT (MAP flatten args))) /\
    locals_rel (ctxt_fc (funcs ctxt) (eids ctxt) (MAP FST vshs) (MAP SND vshs)
                  (GENLIST I (size_of_shape (Comb (MAP SND vshs))))) newlocals
      (FEMPTY |++ ZIP (GENLIST I (size_of_shape (Comb (MAP SND vshs))), FLAT (MAP flatten args))).
Proof.
  intros Ha Hlc Hs Hc Hl Hloc.
  pose proof (args_wf s t ctxt argexps args Ha Hs Hc Hl Hloc) as Hwf.
  unfold panSem.lookup_code in Hlc.
  destruct (FLOOKUP (panSem.code s) fname) as [[vshs [p0 rsh0]]|] eqn:Ef; [|discriminate].
  destruct (ALL_DISTINCT (MAP fst vshs)) eqn:Ed; [|discriminate].
  destruct (bool_decide _) eqn:Er; [|discriminate]. cbn [andb] in Hlc.
  apply bool_decide_spec in Er. injection Hlc as <- <- <-.
  destruct (Hc fname vshs p0 rsh0 Ef) as (Hlp & Hfn & Htc). cbv zeta in Htc.
  exists vshs. split; [exact Hfn|]. split; [exact Hlp|]. split.
  { apply opt_mmap_eq_some. apply (eval_map_comp_exp_flat_eq argexps args s t ctxt).
    split; [apply opt_mmap_eq_some, Ha|]. csplit; assumption. }
  assert (HL : size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args)))
    by (apply list_rel_length_flatten; assumption).
  split.
  - unfold lookup_code. rewrite Htc. rewrite LENGTH_GENLIST', HL, N.eqb_refl. cbn [andb].
    rewrite (proj2 (ALL_DISTINCT_GENLIST I _)) by (intros m1 m2 (_ & _ & E); exact E). reflexivity.
  - apply call_locals_rel; assumption.
Qed.

Lemma set_locals_dec_clock X Y (t : state a ffi_t) :
  set_locals X (dec_clock (set_locals Y t)) = set_locals X (dec_clock t).
Proof. destruct t; reflexivity. Qed.

Lemma opt_mmap_eval_agree (t : state a ffi_t) L (es : list (exp a)) :
  (forall x, In x (FLAT (MAP var_cexp es)) -> FLOOKUP L x = FLOOKUP (locals t) x) ->
  OPT_MMAP (eval (set_locals L t)) es = OPT_MMAP (eval t) es.
Proof.
  intros H. apply OPT_MMAP_ext_In''. intros e He.
  rewrite (eval_locals_cong t L (locals t) e) by (intros x Hx; apply H; eapply In_FLAT_MAP; eassumption).
  rewrite set_locals_id. reflexivity.
Qed.

Lemma cargs_vars_le ctxt (lcl : fmap mlstring (panSem.v a)) L (argexps : list (panLang.exp a)) y :
  locals_rel ctxt lcl L ->
  In y (FLAT (MAP var_cexp (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))))) -> y <= vmax ctxt.
Proof.
  intros Hl Hy. apply in_concat in Hy as (vs & Hvs & Hy). apply in_map_iff in Hvs as (ce & <- & Hce).
  apply in_concat in Hce as (ces & Hces & Hce). rewrite map_map in Hces.
  apply in_map_iff in Hces as (e & <- & _).
  apply (compile_exp_vars_le ctxt lcl L e y Hl). eapply In_FLAT_MAP; eassumption.
Qed.

Lemma eval_replicate_const (t : state a ffi_t) n :
  MAP (eval t) (REPLICATE n (Const (n2w 0))) = MAP SOME (REPLICATE n (Word (n2w 0))).
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite !(proj2 (REPLICATE_thm n _)). cbn [MAP List.map]. rewrite IH. reflexivity.
Qed.

Lemma var_cexp_replicate_const n : FLAT (MAP var_cexp (REPLICATE n (@Const a (n2w 0)))) = [].
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (REPLICATE_thm n _)). cbn [MAP List.map FLAT List.concat var_cexp]. exact IH.
Qed.

Lemma nested_decs_zeros (t : state a ffi_t) rts p :
  ALL_DISTINCT rts ->
  let '(q, r) := evaluate (p, set_locals (locals t |++ ZIP (rts, REPLICATE (LENGTH rts) (Word (n2w 0)))) t) in
  evaluate (nested_decs rts (REPLICATE (LENGTH rts) (Const (n2w 0))) p, t) =
  (q, set_locals (FOLDL res_var (locals r) (ZIP (rts, MAP (FLOOKUP (locals t)) rts))) r).
Proof.
  intros Hd. apply eval_nested_decs_seq_res_var_eq. split; [apply eval_replicate_const|].
  split; [rewrite LENGTH_REPLICATE; reflexivity|]. split; [|exact Hd].
  rewrite var_cexp_replicate_const. apply distinct_lists_iff. intros x _ [].
Qed.

Lemma opt_mmap_some_not_none {A B} (f : A -> option B) : forall l m x,
  OPT_MMAP f l = SOME m -> In x l -> f x <> NONE.
Proof.
  induction l as [|y l IH]; intros m x Hm Hx; [destruct Hx|]. cbn [OPT_MMAP] in Hm.
  destruct (f y) as [z|] eqn:Ey; [|discriminate].
  destruct (OPT_MMAP f l) as [m'|] eqn:El; [|discriminate].
  destruct Hx as [<-|Hx]; [congruence|exact (IH _ _ eq_refl Hx)].
Qed.

Lemma opt_mmap_the {A B} `{Inhabited B} (f : A -> option B) : forall l m,
  OPT_MMAP f l = SOME m -> MAP (fun x => THE (f x)) l = m.
Proof.
  induction l as [|y l IH]; intros m Hm; cbn [OPT_MMAP] in Hm; [injection Hm as <-; reflexivity|].
  destruct (f y) as [z|] eqn:Ey; [|discriminate].
  destruct (OPT_MMAP f l) as [m'|] eqn:El; [|discriminate]. injection Hm as <-.
  cbn [MAP List.map]. rewrite Ey, (IH m' eq_refl). reflexivity.
Qed.

Lemma pc_handler (s st sp s1 : panSem.state a ffi_t) (t1 : state a ffi_t) ctxt L p evar exn w res :
  pc_P p sp ->
  sp = panSem.set_var evar exn (panSem.set_locals (panSem.locals s) st) ->
  panSem.evaluate (p, sp) = (res, s1) -> res <> SOME panSem.Error ->
  state_rel st t1 -> code_rel ctxt (panSem.code st) (code t1) -> excp_rel (eids ctxt) (panSem.eshapes st) ->
  locals_rel ctxt (panSem.locals s) L ->
  FLOOKUP (panSem.locals s) evar = SOME w -> shape_of exn = shape_of w ->
  panProps.is_wf_shape_nil (shape_of exn) ->
  (1 <= size_of_shape (shape_of exn) ->
   globals_lookup t1 exn = SOME (flatten exn) /\ size_of_shape (shape_of exn) <= 32) ->
  panProps.localised_prog p ->
  exists res1 t2,
    evaluate (Seq (exp_hdl (vars ctxt) evar) (compile ctxt p), set_locals L t1) = (res1, t2) /\
    state_rel s1 t2 /\ code_rel ctxt (panSem.code s1) (code t2) /\
    excp_rel (eids ctxt) (panSem.eshapes s1) /\ pc_post res s1 t2 ctxt res1.
Proof.
  intros IHp -> Hev Hne Hs1 Hc1 He1 Hl Hw Hsh Hwf Hg Hlp.
  destruct (locals_rel_lookup_ctxt ctxt _ _ evar w (conj Hl Hw)) as (nse & Hnse & Hlen & Hov & Hww).
  assert (Hle : LENGTH nse = LENGTH (flatten exn)).
  { rewrite Hlen, (panProps.length_flatten_eq_size_of_shape w Hww),
      (panProps.length_flatten_eq_size_of_shape exn Hwf), Hsh. reflexivity. }
  assert (Hdn : ALL_DISTINCT nse)
    by exact (all_distinct_flookup_all_distinct (vars ctxt) evar _ nse (conj (proj1 Hl) Hnse)).
  assert (Hl2 : locals_rel ctxt (panSem.locals s |+ (evar, exn)) (L |++ ZIP (nse, flatten exn)))
    by (apply (locals_rel_assign ctxt _ _ evar w); try assumption; congruence).
  assert (Hexp : evaluate (exp_hdl (vars ctxt) evar, set_locals L t1) =
                 (NONE, set_locals (L |++ ZIP (nse, flatten exn)) (set_locals L t1))).
  { unfold exp_hdl. rewrite Hnse.
    destruct (N.eq_dec (LENGTH (flatten exn)) 0) as [Hz|Hz].
    - destruct nse as [|x nse]; [|cbn [LENGTH] in Hle; lia].
      destruct (flatten exn) as [|y fl]; [|cbn [LENGTH] in Hz; lia].
      cbn [MAP2 nested_seq LENGTH ZIP]. cstep. f_equal; destruct t1; reflexivity.
    - assert (H1 : 1 <= size_of_shape (shape_of exn))
        by (rewrite <- panProps.length_flatten_eq_size_of_shape by exact Hwf; lia).
      destruct (Hg H1) as [Hgl H32]. unfold globals_lookup in Hgl.
      rewrite <- panProps.length_flatten_eq_size_of_shape in Hgl, H32 by exact Hwf. rewrite <- Hle in Hgl, H32.
      rewrite evaluate_seq_assign_load_globals.
      2:{ split; [exact Hdn|]. split; [rewrite w2n_n2w, N.Div0.mod_0_l; lia|]. split.
          - intros k Hk. ccbn. apply MEM_In in Hk. exact (opt_mmap_some_not_none _ _ _ _ Hov Hk).
          - intros k Hk. ccbn. apply MEM_In in Hk.
            rewrite (GENLIST_ext (fun x => (n2w 0 + n2w x)%w) (fun x => n2w x)) in Hk by (intros; word_ring).
            exact (opt_mmap_some_not_none _ _ _ _ Hgl Hk). }
      ccbn. rewrite (GENLIST_ext (fun x => (n2w 0 + n2w x)%w) (fun x => n2w x)) by (intros; word_ring).
      rewrite (opt_mmap_the _ _ _ Hgl). reflexivity. }
  destruct (IHp res s1 (set_locals (L |++ ZIP (nse, flatten exn)) t1) ctxt) as (res1 & t2 & Ev2 & Hpost).
  { split; [exact Hev|]. split; [exact Hne|]. split; [unfold panSem.set_var; srel Hs1|].
    unfold panSem.set_var; pcbn; ccbn. csplit; assumption. }
  exists res1, t2. split; [|exact Hpost].
  cstep. rewrite Hexp. cbn iota. rewrite set_locals_twice. exact Ev2.
Qed.

Definition call_post (cty : option (list varname * option (word a * prog a))) (L : fmap varname (word_lab a))
    (rs : option (result a) * state a ffi_t) : option (result a) * state a ffi_t :=
  let '(r, st) := rs in
  match r with
  | NONE => (SOME Error, st)
  | SOME (Break _) => (SOME Error, st)
  | SOME (Continue _) => (SOME Error, st)
  | SOME (Return retvs) =>
      match cty with
      | NONE => (SOME (Return retvs), empty_locals st)
      | SOME (rts, _) =>
          if negb (LENGTH retvs =? LENGTH rts) then (SOME Error, st)
          else match OPT_MMAP (FLOOKUP L) rts with
               | SOME _ => (NONE, set_locals (L |++ ZIP (rts, retvs)) st)
               | _ => (SOME Error, st)
               end
      end
  | SOME (Exception eid) =>
      match cty with
      | NONE => (SOME (Exception eid), empty_locals st)
      | SOME (_, NONE) => (SOME (Exception eid), empty_locals st)
      | SOME (_, SOME (eid', p)) =>
          if bool_decide (eid = eid') then evaluate (p, set_locals L st)
          else (SOME (Exception eid), empty_locals st)
      end
  | SOME r' => (SOME r', empty_locals st)
  end.

Lemma crep_call_eval (t : state a ffi_t) cty fname cargs wargs cprog nl :
  OPT_MMAP (eval t) cargs = SOME wargs ->
  lookup_code (code t) fname wargs (LENGTH wargs) = SOME (cprog, nl) ->
  (match cty with NONE => true | SOME (rts, _) => ALL_DISTINCT rts end) = true ->
  clock t <> 0 ->
  evaluate (Call cty fname cargs, t) =
  call_post cty (locals t) (evaluate (cprog, set_locals nl (dec_clock t))).
Proof.
  intros Hea Hlc Hd Hck. cstep. rewrite Hea. rewrite Hlc.
  assert (Hd' : match cty with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end = false)
    by (destruct cty as [[rts h]|]; [rewrite Hd|]; reflexivity).
  rewrite Hd'. apply N.eqb_neq in Hck. rewrite Hck. rewrite fix_clock_evaluate.
  destruct (evaluate (cprog, set_locals nl (dec_clock t))) as [r st].
  destruct r as [[| | | | |eid|]|]; cbn [call_post]; try reflexivity.
  all: destruct cty as [[rts [[eid' p]|]]|]; try reflexivity.
  all: destruct (bool_decide _); [|reflexivity]; rewrite fix_clock_evaluate; reflexivity.
Qed.

Lemma crep_call_clock0 (t : state a ffi_t) cty fname cargs wargs cprog nl :
  OPT_MMAP (eval t) cargs = SOME wargs ->
  lookup_code (code t) fname wargs (LENGTH wargs) = SOME (cprog, nl) ->
  (match cty with NONE => true | SOME (rts, _) => ALL_DISTINCT rts end) = true ->
  clock t = 0 ->
  evaluate (Call cty fname cargs, t) = (SOME TimeOut, empty_locals t).
Proof.
  intros Hea Hlc Hd Hck. cstep. rewrite Hea. rewrite Hlc.
  assert (Hd' : match cty with NONE => false | SOME (rts, _) => negb (ALL_DISTINCT rts) end = false)
    by (destruct cty as [[rts h]|]; [rewrite Hd|]; reflexivity).
  rewrite Hd', Hck. reflexivity.
Qed.

Lemma pc_post_restore res (s1 : panSem.state a ffi_t) (t2 : state a ffi_t) ctxt r L :
  (forall k, k <= vmax ctxt -> FLOOKUP L k = FLOOKUP (locals t2) k) ->
  pc_post res s1 t2 ctxt r -> pc_post res s1 (set_locals L t2) ctxt r.
Proof.
  intros HL Hp. destruct res as [[| | | |v|e0 v|f]|]; cbn [pc_post] in *; try exact Hp.
  all: first
    [ destruct Hp as [-> Hl]; split; [reflexivity|]; apply (locals_rel_agree _ _ (locals t2)); [exact Hl|];
      intros k Hk; ccbn; apply HL, Hk
    | match goal with |- context [FLOOKUP (eids ?c) ?e] => destruct (FLOOKUP (eids c) e) end;
      [|exact Hp]; unfold globals_lookup in *; ccbn; exact Hp ].
Qed.

Lemma excp_rel_inj (ctxt : context a) (seids : fmap eid shape) e e' n :
  excp_rel (eids ctxt) seids -> FLOOKUP (eids ctxt) e = SOME n -> FLOOKUP (eids ctxt) e' = SOME n -> e = e'.
Proof. intros [_ H] H1 H2. exact (H e e' n n (conj H1 (conj H2 eq_refl))). Qed.

Lemma wrap_rt_none_inv {A} sh (xs : list A) : wrap_rt (Some (sh, xs)) = None -> sh = One /\ xs = [].
Proof. destruct sh, xs; cbn; intros H; try discriminate; split; reflexivity. Qed.

Lemma flatten_one (v : panSem.v a) : shape_of v = One -> LENGTH (flatten v) = 1.
Proof. destruct v as [w| |]; cbn; intros H; [reflexivity|discriminate|discriminate]. Qed.

Lemma bool_decide_false (P : Prop) {d : Decision P} : bool_decide P = false <-> ~ P.
Proof. unfold bool_decide; destruct (decide P); split; congruence || tauto. Qed.

Definition hcomp (ctxt : context a) (hdl : option (mlstring * (mlstring * panLang.prog a)))
    : option (word a * prog a) :=
  match hdl with
  | SOME (eid', (evar, p)) =>
      match FLOOKUP (eids ctxt) eid' with
      | SOME neid => SOME (neid, Seq (exp_hdl (vars ctxt) evar) (compile ctxt p))
      | NONE => NONE
      end
  | NONE => NONE
  end.

Lemma pc_call_exc (s st s1 : panSem.state a ffi_t) (t1 : state a ffi_t) ctxt L
    (hdl : option (mlstring * (mlstring * panLang.prog a))) cty eid0 exn n res :
  (forall e v p (sp : panSem.state a ffi_t), hdl = SOME (e, (v, p)) -> panSem.clock sp <= panSem.clock st -> pc_P p sp) ->
  match hdl with
  | SOME (eid', (evar, p)) =>
      if ⌜eid0 = eid'⌝ then
        match FLOOKUP (panSem.eshapes s) eid0 with
        | SOME sh =>
            if ⌜shape_of exn = sh⌝ && panSem.is_valid_value s Local evar exn
            then panSem.evaluate (p, panSem.set_var evar exn (panSem.set_locals (panSem.locals s) st))
            else (SOME panSem.Error, st)
        | NONE => (SOME panSem.Error, st)
        end
      else (SOME (panSem.Exception eid0 exn), panSem.empty_locals st)
  | NONE => (SOME (panSem.Exception eid0 exn), panSem.empty_locals st)
  end = (res, s1) ->
  res <> SOME panSem.Error ->
  (match hdl with SOME (_, (_, p)) => panProps.localised_prog p | NONE => true end) = true ->
  (cty = NONE /\ hcomp ctxt hdl = NONE \/ exists xs, cty = SOME (xs, hcomp ctxt hdl)) ->
  FLOOKUP (eids ctxt) eid0 = SOME n ->
  panProps.is_wf_shape_nil (shape_of exn) ->
  (1 <= size_of_shape (shape_of exn) ->
   globals_lookup t1 exn = SOME (flatten exn) /\ size_of_shape (shape_of exn) <= 32) ->
  state_rel st t1 -> code_rel ctxt (panSem.code st) (code t1) -> excp_rel (eids ctxt) (panSem.eshapes st) ->
  locals_rel ctxt (panSem.locals s) L ->
  exists res2 t2,
    call_post cty L (SOME (Exception n), t1) = (res2, t2) /\
    state_rel s1 t2 /\ code_rel ctxt (panSem.code s1) (code t2) /\
    excp_rel (eids ctxt) (panSem.eshapes s1) /\ pc_post res s1 t2 ctxt res2.
Proof.
  intros IHh H Hne Hlp Hcty En Hw Hg Hs1 Hc1 He1 Hl.
  assert (Hprop : (res, s1) = (SOME (panSem.Exception eid0 exn), panSem.empty_locals st) ->
                  call_post cty L (SOME (Exception n), t1) = (SOME (Exception n), empty_locals t1) ->
                  exists res2 t2,
                    call_post cty L (SOME (Exception n), t1) = (res2, t2) /\
                    state_rel s1 t2 /\ code_rel ctxt (panSem.code s1) (code t2) /\
                    excp_rel (eids ctxt) (panSem.eshapes s1) /\ pc_post res s1 t2 ctxt res2).
  { intros E1 E2. injection E1 as -> ->. rewrite E2. eexists _, _. split; [reflexivity|].
    unfold panSem.empty_locals, empty_locals. split; [srel Hs1|]. pcbn; ccbn.
    split; [exact Hc1|]. split; [exact He1|]. cbn [pc_post]. rewrite En. split; [reflexivity|].
    split; [exact Hw|]. unfold globals_lookup in *. ccbn. exact Hg. }
  assert (Hnone : hcomp ctxt hdl = NONE -> call_post cty L (SOME (Exception n), t1) = (SOME (Exception n), empty_locals t1)).
  { intros Hh. destruct Hcty as [[-> _]|(xs & ->)]; [reflexivity|]. rewrite Hh. reflexivity. }
  destruct hdl as [[eid' [evar p]]|].
  2:{ apply Hprop; [symmetry; exact H|apply Hnone; reflexivity]. }
  cbn [hcomp] in Hcty, Hnone. destruct (FLOOKUP (eids ctxt) eid') as [neid|] eqn:Ene.
  2:{ destruct (bool_decide (eid0 = eid')) eqn:Eq.
      - apply bool_decide_spec in Eq. subst eid'. congruence.
      - apply Hprop; [symmetry; exact H|apply Hnone; reflexivity]. }
  destruct Hcty as [[_ Hc0]|(xs & ->)]; [discriminate Hc0|].
  destruct (bool_decide (eid0 = eid')) eqn:Eq.
  2:{ apply bool_decide_false in Eq.
      assert (Hnn : n <> neid) by (intros ->; apply Eq; exact (excp_rel_inj ctxt _ _ _ _ He1 En Ene)).
      apply Hprop; [symmetry; exact H|]. cbn [call_post].
      rewrite (proj2 (bool_decide_false (n = neid)) Hnn). reflexivity. }
  apply bool_decide_spec in Eq. subst eid'. rewrite En in Ene. injection Ene as <-.
  cbn [call_post]. rewrite (proj2 (bool_decide_spec (n = n)) eq_refl).
  destruct (FLOOKUP (panSem.eshapes s) eid0) as [sh|] eqn:Esh; [|injection H as <- <-; congruence].
  destruct (bool_decide (shape_of exn = sh) && panSem.is_valid_value s Local evar exn) eqn:Eb;
    [|injection H as <- <-; congruence].
  apply andb_prop in Eb as [_ Hvv]. unfold panSem.is_valid_value, panSem.lookup_kvar in Hvv.
  destruct (FLOOKUP (panSem.locals s) evar) as [w|] eqn:Ew; [|discriminate Hvv].
  apply bool_decide_spec in Hvv.
  pose proof (panSem.evaluate_clock _ _ _ _ H) as _.
  destruct (pc_handler s st _ s1 t1 ctxt L p evar exn w res
              (IHh eid0 evar p (panSem.set_var evar exn (panSem.set_locals (panSem.locals s) st)) eq_refl
                 ltac:(unfold panSem.set_var; pcbn; lia))
              eq_refl H Hne Hs1 Hc1 He1 Hl Ew Hvv Hw Hg Hlp) as (res2 & t2 & Ev2 & Hpost).
  exists res2, t2. split; [exact Ev2|exact Hpost].
Qed.

Ltac t0post H := eexists _, _; split; [reflexivity|]; unfold panSem.empty_locals, empty_locals;
  split; [srel H|]; pcbn; ccbn; csplit; assumption || reflexivity.

Lemma pc_Call (s : panSem.state a ffi_t) caltyp fname argexps :
  (forall p' s', panSem.eval_lt (p', s') (panLang.Call caltyp fname argexps, s) -> pc_P p' s') ->
  pc_P (panLang.Call caltyp fname argexps) s.
Proof.
  intros IH. pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hloc Hglob]. apply andb_prop in Hloc as [Hargs Hhdl].
  destruct (OPT_MMAP (panSem.eval s) argexps) as [args|] eqn:Ea; [|injection H as <- <-; congruence].
  destruct (panSem.lookup_code (panSem.code s) fname args) as [[prog0 [newlocals rsh]]|] eqn:Elc;
    [|injection H as <- <-; congruence].
  destruct (call_setup s t ctxt argexps args fname prog0 newlocals rsh Ea Elc Hs Hc Hl Hargs)
    as (vshs & Hfn & Hlp & Hea & Hlct & Hlr).
  set (ns := GENLIST I (size_of_shape (Comb (MAP SND vshs)))) in *.
  set (nctxt := ctxt_fc (funcs ctxt) (eids ctxt) (MAP FST vshs) (MAP SND vshs) ns) in *.
  set (cargs := FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) in *.
  set (wargs := FLAT (MAP flatten args)) in *.
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  assert (Hcn : forall sc tc, code_rel nctxt sc tc -> code_rel ctxt sc tc)
    by (intros sc tc; apply code_rel_ctxt_eq; reflexivity).
  (* the return temporaries of a call whose result is dropped *)
  set (rts := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape rsh)).
  set (tdec := set_locals (locals t |++ ZIP (rts, REPLICATE (LENGTH rts) (Word (n2w 0)))) t).
  assert (Hrd : ALL_DISTINCT rts) by apply temps_all_distinct.
  assert (Hrestore : forall M k, k <= vmax ctxt ->
            FLOOKUP (FOLDL res_var M (ZIP (rts, MAP (FLOOKUP (locals t)) rts))) k = FLOOKUP M k).
  { intros M k Hk. rewrite FOLDL_res_var_map_lookup. destruct (in_dec _ k rts) as [Hin|_]; [|reflexivity].
    apply temps_gt in Hin. lia. }
  assert (Htdec : forall k, k <= vmax ctxt -> FLOOKUP (locals tdec) k = FLOOKUP (locals t) k).
  { intros k Hk. unfold tdec. ccbn. apply FLOOKUP_FUPDATE_LIST_notin. intros Hin.
    apply In_map_fst_ZIP in Hin. apply temps_gt in Hin. lia. }
  assert (Heatd : OPT_MMAP (eval tdec) cargs = SOME wargs).
  { unfold tdec. rewrite opt_mmap_eval_agree; [exact Hea|]. intros x Hx. apply (Htdec x).
    exact (cargs_vars_le ctxt _ _ argexps x Hl Hx). }
  assert (Hlcd : lookup_code (code tdec) fname wargs (LENGTH wargs) =
                 SOME (compile nctxt prog0, FEMPTY |++ ZIP (ns, wargs))) by exact Hlct.
  assert (Hltd : locals_rel ctxt (panSem.locals s) (locals tdec))
    by (apply (locals_rel_agree _ _ (locals t)); [exact Hl|exact Htdec]).
  destruct (panSem.clock s =? 0) eqn:Ec0.
  { (* clock = 0 *)
    injection H as <- <-. apply N.eqb_eq in Ec0. assert (Hct : clock t = 0) by congruence.
    assert (Hctd : clock tdec = 0) by exact Hct.
    destruct caltyp as [[[[rk rt]|] hdl]|]; cbn [compile]; cbv zeta; fold cargs.
    - destruct rk; [|discriminate Hglob].
      destruct (wrap_rt (FLOOKUP (vars ctxt) rt)) as [[sh xs]|] eqn:Ewr.
      + assert (Hxd : ALL_DISTINCT xs)
          by exact (all_distinct_flookup_all_distinct (vars ctxt) rt _ xs (conj (proj1 Hl) (wrap_rt_some _ _ _ Ewr))).
        destruct hdl as [[eid' [evar p]]|]; [destruct (FLOOKUP (eids ctxt) eid') as [neid|]|];
          (rewrite (crep_call_clock0 t _ fname cargs wargs _ _ Hea Hlct) by first [reflexivity|assumption]);
          t0post Hs.
      + destruct hdl as [[eid' [evar p]]|]; [destruct (FLOOKUP (eids ctxt) eid') as [neid|]|];
          (rewrite (crep_call_clock0 t _ fname cargs wargs _ _ Hea Hlct) by first [reflexivity|assumption]);
          t0post Hs.
    - rewrite Hfn. fold rts.
      destruct hdl as [[eid' [evar p]]|]; [destruct (FLOOKUP (eids ctxt) eid') as [neid|]|];
        (match goal with |- context [nested_decs rts _ (Call ?cty fname cargs)] =>
           let N := fresh "N" in
           pose proof (nested_decs_zeros t rts (Call cty fname cargs) Hrd) as N; fold tdec in N;
           rewrite (crep_call_clock0 tdec cty fname cargs wargs _ _ Heatd Hlcd) in N
             by first [reflexivity|assumption];
           cbv beta iota in N; rewrite N
         end); t0post Hs.
    - rewrite (crep_call_clock0 t _ fname cargs wargs _ _ Hea Hlct) by first [reflexivity|assumption].
      t0post Hs. }
  cbn iota in H. rewrite panSem.fix_clock_evaluate in H.
  destruct (panSem.evaluate (prog0, panSem.set_locals newlocals (panSem.dec_clock s))) as [r st] eqn:Ev.
  assert (Hr : r <> SOME panSem.Error) by (intros ->; injection H as <- _; congruence).
  apply N.eqb_neq in Ec0. assert (Hct : clock t <> 0) by congruence.
  assert (Hctd : clock tdec <> 0) by exact Hct.
  destruct (IH prog0 (panSem.set_locals newlocals (panSem.dec_clock s))
              ltac:(left; cbn [fst snd]; unfold panSem.dec_clock; pcbn; lia)
              r st (set_locals (FEMPTY |++ ZIP (ns, wargs)) (dec_clock t)) nctxt)
    as (res1 & t1 & Ev1 & Hs1 & Hc1 & He1 & Hp1).
  { split; [exact Ev|]. split; [exact Hr|]. split; [unfold panSem.dec_clock, dec_clock; srel Hs|].
    split; [apply (code_rel_ctxt_eq ctxt); [reflexivity|reflexivity|exact Hc]|].
    split; [exact He|]. split; [exact Hlr|exact Hlp]. }
  pose proof (panSem.evaluate_clock _ _ _ _ Ev) as Hstc. unfold panSem.dec_clock in Hstc. pcbn.
  apply Hcn in Hc1. change (excp_rel (eids ctxt) (panSem.eshapes st)) in He1.
  destruct caltyp as [[[[rk rt]|] hdl]|]; cbn [compile]; cbv zeta; fold cargs.
  - (* call with a return variable *)
    destruct rk; [|discriminate Hglob].
    destruct (wrap_rt (FLOOKUP (vars ctxt) rt)) as [[sh xs]|] eqn:Ewr.
    + pose proof (wrap_rt_some _ _ _ Ewr) as Hfl.
      assert (Hxd : ALL_DISTINCT xs)
        by exact (all_distinct_flookup_all_distinct (vars ctxt) rt _ xs (conj (proj1 Hl) Hfl)).
      match goal with |- exists _ _, evaluate (?P, t) = _ /\ _ =>
        replace P with (Call (SOME (xs, hcomp ctxt hdl)) fname cargs)
          by (destruct hdl as [[e' [? ?]]|]; cbn [hcomp]; [destruct (FLOOKUP (eids ctxt) e')|]; reflexivity)
      end.
      rewrite (crep_call_eval t (SOME (xs, hcomp ctxt hdl)) fname cargs wargs _ _ Hea Hlct Hxd Hct), Ev1.
      destruct r as [[| | | |rv|eid exn|ff]|]; cbn [pc_post] in Hp1; try congruence.
      * subst res1. cbn [call_post]. injection H as <- <-. t0post Hs1.
      * destruct Hp1 as [-> Hw1]. destruct (negb _) eqn:Eshp; [injection H as <- <-; congruence|].
        unfold panSem.is_valid_value, panSem.lookup_kvar in H.
        destruct (FLOOKUP (panSem.locals s) rt) as [w|] eqn:Ew; [|injection H as <- <-; congruence].
        destruct (bool_decide (shape_of rv = shape_of w)) eqn:Ebw; [|injection H as <- <-; congruence].
        apply bool_decide_spec in Ebw. injection H as <- <-.
        destruct (locals_rel_lookup_ctxt ctxt _ _ rt w (conj Hl Ew)) as (ns' & Hns' & Hlen' & Hov' & Hww).
        rewrite Hfl in Hns'. injection Hns' as -> ->.
        assert (Hlen : LENGTH (flatten rv) = LENGTH ns').
        { rewrite Hlen', (panProps.length_flatten_eq_size_of_shape rv Hw1),
            (panProps.length_flatten_eq_size_of_shape w Hww), Ebw. reflexivity. }
        cbn [call_post]. rewrite Hlen, N.eqb_refl, Hov'. cbn [negb].
        eexists _, _. split; [reflexivity|].
        cbn [panSem.set_kvar] in *. unfold panSem.set_var in *. split; [srel Hs1|]. pcbn; ccbn.
        split; [exact Hc1|]. split; [exact He1|]. cbn [pc_post]. split; [reflexivity|].
        apply (locals_rel_assign ctxt _ _ rt w); try assumption. symmetry; exact Hlen.
      * change (FLOOKUP (eids nctxt) eid) with (FLOOKUP (eids ctxt) eid) in Hp1.
        destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En; [|contradiction]. destruct Hp1 as [-> [Hw1 Hg1]].
        destruct (pc_call_exc s st s1 t1 ctxt (locals t) hdl (SOME (xs, hcomp ctxt hdl)) eid exn n res
                    (fun e v p sp _ Hsp => IH p sp ltac:(left; cbn [fst snd]; lia))
                    H Hne Hhdl (or_intror (ex_intro _ xs eq_refl)) En Hw1 Hg1 Hs1 Hc1 He1 Hl)
          as (res2 & t2 & E2 & Hpost). exists res2, t2. split; [exact E2|exact Hpost].
      * subst res1. cbn [call_post]. injection H as <- <-. t0post Hs1.
    + match goal with |- exists _ _, evaluate (?P, t) = _ /\ _ =>
        replace P with (Call (match hcomp ctxt hdl with NONE => NONE | SOME h => SOME ([], SOME h) end)
                          fname cargs)
          by (destruct hdl as [[e' [? ?]]|]; cbn [hcomp]; [destruct (FLOOKUP (eids ctxt) e')|]; reflexivity)
      end.
      rewrite (crep_call_eval t (match hcomp ctxt hdl with NONE => NONE | SOME h => SOME ([], SOME h) end)
                 fname cargs wargs _ _ Hea Hlct ltac:(destruct (hcomp ctxt hdl); reflexivity) Hct), Ev1.
      destruct r as [[| | | |rv|eid exn|ff]|]; cbn [pc_post] in Hp1; try congruence.
      * subst res1. destruct (hcomp ctxt hdl); cbn [call_post]; injection H as <- <-; t0post Hs1.
      * exfalso. destruct (negb _) eqn:Eshp; [injection H as <- <-; congruence|].
        unfold panSem.is_valid_value, panSem.lookup_kvar in H.
        destruct (FLOOKUP (panSem.locals s) rt) as [w|] eqn:Ew; [|injection H as <- <-; congruence].
        destruct (locals_rel_lookup_ctxt ctxt _ _ rt w (conj Hl Ew)) as (ns' & Hns' & Hlen' & _ & _).
        rewrite Hns' in Ewr. destruct (wrap_rt_none_inv _ _ Ewr) as [E1 ->].
        rewrite (flatten_one w E1) in Hlen'. discriminate Hlen'.
      * change (FLOOKUP (eids nctxt) eid) with (FLOOKUP (eids ctxt) eid) in Hp1.
        destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En; [|contradiction]. destruct Hp1 as [-> [Hw1 Hg1]].
        destruct (pc_call_exc s st s1 t1 ctxt (locals t) hdl
                    (match hcomp ctxt hdl with NONE => NONE | SOME h => SOME ([], SOME h) end) eid exn n res
                    (fun e v p sp _ Hsp => IH p sp ltac:(left; cbn [fst snd]; lia))
                    H Hne Hhdl
                    ltac:(destruct (hcomp ctxt hdl); [right; eexists; reflexivity|left; split; reflexivity])
                    En Hw1 Hg1 Hs1 Hc1 He1 Hl)
          as (res2 & t2 & E2 & Hpost). exists res2, t2. split; [exact E2|exact Hpost].
      * subst res1. destruct (hcomp ctxt hdl); cbn [call_post]; injection H as <- <-; t0post Hs1.
  - (* call whose return value is dropped *)
    rewrite Hfn. fold rts.
    match goal with |- exists _ _, evaluate (?P, t) = _ /\ _ =>
      replace P with (nested_decs rts (REPLICATE (LENGTH rts) (Const (n2w 0)))
                        (Call (SOME (rts, hcomp ctxt hdl)) fname cargs))
        by (destruct hdl as [[e' [? ?]]|]; cbn [hcomp]; [destruct (FLOOKUP (eids ctxt) e')|]; reflexivity)
    end.
    pose proof (nested_decs_zeros t rts (Call (SOME (rts, hcomp ctxt hdl)) fname cargs) Hrd) as N. fold tdec in N.
    rewrite (crep_call_eval tdec (SOME (rts, hcomp ctxt hdl)) fname cargs wargs _ _ Heatd Hlcd Hrd Hctd) in N.
    replace (set_locals (FEMPTY |++ ZIP (ns, wargs)) (dec_clock tdec))
      with (set_locals (FEMPTY |++ ZIP (ns, wargs)) (dec_clock t)) in N by (unfold tdec; rewrite set_locals_dec_clock; reflexivity).
    rewrite Ev1 in N.
    destruct r as [[| | | |rv|eid exn|ff]|]; cbn [pc_post] in Hp1; try congruence.
    + subst res1. cbn [call_post] in N. rewrite N. injection H as <- <-. t0post Hs1.
    + destruct Hp1 as [-> Hw1]. destruct (negb _) eqn:Eshp; [injection H as <- <-; congruence|].
      injection H as <- <-. apply Bool.negb_false_iff, bool_decide_spec in Eshp.
      assert (Hlen : LENGTH (flatten rv) = LENGTH rts)
        by (unfold rts; rewrite LENGTH_GENLIST', <- Eshp; apply panProps.length_flatten_eq_size_of_shape, Hw1).
      assert (Hom : OPT_MMAP (FLOOKUP (locals tdec)) rts = SOME (REPLICATE (LENGTH rts) (Word (n2w 0)))).
      { unfold tdec. ccbn. apply opt_mmap_some_eq_zip_flookup. split; [exact Hrd|].
        rewrite LENGTH_REPLICATE; reflexivity. }
      cbn [call_post] in N. rewrite Hlen, N.eqb_refl, Hom in N. cbn [negb] in N. rewrite N.
      eexists _, _. split; [reflexivity|]. split; [srel Hs1|]. pcbn; ccbn.
      split; [exact Hc1|]. split; [exact He1|]. cbn [pc_post]. split; [reflexivity|].
      apply (locals_rel_agree _ _ (locals tdec)); [exact Hltd|]. intros k Hk. ccbn. rewrite Hrestore by exact Hk.
      apply FLOOKUP_FUPDATE_LIST_notin. intros Hin. apply In_map_fst_ZIP, temps_gt in Hin. lia.
    + change (FLOOKUP (eids nctxt) eid) with (FLOOKUP (eids ctxt) eid) in Hp1.
      destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En; [|contradiction]. destruct Hp1 as [-> [Hw1 Hg1]].
      destruct (pc_call_exc s st s1 t1 ctxt (locals tdec) hdl (SOME (rts, hcomp ctxt hdl)) eid exn n res
                  (fun e v p sp _ Hsp => IH p sp ltac:(left; cbn [fst snd]; lia))
                  H Hne Hhdl (or_intror (ex_intro _ rts eq_refl)) En Hw1 Hg1 Hs1 Hc1 He1 Hltd)
        as (res2 & t2 & E2 & Hs2 & Hc2 & He2 & Hp2).
      rewrite E2 in N. rewrite N. eexists _, _. split; [reflexivity|]. split; [srel Hs2|]. pcbn; ccbn.
      split; [exact Hc2|]. split; [exact He2|]. apply pc_post_restore; [|exact Hp2].
      intros k Hk. apply Hrestore, Hk.
    + subst res1. cbn [call_post] in N. rewrite N. injection H as <- <-. t0post Hs1.
  - (* tail call *)
    rewrite (crep_call_eval t NONE fname cargs wargs _ _ Hea Hlct eq_refl Hct), Ev1. cbn [call_post].
    destruct r as [[| | | |rv|eid exn|ff]|]; cbn [pc_post] in Hp1; try congruence.
    + subst res1. injection H as <- <-. t0post Hs1.
    + destruct Hp1 as [-> Hw1]. destruct (negb _); injection H as <- <-; [congruence|].
      eexists _, _. split; [reflexivity|].
      unfold panSem.empty_locals, empty_locals. split; [srel Hs1|]. pcbn; ccbn. cbn [pc_post].
      csplit; assumption || reflexivity.
    + change (FLOOKUP (eids nctxt) eid) with (FLOOKUP (eids ctxt) eid) in Hp1.
      destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En; [|contradiction]. destruct Hp1 as [-> Hg1].
      injection H as <- <-. eexists _, _. split; [reflexivity|].
      unfold panSem.empty_locals, empty_locals. split; [srel Hs1|]. pcbn; ccbn. cbn [pc_post]. rewrite En.
      unfold globals_lookup in *. ccbn. split; [exact Hc1|]. split; [exact He1|]. split; [reflexivity|exact Hg1].
    + subst res1. injection H as <- <-. t0post Hs1.
Qed.

Lemma dec_restore_rel (ctxt : context a) v shv (lcl lst : fmap mlstring (panSem.v a))
    (L0 : fmap varname (word_lab a)) (tc r : state a ffi_t) p res0 :
  locals_rel ctxt lcl L0 ->
  (forall k, k <= vmax ctxt -> FLOOKUP (locals tc) k = FLOOKUP L0 k) ->
  (res0 = NONE \/ res0 = SOME (Continue 0) \/ res0 = SOME (Break 0)) ->
  evaluate (compile {| vars := FUPDATE (vars ctxt) (v, (shv, GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape shv)));
                       funcs := funcs ctxt; eids := eids ctxt; vmax := vmax ctxt + size_of_shape shv |} p, tc)
    = (res0, r) ->
  locals_rel {| vars := FUPDATE (vars ctxt) (v, (shv, GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape shv)));
                funcs := funcs ctxt; eids := eids ctxt; vmax := vmax ctxt + size_of_shape shv |} lst (locals r) ->
  locals_rel ctxt (res_var lst (v, FLOOKUP lcl v))
    (FOLDL res_var (locals r) (ZIP (GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape shv),
                                    MAP (FLOOKUP L0) (GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape shv))))).
Proof.
  set (nvars := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape shv)).
  set (nctxt := {| vars := FUPDATE (vars ctxt) (v, (shv, nvars)); funcs := funcs ctxt; eids := eids ctxt;
                   vmax := vmax ctxt + size_of_shape shv |}).
  intros Hl HL Hres0 Ev0 (Hno' & Hmx' & Hlr). pose proof Hl as (Hno & Hmx & Hl0).
  split; [exact Hno|]. split; [exact Hmx|].
  intros vn w Hw. rewrite panProps.FLOOKUP_pan_res_var_thm in Hw.
  assert (Hfold : forall ns, (forall k, In k ns -> k <= vmax ctxt) ->
             OPT_MMAP (FLOOKUP (FOLDL res_var (locals r) (ZIP (nvars, MAP (FLOOKUP L0) nvars)))) ns =
             OPT_MMAP (FLOOKUP (locals r)) ns).
  { intros ns Hns. apply OPT_MMAP_ext_In''. intros k Hk. rewrite FOLDL_res_var_map_lookup.
    destruct (in_dec _ k nvars) as [Hin|_]; [|reflexivity].
    exfalso. apply temps_gt in Hin. specialize (Hns k Hk). lia. }
  destruct (decide (vn = v)) as [->|Hvn].
  - destruct (Hl0 _ _ Hw) as (ns & vs & H1 & H2 & H3 & H4). exists ns, vs. split; [exact H1|].
    split; [|split; assumption].
    assert (Hnsle : forall k, In k ns -> k <= vmax ctxt)
      by (intros k Hk; destruct Hmx as [_ Hmx]; exact (Hmx _ _ _ H1 k (proj2 (MEM_In _ _) Hk))).
    rewrite Hfold by exact Hnsle. rewrite <- H2. apply OPT_MMAP_ext_In''. intros k Hk.
    assert (Hdn : distinct_lists ns (assigned_free_vars (compile nctxt p))).
    { apply (rewritten_context_unassigned p nctxt v ctxt ns nvars shv (shape_of w)).
      split; [reflexivity|]. split; [exact H1|]. split; [exact Hno|]. split; [exact Hmx|].
      split; [exact Hno'|]. split; [exact Hmx'|]. apply temps_distinct. exact Hnsle. }
    assert (Hnm : ~ MEM k (assigned_free_vars (compile nctxt p))).
    { intros Hm. apply MEM_In in Hm. exact (proj1 (distinct_lists_iff _ _) Hdn k Hk Hm). }
    rewrite (unassigned_vars_evaluate_same (compile nctxt p) tc res0 r k 0 (conj Ev0 (conj Hres0 Hnm))).
    apply HL, Hnsle, Hk.
  - destruct (Hlr _ _ Hw) as (ns & vs & H1 & H2 & H3 & H4). cbn [vars nctxt] in H1.
    rewrite FLOOKUP_UPDATE in H1. destruct (decide (v = vn)) as [E|_]; [congruence|].
    exists ns, vs. split; [exact H1|]. split; [|split; assumption].
    rewrite Hfold; [exact H2|]. intros k Hk. destruct Hmx as [_ Hmx].
    exact (Hmx _ _ _ H1 k (proj2 (MEM_In _ _) Hk)).
Qed.

Lemma pc_DecCall (s : panSem.state a ffi_t) rt shp fname argexps prog1 :
  (forall p' s', panSem.eval_lt (p', s') (panLang.DecCall rt shp fname argexps prog1, s) -> pc_P p' s') ->
  pc_P (panLang.DecCall rt shp fname argexps prog1) s.
Proof.
  intros IH. pc_intro. pstep H. cbn [panProps.localised_prog] in Hloc.
  apply andb_prop in Hloc as [Hargs Hlp1].
  destruct (OPT_MMAP (panSem.eval s) argexps) as [args|] eqn:Ea; [|injection H as <- <-; congruence].
  destruct (panSem.lookup_code (panSem.code s) fname args) as [[prog0 [newlocals rsh]]|] eqn:Elc;
    [|injection H as <- <-; congruence].
  destruct (call_setup s t ctxt argexps args fname prog0 newlocals rsh Ea Elc Hs Hc Hl Hargs)
    as (vshs & Hfn & Hlp & Hea & Hlct & Hlr).
  set (ns := GENLIST I (size_of_shape (Comb (MAP SND vshs)))) in *.
  set (nctxt := ctxt_fc (funcs ctxt) (eids ctxt) (MAP FST vshs) (MAP SND vshs) ns) in *.
  set (cargs := FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) in *.
  set (wargs := FLAT (MAP flatten args)) in *.
  pose proof Hs as (Hm0 & Hma & Hsh & Hstr & Hgl & Hck & Hbe & Hff & Hba & Hta).
  assert (Hcn : forall sc tc, code_rel nctxt sc tc -> code_rel ctxt sc tc)
    by (intros sc tc; apply code_rel_ctxt_eq; reflexivity).
  cbn [compile]. cbv zeta. fold cargs.
  set (nvars := GENLIST (fun x => vmax ctxt + SUC x) (size_of_shape shp)).
  set (dctxt := {| vars := FUPDATE (vars ctxt) (rt, (shp, nvars)); funcs := funcs ctxt;
                   eids := eids ctxt; vmax := vmax ctxt + size_of_shape shp |}).
  set (tdec := set_locals (locals t |++ ZIP (nvars, REPLICATE (LENGTH nvars) (Word (n2w 0)))) t).
  assert (Hrd : ALL_DISTINCT nvars) by apply temps_all_distinct.
  assert (Htdec : forall k, k <= vmax ctxt -> FLOOKUP (locals tdec) k = FLOOKUP (locals t) k).
  { intros k Hk. unfold tdec. ccbn. apply FLOOKUP_FUPDATE_LIST_notin. intros Hin.
    apply In_map_fst_ZIP in Hin. apply temps_gt in Hin. lia. }
  assert (Heatd : OPT_MMAP (eval tdec) cargs = SOME wargs).
  { unfold tdec. rewrite opt_mmap_eval_agree; [exact Hea|]. intros x Hx. apply (Htdec x).
    exact (cargs_vars_le ctxt _ _ argexps x Hl Hx). }
  assert (Hlcd : lookup_code (code tdec) fname wargs (LENGTH wargs) =
                 SOME (compile nctxt prog0, FEMPTY |++ ZIP (ns, wargs))) by exact Hlct.
  assert (Hltd : locals_rel ctxt (panSem.locals s) (locals tdec))
    by (apply (locals_rel_agree _ _ (locals t)); [exact Hl|exact Htdec]).
  pose proof (nested_decs_zeros t nvars (Seq (Call (SOME (nvars, NONE)) fname cargs) (compile dctxt prog1)) Hrd)
    as N.
  fold tdec in N.
  destruct (panSem.clock s =? 0) eqn:Ec0.
  { injection H as <- <-. apply N.eqb_eq in Ec0. assert (Hct : clock tdec = 0) by (cbn; congruence).
    assert (Hseq : evaluate (Seq (Call (SOME (nvars, NONE)) fname cargs) (compile dctxt prog1), tdec) =
                   (SOME TimeOut, empty_locals tdec)).
    { cstep. rewrite (crep_call_clock0 tdec (SOME (nvars, NONE)) fname cargs wargs _ _ Heatd Hlcd Hrd Hct).
      reflexivity. }
    rewrite Hseq in N. cbv beta iota in N. rewrite N. unfold tdec. t0post Hs. }
  cbn iota in H. rewrite panSem.fix_clock_evaluate in H.
  destruct (panSem.evaluate (prog0, panSem.set_locals newlocals (panSem.dec_clock s))) as [r st] eqn:Ev.
  assert (Hr : r <> SOME panSem.Error) by (intros ->; injection H as <- _; congruence).
  apply N.eqb_neq in Ec0. assert (Hct : clock t <> 0) by congruence.
  assert (Hctd : clock tdec <> 0) by exact Hct.
  destruct (IH prog0 (panSem.set_locals newlocals (panSem.dec_clock s))
              ltac:(left; cbn [fst snd]; unfold panSem.dec_clock; pcbn; lia)
              r st (set_locals (FEMPTY |++ ZIP (ns, wargs)) (dec_clock t)) nctxt)
    as (res1 & t1 & Ev1 & Hs1 & Hc1 & He1 & Hp1).
  { split; [exact Ev|]. split; [exact Hr|]. split; [unfold panSem.dec_clock, dec_clock; srel Hs|].
    split; [apply (code_rel_ctxt_eq ctxt); [reflexivity|reflexivity|exact Hc]|].
    split; [exact He|]. split; [exact Hlr|exact Hlp]. }
  pose proof (panSem.evaluate_clock _ _ _ _ Ev) as Hstc. unfold panSem.dec_clock in Hstc. pcbn.
  apply Hcn in Hc1. change (excp_rel (eids ctxt) (panSem.eshapes st)) in He1.
  assert (Hseq : evaluate (Seq (Call (SOME (nvars, NONE)) fname cargs) (compile dctxt prog1), tdec) =
                 match call_post (SOME (nvars, NONE)) (locals tdec) (res1, t1) with
                 | (NONE, s') => evaluate (compile dctxt prog1, s')
                 | (r', s') => (r', s')
                 end).
  { cstep. rewrite (crep_call_eval tdec (SOME (nvars, NONE)) fname cargs wargs _ _ Heatd Hlcd Hrd Hctd).
    replace (set_locals (FEMPTY |++ ZIP (ns, wargs)) (dec_clock tdec))
      with (set_locals (FEMPTY |++ ZIP (ns, wargs)) (dec_clock t)) by (unfold tdec; rewrite set_locals_dec_clock; reflexivity).
    rewrite Ev1. destruct (call_post _ _ _) as [[r'|] s']; reflexivity. }
  rewrite Hseq in N.
  destruct r as [[| | | |rv|eid exn|ff]|]; cbn [pc_post] in Hp1; try congruence.
  - subst res1. cbn [call_post] in N. cbv beta iota in N. rewrite N. injection H as <- <-. t0post Hs1.
  - destruct Hp1 as [-> Hw1].
    destruct (bool_decide (shape_of rv = shp) && bool_decide (shape_of rv = rsh)) eqn:Eb;
      [|injection H as <- <-; congruence].
    apply andb_prop in Eb as [Eb _]. apply bool_decide_spec in Eb. subst shp.
    assert (Hlen : LENGTH (flatten rv) = LENGTH nvars)
      by (unfold nvars; rewrite LENGTH_GENLIST'; apply panProps.length_flatten_eq_size_of_shape, Hw1).
    assert (Hom : OPT_MMAP (FLOOKUP (locals tdec)) nvars = SOME (REPLICATE (LENGTH nvars) (Word (n2w 0)))).
    { unfold tdec. ccbn. apply opt_mmap_some_eq_zip_flookup. split; [exact Hrd|].
      rewrite LENGTH_REPLICATE; reflexivity. }
    cbn [call_post] in N. rewrite Hlen, N.eqb_refl, Hom in N. cbn [negb] in N.
    set (sp := panSem.set_var rt rv (panSem.set_locals (panSem.locals s) st)) in H.
    set (tc := set_locals (locals tdec |++ ZIP (nvars, flatten rv)) t1) in N.
    destruct (panSem.evaluate (prog1, sp)) as [res' st'] eqn:Ev'. injection H as <- <-.
    assert (Hr' : res' <> SOME panSem.Error) by exact Hne.
    destruct (IH prog1 sp ltac:(left; cbn [fst snd]; unfold sp, panSem.set_var; pcbn; lia)
                res' st' tc dctxt) as (res2 & t2 & Ev2 & Hs2 & Hc2 & He2 & Hp2).
    { split; [exact Ev'|]. split; [exact Hr'|]. split; [unfold sp, tc, panSem.set_var; srel Hs1|].
      unfold sp, tc, panSem.set_var. pcbn; ccbn.
      split; [apply (code_rel_ctxt_eq ctxt); [reflexivity|reflexivity|exact Hc1]|].
      split; [exact He1|]. split; [|exact Hlp1].
      exact (locals_rel_nctxt ctxt _ _ rt rv Hltd Hw1). }
    rewrite Ev2 in N. cbv beta iota in N. rewrite N.
    eexists _, _. split; [reflexivity|]. split; [srel Hs2|]. pcbn; ccbn.
    split; [apply (code_rel_ctxt_eq dctxt); [reflexivity|reflexivity|exact Hc2]|].
    split; [exact He2|].
    assert (Hrest : forall res0, (res0 = NONE \/ res0 = SOME (Continue 0) \/ res0 = SOME (Break 0)) ->
              evaluate (compile dctxt prog1, tc) = (res0, t2) ->
              locals_rel dctxt (panSem.locals st') (locals t2) ->
              locals_rel ctxt (res_var (panSem.locals st') (rt, FLOOKUP (panSem.locals s) rt))
                (FOLDL res_var (locals t2) (ZIP (nvars, MAP (FLOOKUP (locals t)) nvars)))).
    { intros res0 Hres0 Ev0 Hlr0.
      apply (dec_restore_rel ctxt rt (shape_of rv) (panSem.locals s) (panSem.locals st') (locals t) tc t2
               prog1 res0 Hl); try assumption.
      intros k Hk. unfold tc. ccbn. rewrite FLOOKUP_FUPDATE_LIST_notin; [apply Htdec, Hk|].
      intros Hin. apply In_map_fst_ZIP, temps_gt in Hin. lia. }
    destruct res' as [[| | | |rv'|eid' ev'|ff']|]; cbn [pc_post] in Hp2 |- *; try contradiction.
    + exact Hp2.
    + destruct Hp2 as [-> Hlr2]. split; [reflexivity|]. exact (Hrest _ (or_intror (or_intror eq_refl)) Ev2 Hlr2).
    + destruct Hp2 as [-> Hlr2]. split; [reflexivity|]. exact (Hrest _ (or_intror (or_introl eq_refl)) Ev2 Hlr2).
    + exact Hp2.
    + change (FLOOKUP (eids dctxt) eid') with (FLOOKUP (eids ctxt) eid') in Hp2.
      destruct (FLOOKUP (eids ctxt) eid'); [|contradiction]. unfold globals_lookup in *. ccbn. exact Hp2.
    + exact Hp2.
    + destruct Hp2 as [-> Hlr2]. split; [reflexivity|]. exact (Hrest _ (or_introl eq_refl) Ev2 Hlr2).
  - change (FLOOKUP (eids nctxt) eid) with (FLOOKUP (eids ctxt) eid) in Hp1.
    destruct (FLOOKUP (eids ctxt) eid) as [n|] eqn:En; [|contradiction]. destruct Hp1 as [-> Hg1].
    cbn [call_post] in N. cbv beta iota in N. rewrite N. injection H as <- <-.
    eexists _, _. split; [reflexivity|]. unfold panSem.empty_locals, empty_locals. split; [srel Hs1|].
    pcbn; ccbn. split; [exact Hc1|]. split; [exact He1|]. cbn [pc_post]. rewrite En. split; [reflexivity|].
    unfold globals_lookup in *. ccbn. exact Hg1.
  - subst res1. cbn [call_post] in N. cbv beta iota in N. rewrite N. injection H as <- <-. t0post Hs1.
Qed.

Lemma pc_all : forall x : panLang.prog a * panSem.state a ffi_t, pc_P (fst x) (snd x).
Proof.
  intros x; induction x as [[p s] IH] using (well_founded_induction panSem.eval_lt_wf).
  assert (IH' : forall p' s', panSem.eval_lt (p', s') (p, s) -> pc_P p' s')
    by (intros p' s' Hlt; exact (IH (p', s') Hlt)).
  cbn [fst snd]. destruct p.
  - apply pc_Skip.
  - apply pc_Dec; exact IH'.
  - apply pc_Assign.
  - apply pc_Primitive.
  - apply pc_Store.
  - apply pc_Store32.
  - apply pc_StoreByte.
  - apply pc_Seq; exact IH'.
  - apply pc_If; exact IH'.
  - apply pc_While; exact IH'.
  - apply pc_Break.
  - apply pc_Continue.
  - apply pc_Call; exact IH'.
  - apply pc_DecCall; exact IH'.
  - apply pc_ExtCall.
  - apply pc_Raise.
  - apply pc_Return.
  - apply pc_ShMemLoad.
  - apply pc_ShMemStore.
  - apply pc_Tick.
  - apply pc_Annot.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct" *)
Theorem pc_compile_correct : forall (v : panLang.prog a) (v1 : panSem.state a ffi_t) res s1
    (t : state a ffi_t) ctxt,
  panSem.evaluate (v, v1) = (res, s1) /\ res <> SOME panSem.Error /\ state_rel v1 t /\
  code_rel ctxt (panSem.code v1) (code t) /\ excp_rel (eids ctxt) (panSem.eshapes v1) /\
  locals_rel ctxt (panSem.locals v1) (locals t) /\ panProps.localised_prog v ->
  exists res1 t1,
    evaluate (compile ctxt v, t) = (res1, t1) /\ state_rel s1 t1 /\
    code_rel ctxt (panSem.code s1) (code t1) /\ excp_rel (eids ctxt) (panSem.eshapes s1) /\
    match res with
    | NONE => res1 = NONE /\ locals_rel ctxt (panSem.locals s1) (locals t1)
    | SOME panSem.Error => False
    | SOME panSem.TimeOut => res1 = SOME TimeOut
    | SOME panSem.Break => res1 = SOME (Break 0) /\ locals_rel ctxt (panSem.locals s1) (locals t1)
    | SOME panSem.Continue => res1 = SOME (Continue 0) /\ locals_rel ctxt (panSem.locals s1) (locals t1)
    | SOME (panSem.Return v) => res1 = SOME (Return (flatten v))
    | SOME (panSem.Exception eid v') =>
        match FLOOKUP (eids ctxt) eid with
        | NONE => False
        | SOME n =>
            res1 = SOME (Exception n) /\
            (1 <= size_of_shape (shape_of v') ->
             globals_lookup t1 v' = SOME (flatten v') /\ size_of_shape (shape_of v') <= 32)
        end
    | SOME (panSem.FinalFFI f) => res1 = SOME (FinalFFI f)
    end.
Proof.
  intros v v1 res s1 t ctxt Hpre.
  destruct (pc_all (v, v1) res s1 t ctxt Hpre) as (res1 & t1 & E & Hs & Hc & He & Hp).
  exists res1, t1. split; [exact E|]. split; [exact Hs|]. split; [exact Hc|]. split; [exact He|].
  destruct res as [[| | | |rv|e0 ev|f]|]; cbn [pc_post] in Hp; try exact Hp.
  - exact (proj1 Hp).
  - destruct (FLOOKUP (eids ctxt) e0); [|exact Hp]. destruct Hp as (H1 & _ & H3). split; assumption.
Qed.

End PC.

(** ** Whole programs *)

Section Programs.
Context {a : N}.

Lemma MAP_FST_compile_to_crep (prog : list (decl a)) :
  MAP FST (compile_to_crep prog) = MAP FST (functions prog).
Proof.
  unfold compile_to_crep. cbv zeta.
  generalize (comp_func (make_funcs (functions prog)) (get_eids_from_decls prog)) as cf.
  generalize (functions prog) as l. intros l cf.
  induction l as [|[n [p [b r]]] l IH]; [reflexivity|]. cbn [MAP List.map FST fst]. f_equal. exact IH.
Qed.

Lemma MAP_FST_compile_inl_prog inl (prog : list (mlstring * (list N * crepLang.prog a))) :
  MAP FST (crep_inline.compile_inl_prog inl prog) = MAP FST prog.
Proof.
  unfold crep_inline.compile_inl_prog. induction prog as [|[n [p b]] l IH]; [reflexivity|].
  cbn [MAP List.map FST fst]. f_equal. exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "first_compile_prog_all_distinct" *)
Theorem first_compile_prog_all_distinct : forall prog : list (decl a),
  ALL_DISTINCT (MAP FST (functions prog)) ->
  ALL_DISTINCT (MAP FST (compile_prog prog)).
Proof.
  intros prog H. unfold compile_prog, crep_inline.compile_inl_top. cbv zeta.
  rewrite MAP_FST_compile_inl_prog, MAP_FST_compile_to_crep. exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "first_compile_to_crep_all_distinct" *)
Theorem first_compile_to_crep_all_distinct : forall prog : list (decl a),
  ALL_DISTINCT (MAP FST (functions prog)) ->
  ALL_DISTINCT (MAP FST (compile_to_crep prog)).
Proof. intros prog H. rewrite MAP_FST_compile_to_crep. exact H. Qed.

Lemma ALOOKUP_compile_to_crep (prog : list (decl a)) f :
  ALOOKUP (compile_to_crep prog) f =
  OPTION_MAP (fun '(params, (body, ret)) =>
                (crep_vars params, comp_func (make_funcs (functions prog)) (get_eids_from_decls prog) params body))
             (ALOOKUP (functions prog) f).
Proof.
  unfold compile_to_crep. cbv zeta.
  generalize (comp_func (make_funcs (functions prog)) (get_eids_from_decls prog)) as cf.
  generalize (functions prog) as l. intros l cf.
  induction l as [|[n [p [b r]]] l IH]; [reflexivity|]. cbn [MAP List.map ALOOKUP].
  destruct (decide (n = f)); [reflexivity|exact IH].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "alookup_compile_prog_code" *)
Theorem alookup_compile_prog_code : forall (pan_code : list (decl a)) start prog rshape,
  ALL_DISTINCT (MAP FST (functions pan_code)) /\
  ALOOKUP (functions pan_code) start = SOME ([], (prog, rshape)) ->
  ALOOKUP (compile_to_crep pan_code) start =
  SOME ([], comp_func (make_funcs (functions pan_code)) (get_eids_from_decls pan_code) [] prog).
Proof.
  intros pan_code start prog rshape [_ H]. rewrite ALOOKUP_compile_to_crep, H. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "el_compile_prog_el_prog_eq" *)
Theorem el_compile_prog_el_prog_eq : forall (prog : list (decl a)) n start cprog p rshape,
  EL n (compile_to_crep prog) = (start, ([], cprog)) /\
  ALL_DISTINCT (MAP FST (functions prog)) /\ n < LENGTH (functions prog) /\
  ALOOKUP (functions prog) start = SOME ([], (p, rshape)) ->
  EL n (functions prog) = (start, ([], (p, rshape))).
Proof.
  intros prog n start cprog p rshape (Hel & Hd & Hn & Hal).
  assert (Hfst : FST (EL n (functions prog)) = start).
  { pose proof (f_equal FST Hel) as E. cbn [FST fst] in E. rewrite <- E.
    rewrite <- !(EL_MAP' FST) by (try rewrite LENGTH_MAP'; try (unfold compile_to_crep; cbv zeta; rewrite LENGTH_MAP'); exact Hn).
    rewrite MAP_FST_compile_to_crep. reflexivity. }
  pose proof (ALOOKUP_ALL_DISTINCT_EL (functions prog) n (conj Hn Hd)) as E.
  rewrite Hfst, Hal in E. injection E as E.
  destruct (EL n (functions prog)) as [x y]. cbn [FST SND fst snd] in Hfst, E. subst. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mod_eq_lt_eq" *)
Theorem mod_eq_lt_eq : forall n x m : N, n < x /\ m < x /\ n mod x = m mod x -> n = m.
Proof. intros n x m (H1 & H2 & E). rewrite !N.mod_small in E by assumption. exact E. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "compile_prog_distinct_params" *)
Theorem compile_prog_distinct_params : forall prog : list (decl a),
  EVERY (fun '(name, (params, body)) => ALL_DISTINCT params) (compile_prog prog).
Proof.
  intros prog. unfold compile_prog, crep_inline.compile_inl_top, crep_inline.compile_inl_prog, compile_to_crep.
  cbv zeta. generalize (comp_func (make_funcs (functions prog)) (get_eids_from_decls prog)) as cf.
  generalize (functions prog) as l. intros l cf. unfold is_true. rewrite EVERY_Forall, Forall_forall.
  intros x Hx. apply in_map_iff in Hx as ([n [ps b]] & <- & Hx).
  apply in_map_iff in Hx as ([n' [ps' [b' r']]] & E & _). injection E as <- <- _.
  unfold crep_vars. cbv zeta. apply ALL_DISTINCT_GENLIST. intros m1 m2 (_ & _ & E). exact E.
Qed.

Lemma make_funcs_lookup (l : list (mlstring * (list (mlstring * shape) * (panLang.prog a * shape)))) f :
  FLOOKUP (make_funcs l) f = OPTION_MAP (fun '(p, (b, r)) => (p, r)) (ALOOKUP l f).
Proof.
  unfold make_funcs. cbv zeta. rewrite FLOOKUP_alist_to_fmap.
  induction l as [|[n [p [b r]]] l IH]; [reflexivity|]. cbn. destruct (decide (n = f)); [reflexivity|exact IH].
Qed.

Lemma MAX_LIST_GENLIST_I n : MAX_LIST (GENLIST I n) = n - 1.
Proof.
  assert (Happ : forall l x, MAX_LIST (l ++ [x]) = N.max (MAX_LIST l) x).
  { induction l as [|y l IH]; intros x; cbn [app MAX_LIST]; unfold MAX.
    - destruct (N.ltb_spec x 0); lia.
    - rewrite IH. unfold MAX. destruct (N.ltb_spec y (N.max (MAX_LIST l) x)), (N.ltb_spec y (MAX_LIST l)); lia. }
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm I n)), SNOC_app, Happ, IH. unfold I. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mk_ctxt_code_imp_code_rel" *)
Theorem mk_ctxt_code_imp_code_rel : forall pan_code : list (decl a),
  ALL_DISTINCT (MAP FST (functions pan_code)) /\
  EVERY (panProps.localised_prog ∘ FST ∘ SND ∘ SND) (functions pan_code) ->
  code_rel (mk_ctxt FEMPTY (make_funcs (functions pan_code)) 0 (get_eids_from_decls pan_code))
    (alist_to_fmap (functions pan_code)) (alist_to_fmap (compile_to_crep pan_code)).
Proof.
  intros pan_code [_ Hloc] f vshs prog rsh Hf. rewrite FLOOKUP_alist_to_fmap in Hf.
  split.
  { unfold is_true in Hloc. rewrite EVERY_Forall, Forall_forall in Hloc.
    exact (Hloc _ (ALOOKUP_In _ _ _ Hf)). }
  split; [unfold mk_ctxt; cbn [funcs]; rewrite make_funcs_lookup, Hf; reflexivity|].
  cbv zeta. rewrite FLOOKUP_alist_to_fmap, ALOOKUP_compile_to_crep, Hf. cbn [OPTION_MAP].
  unfold mk_ctxt, comp_func, crep_vars, make_vmap, ctxt_fc. cbv zeta. cbn [funcs eids].
  rewrite MAX_LIST_GENLIST_I. reflexivity.
Qed.

Lemma LENGTH_exceptions (pc : list (decl a)) : LENGTH (exceptions pc) = LENGTH (FILTER is_exn_decl pc).
Proof. induction pc as [|[] pc IH]; cbn; try rewrite IH; reflexivity. Qed.

Lemma ALOOKUP_MAP2_GENLIST {B} : forall (xs : list mlstring) (f : N -> B) e v,
  ALOOKUP (MAP2 (fun x y => (x, y)) xs (GENLIST f (LENGTH xs))) e = SOME v ->
  exists i, i < LENGTH xs /\ v = f i /\ EL i xs = e.
Proof.
  induction xs as [|x xs IH]; intros f e v H; [discriminate|].
  replace (LENGTH (x :: xs)) with (SUC (LENGTH xs)) in H |- * by (cbn [LENGTH]; lia).
  rewrite GENLIST_CONS_aux in H.
  cbn [MAP2 ALOOKUP] in H. destruct (decide (x = e)) as [->|Hne].
  - injection H as <-. exists 0. split; [lia|]. split; [reflexivity|apply EL_cons_0].
  - destruct (IH (fun i => f (SUC i)) e v H) as (i & Hi & -> & Hel).
    exists (SUC i). split; [lia|]. split; [reflexivity|]. rewrite EL_cons_pos by lia.
    replace (SUC i - 1) with i by lia. exact Hel.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "get_eids_imp_excp_rel" *)
Theorem get_eids_imp_excp_rel : forall (seids : fmap eid shape) (pc : list (decl a)),
  size_of_eids pc < dimword a /\ FDOM seids = FDOM (get_eids_from_decls pc) ->
  excp_rel (get_eids_from_decls pc) seids.
Proof.
  intros seids pc [Hsz Hd]. split; [exact Hd|]. intros e e' n n' (H1 & H2 & <-).
  unfold get_eids_from_decls in H1, H2. cbv zeta in H1, H2. rewrite FLOOKUP_alist_to_fmap in H1, H2.
  destruct (ALOOKUP_MAP2_GENLIST _ (fun x => n2w x) _ _ H1) as (i & Hi & Ei & Eli).
  destruct (ALOOKUP_MAP2_GENLIST _ (fun x => n2w x) _ _ H2) as (j & Hj & Ej & Elj).
  rewrite LENGTH_MAP', LENGTH_exceptions in Hi, Hj. unfold size_of_eids in Hsz.
  rewrite Ei in Ej. apply (f_equal w2n) in Ej. rewrite !w2n_n2w, !N.mod_small in Ej by lia.
  subst j. rewrite <- Eli, <- Elj. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mk_ctxt_imp_locals_rel" *)
Theorem mk_ctxt_imp_locals_rel :
  forall (pc : list (mlstring * (list (mlstring * shape) * (panLang.prog a * shape))))
    (lcl : fmap varname (word_lab a)) es,
  locals_rel (mk_ctxt FEMPTY (make_funcs pc) 0 es) FEMPTY lcl.
Proof.
  intros pc lcl es. split; [split|split; [split|]].
  - intros x a0 xs H. discriminate H.
  - intros x y a0 b xs ys (H & _). discriminate H.
  - lia.
  - intros v a0 xs H. discriminate H.
  - intros vn v H. discriminate H.
Qed.

End Programs.

(** ** Observable semantics *)

Section SemanticsProof.
Context {a : N} {ffi_t : Type}.

(** Galette-only: [panSem.semantics] in the form of
    [crep_to_loopProof.semantics_wrapper] (cf. [crep_sem_is_wrapper]). *)
Lemma pan_sem_is_wrapper (s : panSem.state a ffi_t) start :
  panSem.semantics s start =
  let prog := panLang.Call NONE start [] in
  crep_to_loopProof.semantics_wrapper
    (((fun res => match res with
                  | SOME panSem.TimeOut => Incomplete
                  | SOME (panSem.FinalFFI e) => CompleteResult (FFI_outcome e)
                  | SOME (panSem.Return _) => CompleteResult Success
                  | _ => RunError
                  end) ## (fun s => io_events (panSem.ffi s))) ∘
     (fun k => panSem.evaluate (prog, panSem.set_clock k s))).
Proof.
  unfold panSem.semantics, crep_to_loopProof.semantics_wrapper. cbv zeta.
  match goal with |- (if classical_dec ?P1 then _ else _) = (if classical_dec ?P2 then _ else _) =>
    replace P2 with P1
  end.
  2: { apply propositional_extensionality. split.
       - intros [k Hk]. exists k. eexists. unfold PAIR_MAP.
         destruct (fst (panSem.evaluate _)) as [[]|]; try contradiction; reflexivity.
       - intros [k [v Hk]]. exists k. pose proof (f_equal fst Hk) as Hk'. clear Hk.
         unfold PAIR_MAP in Hk'. cbv beta in Hk'. cbn [fst] in Hk'.
         destruct (fst (panSem.evaluate _)) as [[]|]; try discriminate; exact Logic.I. }
  destruct (classical_dec _); [reflexivity|].
  match goal with |- match some ?Q1 with _ => _ end = match some ?Q2 with _ => _ end =>
    replace Q2 with Q1
  end.
  2: { apply functional_extensionality; intros res; apply propositional_extensionality. split.
       - intros (k & t & r & out & H1 & H2 & H3). exists k, out, (io_events (panSem.ffi t)).
         unfold PAIR_MAP. rewrite H1. cbn [fst snd].
         split; [|exact H3]. destruct r as [[]|]; try contradiction; subst out; reflexivity.
       - intros (k & r & ev & H1 & H2).
         pose proof (f_equal snd H1) as H1'. pose proof (f_equal fst H1) as H1''. clear H1.
         unfold PAIR_MAP in H1', H1''. cbn [fst snd] in H1', H1''. rename H1'' into H1.
         exists k, (snd (panSem.evaluate (panLang.Call NONE start [], panSem.set_clock k s))),
           (fst (panSem.evaluate (panLang.Call NONE start [], panSem.set_clock k s))), r.
         split; [apply surjective_pairing|]. rewrite <- H1' in H2.
         split; [|exact H2].
         destruct (fst (panSem.evaluate _)) as [[]|]; try discriminate; injection H1 as <-;
           reflexivity. }
  reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics_to_crep" *)
Theorem state_rel_imp_semantics_to_crep :
  forall (s : panSem.state a ffi_t) (t : state a ffi_t) (pan_code : list (decl a)) start,
    state_rel s t /\
    ALL_DISTINCT (MAP FST (functions pan_code)) /\
    panSem.code s = alist_to_fmap (functions pan_code) /\
    code t = alist_to_fmap (compile_to_crep pan_code) /\
    panSem.locals s = FEMPTY /\
    EVERY (panProps.localised_prog ∘ FST ∘ SND ∘ SND) (functions pan_code) /\
    size_of_eids pan_code < dimword a /\
    FDOM (panSem.eshapes s) = FDOM (get_eids_from_decls pan_code) /\
    panSem.semantics s start <> Fail ->
    semantics t start = panSem.semantics s start.
Proof.
  intros s t pan_code start (Hs & Hd & Hsc & Htc & Hsl & Hloc & Hsz & Hfd & Hsem).
  set (nctxt := mk_ctxt FEMPTY (make_funcs (functions pan_code)) 0 (get_eids_from_decls pan_code)).
  assert (Hcr : code_rel nctxt (panSem.code s) (code t))
    by (rewrite Hsc, Htc; apply mk_ctxt_code_imp_code_rel; split; assumption).
  assert (Her : excp_rel (eids nctxt) (panSem.eshapes s))
    by (apply get_eids_imp_excp_rel; split; assumption).
  assert (Hlr : locals_rel nctxt (panSem.locals s) (locals t)) by (rewrite Hsl; apply mk_ctxt_imp_locals_rel).
  rewrite pan_sem_is_wrapper in Hsem |- *. rewrite crep_to_loopProof.crep_sem_is_wrapper. cbv zeta in Hsem |- *.
  f_equal. apply functional_extensionality. intros k. unfold PAIR_MAP. cbv beta.
  destruct (panSem.evaluate (panLang.Call NONE start [], panSem.set_clock k s)) as [q u] eqn:E.
  assert (Hq : q <> SOME panSem.Error).
  { intros ->. apply Hsem. unfold crep_to_loopProof.semantics_wrapper.
    destruct (classical_dec _) as [_|Hn]; [reflexivity|]. exfalso; apply Hn.
    exists k, (io_events (panSem.ffi u)). unfold PAIR_MAP. cbv beta. rewrite E. reflexivity. }
  destruct (pc_compile_correct (panLang.Call NONE start []) (panSem.set_clock k s) q u (set_clock k t) nctxt)
    as (res1 & t1 & E1 & Hs1 & _ & _ & Hpost).
  { split; [exact E|]. split; [exact Hq|]. split; [srel Hs|]. pcbn; ccbn. csplit; try assumption.
    reflexivity. }
  cbn [compile MAP List.map FLAT List.concat] in E1. rewrite E1. cbn [fst snd].
  pose proof Hs1 as (_ & _ & _ & _ & _ & _ & _ & Hff1 & _). rewrite Hff1.
  destruct q as [[| | | |rv|e0 ev|f]|]; try contradiction.
  all: try (subst res1; reflexivity).
  all: try (destruct Hpost as [-> _]; reflexivity).
  destruct (FLOOKUP (eids nctxt) e0); [|contradiction]. destruct Hpost as [-> _]. reflexivity.
Qed.

End SemanticsProof.


Section DeclsProof.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "decs_stcnames_lemma" *)
Local Theorem decs_stcnames_lemma : forall ctxt (code : list (decl a)),
  EVERY (fun d => is_function d || is_exn_decl d) code ->
  panSem.decs_stcnames ctxt code = SOME ctxt.
Proof.
  intros ctxt code H. apply panProps.decs_stcnames_only_functions.
  unfold is_true in *. rewrite EVERY_Forall in *. eapply Forall_impl; [|exact H].
  intros d. unfold is_true. destruct d; cbn; congruence.
Qed.

Lemma FDOM_FEMPTY_FUPDATE_LIST {K V} `{EqDecision K} (l : list (K * V)) k :
  FDOM (FEMPTY |++ l) k <-> In k (map fst l).
Proof.
  unfold FDOM. rewrite flookup_fupdate_list. cbn [FLOOKUP].
  destruct (ALOOKUP (REVERSE l) k) eqn:E.
  - split; [intros _|intros _; discriminate]. apply ALOOKUP_In, in_rev in E.
    exact (in_map fst _ _ E).
  - apply ALOOKUP_None_iff in E. split; [intros C; contradiction|]. intros Hin. exfalso. apply E.
    rewrite map_rev. apply (proj1 (in_rev _ _)). exact Hin.
Qed.

Lemma map_fst_MAP2_pair {K V} (ks : list K) (vs : list V) :
  LENGTH ks = LENGTH vs -> map fst (MAP2 (fun x y => (x, y)) ks vs) = ks.
Proof.
  revert vs; induction ks as [|k ks IH]; intros [|v vs] Hl; cbn [LENGTH] in Hl; try lia; [reflexivity|].
  cbn [MAP2 map fst]. f_equal. apply IH. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics_decls_to_crep" *)
Theorem state_rel_imp_semantics_decls_to_crep :
  forall (s : panSem.state a ffi_t) (t : state a ffi_t) (pan_code : list (decl a)) start,
    state_rel (panSem.set_structs [] s) t /\
    ALL_DISTINCT (MAP FST (functions pan_code)) /\
    panSem.code s = FEMPTY /\
    code t = alist_to_fmap (compile_to_crep pan_code) /\
    panSem.locals s = FEMPTY /\
    panSem.eshapes s = FEMPTY /\
    EVERY (panProps.localised_prog ∘ FST ∘ SND ∘ SND) (functions pan_code) /\
    EVERY (fun x => is_function x || is_exn_decl x) pan_code /\
    size_of_eids pan_code < dimword a /\
    panSem.semantics_decls s start pan_code <> Fail ->
    semantics t start = panSem.semantics_decls s start pan_code.
Proof.
  intros s t pan_code start (Hs & Hd & Hsc & Htc & Hsl & Hse & Hloc & Hfe & Hsz & Hsem).
  unfold panSem.semantics_decls in *. rewrite decs_stcnames_lemma in * by exact Hfe.
  destruct (panSem.evaluate_decls (panSem.set_structs [] s) pan_code) as [s'|] eqn:Ed; [|contradiction].
  rewrite (panProps.evaluate_decls_only_funs_and_exn_decls _ _ _ (conj Hfe Ed)) in Hsem |- *.
  cbn [panSem.set_structs panSem.eshapes panSem.code] in Hsem |- *. rewrite Hsc, Hse in Hsem |- *.
  apply (state_rel_imp_semantics_to_crep _ _ pan_code). pcbn. cbn [panSem.set_eshapes panSem.set_code panSem.set_structs
    panSem.eshapes panSem.code panSem.locals].
  split; [|split; [exact Hd|]].
  { unfold state_rel in *. pcbn. cbn [panSem.set_eshapes panSem.set_code panSem.set_structs] in *.
    pcbn. exact Hs. }
  split.
  { apply fmap_ext. intros k. rewrite FLOOKUP_FEMPTY_FUPDATE_LIST_distinct, FLOOKUP_alist_to_fmap; [reflexivity|].
    apply ALL_DISTINCT_iff. exact Hd. }
  split; [exact Htc|]. split; [exact Hsl|]. split; [exact Hloc|]. split; [exact Hsz|].
  split; [|exact Hsem].
  apply functional_extensionality. intros k. apply propositional_extensionality.
  rewrite FDOM_FEMPTY_FUPDATE_LIST. unfold get_eids_from_decls. cbv zeta. unfold FDOM.
  rewrite FLOOKUP_alist_to_fmap. split.
  - intros Hin E. apply ALOOKUP_None_iff in E. apply E.
    rewrite map_fst_MAP2_pair by (rewrite LENGTH_GENLIST'; reflexivity). exact Hin.
  - intros Hn. destruct (in_dec (fun x y => decide (x = y)) k (map fst (exceptions pan_code))) as [Hin|Hnin];
      [exact Hin|]. exfalso. apply Hn. apply ALOOKUP_None_iff.
    rewrite map_fst_MAP2_pair by (rewrite LENGTH_GENLIST'; reflexivity). exact Hnin.
Qed.

(** Galette-only: [semantics] is [Fail] when the start function is not in
    the code. *)
Lemma semantics_no_start (t : state a ffi_t) start :
  FLOOKUP (code t) start = NONE -> semantics t start = Fail.
Proof.
  intros Hf. unfold semantics. cbv zeta. destruct (classical_dec _) as [_|Hn]; [reflexivity|].
  exfalso. apply Hn. exists 0. rewrite crepProps.evaluate_unfold. cbn [evaluate_body OPT_MMAP].
  unfold lookup_code. cbn [code set_clock]. rewrite Hf. exact Logic.I.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics :
  forall (s : panSem.state a ffi_t) (t : state a ffi_t) (pan_code : list (decl a)) start,
    state_rel s t /\
    ALL_DISTINCT (MAP FST (functions pan_code)) /\
    panSem.code s = alist_to_fmap (functions pan_code) /\
    code t = alist_to_fmap (compile_prog pan_code) /\
    panSem.locals s = FEMPTY /\
    EVERY (panProps.localised_prog ∘ FST ∘ SND ∘ SND) (functions pan_code) /\
    size_of_eids pan_code < dimword a /\
    FDOM (panSem.eshapes s) = FDOM (get_eids_from_decls pan_code) /\
    panSem.semantics s start <> Fail ->
    semantics t start = panSem.semantics s start.
Proof.
  intros s t pan_code start (Hs & Hd & Hsc & Htc & Hsl & Hloc & Hsz & Hfd & Hsem).
  set (crep_code := compile_to_crep pan_code).
  set (t_un := set_code (alist_to_fmap crep_code) t).
  assert (E1 : semantics t_un start = panSem.semantics s start).
  { apply (state_rel_imp_semantics_to_crep s t_un pan_code start).
    split; [exact Hs|]. split; [exact Hd|]. split; [exact Hsc|]. split; [reflexivity|].
    split; [exact Hsl|]. split; [exact Hloc|]. split; [exact Hsz|]. split; [exact Hfd|exact Hsem]. }
  rewrite <- E1. rewrite <- E1 in Hsem.
  destruct (FLOOKUP (code t_un) start) as [[ns prog]|] eqn:Hf.
  - apply (crep_inlineProof.state_rel_imp_semantics t_un t crep_code start
             (MAP FST (functions (FILTER inlinable pan_code))) ns prog).
    split; [repeat split|]. split; [reflexivity|].
    split; [apply first_compile_to_crep_all_distinct, Hd|]. split; [reflexivity|].
    split; [rewrite Htc; reflexivity|]. split; [exact Hf|exact Hsem].
  - exfalso. apply Hsem. apply semantics_no_start, Hf.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics_decls" *)
Theorem state_rel_imp_semantics_decls :
  forall (s : panSem.state a ffi_t) (t : state a ffi_t) (pan_code : list (decl a)) start,
    state_rel (panSem.set_structs [] s) t /\
    ALL_DISTINCT (MAP FST (functions pan_code)) /\
    panSem.code s = FEMPTY /\
    code t = alist_to_fmap (compile_prog pan_code) /\
    panSem.locals s = FEMPTY /\
    panSem.eshapes s = FEMPTY /\
    EVERY (panProps.localised_prog ∘ FST ∘ SND ∘ SND) (functions pan_code) /\
    EVERY (fun x => is_function x || is_exn_decl x) pan_code /\
    size_of_eids pan_code < dimword a /\
    panSem.semantics_decls s start pan_code <> Fail ->
    semantics t start = panSem.semantics_decls s start pan_code.
Proof.
  intros s t pan_code start (Hs & Hd & Hsc & Htc & Hsl & Hse & Hloc & Hfe & Hsz & Hsem).
  unfold panSem.semantics_decls in *. rewrite decs_stcnames_lemma in * by exact Hfe.
  destruct (panSem.evaluate_decls (panSem.set_structs [] s) pan_code) as [s'|] eqn:Ed; [|contradiction].
  rewrite (panProps.evaluate_decls_only_funs_and_exn_decls _ _ _ (conj Hfe Ed)) in Hsem |- *.
  cbn [panSem.set_structs panSem.eshapes panSem.code] in Hsem |- *. rewrite Hsc, Hse in Hsem |- *.
  apply (state_rel_imp_semantics _ _ pan_code). pcbn. cbn [panSem.set_eshapes panSem.set_code panSem.set_structs
    panSem.eshapes panSem.code panSem.locals].
  split; [|split; [exact Hd|]].
  { unfold state_rel in *. pcbn. cbn [panSem.set_eshapes panSem.set_code panSem.set_structs] in *.
    pcbn. exact Hs. }
  split.
  { apply fmap_ext. intros k. rewrite FLOOKUP_FEMPTY_FUPDATE_LIST_distinct, FLOOKUP_alist_to_fmap; [reflexivity|].
    apply ALL_DISTINCT_iff. exact Hd. }
  split; [exact Htc|]. split; [exact Hsl|]. split; [exact Hloc|]. split; [exact Hsz|].
  split; [|exact Hsem].
  apply functional_extensionality. intros k. apply propositional_extensionality.
  rewrite FDOM_FEMPTY_FUPDATE_LIST. unfold get_eids_from_decls. cbv zeta. unfold FDOM.
  rewrite FLOOKUP_alist_to_fmap. split.
  - intros Hin E. apply ALOOKUP_None_iff in E. apply E.
    rewrite map_fst_MAP2_pair by (rewrite LENGTH_GENLIST'; reflexivity). exact Hin.
  - intros Hn. destruct (in_dec (fun x y => decide (x = y)) k (map fst (exceptions pan_code))) as [Hin|Hnin];
      [exact Hin|]. exfalso. apply Hn. apply ALOOKUP_None_iff.
    rewrite map_fst_MAP2_pair by (rewrite LENGTH_GENLIST'; reflexivity). exact Hnin.
Qed.

End DeclsProof.

(** ** Further lemmas of the HOL script (not used by the proofs above) *)

Section Aux.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_funcs_eq" *)
Theorem ctxt_fc_funcs_eq : forall cvs (em : fmap eid (word a)) vs shs ns,
  funcs (ctxt_fc cvs em vs shs ns) = cvs.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_eids_eq" *)
Theorem ctxt_fc_eids_eq : forall cvs (em : fmap eid (word a)) vs shs ns,
  eids (ctxt_fc cvs em vs shs ns) = em.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "ctxt_fc_vmax" *)
Theorem ctxt_fc_vmax : forall (ctxt : context a) (em : fmap eid (word a)) vs shs ns,
  vmax (ctxt_fc (funcs ctxt) em vs shs ns) = MAX_LIST ns.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_def" *)
Definition slc (vshs : list (mlstring * shape)) (args : list (panSem.v a)) : fmap mlstring (panSem.v a) :=
  FEMPTY |++ ZIP (MAP FST vshs, args).

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "tlc_def" *)
Definition tlc (ns : list N) (args : list (panSem.v a)) : fmap N (word_lab a) :=
  FEMPTY |++ ZIP (ns, FLAT (MAP flatten args)).

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_tlc_rw" *)
Theorem slc_tlc_rw : forall vsh (args : list (panSem.v a)) ns,
  FEMPTY |++ ZIP (MAP FST vsh, args) = slc vsh args /\
  FEMPTY |++ ZIP (ns, FLAT (MAP flatten args)) = tlc ns args.
Proof. split; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_APPEND" *)
Theorem MAX_LIST_APPEND : forall l1 l2 : list N, MAX_LIST (l1 ++ l2) = MAX (MAX_LIST l1) (MAX_LIST l2).
Proof.
  induction l1 as [|y l1 IH]; intros l2; cbn [app MAX_LIST].
  - unfold MAX. destruct (N.ltb_spec 0 (MAX_LIST l2)); lia.
  - rewrite IH. unfold MAX.
    destruct (N.ltb_spec (MAX_LIST l1) (MAX_LIST l2)), (N.ltb_spec y (MAX_LIST l1)),
      (N.ltb_spec y (MAX_LIST l2)), (N.ltb_spec y (if MAX_LIST l1 <? MAX_LIST l2 then MAX_LIST l2 else MAX_LIST l1));
      try lia; destruct (N.ltb_spec (MAX_LIST l1) (MAX_LIST l2)); lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MAX_LIST_NOT_MEM" *)
Theorem MAX_LIST_NOT_MEM : forall (x : N) l, x > MAX_LIST l -> ~ MEM x l.
Proof. intros x l Hx Hm. apply MEM_In, MAX_LIST_ge in Hm. lia. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "evaluate_replicate_const" *)
Theorem evaluate_replicate_const : forall n (s : state a ffi_t),
  OPT_MMAP (eval s) (REPLICATE n (Const (n2w 0))) = SOME (REPLICATE n (Word (n2w 0))).
Proof. intros n s. apply opt_mmap_eq_some, eval_replicate_const. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "not_none_then_some" *)
Theorem not_none_then_some : forall {A} (x : option A), x <> NONE <-> exists a0, x = SOME a0.
Proof. intros A [y|]; split; [intros _; exists y; reflexivity|discriminate|intros H; contradiction|]. intros [y H]; discriminate. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_id_update" *)
Local Theorem locals_id_update : forall t : state a ffi_t, set_locals (locals t) t = t.
Proof. exact set_locals_id. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "flookup_res_var_thm_quant" *)
Theorem flookup_res_var_thm_quant : forall (l : fmap varname (word_lab a)) m (v : option (word_lab a)) n,
  FLOOKUP (res_var l (m, v)) n = if decide (n = m) then v else FLOOKUP l n.
Proof. intros; apply FLOOKUP_res_var. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "res_var_commutes'" *)
Theorem res_var_commutes' : forall n h (lc : fmap varname (word_lab a)) v v',
  n <> h -> res_var (res_var lc (h, v)) (n, v') = res_var (res_var lc (n, v')) (h, v).
Proof.
  intros n h lc v v' Hne. apply fmap_ext. intros k. rewrite !FLOOKUP_res_var.
  destruct (decide (k = n)), (decide (k = h)); congruence.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "update_locals_not_vars_eval_mmap" *)
Theorem update_locals_not_vars_eval_mmap : forall (es : list (exp a)) x v (t : state a ffi_t),
  (forall n e, MEM e es /\ MEM n (var_cexp e) -> n <> x) ->
  OPT_MMAP (eval (set_locals (locals t |+ (x, v)) t)) es = OPT_MMAP (eval t) es.
Proof.
  intros es x v t H. apply OPT_MMAP_ext_In''. intros e He.
  apply update_locals_not_vars_eval_eq'; [exact v|]. intros Hm. apply (H x e); [|reflexivity].
  split; [apply MEM_In, He|exact Hm].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_distinct_lists_not_affect" *)
Theorem eval_distinct_lists_not_affect : forall vs (s : state a ffi_t) e (nvals : list (word_lab a)),
  LENGTH vs = LENGTH nvals /\ distinct_lists vs (var_cexp e) ->
  eval (set_locals (locals s |++ ZIP (vs, nvals)) s) e = eval s e.
Proof.
  intros vs s e nvals [_ Hd].
  rewrite (eval_locals_cong s _ (locals s) e); [apply f_equal2; [|reflexivity]; apply set_locals_id|].
  intros n Hn. apply FLOOKUP_FUPDATE_LIST_notin. intros Hin. apply In_map_fst_ZIP in Hin.
  exact (proj1 (distinct_lists_iff _ _) Hd n Hin Hn).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_distinct_lists_not_affect'" *)
Theorem eval_distinct_lists_not_affect' : forall vs (s : state a ffi_t) e w (nvals : list (word_lab a)),
  eval s e = SOME w /\ LENGTH vs = LENGTH nvals /\ distinct_lists vs (var_cexp e) ->
  eval (set_locals (locals s |++ ZIP (vs, nvals)) s) e = SOME w.
Proof.
  intros vs s e w nvals (He & Hl & Hd). rewrite eval_distinct_lists_not_affect by (split; assumption). exact He.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "opt_mmap_eval_distinct_lists_not_affect'" *)
Theorem opt_mmap_eval_distinct_lists_not_affect' : forall (es : list (exp a)) (s : state a ffi_t) vs
    (nvals : list (word_lab a)),
  LENGTH vs = LENGTH nvals /\ distinct_lists vs (FLAT (MAP var_cexp es)) ->
  OPT_MMAP (eval (set_locals (locals s |++ ZIP (vs, nvals)) s)) es = OPT_MMAP (eval s) es.
Proof.
  intros es s vs nvals [Hl Hd]. apply OPT_MMAP_ext_In''. intros e He.
  apply eval_distinct_lists_not_affect. split; [exact Hl|].
  apply distinct_lists_iff. intros x Hx Hy. apply (proj1 (distinct_lists_iff _ _) Hd x Hx).
  eapply In_FLAT_MAP; eassumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "opt_mmap_eval_distinct_lists_not_affect" *)
Theorem opt_mmap_eval_distinct_lists_not_affect : forall (es : list (exp a)) (s : state a ffi_t) ws vs
    (nvals : list (word_lab a)),
  OPT_MMAP (eval s) es = SOME ws /\
  LENGTH vs = LENGTH nvals /\ distinct_lists vs (FLAT (MAP var_cexp es)) ->
  OPT_MMAP (eval (set_locals (locals s |++ ZIP (vs, nvals)) s)) es = SOME ws.
Proof.
  intros es s ws vs nvals (He & Hl & Hd).
  rewrite opt_mmap_eval_distinct_lists_not_affect' by (split; assumption). exact He.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "no_overlap_wrap_rt_some_all_distinct" *)
Theorem no_overlap_wrap_rt_some_all_distinct : forall {K} `{EqDecision K} (fm : fmap K (shape * list N)) r vsh ns,
  no_overlap fm /\ wrap_rt (FLOOKUP fm r) = SOME (vsh, ns) -> ALL_DISTINCT ns.
Proof.
  intros K EK fm r vsh ns [Hno Hw]. apply wrap_rt_some in Hw.
  exact (all_distinct_flookup_all_distinct fm r vsh ns (conj Hno Hw)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "shape_of_alt" *)
Theorem shape_of_alt : forall x : word_lab a, shape_of (panSem.Val x) = One.
Proof. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "filter_not_mem_self" *)
Theorem filter_not_mem_self : forall l : list N, FILTER (fun x => negb (MEM x l)) l = [].
Proof.
  intros l. destruct (filter (fun x => negb (MEM x l)) l) as [|y m] eqn:E; [reflexivity|exfalso].
  assert (Hy : In y (filter (fun x => negb (MEM x l)) l)) by (rewrite E; left; reflexivity).
  apply filter_In in Hy as [Hy Hn]. apply MEM_In in Hy. rewrite Hy in Hn. discriminate.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "EL_load_globals" *)
Theorem EL_load_globals : forall n m (w : word 5),
  n < m -> EL n (@load_globals a w m) = LoadGlob (w + n2w n)%w.
Proof.
  intros n m. revert n. induction m as [|m IH] using N.peano_ind; intros n w Hn; [lia|].
  rewrite (proj2 (load_globals_def w m)).
  destruct (N.eq_dec n 0) as [->|Hn0].
  - rewrite EL_cons_0. f_equal. word_ring.
  - rewrite EL_cons_pos by lia. rewrite IH by lia. f_equal.
    replace n with (1 + (n - 1)) at 2 by lia. rewrite <- word_add_n2w. word_ring.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "MEM_compile_exp_vmax" *)
Theorem MEM_compile_exp_vmax : forall (ctxt : context a) exp n e,
  ctxt_max (vmax ctxt) (vars ctxt) /\ MEM n (var_cexp e) /\ MEM e (FST (compile_exp ctxt exp)) ->
  n <= vmax ctxt.
Proof.
  intros ctxt exp n e ([_ Hmx] & Hn & He).
  destruct (compile_exp_vars ctxt exp n) as (v & shp & ns & H1 & H2).
  - eapply In_FLAT_MAP; [apply MEM_In, He|apply MEM_In, Hn].
  - exact (Hmx _ _ _ H1 n (proj2 (MEM_In _ _) H2)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "genlist_vmax_distinct_lists_compiled_exps" *)
Theorem genlist_vmax_distinct_lists_compiled_exps : forall (ctxt : context a) n argexps,
  ctxt_max (vmax ctxt) (vars ctxt) ->
  distinct_lists (GENLIST (fun x => SUC x + vmax ctxt) n)
    (FLAT (MAP var_cexp (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))))).
Proof.
  intros ctxt n argexps Hmx. apply distinct_lists_iff. intros x Hx Hy.
  apply In_GENLIST_iff in Hx as (i & _ & ->).
  apply in_concat in Hy as (vs & Hvs & Hy). apply in_map_iff in Hvs as (ce & <- & Hce).
  apply in_concat in Hce as (ces & Hces & Hce). rewrite map_map in Hces.
  apply in_map_iff in Hces as (e & <- & _).
  pose proof (MEM_compile_exp_vmax ctxt e (SUC i + vmax ctxt) ce
                (conj Hmx (conj (proj2 (MEM_In _ _) Hy) (proj2 (MEM_In _ _) Hce)))). lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "local_rel_gt_vmax_preserved" *)
Theorem local_rel_gt_vmax_preserved : forall (ct : context a) l (l' : fmap varname (word_lab a)) n v,
  locals_rel ct l l' /\ vmax ct < n -> locals_rel ct l (l' |+ (n, v)).
Proof.
  intros ct l l' n v [Hl Hn]. apply (locals_rel_agree _ _ l'); [exact Hl|]. intros k Hk.
  rewrite FLOOKUP_UPDATE. destruct (decide (n = k)); [lia|reflexivity].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "local_rel_le_zip_update_preserved" *)
Theorem local_rel_le_zip_update_preserved : forall (ct : context a) l (l' : fmap varname (word_lab a)) x v sh ns v',
  locals_rel ct l l' /\ FLOOKUP l x = SOME v /\ FLOOKUP (vars ct) x = SOME (sh, ns) /\
  shape_of v = shape_of v' /\ ALL_DISTINCT ns ->
  locals_rel ct (l |+ (x, v')) (l' |++ ZIP (ns, flatten v')).
Proof.
  intros ct l l' x v sh ns v' (Hl & Hv & Hx & Hsh & _).
  destruct (locals_rel_lookup_ctxt ct _ _ x v (conj Hl Hv)) as (ns' & Hns' & Hlen & _ & Hw).
  rewrite Hx in Hns'. injection Hns' as -> <-.
  apply (locals_rel_assign ct _ _ x v); try assumption; [congruence|rewrite <- Hsh; exact Hw|].
  rewrite Hlen, (panProps.length_flatten_eq_size_of_shape v Hw),
    (panProps.length_flatten_eq_size_of_shape v' ltac:(rewrite <- Hsh; exact Hw)), Hsh. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "flatten_nil_no_size" *)
Local Theorem flatten_nil_no_size : forall x : panSem.v a,
  panProps.is_wf_shape_nil (shape_of x) -> (flatten x = [] <-> size_of_shape (shape_of x) = 0).
Proof.
  intros x Hw. rewrite <- (panProps.length_flatten_eq_size_of_shape x Hw).
  destruct (flatten x); cbn [LENGTH]; split; intros H; try reflexivity; try discriminate; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "is_wf_shape_nil_length_flatten" *)
Theorem is_wf_shape_nil_length_flatten : forall (v : panSem.v a) (l : list (word_lab a)),
  panProps.is_wf_shape_nil (shape_of v) /\
  (size_of_shape (shape_of v) = 0 -> l = []) /\
  (0 < size_of_shape (shape_of v) -> l = flatten v) ->
  LENGTH l = size_of_shape (shape_of v).
Proof.
  intros v l (Hw & H0 & H1). destruct (N.eq_dec (size_of_shape (shape_of v)) 0) as [Hz|Hz].
  - rewrite (H0 Hz), Hz. reflexivity.
  - rewrite H1 by lia. apply panProps.length_flatten_eq_size_of_shape, Hw.
Qed.

End Aux.

Section Aux2.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pair_map_I" *)
Local Theorem pair_map_I : forall {A B}, (fun p : A * B => let '(x, y) := p in (x, y)) = I.
Proof. intros A B. apply functional_extensionality. intros [x y]. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_wf_shape" 2345 *)
Theorem locals_rel_wf_shape : forall (ctxt : context a) s_locs (t_locs : fmap varname (word_lab a)) nm v,
  locals_rel ctxt s_locs t_locs /\ FLOOKUP s_locs nm = SOME v -> panProps.is_wf_shape_v [] v.
Proof.
  intros ctxt s_locs t_locs nm v [(_ & _ & Hl) Hv]. destruct (Hl _ _ Hv) as (ns & vs & _ & _ & _ & Hw).
  rewrite <- panProps.is_wf_shape_v_nil_thm by reflexivity. exact Hw.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_wf_shape" 3008 *)
Local Theorem locals_rel_wf_shape' : forall (ctxt : context a) s_locs (t_locs : fmap varname (word_lab a))
    ss (s : panSem.state a ffi_t),
  locals_rel ctxt s_locs t_locs /\ ss = TAKE 0 (panSem.structs s) ->
  FEVERY (fun '(nm, v) => is_true (panProps.is_wf_shape_v ss v)) s_locs.
Proof.
  intros ctxt s_locs t_locs ss s [Hl ->] k v Hv. rewrite TAKE_firstn. cbn [firstn N.to_nat].
  exact (locals_rel_wf_shape ctxt s_locs t_locs k v (conj Hl Hv)).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "opt_mmap_eval_is_wf_shape_v" *)
Theorem opt_mmap_eval_is_wf_shape_v : forall (s : panSem.state a ffi_t) es vs (t : state a ffi_t) ctxt t_locs,
  OPT_MMAP (panSem.eval s) es = SOME vs /\ state_rel s t /\ locals_rel ctxt (panSem.locals s) t_locs ->
  EVERY (panProps.is_wf_shape_v []) vs.
Proof.
  intros s es vs t ctxt t_locs (Ho & Hs & Hl). pose proof Hs as (_ & _ & _ & Hstr & Hgl & _).
  apply opt_mmap_eq_some in Ho. unfold is_true. rewrite EVERY_Forall, Forall_forall. intros v Hv.
  assert (Hin : In (SOME v) (MAP (panSem.eval s) es)) by (rewrite Ho; apply in_map, Hv).
  apply in_map_iff in Hin as (e & He & _).
  rewrite <- Hstr. apply (panProps.eval_is_wf_shape_v s e v). split; [exact He|]. split.
  - intros k w Hw. rewrite Hstr. exact (locals_rel_wf_shape ctxt _ t_locs k w (conj Hl Hw)).
  - intros k w Hw. rewrite Hgl in Hw. discriminate Hw.
Qed.

End Aux2.
