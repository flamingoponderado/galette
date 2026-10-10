(** * Pancake [pan_to_wordProof]: correctness of the composed [pan_to_word]

    Port of [cakeml/pancake/proofs/pan_to_wordProofScript.sml].

    The source language ([panLang], [panSem], [panProps]) is imported; the
    intermediate languages and the per-pass proofs are qualified
    ([crepSem.X], [loopSem.X], [wordSem.X], [pan_globalsProof.X], ...).
    HOL's record literals [<| ... |>] are Rocq record literals and HOL's
    [s with f := x] is [panSem.set_f x s].  HOL's [«main»] is
    [strlit "main"] and [first_name] is [crep_to_loop.first_name].

    Statement notes:
    - [wloc_wlab] is HOL's partial [wloc_wlab_def] (only the [Word] case);
      the [Loc] case, unspecified in HOL, is [ARB].
    - [distinct_params] is boolean ([EVERY] of [ALL_DISTINCT]).
    - HOL's [EVERY] of [Prop]-valued predicates is [EVERY] of [⌜...⌝].
    - [semantics_decls_has_main'] (an [∃] over the [ALOOKUP] of the
      functions) is stated as in HOL; its [local] twin
      [semantics_decls_has_main''] is the same with the behaviour named.
    - HOL has two [local] theorems named
      [FDOM_get_eids_structs_compile_decs_eq]; the second (about
      [size_of_eids], shadowing the first) is
      [size_of_eids_structs_compile_decs_eq] here.
    - HOL's [get_eids_from_decls] only depends on the exception names, so
      the [FDOM] lemmas go through [exceptions] rather than [exp_ids].
    - [ALL_DISTINCT_MAP_INJ_o] (a [local] derived rule) is not needed and
      not ported.
    - HOL's predicate [λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2] (and
      its [Crepop] twin) is [fun x => ⌜forall op es, ...⌝]; HOL's [⇔] and
      [=] between booleans are [<->].  [loop_state_simps] states HOL's
      [(...).be ⇔ s.be] as an equality.
    - HOL's [every_inst_ok_less_pan_to_crep_compile] quantifies an unused
      [e] and [every_inst_ok_less_pan_structs_compile_top] an unused
      [ctxt]; both are dropped.
    - [compile_shape_no_name] is stated about
      [pan_structsProof.compile_shape_n], where HOL's [compile_shape_n]
      lives in the Galette port.
    - [exps_of] on Pancake programs is [panProps.exps_of] (appended to
      [panProps.v] for this file).

    Untagged lemmas are Galette-only helpers; in particular [crok] and
    [pok] are the instruction side conditions on crepLang and Pancake
    expressions as propositions, and most [every_inst_ok_*] theorems are
    corollaries of [Forall]-valued helpers about them. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require wordLang stackLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem wordConvs.
From Galette.cakeml.compiler.backend.semantics.wordProps Require code.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake Require pan_simp pan_structs pan_globals pan_to_crep crepLang
  crep_to_loop loopLang loop_to_word pan_to_word loop_live crep_arith.
From Galette.cakeml.pancake.semantics Require Import panSem panProps.
From Galette.cakeml.pancake.semantics Require crepSem loopSem loopProps crepProps.
From Galette.cakeml.pancake.proofs Require pan_simpProof pan_structsProof pan_globalsProof
  pan_to_crepProof crep_to_loopProof loop_to_wordProof.
Open Scope N_scope.
Open Scope hol_string_scope.

(** ** Intermediate states *)

Section States.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "crep_state_def" *)
Definition crep_state (s : panSem.state a ffi_t) (pan_code : list (decl a))
    (mem : word a -> word_lab a) : crepSem.state a ffi_t :=
  {| crepSem.locals := FEMPTY;
     crepSem.globals := FEMPTY;
     crepSem.code := alist_to_fmap (pan_to_crep.compile_prog pan_code);
     crepSem.memory := mem;
     crepSem.memaddrs := memaddrs s;
     crepSem.sh_memaddrs := sh_memaddrs s;
     crepSem.clock := clock s;
     crepSem.be := be s;
     crepSem.ffi := ffi s;
     crepSem.base_addr := base_addr s;
     crepSem.top_addr := top_addr s |}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "wloc_wlab_def" *)
Definition wloc_wlab (w : wordLang.word_loc a) : word_lab a :=
  match w with
  | wordLang.Word w => Word w
  | _ => ARB
  end.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "wloc_wlab_wlab_wloc" *)
Theorem wloc_wlab_wlab_wloc : forall w, wloc_wlab (crep_to_loopProof.wlab_wloc w) = w.
Proof. intros [w]; reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "no_labels_def" *)
Definition no_labels (mem : word a -> wordLang.word_loc a) (dom : word a -> Prop) : Prop :=
  forall a0, a0 IN dom -> exists w, mem a0 = wordLang.Word w.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "loop_state_def" *)
Definition loop_state (s : crepSem.state a ffi_t) (c : architecture)
    (crep_code : list (mlstring * (list N * crepLang.prog a))) (ck : N)
    (mem : word a -> wordLang.word_loc a) : loopSem.state a ffi_t :=
  {| loopSem.locals := LN;
     loopSem.globals := FEMPTY;
     loopSem.memory := mem;
     loopSem.mdomain := crepSem.memaddrs s;
     loopSem.sh_mdomain := crepSem.sh_memaddrs s;
     loopSem.code := fromAList (crep_to_loop.compile_prog c crep_code);
     loopSem.clock := ck;
     loopSem.be := crepSem.be s;
     loopSem.ffi := crepSem.ffi s;
     loopSem.base_addr := crepSem.base_addr s;
     loopSem.top_addr := crepSem.top_addr s |}.

End States.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "distinct_params_def" *)
Definition distinct_params {A B C} `{EqDecision B} (prog : list (A * (list B * C))) : bool :=
  EVERY (fun '(name, (params, body)) => ALL_DISTINCT params) prog.

Section Basic.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "lookup_first_name_compile_prog_main" *)
Theorem lookup_first_name_compile_prog_main : forall c
    (crep_code : list (mlstring * (list N * crepLang.prog a))),
  FLOOKUP (crep_to_loop.make_funcs crep_code) (strlit "main") = SOME (crep_to_loop.first_name, 0) ->
  exists prog, lookup crep_to_loop.first_name (fromAList (crep_to_loop.compile_prog c crep_code)) =
               SOME ([], prog).
Proof.
  intros c crep_code H. rewrite crep_to_loopProof.make_funcs_mf in H.
  destruct (crep_to_loopProof.mf_list_inv _ _ _ _ H) as (ns & p0 & Ep).
  destruct (crep_to_loopProof.mf_list_found crep_code crep_to_loop.first_name (strlit "main") ns p0
              (fun params body => loop_live.optimise
                 (crep_to_loop.comp_func c (crep_to_loop.make_funcs crep_code) params
                    (crep_arith.simp_prog body))) Ep)
    as (i & H1 & H2).
  rewrite H1 in H. injection H as Hi Hl.
  assert (Hi0 : i = 0) by lia. subst i. rewrite N.add_0_l in H2.
  destruct ns; [|cbn in Hl; lia].
  eexists. rewrite lookup_fromAList, crep_to_loopProof.compile_prog_cp, H2. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "loop_state_simps" *)
Theorem loop_state_simps : forall (s : crepSem.state a ffi_t) c crep_code ck
    (mem : word a -> wordLang.word_loc a),
  loopSem.memory (loop_state s c crep_code ck mem) = mem /\
  loopSem.mdomain (loop_state s c crep_code ck mem) = crepSem.memaddrs s /\
  loopSem.sh_mdomain (loop_state s c crep_code ck mem) = crepSem.sh_memaddrs s /\
  loopSem.clock (loop_state s c crep_code ck mem) = ck /\
  loopSem.be (loop_state s c crep_code ck mem) = crepSem.be s /\
  loopSem.ffi (loop_state s c crep_code ck mem) = crepSem.ffi s /\
  loopSem.base_addr (loop_state s c crep_code ck mem) = crepSem.base_addr s /\
  loopSem.top_addr (loop_state s c crep_code ck mem) = crepSem.top_addr s /\
  loopSem.globals (loop_state s c crep_code ck mem) = FEMPTY /\
  isEmpty (loopSem.locals (loop_state s c crep_code ck mem)) /\
  loopSem.code (loop_state s c crep_code ck mem) =
    fromAList (crep_to_loop.compile_prog c crep_code).
Proof. intros. repeat split. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "first_compile_prog_all_distinct" *)
Theorem first_compile_prog_all_distinct : forall c (prog : list (decl a)),
  ALL_DISTINCT (MAP FST (functions prog)) ->
  ALL_DISTINCT (MAP FST (pan_to_word.compile_prog c prog)).
Proof.
  intros c prog _. unfold pan_to_word.compile_prog. cbv zeta.
  apply loop_to_wordProof.first_compile_all_distinct, crep_to_loopProof.first_compile_prog_all_distinct.
Qed.

End Basic.

(** ** Syntactic facts about the front-end passes *)

Section Syntax.
Context {a : N}.

Lemma exceptions_pan_simp_compile_prog (prog : list (decl a)) :
  exceptions (pan_simp.compile_prog prog) = exceptions prog.
Proof.
  unfold pan_simp.compile_prog. induction prog as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    cbn [List.map exceptions]; rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "get_eids_pan_simp_compile_eq" *)
Theorem get_eids_pan_simp_compile_eq : forall prog : list (decl a),
  FDOM (pan_to_crep.get_eids_from_decls prog) =
  FDOM (pan_to_crep.get_eids_from_decls (pan_simp.compile_prog prog)).
Proof.
  intros prog. unfold pan_to_crep.get_eids_from_decls. rewrite exceptions_pan_simp_compile_prog.
  reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "map_map2_fst_lemma" *)
Theorem map_map2_fst_lemma : forall {A B} (xs : list A) (ys : list B),
  MAP FST (MAP2 (fun x y => (x, y)) xs ys) = TAKE (MIN (LENGTH xs) (LENGTH ys)) xs.
Proof.
  intros A B xs; induction xs as [|x xs IH]; intros [|y ys]; cbn [MAP2 List.map TAKE]; try reflexivity.
  - rewrite !LENGTH_length. cbn [Datatypes.length]. unfold MIN.
    match goal with |- context [if ?x <? ?y then _ else _] => destruct (N.ltb_spec x y) end; [lia|].
    reflexivity.
  - rewrite IH. rewrite !LENGTH_length. cbn [Datatypes.length]. unfold MIN.
    repeat match goal with |- context [if ?x <? ?y then _ else _] => destruct (N.ltb_spec x y) end;
      try lia; cbn [TAKE];
    match goal with |- context [?k =? 0] => destruct (N.eqb_spec k 0); [lia|] end;
    repeat f_equal; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_nested_seq" *)
Theorem exp_ids_nested_seq : forall ps : list (prog a),
  exp_ids (nested_seq ps) = FLAT (MAP exp_ids ps).
Proof. intros ps; induction ps as [|p ps IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Ltac exp_ids_tac :=
  repeat match goal with
         | H : match ?x with _ => _ end |- _ => destruct x
         | |- context [match ?x with _ => _ end] => destruct x
         end;
  cbn [exp_ids app] in *; rewrite ?app_nil_r; try congruence.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_compile_globals" *)
Theorem exp_ids_compile_globals : forall ctxt (p : prog a),
  exp_ids (pan_globals.compile ctxt p) = exp_ids p.
Proof.
  intros ctxt p. induction p using pan_globalsProof.prog_nested_ind;
    cbn [pan_globals.compile]; exp_ids_tac.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_fperm" *)
Theorem exp_ids_fperm : forall f g (p : prog a),
  exp_ids (pan_globals.fperm f g p) = exp_ids p.
Proof.
  intros f g p. induction p using pan_globalsProof.prog_nested_ind;
    cbn [pan_globals.fperm]; exp_ids_tac.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_decs_exp_ids" *)
Theorem compile_decs_exp_ids : forall ctxt (pan_code : list (decl a)),
  MAP (exp_ids ∘ FST ∘ SND ∘ SND) (functions (FST (SND (pan_globals.compile_decs ctxt pan_code)))) =
  MAP (exp_ids ∘ FST ∘ SND ∘ SND) (functions pan_code).
Proof.
  intros ctxt pan_code; revert ctxt.
  induction pan_code as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt; cbn [pan_globals.compile_decs];
    try reflexivity;
    try (match goal with |- context [pan_globals.compile_decs ?c ds] =>
           specialize (IH c); destruct (pan_globals.compile_decs c ds) as [d1 [f1 [e1 c1]]] end;
         cbn [FST SND fst snd functions List.map panLang.body] in *; rewrite ?IH, ?exp_ids_compile_globals;
         reflexivity).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "fperm_exp_ids" *)
Theorem fperm_exp_ids : forall f g (pan_code : list (decl a)),
  MAP (exp_ids ∘ FST ∘ SND ∘ SND) (functions (pan_globals.fperm_decs f g pan_code)) =
  MAP (exp_ids ∘ FST ∘ SND ∘ SND) (functions pan_code).
Proof.
  intros f g pan_code.
  induction pan_code as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    cbn [pan_globals.fperm_decs functions List.map FST SND fst snd panLang.body];
    rewrite ?IH, ?exp_ids_fperm; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_decs_no_exp_ids_main" *)
Theorem compile_decs_no_exp_ids_main : forall ctxt (prog : list (decl a)),
  EVERY (fun x => ⌜exp_ids x = []⌝) (FST (pan_globals.compile_decs ctxt prog)).
Proof.
  intros ctxt prog; revert ctxt.
  induction prog as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt; cbn [pan_globals.compile_decs];
    try reflexivity; try apply IH;
    match goal with |- context [pan_globals.compile_decs ?c ds] =>
      specialize (IH c); destruct (pan_globals.compile_decs c ds) as [d1 [f1 [e1 c1]]] end;
    cbn [FST fst EVERY] in *; try exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "functions_resort_decls" *)
Theorem functions_resort_decls : forall xs : list (decl a),
  functions (pan_globals.resort_decls xs) = functions xs.
Proof.
  intros xs. unfold pan_globals.resort_decls. rewrite !functions_append.
  assert (H : forall q, (forall d, is_function d = true -> q d = false) -> functions (FILTER q xs) = []).
  { intros q Hq. induction xs as [|d ds IH]; [reflexivity|]. cbn [List.filter].
    destruct (q d) eqn:Eq; [|exact IH].
    destruct d; cbn [functions]; try exact IH. rewrite Hq in Eq by reflexivity. discriminate. }
  rewrite (H is_name), (H is_exn_decl), (H is_decl) by (intros [] Hd; first [reflexivity | discriminate Hd]).
  cbn [app]. clear H. induction xs as [|[] ds IH]; cbn [List.filter is_function functions]; rewrite ?IH; reflexivity.
Qed.

Lemma exceptions_compile_top (pan_code : list (decl a)) main args body rshape :
  ALOOKUP (functions pan_code) main = SOME (args, (body, rshape)) ->
  exceptions (pan_globals.compile_top pan_code main) = exceptions pan_code.
Proof.
  intros Hm. unfold pan_globals.compile_top. rewrite Hm. cbv zeta.
  match goal with |- context [pan_globals.compile_decs ?c ?l] =>
    destruct (pan_globals.compile_decs c l) as [decls [funs [exns ctxt]]] eqn:E end.
  pose proof (pan_globalsProof.compile_decs_exns_are_exns _ _ _ _ _ _ E) as Hx.
  pose proof (pan_globalsProof.compile_decs_EVERY_is_function _ _ _ _ _ _ E) as Hf.
  rewrite pan_globalsProof.exceptions_append. cbn [exceptions].
  assert (Hn : exceptions funs = []).
  { clear -Hf. induction funs as [|d ds IH]; [reflexivity|]. cbn [EVERY] in Hf. unfold is_true in *.
    apply andb_prop in Hf as [H1 H2]. destruct d; try discriminate H1. cbn. exact (IH H2). }
  rewrite Hn, app_nil_r, Hx.
  rewrite (proj1 (proj2 (proj2 (pan_globalsProof.exceptions_FILTER_is_function _)))).
  assert (Hp : forall f g (l : list (decl a)), exceptions (pan_globals.fperm_decs f g l) = exceptions l)
    by (intros f g l; induction l as [|[] ds IH]; cbn; rewrite ?IH; reflexivity).
  rewrite Hp. unfold pan_globals.resort_decls. rewrite !pan_globalsProof.exceptions_append.
  destruct (pan_globalsProof.exceptions_FILTER_is_function pan_code) as (H1 & _ & H3 & H4 & H5).
  rewrite H3, H4, H5, H1. cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_pan_globals_compile_eq" *)
Theorem FDOM_get_eids_pan_globals_compile_eq : forall (pan_code : list (decl a)) main args body rshape,
  ALOOKUP (functions pan_code) main = SOME (args, (body, rshape)) ->
  FDOM (pan_to_crep.get_eids_from_decls (pan_globals.compile_top pan_code main)) =
  FDOM (pan_to_crep.get_eids_from_decls pan_code).
Proof.
  intros pan_code main args body rshape Hm. unfold pan_to_crep.get_eids_from_decls.
  rewrite (exceptions_compile_top _ _ _ _ _ Hm). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "dec_shapes_compile_prog" *)
Theorem dec_shapes_compile_prog : forall pan_code : list (decl a),
  pan_globals.dec_shapes (pan_simp.compile_prog pan_code) = pan_globals.dec_shapes pan_code.
Proof.
  unfold pan_simp.compile_prog. intros pan_code.
  induction pan_code as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; cbn [List.map pan_globals.dec_shapes];
    rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "function_names_compile_prog" *)
Theorem function_names_compile_prog : forall pan_code : list (decl a),
  MAP FST (functions (pan_simp.compile_prog pan_code)) = MAP FST (functions pan_code).
Proof. exact pan_simpProof.MAP_FST_functions_compile_prog. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "function_names_structs_compile_decs" *)
Local Theorem function_names_structs_compile_decs : forall ctxt (pan_code : list (decl a)),
  MAP FST (functions (FST (pan_structs.compile_decs ctxt pan_code))) = MAP FST (functions pan_code).
Proof.
  intros ctxt pan_code; revert ctxt.
  induction pan_code as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt; cbn [pan_structs.compile_decs];
    try reflexivity; try apply IH;
    match goal with |- context [pan_structs.compile_decs ?c ds] =>
      specialize (IH c); destruct (pan_structs.compile_decs c ds) as [ds' c'] end;
    cbn [FST fst functions List.map panLang.name] in *; rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exp_ids_structs_compile" *)
Local Theorem exp_ids_structs_compile : forall ctxt (prog : prog a),
  exp_ids (pan_structs.compile ctxt prog) = exp_ids prog.
Proof.
  intros ctxt p; revert ctxt. induction p using pan_globalsProof.prog_nested_ind; intros ctxt;
    cbn [pan_structs.compile];
    repeat match goal with
           | H : match ?x with _ => _ end |- _ => destruct x
           | |- context [match ?x with _ => _ end] => destruct x
           end;
    cbn [exp_ids app] in *; rewrite ?app_nil_r;
    repeat match goal with
           | H : forall c, exp_ids (pan_structs.compile c ?q) = exp_ids ?q |- _ => rewrite H
           end; reflexivity.
Qed.

Lemma exceptions_structs_compile_decs ctxt (prog : list (decl a)) :
  MAP FST (exceptions (FST (pan_structs.compile_decs ctxt prog))) = MAP FST (exceptions prog).
Proof.
  revert ctxt.
  induction prog as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt; cbn [pan_structs.compile_decs];
    try reflexivity; try apply IH;
    match goal with |- context [pan_structs.compile_decs ?c ds] =>
      specialize (IH c); destruct (pan_structs.compile_decs c ds) as [ds' c'] end;
    cbn [FST fst exceptions List.map] in *; rewrite ?IH; reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_structs_compile_decs_eq" 273 *)
Local Theorem FDOM_get_eids_structs_compile_decs_eq : forall ctxt (prog : list (decl a)),
  FDOM (pan_to_crep.get_eids_from_decls prog) =
  FDOM (pan_to_crep.get_eids_from_decls (FST (pan_structs.compile_decs ctxt prog))).
Proof.
  intros ctxt prog. unfold pan_to_crep.get_eids_from_decls.
  rewrite exceptions_structs_compile_decs. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_structs_compile_eq" *)
Local Theorem FDOM_get_eids_structs_compile_eq : forall prog : list (decl a),
  FDOM (pan_to_crep.get_eids_from_decls (pan_structs.compile_top prog)) =
  FDOM (pan_to_crep.get_eids_from_decls prog).
Proof.
  intros prog. unfold pan_structs.compile_top. cbv zeta.
  symmetry. apply FDOM_get_eids_structs_compile_decs_eq.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FDOM_get_eids_structs_compile_decs_eq" 293 *)
Local Theorem size_of_eids_structs_compile_decs_eq : forall ctxt (prog : list (decl a)),
  size_of_eids prog = size_of_eids (FST (pan_structs.compile_decs ctxt prog)).
Proof.
  unfold size_of_eids. intros ctxt prog; revert ctxt.
  induction prog as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; intros ctxt; cbn [pan_structs.compile_decs];
    try reflexivity; try apply IH;
    match goal with |- context [pan_structs.compile_decs ?c ds] =>
      specialize (IH c); destruct (pan_structs.compile_decs c ds) as [ds' c'] end;
    cbn [FST fst List.filter is_exn_decl] in *; rewrite !LENGTH_length in *; cbn [Datatypes.length]; lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "size_of_eids_structs_compile_eq" *)
Local Theorem size_of_eids_structs_compile_eq : forall prog : list (decl a),
  size_of_eids (pan_structs.compile_top prog) = size_of_eids prog.
Proof.
  intros prog. unfold pan_structs.compile_top. cbv zeta.
  symmetry. apply size_of_eids_structs_compile_decs_eq.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "function_names_structs_compile_top" *)
Theorem function_names_structs_compile_top : forall pan_code : list (decl a),
  MAP FST (functions (pan_structs.compile_top pan_code)) = MAP FST (functions pan_code).
Proof. intros pan_code. unfold pan_structs.compile_top. apply function_names_structs_compile_decs. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "no_names_compile_prog" *)
Theorem no_names_compile_prog : forall pan_code : list (decl a),
  EVERY (fun d => is_function d || is_decl d || is_exn_decl d) pan_code ->
  EVERY (fun d => is_function d || is_decl d || is_exn_decl d) (pan_simp.compile_prog pan_code).
Proof.
  unfold pan_simp.compile_prog. intros pan_code.
  induction pan_code as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; cbn [List.map EVERY]; unfold is_true;
    intros H; try reflexivity; apply andb_prop in H as [H1 H2]; rewrite (IH H2), andb_true_r;
    first [reflexivity | exact H1].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_decs_fun_names" *)
Theorem compile_decs_fun_names : forall ctxt (code0 : list (decl a)),
  MAP FST (functions (FST (SND (pan_globals.compile_decs ctxt code0)))) = MAP FST (functions code0).
Proof.
  intros ctxt code0.
  destruct (pan_globals.compile_decs ctxt code0) as [decs [funs [exns ctxt']]] eqn:E.
  exact (pan_globalsProof.compile_decs_preserve_functions _ _ _ _ _ _ E).
Qed.

Lemma FILTER_is_exn_decl_fperm_decs f g (l : list (decl a)) :
  FILTER is_exn_decl (pan_globals.fperm_decs f g l) = FILTER is_exn_decl l.
Proof. induction l as [|[fi|sh v0 e|eid sh|nm flds] ds IH]; cbn; rewrite ?IH; reflexivity. Qed.

Lemma FILTER_is_exn_decl_resort_decls (l : list (decl a)) :
  FILTER is_exn_decl (pan_globals.resort_decls l) = FILTER is_exn_decl l.
Proof.
  unfold pan_globals.resort_decls. rewrite !filter_app.
  assert (H : forall q, (forall d, is_exn_decl d = true -> q d = false) ->
            FILTER is_exn_decl (FILTER q l) = []).
  { intros q Hq. induction l as [|d ds IH]; [reflexivity|]. cbn [List.filter].
    destruct (q d) eqn:Eq; cbn [List.filter]; [|exact IH].
    destruct (is_exn_decl d) eqn:Ed; [rewrite (Hq _ Ed) in Eq; discriminate|exact IH]. }
  rewrite (H is_name), (H is_decl), (H is_function) by (intros [] Hd; first [reflexivity | discriminate Hd]).
  cbn [app].
  assert (Hi : forall l0 : list (decl a), FILTER is_exn_decl (FILTER is_exn_decl l0) = FILTER is_exn_decl l0).
  { intros l0; induction l0 as [|d ds IH]; [reflexivity|]. cbn [List.filter].
    destruct (is_exn_decl d) eqn:Ed; cbn [List.filter]; rewrite ?Ed, ?IH; reflexivity. }
  rewrite Hi, app_nil_r. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "size_of_eids_compile_top" *)
Theorem size_of_eids_compile_top : forall (pan_code : list (decl a)) main args body rshape,
  ALOOKUP (functions pan_code) main = SOME (args, (body, rshape)) ->
  size_of_eids (pan_globals.compile_top pan_code main) = size_of_eids pan_code.
Proof.
  intros pan_code main args body rshape Hm. unfold size_of_eids, pan_globals.compile_top.
  rewrite Hm. cbv zeta.
  match goal with |- context [pan_globals.compile_decs ?c ?l] =>
    destruct (pan_globals.compile_decs c l) as [decls [funs [exns ctxt]]] eqn:E end.
  pose proof (pan_globalsProof.compile_decs_exns_are_exns _ _ _ _ _ _ E) as Hx.
  pose proof (pan_globalsProof.compile_decs_EVERY_is_function _ _ _ _ _ _ E) as Hf.
  rewrite filter_app. cbn [List.filter is_exn_decl].
  assert (Hn : FILTER is_exn_decl funs = []).
  { clear -Hf. induction funs as [|d ds IH]; [reflexivity|]. cbn [EVERY] in Hf. unfold is_true in *.
    apply andb_prop in Hf as [H1 H2]. destruct d; try discriminate H1. cbn. exact (IH H2). }
  rewrite Hn, app_nil_r, Hx.
  assert (Hi : forall l0 : list (decl a), FILTER is_exn_decl (FILTER is_exn_decl l0) = FILTER is_exn_decl l0).
  { intros l0; induction l0 as [|d ds IH]; [reflexivity|]. cbn [List.filter].
    destruct (is_exn_decl d) eqn:Ed; cbn [List.filter]; rewrite ?Ed, ?IH; reflexivity. }
  rewrite Hi, FILTER_is_exn_decl_fperm_decs, FILTER_is_exn_decl_resort_decls. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "functions_FILTER_nil" *)
Theorem functions_FILTER_nil : forall xs : list (decl a), functions (FILTER is_exn_decl xs) = [].
Proof. exact pan_globalsProof.functions_FILTER_exn_decl. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "FLOOKUP_make_funcs_main" *)
Theorem FLOOKUP_make_funcs_main : forall (pan_code : list (decl a)) main body rshape,
  ALOOKUP (functions pan_code) main = SOME ([], (body, rshape)) ->
  FLOOKUP (crep_to_loop.make_funcs (pan_to_crep.compile_prog (pan_globals.compile_top pan_code main)))
    main = SOME (crep_to_loop.first_name, 0).
Proof.
  intros pan_code main body rshape Hm.
  assert (Hf : exists rest body',
             functions (pan_globals.compile_top pan_code main) = (main, ([], (body', rshape))) :: rest).
  { unfold pan_globals.compile_top. rewrite Hm. cbv zeta.
    match goal with |- context [pan_globals.compile_decs ?c ?l] =>
      destruct (pan_globals.compile_decs c l) as [decls [funs [exns ctxt]]] eqn:E end.
    rewrite (pan_globalsProof.compile_decs_exns_are_exns _ _ _ _ _ _ E).
    rewrite functions_append, functions_FILTER_nil. cbn [app functions panLang.name panLang.params
      panLang.body fun_decl_return List.map]. eexists _, _. reflexivity. }
  destruct Hf as (rest & body' & Hf).
  unfold pan_to_crep.compile_prog, crep_inline.compile_inl_top, crep_inline.compile_inl_prog,
    pan_to_crep.compile_to_crep. cbv zeta. rewrite Hf. cbn [List.map].
  rewrite crep_to_loopProof.make_funcs_mf, crep_to_loopProof.mf_list_cons.
  cbn [ALOOKUP FST SND fst snd]. destruct (decide (main = main)) as [_|C]; [|contradiction C; reflexivity].
  reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "compile_shape_no_name" *)
Theorem compile_shape_no_name : forall ctxt n sh,
  is_wf_shape_nil (pan_structsProof.compile_shape_n ctxt n sh).
Proof. exact pan_structsProof.compile_shape_n_no_name. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "functions_compile_decs_exns" *)
Theorem functions_compile_decs_exns : forall ctxt (prog : list (decl a)),
  functions (FST (SND (SND (pan_globals.compile_decs ctxt prog)))) = [].
Proof.
  intros ctxt prog.
  destruct (pan_globals.compile_decs ctxt prog) as [decs [funs [exns ctxt']]] eqn:E. cbn [FST SND fst snd].
  rewrite (pan_globalsProof.compile_decs_exns_are_exns _ _ _ _ _ _ E). apply functions_FILTER_nil.
Qed.

End Syntax.

(** ** Global declarations *)

Section Globals.
Context {a : N} {ffi_t : Type}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "globals_allocatable_def" *)
Definition globals_allocatable (s : panSem.state a ffi_t) (pan_code : list (decl a)) : Prop :=
  let dec_shs := pan_globals.dec_shapes pan_code in
  let struct_ctxt := decs_stcnames [] pan_code in
  let sz := SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs) in
  struct_ctxt <> NONE /\
  DISJOINT (memaddrs s) (pan_globalsProof.addresses (top_addr s) sz) /\
  (top_addr s + bytes_in_word * n2w sz)%w NOTIN memaddrs s /\
  sz * w2n (bytes_in_word : word a) < dimword a.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_decls_has_main'" *)
Theorem semantics_decls_has_main' : forall (s : panSem.state a ffi_t) start (code0 : list (decl a)),
  code s = FEMPTY /\
  ALL_DISTINCT (MAP FST (functions code0)) /\
  semantics_decls s start code0 <> Fail ->
  exists body rshape, ALOOKUP (functions code0) start = SOME ([], (body, rshape)).
Proof.
  intros s start code0 (Hc & Hd & Hsem).
  destruct (panProps.semantics_decls_has_main' s start code0 Hsem) as (body & rshape & H).
  rewrite Hc, pan_globalsProof.FLOOKUP_FUPDATE_LIST_ALOOKUP in H by exact Hd.
  destruct (ALOOKUP (functions code0) start) as [x|] eqn:E; [|discriminate].
  injection H as ->. eauto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_decls_has_main''" *)
Local Theorem semantics_decls_has_main'' : forall (s : panSem.state a ffi_t) start
    (code0 : list (decl a)) v0,
  semantics_decls s start code0 = v0 /\
  code s = FEMPTY /\
  ALL_DISTINCT (MAP FST (functions code0)) /\
  v0 <> Fail ->
  exists body rshape, ALOOKUP (functions code0) start = SOME ([], (body, rshape)).
Proof.
  intros s start code0 v0 (<- & Hc & Hd & Hsem). exact (semantics_decls_has_main' s start code0 (conj Hc (conj Hd Hsem))).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "size_decs_stcnames_compile_decs_structs" *)
Theorem size_decs_stcnames_compile_decs_structs : forall (s : panSem.state a ffi_t) pan_code ctxt s'
    code' ctxt',
  evaluate_decls s pan_code = SOME s' /\
  pan_structs.compile_decs ctxt pan_code = (code', ctxt') /\
  pan_structsProof.struct_infos_ok (structs s) /\
  FEVERY (fun '(nm, v0) => is_true (is_wf_shape_v (structs s) v0)) (globals s) /\
  pan_structs.structs ctxt = MAP (fun '(nm, info) => (nm, fields info)) (structs s) ->
  MAP size_of_shape (pan_globals.dec_shapes code') =
  MAP (size_of_sh_with_ctxt (structs s)) (pan_globals.dec_shapes pan_code).
Proof.
  intros s pan_code; revert s.
  induction pan_code as [|[fi|sh v0 e|eid sh|nm flds] ds IH];
    intros s ctxt s' code' ctxt' (Hev & Hc & Hok & Hg & Hst); cbn [evaluate_decls] in Hev;
    cbn [pan_structs.compile_decs] in Hc.
  - injection Hc as <- <-. reflexivity.
  - (* Function *)
    destruct (_ && _); [|discriminate].
    destruct (pan_structs.compile_decs ctxt ds) as [ds' c'] eqn:E. injection Hc as <- <-.
    cbn [pan_globals.dec_shapes].
    exact (IH _ ctxt s' ds' c' (conj Hev (conj E (conj Hok (conj Hg Hst))))).
  - (* Decl *)
    destruct (eval (set_locals FEMPTY s) e) as [res|] eqn:Ee; [|discriminate].
    destruct (bool_decide (sh = shape_of res)) eqn:Eb; [|discriminate].
    apply bool_decide_spec in Eb. subst sh.
    match type of Hc with context [pan_structs.compile_decs ?c ds] =>
      destruct (pan_structs.compile_decs c ds) as [ds' c'] eqn:E end.
    injection Hc as <- <-. cbn [pan_globals.dec_shapes List.map].
    assert (Hwf : is_true (is_wf_shape_v (structs s) res)).
    { apply (eval_is_wf_shape_v (set_locals FEMPTY s) e res). split; [exact Ee|].
      split; [apply FEVERY_FEMPTY|exact Hg]. }
    f_equal.
    + apply (pan_structsProof.size_of_shape_compile_pass_eq s). split; [exact Hok|].
      split; [apply is_wf_shape_of_v, Hwf|exact Hst].
    + refine (IH (set_globals (globals s |+ (v0, res)) s) _ s' ds' c' (conj Hev (conj E _))).
      cbn [structs set_globals globals]. split; [exact Hok|]. split; [|exact Hst].
      intros k v1 Hk. rewrite FLOOKUP_UPDATE in Hk. destruct (decide (v0 = k)).
      * injection Hk as <-. exact Hwf.
      * exact (Hg _ _ Hk).
  - (* ExnDecl *)
    destruct (_ && _); [|discriminate].
    destruct (pan_structs.compile_decs ctxt ds) as [ds' c'] eqn:E. injection Hc as <- <-.
    cbn [pan_globals.dec_shapes].
    exact (IH _ ctxt s' ds' c' (conj Hev (conj E (conj Hok (conj Hg Hst))))).
  - (* Name *)
    cbn [pan_globals.dec_shapes].
    exact (IH _ ctxt s' code' ctxt' (conj Hev (conj Hc (conj Hok (conj Hg Hst))))).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_size_decs_stcnames_compile_structs" *)
Theorem semantics_size_decs_stcnames_compile_structs : forall (s : panSem.state a ffi_t) nm
    (pan_code : list (decl a)),
  semantics_decls s nm pan_code <> Fail /\ globals s = FEMPTY ->
  MAP size_of_shape (pan_globals.dec_shapes (pan_structs.compile_top pan_code)) =
  MAP (size_of_sh_with_ctxt (THE (decs_stcnames [] pan_code))) (pan_globals.dec_shapes pan_code).
Proof.
  intros s nm pan_code (Hsem & Hg). unfold semantics_decls in Hsem.
  destruct (decs_stcnames [] pan_code) as [res|] eqn:Ed; [|contradiction].
  destruct (evaluate_decls (set_structs res s) pan_code) as [s'|] eqn:Ev; [|contradiction].
  cbn [THE]. unfold pan_structs.compile_top. cbv zeta.
  set (nm_ctxt := pan_structs.get_names {| pan_structs.structs := []; pan_structs.locals := [];
                                           pan_structs.globals := [] |} pan_code).
  assert (Hnm : nm_ctxt = {| pan_structs.structs := MAP (fun '(nm, info) => (nm, fields info)) res;
                             pan_structs.locals := []; pan_structs.globals := [] |})
    by (apply (pan_structsProof.decs_stcnames_to_get_names [] pan_code res); split; [exact Ed|reflexivity]).
  assert (Hok : pan_structsProof.struct_infos_ok res).
  { apply (pan_structsProof.decs_stcnames_infos_ok [] pan_code res nm_ctxt). split; [exact Ed|].
    unfold pan_structsProof.struct_infos_ok; cbn. repeat split. intros i nm0 info [Hi _]. cbn in Hi; lia. }
  destruct (pan_structs.compile_decs nm_ctxt pan_code) as [code' ctxt'] eqn:Ec. cbn [FST fst].
  apply (size_decs_stcnames_compile_decs_structs (set_structs res s) pan_code nm_ctxt s' code' ctxt').
  split; [exact Ev|]. split; [exact Ec|]. cbn [structs set_structs globals]. split; [exact Hok|].
  split; [rewrite Hg; apply FEVERY_FEMPTY|]. rewrite Hnm. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "semantics_decls_decl_structs" *)
Theorem semantics_decls_decl_structs : forall (s : panSem.state a ffi_t) start (pan_code : list (decl a)),
  semantics_decls s start pan_code <> Fail ->
  exists s_ctxt, decs_stcnames [] pan_code = SOME s_ctxt.
Proof.
  intros s start pan_code H. unfold semantics_decls in H.
  destruct (decs_stcnames [] pan_code) as [r|]; [eauto|contradiction].
Qed.

End Globals.

(** ** Semantics preservation *)

Section Semantics.
Context {a : N} {b ffi_t : Type}.

(** Decidable equality on shapes, classically (HOL equality); used by
    [distinct_params] on Pancake parameter lists. *)
#[local] Instance shape_eq_dec_cl : EqDecision shape := fun x y => classical_dec (x = y).

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "state_rel_imp_semantics" *)
Theorem state_rel_imp_semantics : forall (s : panSem.state a ffi_t) (t : wordSem.state a b ffi_t)
    start globals_size (pan_code : list (decl a)) heap_len c,
  (forall addr', addr' IN memaddrs s ->
     wordSem.memory t addr' = crep_to_loopProof.wlab_wloc (memory s addr')) /\
  no_labels (wordSem.memory t) (wordSem.mdomain t) /\
  start = strlit "main" /\
  globals_size = (let dec_shs := pan_globals.dec_shapes pan_code in
                  let struct_ctxt := decs_stcnames [] pan_code in
                  SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) /\
  distinct_params (functions pan_code) /\
  wordSem.mdomain t = memaddrs s UNION pan_globalsProof.addresses (top_addr s) globals_size /\
  wordSem.sh_mdomain t = sh_memaddrs s /\
  wordSem.be t = be s /\
  wordSem.ffi t = ffi s /\
  ALOOKUP (fmap_to_alist (wordSem.store t)) stackLang.CurrHeap = SOME (wordLang.Word (base_addr s)) /\
  ALOOKUP (fmap_to_alist (wordSem.store t)) stackLang.HeapLength = SOME (wordLang.Word heap_len) /\
  top_addr s = (base_addr s + n2w 2 * heap_len - bytes_in_word * n2w globals_size)%w /\
  ALL_DISTINCT (MAP FST (functions pan_code)) /\
  byte_aligned (top_addr s) /\
  globals_allocatable s pan_code /\
  code s = FEMPTY /\
  wordSem.code t = fromAList (pan_to_word.compile_prog c pan_code) /\
  globals s = FEMPTY /\
  locals s = FEMPTY /\ size_of_eids pan_code < dimword a /\
  eshapes s = FEMPTY /\
  lookup 0 (wordSem.locals t) = SOME (wordLang.Loc 1 0) /\ good_dimindex a /\
  semantics_decls s start pan_code <> Fail ->
  wordSem.semantics t crep_to_loop.first_name = semantics_decls s start pan_code.
Proof.
  intros s t start globals_size pan_code heap_len c
    (Hmem & Hnl & -> & Hgs & _ & Hmd & Hsh & Hbe & Hffi & Hch & Hhl & Htop & Hd & Hal & Hga & Hsc & Htc
     & Hsg & Hsl & Hsz & Hse & H0 & Hg & Hsem).
  set (main := strlit "main") in *.
  (* pan_simp *)
  set (P1 := pan_simp.compile_prog pan_code).
  assert (E1 : semantics_decls s main pan_code = semantics_decls s main P1).
  { apply pan_simpProof.state_rel_imp_semantics_decls.
    split; [|split; [exact Hd|split; [exact Hsc|split; [exact Hsc|exact Hsem]]]].
    split; [destruct s; reflexivity|].
    split; [intros f Hf; exact Hf|].
    intros f vshs prog rshape Hf. rewrite Hsc, FLOOKUP_EMPTY in Hf. discriminate. }
  assert (Hsem1 : semantics_decls s main P1 <> Fail) by (rewrite <- E1; exact Hsem).
  (* pan_structs *)
  set (P2 := pan_structs.compile_top P1).
  assert (E2 : semantics_decls s main P1 = semantics_decls s main P2).
  { rewrite (pan_structsProof.compile_top_semantics_decls s main P1 (conj Hsem1 (conj Hsl (conj Hsc Hsg)))).
    f_equal. rewrite Hse, FMAP_MAP2_FEMPTY. destruct s; cbn in Hse |- *; subst; reflexivity. }
  assert (Hsem2 : semantics_decls s main P2 <> Fail) by (rewrite <- E2; exact Hsem1).
  assert (Hsz2 : SUM (MAP size_of_shape (pan_globals.dec_shapes P2)) = globals_size).
  { unfold P2. rewrite (semantics_size_decs_stcnames_compile_structs s main P1 (conj Hsem1 Hsg)).
    unfold P1. rewrite pan_simpProof.decs_stcnames_compile_prog, dec_shapes_compile_prog.
    rewrite Hgs. reflexivity. }
  assert (HdP2 : ALL_DISTINCT (MAP FST (functions P2))).
  { unfold P2, P1. rewrite function_names_structs_compile_top, function_names_compile_prog. exact Hd. }
  destruct (semantics_decls_has_main' s main P2 (conj Hsc (conj HdP2 Hsem2))) as (body2 & rsh2 & Hm2).
  (* pan_globals *)
  set (P3 := pan_globals.compile_top P2 main).
  set (free := pan_globalsProof.addresses (top_addr s) globals_size).
  set (mgs := (bytes_in_word * n2w globals_size : word a)%w).
  set (t1 := set_locals (locals s) (set_memory (wloc_wlab ∘ wordSem.memory t)
               (panProps.set_memaddrs (memaddrs s UNION free)
                 (pan_globalsProof.set_top_addr (top_addr s + mgs)%w s)))).
  unfold globals_allocatable in Hga. cbv zeta in Hgs, Hga. rewrite <- Hgs in Hga.
  destruct Hga as (_ & Hdis & Hnot & Hbnd).
  assert (E3 : semantics_decls s main P2 = semantics_decls t1 main P3).
  { apply (pan_globalsProof.compile_top_semantics_decls s t1 main P2 mgs free
             (wloc_wlab ∘ wordSem.memory t) (locals s)).
    split; [exact HdP2|]. split; [reflexivity|]. split; [exact Hsc|]. split; [exact Hsg|].
    split; [exact Hal|]. split; [exact Hg|]. split; [unfold mgs; rewrite Hsz2; reflexivity|].
    split; [unfold free; rewrite Hsz2; reflexivity|]. split; [exact Hdis|].
    split; [intros ad Had; rewrite Hmem by exact Had; symmetry; apply wloc_wlab_wlab_wloc|].
    split; [exact Hnot|]. split; [rewrite Hsz2, N.mul_comm; exact Hbnd|].
    split; [apply pan_structsProof.compile_top_no_names|exact Hsem2]. }
  assert (Hsem3 : semantics_decls t1 main P3 <> Fail) by (rewrite <- E3; exact Hsem2).
  assert (HdP3 : ALL_DISTINCT (MAP FST (functions P3))) by (apply pan_globalsProof.ALL_DISTINCT_compile_top, HdP2).
  (* pan_to_crep *)
  set (crep_t := crep_state t1 P3 (memory t1)).
  assert (E4 : crepSem.semantics crep_t main = semantics_decls t1 main P3).
  { apply pan_to_crepProof.state_rel_imp_semantics_decls.
    split; [unfold pan_to_crepProof.state_rel; cbn; repeat split; exact Hsg|].
    split; [exact HdP3|]. split; [exact Hsc|]. split; [reflexivity|].
    split; [exact Hsl|]. split; [exact Hse|].
    split; [apply pan_globalsProof.compile_top_localised|].
    split; [apply pan_globalsProof.compile_top_only_functions_or_exns|].
    split; [|exact Hsem3].
    unfold P3. rewrite (size_of_eids_compile_top _ _ _ _ _ Hm2). unfold P2, P1.
    rewrite size_of_eids_structs_compile_eq, pan_simpProof.size_of_eids_compile_eq. exact Hsz. }
  assert (Hsem4 : crepSem.semantics crep_t main <> Fail) by (rewrite E4; exact Hsem3).
  (* crep_to_loop *)
  set (crep_code := pan_to_crep.compile_prog P3).
  set (loop_t := loop_state crep_t c crep_code (wordSem.clock t) (wordSem.memory t)).
  assert (E5 : loopSem.semantics loop_t crep_to_loop.first_name = crepSem.semantics crep_t main).
  { apply (crep_to_loopProof.state_rel_imp_semantics crep_t loop_t crep_code main crep_to_loop.first_name c).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { intros ad Had. cbn in Had |- *.
      assert (Had' : ad IN wordSem.mdomain t) by (rewrite Hmd; exact Had).
      destruct (Hnl ad Had') as [w ->]. reflexivity. }
    split; [intros ad v Hv; change (FLOOKUP (FEMPTY : fmap (word 5) (word_lab a)) ad = SOME v) in Hv;
            rewrite FLOOKUP_EMPTY in Hv; discriminate|].
    split; [apply pan_to_crepProof.first_compile_prog_all_distinct, HdP3|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply (FLOOKUP_make_funcs_main P2 main body2 rsh2 Hm2)|exact Hsem4]. }
  assert (Hsem5 : loopSem.semantics loop_t crep_to_loop.first_name <> Fail) by (rewrite E5; exact Hsem4).
  (* loop_to_word *)
  assert (E6 : wordSem.semantics t crep_to_loop.first_name = loopSem.semantics loop_t crep_to_loop.first_name).
  { apply loop_to_wordProof.state_rel_imp_semantics.
    split.
    { exists heap_len. cbn.
      split; [reflexivity|]. split; [rewrite Hmd; reflexivity|]. split; [exact Hsh|].
      split; [reflexivity|]. split; [exact Hbe|]. split; [exact Hffi|].
      split; [exact Hch|]. split; [exact Hhl|].
      split; [unfold mgs; rewrite Htop; apply WORD_SUB_ADD|].
      split; [intros n v Hv; rewrite FLOOKUP_EMPTY in Hv; discriminate|].
      rewrite Htc. unfold pan_to_word.compile_prog. cbv zeta. fold main.
      intros name params body Hl. split.
      - unfold loop_to_word.compile. apply loop_to_wordProof.lookup_prog_some_lookup_compile_prog, Hl.
      - pose proof (crep_to_loopProof.compile_prog_distinct_params crep_code c
                      (pan_to_crepProof.compile_prog_distinct_params P3)) as Hp.
        rewrite lookup_fromAList in Hl. apply ALOOKUP_In in Hl.
        unfold is_true in Hp. rewrite EVERY_Forall, Forall_forall in Hp.
        exact (Hp _ Hl). }
    split; [reflexivity|]. split; [exact Hg|]. split; [exact H0|].
    split; [apply lookup_first_name_compile_prog_main, (FLOOKUP_make_funcs_main P2 main body2 rsh2 Hm2)|].
    exact Hsem5. }
  rewrite E6, E5, E4, <- E3, <- E2, <- E1. reflexivity.
Qed.

End Semantics.

(** ** Syntactic properties of the generated wordLang code *)

Section Code.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_no_install_code" *)
Theorem pan_to_word_compile_prog_no_install_code : forall c (prog : list (decl a)) prog',
  pan_to_word.compile_prog c prog = prog' ->
  code.no_install_code (fromAList prog').
Proof. intros c prog prog' <-. apply loop_to_wordProof.loop_compile_no_install_code. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_no_alloc_code" *)
Theorem pan_to_word_compile_prog_no_alloc_code : forall c (prog : list (decl a)) prog',
  pan_to_word.compile_prog c prog = prog' ->
  code.no_alloc_code (fromAList prog').
Proof. intros c prog prog' <-. apply loop_to_wordProof.loop_compile_no_alloc_code. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_no_mt_code" *)
Theorem pan_to_word_compile_prog_no_mt_code : forall c (prog : list (decl a)) prog',
  pan_to_word.compile_prog c prog = prog' ->
  code.no_mt_code (fromAList prog').
Proof. intros c prog prog' <-. apply loop_to_wordProof.loop_compile_no_mt_code. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_good_handlers" *)
Theorem pan_to_word_good_handlers : forall c (prog : list (decl a)) prog',
  pan_to_word.compile_prog c prog = prog' ->
  EVERY (fun '(n, (m, pp)) => wordConvs.good_handlers n pp) prog'.
Proof.
  intros c prog prog' <-. unfold pan_to_word.compile_prog, loop_to_word.compile. cbv zeta.
  eapply loop_to_wordProof.loop_to_word_good_handlers. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_lab_pres" *)
Theorem pan_to_word_compile_lab_pres : forall c (prog : list (decl a)) prog',
  pan_to_word.compile_prog c prog = prog' ->
  EVERY (fun '(n, (m, p)) =>
           let labs := wordConvs.extract_labels p in
           EVERY (fun '(l1, l2) => (l1 =? n) && negb (l2 =? 0) && negb (l2 =? 1)) labs &&
           ALL_DISTINCT labs) prog'.
Proof.
  intros c prog prog' <-. unfold pan_to_word.compile_prog, loop_to_word.compile. cbv zeta.
  eapply loop_to_wordProof.loop_to_word_compile_prog_lab_pres. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_compile_prog_lab_min" *)
Theorem pan_to_word_compile_prog_lab_min : forall c (pprog : list (decl a)) wprog,
  pan_to_word.compile_prog c pprog = wprog ->
  EVERY (fun prog => 60 <=? FST prog) wprog.
Proof.
  intros c pprog wprog <-. unfold pan_to_word.compile_prog. cbv zeta.
  eapply loop_to_wordProof.loop_to_word_compile_lab_min. split; [reflexivity|].
  eapply crep_to_loopProof.crep_to_loop_compile_prog_lab_min. reflexivity.
Qed.

End Code.

(** ** Instruction side conditions: loopLang passes *)

Section InstOkLoop.
Context {a : N}.

Lemma EVERY_bd_Forall {A} (Q : A -> Prop) (l : list A) :
  EVERY (fun x => ⌜Q x⌝) l <-> Forall Q l.
Proof.
  unfold is_true. rewrite EVERY_Forall. split; intros H; eapply Forall_impl; try exact H;
    intros x Hx; cbv beta in *; [exact (proj1 (bool_decide_spec _) Hx)|exact (proj2 (bool_decide_spec _) Hx)].
Qed.

Ltac lok_simp := cbn [FST fst SND snd loopProps.every_prog loop_to_wordProof.loop_inst_ok] in *.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_loop_call" *)
Theorem every_inst_ok_loop_call : forall (c : asm_config a) l (prog : loopLang.prog a),
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) prog ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (FST (loop_call.comp l prog)).
Proof.
  intros c l prog; revert l.
  induction prog using loopProps.prog_nested_ind; intros l0 Hev; cbn [loop_call.comp]; lok_simp;
    try exact Hev; try exact Logic.I.
  - destruct e; exact Logic.I.
  - destruct (loop_call.comp l0 prog1) as [np nl] eqn:E1.
    destruct (loop_call.comp nl prog2) as [nq nl'] eqn:E2. lok_simp.
    pose proof (IHprog1 l0 (proj1 (proj2 Hev))) as H1. pose proof (IHprog2 nl (proj2 (proj2 Hev))) as H2.
    rewrite E1 in H1. rewrite E2 in H2. lok_simp. tauto.
  - destruct (loop_call.comp l0 prog1) as [np nl] eqn:E1.
    destruct (loop_call.comp l0 prog2) as [nq nl'] eqn:E2. lok_simp.
    pose proof (IHprog1 l0 (proj1 (proj2 Hev))) as H1. pose proof (IHprog2 l0 (proj2 (proj2 Hev))) as H2.
    rewrite E1 in H1. rewrite E2 in H2. lok_simp. tauto.
  - destruct (loop_call.comp LN prog) as [np nl] eqn:E1. lok_simp.
    pose proof (IHprog LN (proj2 Hev)) as H1. rewrite E1 in H1. lok_simp. tauto.
  - destruct (loop_call.comp l0 prog) as [np nl] eqn:E1. lok_simp.
    pose proof (IHprog l0 (proj2 Hev)) as H1. rewrite E1 in H1. lok_simp. tauto.
  - destruct dest; [exact Hev|]. destruct args; [exact Logic.I|].
    destruct (lookup _ l0); lok_simp; exact Hev.
Qed.

Lemma every_inst_ok_shrink (c : asm_config a) : forall (prog : loopLang.prog a) lt l,
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) prog ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (FST (loop_live.shrink lt prog l)).
Proof.
  induction prog using loopProps.prog_nested_ind; intros lt l0 Hev; cbn [loop_live.shrink]; lok_simp;
    try exact Hev; try exact Logic.I.
  - destruct (lookup n l0); exact Logic.I.
  - destruct (loop_live.shrink lt prog2 l0) as [p2 l2] eqn:E2.
    destruct (loop_live.shrink lt prog1 l2) as [p1 l1] eqn:E1. lok_simp.
    pose proof (IHprog1 lt l2 (proj1 (proj2 Hev))) as H1. pose proof (IHprog2 lt l0 (proj2 (proj2 Hev))) as H2.
    rewrite E1 in H1. rewrite E2 in H2. lok_simp. tauto.
  - destruct (loop_live.shrink lt prog1 _) as [p1 l1] eqn:E1.
    destruct (loop_live.shrink lt prog2 _) as [p2 l2] eqn:E2. lok_simp.
    pose proof (IHprog1 lt (inter l0 l) (proj1 (proj2 Hev))) as H1.
    pose proof (IHprog2 lt (inter l0 l) (proj2 (proj2 Hev))) as H2.
    rewrite E1 in H1. rewrite E2 in H2. lok_simp. tauto.
  - change (loop_live.fixedpoint_f (fun lt0 l1 => loop_live.shrink lt0 prog l1)
              (loop_live.fixedpoint_fuel l1 LN) lt l1 LN (union l1 (inter l2 l0)))
      with (loop_live.fixedpoint lt l1 LN (union l1 (inter l2 l0)) prog).
    destruct (loop_live.fixedpoint lt l1 LN (union l1 (inter l2 l0)) prog) as [[b l3]|] eqn:Ef.
    + apply loop_live.fixedpoint_thm in Ef. lok_simp.
      match type of Ef with loop_live.shrink ?x prog ?y = _ =>
        pose proof (IHprog x y (proj2 Hev)) as H1 end. rewrite Ef in H1. lok_simp. tauto.
    + destruct (loop_live.shrink _ prog _) as [b l3] eqn:E. lok_simp.
      match type of E with loop_live.shrink ?x prog ?y = _ =>
        pose proof (IHprog x y (proj2 Hev)) as H1 end. rewrite E in H1. lok_simp. tauto.
  - exact (IHprog _ _ (proj2 Hev)).
  - destruct (lookup n l0); exact Logic.I.
  - destruct ret as [[ns l1]|]; [|lok_simp; tauto].
    destruct h as [[e [hp [rp lo]]]|]; [|lok_simp; tauto].
    destruct H as [IH1 IH2].
    destruct (loop_live.shrink lt rp l0) as [r' l2] eqn:E2.
    destruct (loop_live.shrink lt hp l0) as [h' l3] eqn:E3. lok_simp.
    destruct Hev as [_ [Hh Hr]].
    pose proof (IH1 lt l0 Hh) as H1. pose proof (IH2 lt l0 Hr) as H2.
    rewrite E3 in H1. rewrite E2 in H2. lok_simp. tauto.
Qed.

Lemma every_inst_ok_mark_all (c : asm_config a) : forall prog : loopLang.prog a,
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) prog ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (FST (loop_live.mark_all prog)).
Proof.
  induction prog using loopProps.prog_nested_ind; intros Hev; cbn [loop_live.mark_all]; lok_simp;
    try (split; [exact Logic.I|exact Hev]).
  - destruct (loop_live.mark_all prog1) as [p1 t1] eqn:E1.
    destruct (loop_live.mark_all prog2) as [p2 t2] eqn:E2.
    pose proof (IHprog1 (proj1 (proj2 Hev))) as H1. pose proof (IHprog2 (proj2 (proj2 Hev))) as H2.
    try rewrite E1 in H1; try rewrite E2 in H2. destruct (t1 && t2); lok_simp; tauto.
  - destruct (loop_live.mark_all prog1) as [p1 t1] eqn:E1.
    destruct (loop_live.mark_all prog2) as [p2 t2] eqn:E2.
    pose proof (IHprog1 (proj1 (proj2 Hev))) as H1. pose proof (IHprog2 (proj2 (proj2 Hev))) as H2.
    try rewrite E1 in H1; try rewrite E2 in H2. destruct (t1 && t2); lok_simp; tauto.
  - destruct (loop_live.mark_all prog) as [p1 t1] eqn:E1.
    pose proof (IHprog (proj2 Hev)) as H1. try rewrite E1 in H1. lok_simp. tauto.
  - exact (IHprog (proj2 Hev)).
  - destruct h as [[ns [p1 [p2 l]]]|]; [|lok_simp; tauto].
    destruct H as [IH1 IH2]. destruct Hev as [_ [Hp1 Hp2]].
    destruct (loop_live.mark_all p1) as [q1 t1] eqn:E1.
    destruct (loop_live.mark_all p2) as [q2 t2] eqn:E2.
    pose proof (IH1 Hp1) as H1. pose proof (IH2 Hp2) as H2.
    try rewrite E1 in H1; try rewrite E2 in H2. destruct (t1 && t2); lok_simp; tauto.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_loop_live" *)
Theorem every_inst_ok_loop_live : forall (c : asm_config a) (prog : loopLang.prog a),
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) prog ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (loop_live.comp prog).
Proof.
  intros c prog H. unfold loop_live.comp. apply every_inst_ok_mark_all, every_inst_ok_shrink, H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_optimise" *)
Theorem every_inst_ok_less_optimise : forall (c : asm_config a) (prog : loopLang.prog a),
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) prog ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (loop_live.optimise prog).
Proof.
  intros c prog H. unfold loop_live.optimise.
  apply every_inst_ok_loop_live, every_inst_ok_loop_call, H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_prog_loop_inst_ok_nested_seq" *)
Theorem every_prog_loop_inst_ok_nested_seq : forall (c : asm_config a) (ps : list (loopLang.prog a)),
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (loopLang.nested_seq ps) <->
  EVERY (fun p => ⌜loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) p⌝) ps.
Proof.
  intros c ps. rewrite EVERY_bd_Forall.
  induction ps as [|p ps IH]; cbn [loopLang.nested_seq]; lok_simp.
  - split; intros _; [constructor|exact Logic.I].
  - rewrite Forall_cons_iff, <- IH. tauto.
Qed.

End InstOkLoop.

(** ** Instruction side conditions: crepLang to loopLang *)

Lemma EVERY_app_iff {A} (P : A -> bool) l1 l2 :
  is_true (EVERY P (l1 ++ l2)) <-> is_true (EVERY P l1) /\ is_true (EVERY P l2).
Proof.
  unfold is_true. induction l1 as [|x l1 IH]; cbn [app EVERY]; [tauto|].
  rewrite !Bool.andb_true_iff, IH. tauto.
Qed.

Section InstOkCrep.
Context {a : N}.

Lemma Pc_other (x : crepLang.exp a) :
  (forall op es, x <> crepLang.Crepop op es) ->
  ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝ = true.
Proof. intros H. apply bool_decide_spec. intros op es E. exfalso. exact (H op es E). Qed.

Lemma Pc_crepop op (es : list (crepLang.exp a)) :
  ⌜forall op' es', crepLang.Crepop op es = crepLang.Crepop op' es' -> LENGTH es' = 2⌝ = true <->
  LENGTH es = 2.
Proof.
  rewrite bool_decide_spec. split; [intros H; exact (H op es eq_refl)|].
  intros H op' es' E. injection E as _ <-. exact H.
Qed.

Ltac pc_kill :=
  repeat match goal with
         | |- context [⌜forall op es, ?x = crepLang.Crepop op es -> LENGTH es = 2⌝] =>
             rewrite (Pc_other x) by (intros ? ? ?Hc; discriminate Hc)
         end.

Ltac ee_split :=
  repeat match goal with
         | H : (_ && _) = true |- _ => apply andb_prop in H as [?H ?H]
         | H : is_true (_ && _) |- _ => apply andb_prop in H as [?H ?H]
         end.

Ltac lok_simp := cbn [FST fst SND snd loopProps.every_prog loop_to_wordProof.loop_inst_ok] in *.

Lemma length_compile_exps ctxt : forall (es : list (crepLang.exp a)) n ns,
  LENGTH (FST (SND (crep_to_loop.compile_exps ctxt n ns es))) = LENGTH es.
Proof.
  induction es as [|e es IH]; intros n ns; cbn [crep_to_loop.compile_exps]; [reflexivity|].
  destruct (crep_to_loop.compile_exp ctxt n ns e) as [p [le [tmp l]]].
  specialize (IH tmp l). destruct (crep_to_loop.compile_exps ctxt tmp l es) as [p1 [les [tmp' l']]].
  cbn [FST SND fst snd] in *. rewrite !LENGTH_length in *. cbn [Datatypes.length]. lia.
Qed.

Lemma Forall_MAPi_Assign (c : asm_config a) : forall (les : list (loopLang.exp a)) i tmp,
  Forall (loopProps.every_prog (loop_to_wordProof.loop_inst_ok c))
    (crep_to_loop.MAPi_from i (fun n => loopLang.Assign (tmp + n)) les).
Proof. induction les as [|e les IH]; intros i tmp; cbn; constructor; [exact Logic.I|apply IH]. Qed.

Lemma Forall_MAP2_Assign (c : asm_config a) : forall (xs : list N) (les : list (loopLang.exp a)),
  Forall (loopProps.every_prog (loop_to_wordProof.loop_inst_ok c)) (MAP2 loopLang.Assign xs les).
Proof. induction xs as [|x xs IH]; intros [|e les]; cbn; constructor; [exact Logic.I|apply IH]. Qed.

Lemma cl_exps (c : asm_config a) ctxt : forall es : list (crepLang.exp a),
  Forall (fun e => forall n ns,
            is_true (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e) ->
            Forall (loopProps.every_prog (loop_to_wordProof.loop_inst_ok c))
              (FST (crep_to_loop.compile_exp ctxt n ns e))) es ->
  forall n ns,
  is_true (EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es) ->
  Forall (loopProps.every_prog (loop_to_wordProof.loop_inst_ok c))
    (FST (crep_to_loop.compile_exps ctxt n ns es)).
Proof.
  induction es as [|e es IH]; intros HI n ns H; cbn [crep_to_loop.compile_exps]; [constructor|].
  inversion HI as [|? ? He HI']; subst. cbn [EVERY] in H. apply andb_prop in H as [Hh Ht].
  specialize (He n ns Hh).
  destruct (crep_to_loop.compile_exp ctxt n ns e) as [p [le [tmp l]]].
  specialize (IH HI' tmp l Ht).
  destruct (crep_to_loop.compile_exps ctxt tmp l es) as [p1 [les [tmp' l']]].
  cbn [FST fst] in *. apply Forall_app. split; assumption.
Qed.

Lemma cl_exp (c : asm_config a) ctxt : crep_to_loop.target ctxt = ISA c ->
  forall (e : crepLang.exp a) n ns,
  is_true (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e) ->
  Forall (loopProps.every_prog (loop_to_wordProof.loop_inst_ok c))
    (FST (crep_to_loop.compile_exp ctxt n ns e)).
Proof.
  intros Ht e. induction e as [w|v0|e IH|e IH|e IH|g|op es IH|op es IH|cm e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using crepProps.cexp_nested_ind; intros n ns H; cbn [crep_to_loop.compile_exp] in *;
    cbn [crepProps.every_exp] in H; try (constructor; fail).
  - apply andb_prop in H as [_ He].
    specialize (IH n ns He). destruct (crep_to_loop.compile_exp ctxt n ns e) as [p [le [tmp l]]]. exact IH.
  - apply andb_prop in H as [_ He].
    specialize (IH n ns He). destruct (crep_to_loop.compile_exp ctxt n ns e) as [p [le [tmp l]]].
    cbn [FST fst]. apply Forall_app. split; [exact IH|]. repeat constructor.
  - apply andb_prop in H as [_ He].
    specialize (IH n ns He). destruct (crep_to_loop.compile_exp ctxt n ns e) as [p [le [tmp l]]].
    cbn [FST fst]. apply Forall_app. split; [exact IH|]. repeat constructor.
  - apply andb_prop in H as [_ He].
    rewrite crep_to_loop.compile_exps_nested. pose proof (cl_exps c ctxt es IH n ns He) as Hp.
    destruct (crep_to_loop.compile_exps ctxt n ns es) as [p [les [tmp l]]]. exact Hp.
  - apply andb_prop in H as [H0 He].
    rewrite crep_to_loop.compile_exps_nested. pose proof (cl_exps c ctxt es IH n ns He) as Hp.
    apply Pc_crepop in H0.
    pose proof (length_compile_exps ctxt es n ns) as Hl.
    destruct (crep_to_loop.compile_exps ctxt n ns es) as [p [les [tmp l]]]. cbn [FST SND fst snd] in Hp, Hl.
    destruct op. unfold crep_to_loop.compile_crepop. rewrite Ht.
    destruct (decide (ISA c = ARMv7)) as [HA|HA]; cbn [FST fst];
      apply Forall_app; (split; [exact Hp|]); apply Forall_app; (split; [apply Forall_MAPi_Assign|]);
      repeat constructor; lok_simp; rewrite ?Hl, ?H0.
    all: first [lia | intros HX; first [lia | contradiction | (destruct HX as [HX|[HX|HX]]; congruence)]].
  - apply andb_prop in H as [H' He2]. apply andb_prop in H' as [_ He1].
    specialize (IH1 n ns He1). destruct (crep_to_loop.compile_exp ctxt n ns e1) as [p [le [tmp l]]].
    specialize (IH2 tmp l He2). destruct (crep_to_loop.compile_exp ctxt tmp l e2) as [p' [le' [tmp' l']]].
    cbn [FST fst] in *. unfold crep_to_loop.prog_if.
    apply Forall_app. split; [exact IH1|]. apply Forall_app. split; [exact IH2|].
    repeat constructor.
  - apply andb_prop in H as [H' He2]. apply andb_prop in H' as [_ He1].
    specialize (IH1 n ns He1). destruct (crep_to_loop.compile_exp ctxt n ns e1) as [p [le [tmp l]]].
    specialize (IH2 tmp l He2). destruct (crep_to_loop.compile_exp ctxt tmp l e2) as [p' [le' [tmp' l']]].
    cbn [FST fst] in *. apply Forall_app. split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_crep_to_loop_compile_exp" *)
Theorem every_inst_ok_less_crep_to_loop_compile_exp : forall c : asm_config a,
  (forall ctxt n ns (e : crepLang.exp a),
     crep_to_loop.target ctxt = ISA c /\
     crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e ->
     EVERY (fun p => ⌜loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) p⌝)
       (FST (crep_to_loop.compile_exp ctxt n ns e))) /\
  (forall ctxt n ns (es : list (crepLang.exp a)),
     crep_to_loop.target ctxt = ISA c /\
     EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es ->
     EVERY (fun p => ⌜loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) p⌝)
       (FST (crep_to_loop.compile_exps ctxt n ns es))).
Proof.
  intros c. split.
  - intros ctxt n ns e [Ht He]. apply EVERY_bd_Forall. exact (cl_exp c ctxt Ht e n ns He).
  - intros ctxt n ns es [Ht He]. apply EVERY_bd_Forall. apply (cl_exps c ctxt es); [|exact He].
    apply Forall_forall. intros e _ n' ns' He'. exact (cl_exp c ctxt Ht e n' ns' He').
Qed.

Lemma Forall_every_prog_nested_seq (c : asm_config a) (ps : list (loopLang.prog a)) :
  Forall (loopProps.every_prog (loop_to_wordProof.loop_inst_ok c)) ps ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (loopLang.nested_seq ps).
Proof. intros H. apply every_prog_loop_inst_ok_nested_seq, EVERY_bd_Forall, H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_crep_to_loop_compile" *)
Theorem every_inst_ok_less_crep_to_loop_compile : forall (c : asm_config a) ctxt ns
    (body : crepLang.prog a),
  crep_to_loop.target ctxt = ISA c /\
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (crepProps.exps_of body) ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) (crep_to_loop.compile ctxt ns body).
Proof.
  intros c ctxt ns body; revert ctxt ns.
  induction body as [|v e p IH|v e|l op r|e1 e2|e1 e2|e1 e2|g e|p q IHp IHq|e p q IHp IHq|e p IH
                    |n|n|o f es Hc|f p1 l1 p2 l2|w|es|op v e|]
    using crepProps.cprog_nested_ind;
    intros ctxt ns [Ht H]; cbn [crep_to_loop.compile]; cbn [crepProps.exps_of EVERY] in H;
    try (apply andb_prop in H as [H0 H1]); try (pose proof H as H2);
    lok_simp; try exact Logic.I.
  - (* Dec *)
    pose proof (cl_exp c ctxt Ht e (crep_to_loop.vmax ctxt + 1) ns H0) as He.
    destruct (crep_to_loop.compile_exp ctxt _ ns e) as [p0 [le [tmp nl]]]. lok_simp.
    split; [exact Logic.I|]. split; [apply Forall_every_prog_nested_seq, He|].
    split; [exact Logic.I|]. split; [exact Logic.I|].
    apply IH. split; [exact Ht|exact H1].
  - (* Assign *)
    destruct (FLOOKUP (crep_to_loop.vars ctxt) v) as [n|]; [|exact Logic.I].
    pose proof (cl_exp c ctxt Ht e (crep_to_loop.vmax ctxt + 1) ns H0) as He.
    destruct (crep_to_loop.compile_exp ctxt _ ns e) as [p0 [le [tmp nl]]]. lok_simp.
    apply Forall_every_prog_nested_seq, Forall_app. split; [exact He|]. repeat constructor.
  - (* Primitive *)
    repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; exact Logic.I.
  - (* Store *)
    apply andb_prop in H1 as [H2 _].
    pose proof (cl_exp c ctxt Ht e1 (crep_to_loop.vmax ctxt + 1) ns H0) as He1.
    destruct (crep_to_loop.compile_exp ctxt _ ns e1) as [p0 [le [tmp nl]]].
    pose proof (cl_exp c ctxt Ht e2 tmp nl H2) as He2.
    destruct (crep_to_loop.compile_exp ctxt tmp nl e2) as [p1 [le' [tmp' nl']]]. lok_simp.
    apply Forall_every_prog_nested_seq. repeat (apply Forall_app; split; [assumption|]). repeat constructor.
  - (* Store32 *)
    apply andb_prop in H1 as [H2 _].
    pose proof (cl_exp c ctxt Ht e1 (crep_to_loop.vmax ctxt + 1) ns H0) as He1.
    destruct (crep_to_loop.compile_exp ctxt _ ns e1) as [p0 [le [tmp nl]]].
    pose proof (cl_exp c ctxt Ht e2 tmp nl H2) as He2.
    destruct (crep_to_loop.compile_exp ctxt tmp nl e2) as [p1 [le' [tmp' nl']]]. lok_simp.
    apply Forall_every_prog_nested_seq. repeat (apply Forall_app; split; [assumption|]). repeat constructor.
  - (* StoreByte *)
    apply andb_prop in H1 as [H2 _].
    pose proof (cl_exp c ctxt Ht e1 (crep_to_loop.vmax ctxt + 1) ns H0) as He1.
    destruct (crep_to_loop.compile_exp ctxt _ ns e1) as [p0 [le [tmp nl]]].
    pose proof (cl_exp c ctxt Ht e2 tmp nl H2) as He2.
    destruct (crep_to_loop.compile_exp ctxt tmp nl e2) as [p1 [le' [tmp' nl']]]. lok_simp.
    apply Forall_every_prog_nested_seq. repeat (apply Forall_app; split; [assumption|]). repeat constructor.
  - (* StoreGlob *)
    pose proof (cl_exp c ctxt Ht e (crep_to_loop.vmax ctxt + 1) ns H0) as He.
    destruct (crep_to_loop.compile_exp ctxt _ ns e) as [p0 [le [tmp nl]]]. lok_simp.
    apply Forall_every_prog_nested_seq, Forall_app. split; [exact He|]. repeat constructor.
  - (* Seq *)
    apply EVERY_app_iff in H. destruct H as [Hq1 Hq2].
    split; [exact Logic.I|]. split; [apply IHp; split; assumption|apply IHq; split; assumption].
  - (* If *)
    apply EVERY_app_iff in H1. destruct H1 as [H2 H3].
    pose proof (cl_exp c ctxt Ht e (crep_to_loop.vmax ctxt + 1) ns H0) as He.
    destruct (crep_to_loop.compile_exp ctxt _ ns e) as [p0 [le [tmp nl]]]. lok_simp.
    apply Forall_every_prog_nested_seq, Forall_app. split; [exact He|].
    constructor; [exact Logic.I|]. constructor; [|constructor]. lok_simp.
    split; [exact Logic.I|]. split; [apply IHp; split; assumption|apply IHq; split; assumption].
  - (* While *)
    pose proof (cl_exp c ctxt Ht e (crep_to_loop.vmax ctxt + 1) ns H0) as He.
    destruct (crep_to_loop.compile_exp ctxt _ ns e) as [p0 [le [tmp nl]]]. lok_simp.
    split; [exact Logic.I|]. apply Forall_every_prog_nested_seq, Forall_app. split; [exact He|].
    constructor; [exact Logic.I|]. constructor; [|constructor]. lok_simp.
    split; [exact Logic.I|]. split; [|split; exact Logic.I].
    split; [exact Logic.I|]. split; [apply IH; split; assumption|exact Logic.I].
  - (* Call *)
    assert (Hes : is_true (EVERY (crepProps.every_exp
                  (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es)).
    { destruct o as [[rts [[w p]|]]|]; cbn [crepProps.exps_of] in H; try exact H.
      apply EVERY_app_iff in H. exact (proj1 H). }
    pose proof (cl_exps c ctxt es (proj2 (Forall_forall _ _) (fun e _ n' ns' He' => cl_exp c ctxt Ht e n' ns' He'))
                  (crep_to_loop.vmax ctxt + 1) ns Hes) as Hp.
    destruct (crep_to_loop.compile_exps ctxt _ ns es) as [p0 [les [tmp nl]]]. cbn [FST fst] in Hp.
    match goal with |- context [let '(rt1, rt2) := ?m in _] => destruct m as [rt1 rt2] eqn:Ert end.
    apply Forall_every_prog_nested_seq, Forall_app. split; [exact Hp|].
    apply Forall_app. split; [apply Forall_MAP2_Assign|]. constructor; [|constructor]. lok_simp.
    split; [exact Logic.I|].
    destruct o as [[rts hdl]|]; [|injection Ert as <- <-; exact Logic.I].
    injection Ert as <- <-. cbv zeta. split; [|exact Logic.I].
    destruct hdl as [[eid ep]|]; lok_simp; [|exact Logic.I].
    split; [exact Logic.I|]. split; [exact Logic.I|]. split; [exact Logic.I|].
    split; [exact Logic.I|]. apply (Hc rts eid ep eq_refl). split; [exact Ht|].
    cbn [crepProps.exps_of] in H. apply EVERY_app_iff in H. exact (proj2 H).
  - (* ExtCall *)
    repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; exact Logic.I.
  - (* Raise *)
    repeat split.
  - (* Return *)
    pose proof (cl_exps c ctxt es (proj2 (Forall_forall _ _) (fun e _ n' ns' He' => cl_exp c ctxt Ht e n' ns' He'))
                  (crep_to_loop.vmax ctxt + 1) ns H) as Hp.
    destruct (crep_to_loop.compile_exps ctxt _ ns es) as [p0 [les [tmp nl]]]. cbn [FST fst] in Hp.
    apply Forall_every_prog_nested_seq, Forall_app. split; [exact Hp|].
    apply Forall_app. split; [apply Forall_MAP2_Assign|]. repeat constructor.
  - (* ShMem *)
    destruct (FLOOKUP (crep_to_loop.vars ctxt) v) as [n|]; [|exact Logic.I].
    pose proof (cl_exp c ctxt Ht e (crep_to_loop.vmax ctxt + 1) ns H0) as He.
    destruct (crep_to_loop.compile_exp ctxt _ ns e) as [p0 [le [tmp nl]]]. lok_simp.
    apply Forall_every_prog_nested_seq, Forall_app. split; [exact He|]. repeat constructor.
Qed.

End InstOkCrep.

Section InstOkCrep2.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_comp_func" *)
Theorem every_inst_ok_less_comp_func : forall (c : asm_config a)
    (prog : list (mlstring * (list N * crepLang.prog a))) params (body : crepLang.prog a),
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (crepProps.exps_of body) ->
  loopProps.every_prog (loop_to_wordProof.loop_inst_ok c)
    (crep_to_loop.comp_func (ISA c) (crep_to_loop.make_funcs prog) params body).
Proof.
  intros c prog params body H. unfold crep_to_loop.comp_func. cbv zeta.
  apply every_inst_ok_less_crep_to_loop_compile. split; [reflexivity|exact H].
Qed.

Lemma mul_const_ok (e : crepLang.exp a) w :
  is_true (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e) ->
  is_true (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)
    (crep_arith.mul_const e w)).
Proof.
  intros H. unfold crep_arith.mul_const.
  destruct (decide (w = n2w 0)); [cbn; apply Pc_other; intros ? ? C; discriminate C|].
  destruct (decide (w = n2w 1)); [exact H|].
  destruct (crep_arith.dest_2exp 0 w); cbn [crepProps.every_exp EVERY]; unfold is_true in *.
  - rewrite H, (Pc_other (crepLang.Shift _ _ _)), (Pc_other (crepLang.Const _));
      [reflexivity|intros ? ? C; discriminate C|intros ? ? C; discriminate C].
  - rewrite H, (Pc_other (crepLang.Const _)) by (intros ? ? C; discriminate C).
    rewrite (proj2 (Pc_crepop _ _)) by reflexivity. reflexivity.
Qed.

Lemma EVERY_MAP_simp_exp (f : crepLang.exp a -> crepLang.exp a)
    (P : crepLang.exp a -> bool) (es : list (crepLang.exp a)) :
  Forall (fun e => is_true (P e) -> is_true (P (f e))) es ->
  is_true (EVERY P es) -> is_true (EVERY P (MAP f es)).
Proof.
  unfold is_true. intros HF; induction HF as [|e es He HF IH]; cbn [EVERY List.map]; [reflexivity|].
  intros H. apply andb_prop in H as [H1 H2]. rewrite (He H1), (IH H2). reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_arith_simp_exp" *)
Theorem every_inst_ok_arith_simp_exp : forall exp : crepLang.exp a,
  crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) exp ->
  crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)
    (crep_arith.simp_exp exp).
Proof.
  intros e. unfold is_true.
  induction e as [w|v0|e IH|e IH|e IH|g|op es IH|op es IH|cm e1 e2 IH1 IH2|sh e1 e2 IH1 IH2| |]
    using crepProps.cexp_nested_ind; intros H; cbn [crep_arith.simp_exp]; try exact H;
    cbn [crepProps.every_exp] in H |- *; cbv beta in H |- *.
  - apply andb_prop in H as [_ H1]. rewrite (IH H1), Pc_other by (intros ? ? C; discriminate C). reflexivity.
  - apply andb_prop in H as [_ H1]. rewrite (IH H1), Pc_other by (intros ? ? C; discriminate C). reflexivity.
  - apply andb_prop in H as [_ H1]. rewrite (IH H1), Pc_other by (intros ? ? C; discriminate C). reflexivity.
  - apply andb_prop in H as [H0 H1]. rewrite (Pc_other (crepLang.Op _ _)) by (intros ? ? C; discriminate C).
    exact (EVERY_MAP_simp_exp _ _ es IH H1).
  - apply andb_prop in H as [H0 H1]. apply Pc_crepop in H0.
    destruct op. rewrite LENGTH_length in H0.
    destruct es as [|e1 [|e2 [|e3 es]]]; cbn [Datatypes.length] in H0; try lia.
    apply Forall_cons_iff in IH as [IH1 IH']. apply Forall_cons_iff in IH' as [IH2 _].
    cbn [EVERY] in H1. apply andb_prop in H1 as [He1 H1]. apply andb_prop in H1 as [He2 _].
    specialize (IH1 He1). specialize (IH2 He2).
    cbn [List.map].
    destruct (crep_arith.dest_const (crep_arith.simp_exp e1)) as [w1|] eqn:D1;
    destruct (crep_arith.dest_const (crep_arith.simp_exp e2)) as [w2|] eqn:D2.
    + cbn. apply Pc_other. intros ? ? C; discriminate C.
    + apply mul_const_ok, IH2.
    + apply mul_const_ok, IH1.
    + cbn [crepProps.every_exp EVERY]. rewrite IH1, IH2. rewrite (proj2 (Pc_crepop _ _)) by reflexivity.
      reflexivity.
  - apply andb_prop in H as [H0 H2]. apply andb_prop in H0 as [H0 H1].
    rewrite (IH1 H1), (IH2 H2), Pc_other by (intros ? ? C; discriminate C). reflexivity.
  - apply andb_prop in H as [H0 H2]. apply andb_prop in H0 as [H0 H1].
    rewrite (IH1 H1), (IH2 H2), Pc_other by (intros ? ? C; discriminate C). reflexivity.
Qed.

Lemma EVERY_ee_MAP_simp (es : list (crepLang.exp a)) :
  is_true (EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es) ->
  is_true (EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (MAP crep_arith.simp_exp es)).
Proof.
  apply EVERY_MAP_simp_exp. apply Forall_forall. intros e _. apply every_inst_ok_arith_simp_exp.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_arith_simp_prog" *)
Theorem every_inst_ok_arith_simp_prog : forall prog : crepLang.prog a,
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (crepProps.exps_of prog) ->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (crepProps.exps_of (crep_arith.simp_prog prog)).
Proof.
  intros prog.
  induction prog as [|v e p IH|v e|l op r|e1 e2|e1 e2|e1 e2|g e|p q IHp IHq|e p q IHp IHq|e p IH
                    |n|n|o f es Hc|f p1 l1 p2 l2|w|es|op v e|]
    using crepProps.cprog_nested_ind;
    intros H; cbn [crep_arith.simp_prog crepProps.exps_of] in H |- *; try exact H.
  - cbn [EVERY] in H |- *. apply andb_prop in H as [H0 H1].
    apply andb_true_intro. split; [apply every_inst_ok_arith_simp_exp, H0|apply IH, H1].
  - exact (EVERY_ee_MAP_simp [e] H).
  - exact (EVERY_ee_MAP_simp [e1; e2] H).
  - exact (EVERY_ee_MAP_simp [e1; e2] H).
  - exact (EVERY_ee_MAP_simp [e1; e2] H).
  - exact (EVERY_ee_MAP_simp [e] H).
  - apply EVERY_app_iff in H as [H1 H2]. apply EVERY_app_iff. split; [apply IHp, H1|apply IHq, H2].
  - cbn [EVERY] in H |- *. apply andb_prop in H as [H0 H1]. apply EVERY_app_iff in H1 as [H1 H2].
    apply andb_true_intro. split; [apply every_inst_ok_arith_simp_exp, H0|].
    apply EVERY_app_iff. split; [apply IHp, H1|apply IHq, H2].
  - cbn [EVERY] in H |- *. apply andb_prop in H as [H0 H1].
    apply andb_true_intro. split; [apply every_inst_ok_arith_simp_exp, H0|apply IH, H1].
  - destruct o as [[rts [[w p]|]]|]; cbn [crepProps.exps_of] in H |- *.
    + apply EVERY_app_iff in H as [H1 H2]. apply EVERY_app_iff.
      split; [apply EVERY_ee_MAP_simp, H1|apply (Hc rts w p eq_refl), H2].
    + apply EVERY_ee_MAP_simp, H.
    + apply EVERY_ee_MAP_simp, H.
  - apply EVERY_ee_MAP_simp, H.
  - exact (EVERY_ee_MAP_simp [e] H).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_crep_to_loop_compile_prog" *)
Theorem every_inst_ok_less_crep_to_loop_compile_prog : forall (c : asm_config a)
    (crep_code : list (mlstring * (list N * crepLang.prog a))),
  EVERY (fun '(name, (params, body)) =>
           EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
             (crepProps.exps_of body)) crep_code ->
  EVERY (fun '(name, (params, body)) => ⌜loopProps.every_prog (loop_to_wordProof.loop_inst_ok c) body⌝)
    (crep_to_loop.compile_prog (ISA c) crep_code).
Proof.
  intros c crep_code H. rewrite crep_to_loopProof.compile_prog_cp.
  generalize crep_to_loop.first_name as k.
  assert (Hg : forall params body,
             is_true (EVERY (crepProps.every_exp
                (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) (crepProps.exps_of body)) ->
             loopProps.every_prog (loop_to_wordProof.loop_inst_ok c)
               (loop_live.optimise (crep_to_loop.comp_func (ISA c) (crep_to_loop.make_funcs crep_code) params
                  (crep_arith.simp_prog body)))).
  { intros params body Hb. apply every_inst_ok_less_optimise, every_inst_ok_less_comp_func,
      every_inst_ok_arith_simp_prog, Hb. }
  revert Hg. generalize (crep_to_loop.make_funcs crep_code) as fs. intros fs Hg.
  induction crep_code as [|[f [ns p]] code IH]; intros k; [reflexivity|].
  rewrite crep_to_loopProof.cp_list_cons. cbn [EVERY] in H |- *. unfold is_true in *.
  apply andb_prop in H as [H1 H2]. apply andb_true_intro. split.
  - apply bool_decide_spec. apply Hg, H1.
  - apply IH, H2.
Qed.

End InstOkCrep2.

(** ** Instruction side conditions: Pancake to crepLang *)

Section InstOkPan.
Context {a : N}.

(** Galette-only: the side condition on crepLang expressions as a
    proposition. *)
Definition crok (e : crepLang.exp a) : Prop :=
  is_true (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e).

Lemma EVERY_crok (es : list (crepLang.exp a)) :
  is_true (EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es)
  <-> Forall crok es.
Proof. unfold is_true. rewrite EVERY_Forall. reflexivity. Qed.

Ltac pck := cbn [crepProps.every_exp]; cbv beta;
  rewrite ?Pc_other by (intros ? ? ?Hc; discriminate Hc); cbn [andb].

Lemma crok_simple :
  (forall w, crok (crepLang.Const w)) /\ (forall v, crok (crepLang.Var v)) /\
  (forall g, crok (crepLang.LoadGlob g)) /\ crok crepLang.BaseAddr /\ crok crepLang.TopAddr.
Proof. unfold crok, is_true. repeat split; intros; pck; reflexivity. Qed.

Lemma crok_load e : crok (crepLang.Load e) <-> crok e.
Proof. unfold crok, is_true. pck. reflexivity. Qed.
Lemma crok_load32 e : crok (crepLang.Load32 e) <-> crok e.
Proof. unfold crok, is_true. pck. reflexivity. Qed.
Lemma crok_loadbyte e : crok (crepLang.LoadByte e) <-> crok e.
Proof. unfold crok, is_true. pck. reflexivity. Qed.
Lemma crok_op bop es : crok (crepLang.Op bop es) <-> Forall crok es.
Proof. unfold crok. rewrite <- EVERY_crok. unfold is_true. pck. reflexivity. Qed.
Lemma crok_crepop op es : crok (crepLang.Crepop op es) <-> LENGTH es = 2 /\ Forall crok es.
Proof.
  unfold crok. rewrite <- EVERY_crok. unfold is_true. cbn [crepProps.every_exp]. cbv beta.
  rewrite andb_true_iff, Pc_crepop. reflexivity.
Qed.
Lemma crok_cmp c e1 e2 : crok (crepLang.Cmp c e1 e2) <-> crok e1 /\ crok e2.
Proof. unfold crok, is_true. pck. rewrite andb_true_iff. reflexivity. Qed.
Lemma crok_shift s e1 e2 : crok (crepLang.Shift s e1 e2) <-> crok e1 /\ crok e2.
Proof. unfold crok, is_true. pck. rewrite andb_true_iff. reflexivity. Qed.

Lemma Forall_TAKE {A} (P : A -> Prop) : forall (l : list A) n, Forall P l -> Forall P (TAKE n l).
Proof.
  induction l as [|x l IH]; intros n H; cbn [TAKE]; [constructor|].
  destruct (n =? 0); [constructor|]. inversion H; subst. constructor; [assumption|apply IH; assumption].
Qed.

Lemma Forall_DROP {A} (P : A -> Prop) : forall (l : list A) n, Forall P l -> Forall P (DROP n l).
Proof.
  induction l as [|x l IH]; intros n H; cbn [DROP]; [constructor|].
  destruct (n =? 0); [exact H|]. inversion H; subst. apply IH; assumption.
Qed.

Lemma exps_of_nested_decs : forall ns es (p : crepLang.prog a),
  LENGTH ns = LENGTH es -> crepProps.exps_of (crepLang.nested_decs ns es p) = es ++ crepProps.exps_of p.
Proof.
  induction ns as [|n ns IH]; intros [|e es] p Hl; cbn [crepLang.nested_decs crepProps.exps_of app];
    try reflexivity; rewrite !LENGTH_length in Hl; cbn [Datatypes.length] in Hl; try lia.
  rewrite IH; [reflexivity|]. rewrite !LENGTH_length. lia.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_nested_decs" *)
Theorem every_inst_ok_nested_decs : forall ns ps (p : crepLang.prog a),
  LENGTH ns = LENGTH ps ->
  (EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
     (crepProps.exps_of (crepLang.nested_decs ns ps p)) <->
   EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) ps /\
   EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
     (crepProps.exps_of p)).
Proof. intros ns ps p Hl. rewrite exps_of_nested_decs by exact Hl. apply EVERY_app_iff. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_comp_field" *)
Theorem every_inst_ok_less_pan_to_crep_comp_field : forall index shapes (es : list (crepLang.exp a)) es' sh,
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es /\
  pan_to_crep.comp_field index shapes es = (es', sh) ->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es'.
Proof.
  intros index shapes; revert index.
  induction shapes as [|s shs IH]; intros index es es' sh [H Hc]; cbn [pan_to_crep.comp_field] in Hc.
  - injection Hc as <- _. apply EVERY_crok. constructor; [apply crok_simple|constructor].
  - destruct (decide (index = 0)).
    + injection Hc as <- _. apply EVERY_crok. apply EVERY_crok in H. apply Forall_TAKE, H.
    + apply (IH (index - 1) (DROP (size_of_shape s) es) es' sh). split; [|exact Hc].
      apply EVERY_crok. apply EVERY_crok in H. apply Forall_DROP, H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_load_shape" *)
Theorem every_inst_ok_less_pan_to_crep_load_shape : forall (w : word a) n e,
  crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e ->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (crepLang.load_shape w n e).
Proof.
  intros w n e He. apply EVERY_crok. revert w.
  induction n as [|n IH] using N.peano_ind; intros w; [rewrite (proj1 (crepLang.load_shape_def w e 0)); constructor|].
  rewrite (proj2 (crepLang.load_shape_def w e n)).
  destruct (decide (w = n2w 0)); constructor; try apply IH.
  - apply crok_load, He.
  - apply crok_load, crok_op. constructor; [exact He|constructor; [apply crok_simple|constructor]].
Qed.

Lemma cexp_heads_some {A} : forall (ces : list (list A)) es,
  pan_to_crep.cexp_heads ces = SOME es ->
  LENGTH es = LENGTH ces /\ Forall2 (fun e ce => exists rest, ce = e :: rest) es ces.
Proof.
  induction ces as [|ce ces IH]; intros es H; cbn [pan_to_crep.cexp_heads] in H.
  - injection H as <-. split; [reflexivity|constructor].
  - destruct ce as [|x xs]; [discriminate|].
    destruct (pan_to_crep.cexp_heads ces) as [ys|]; [|discriminate]. injection H as <-.
    destruct (IH ys eq_refl) as [H1 H2]. split.
    + rewrite !LENGTH_length in *. cbn. lia.
    + constructor; [eexists; reflexivity|exact H2].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_cexp_heads" *)
Theorem every_inst_ok_less_pan_to_crep_cexp_heads : forall (ces : list (list (crepLang.exp a))) es,
  EVERY (EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))) ces /\
  pan_to_crep.cexp_heads ces = SOME es ->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es.
Proof.
  induction ces as [|ce ces IH]; intros es [H Hc]; cbn [pan_to_crep.cexp_heads] in Hc.
  - injection Hc as <-. reflexivity.
  - destruct ce as [|x xs]; [discriminate|].
    destruct (pan_to_crep.cexp_heads ces) as [ys|] eqn:E; [|discriminate]. injection Hc as <-.
    cbn [EVERY] in H |- *. unfold is_true in *. apply andb_prop in H as [H1 H2].
    apply andb_prop in H1 as [H1 _]. rewrite H1. exact (IH ys (conj H2 eq_refl)).
Qed.

(** Galette-only: the Pancake side condition as a proposition. *)
Definition pok (e : panLang.exp a) : Prop :=
  is_true (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) e).

Lemma pok_inv e : pok e ->
  match e with
  | panLang.RStruct es => Forall pok es
  | RField _ e => pok e
  | NField _ e => pok e
  | Load _ e => pok e
  | Load32 e => pok e
  | LoadByte e => pok e
  | Op _ es => Forall pok es
  | Panop _ es => LENGTH es = 2 /\ Forall pok es
  | Cmp _ e1 e2 => pok e1 /\ pok e2
  | Shift _ e1 e2 => pok e1 /\ pok e2
  | _ => True
  end.
Proof.
  unfold pok, is_true. intros H. destruct e; cbn [every_exp] in H; try exact Logic.I;
    repeat (apply andb_prop in H as [?H ?H]); try assumption;
    try (rewrite EVERY_Forall in *; assumption);
    try (split; assumption).
  split; [|rewrite EVERY_Forall in *; assumption].
  match goal with H : ⌜_⌝ = true |- _ => apply bool_decide_spec in H; exact (H _ _ eq_refl) end.
Qed.

Lemma cexp_heads_Forall : forall (ces : list (list (crepLang.exp a))) es,
  Forall (Forall crok) ces -> pan_to_crep.cexp_heads ces = SOME es -> Forall crok es.
Proof.
  intros ces es H Hc. apply EVERY_crok. apply (every_inst_ok_less_pan_to_crep_cexp_heads ces es).
  split; [|exact Hc]. unfold is_true. rewrite EVERY_Forall. eapply Forall_impl; [|exact H].
  intros ce Hce. apply EVERY_crok, Hce.
Qed.

Lemma compile_exp_crok (ctxt : pan_to_crep.context a) : forall e,
  pok e -> Forall crok (FST (pan_to_crep.compile_exp ctxt e)).
Proof.
  intros e. induction e as [w|vk v0|es IH|i e IH|nm es IH|f e IH|sh e IH|e IH|e IH|op es IH|op es IH
                           |cm e1 e2 IH1 IH2|s e1 e2 IH1 IH2| | |]
    using exp_nested_ind; intros H; apply pok_inv in H; cbn [pan_to_crep.compile_exp];
    try (repeat constructor; apply crok_simple).
  - destruct vk; [|repeat constructor; apply crok_simple].
    destruct (FLOOKUP _ v0) as [[shp ns]|]; [|repeat constructor; apply crok_simple].
    cbn [FST fst]. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (n & <- & _). apply crok_simple.
  - cbn [FST fst]. apply Forall_concat, Forall_map, Forall_map.
    rewrite Forall_forall in IH, H |- *. intros x Hx. apply IH; [exact Hx|apply H, Hx].
  - specialize (IH H). destruct (pan_to_crep.compile_exp ctxt e) as [ces shp]. cbn [FST fst] in IH.
    destruct shp; try (repeat constructor; apply crok_simple).
    destruct (pan_to_crep.comp_field i l ces) as [es' sh'] eqn:Ec. cbn [FST fst].
    apply EVERY_crok. apply (every_inst_ok_less_pan_to_crep_comp_field i l ces es' sh').
    split; [apply EVERY_crok, IH|exact Ec].
  - specialize (IH H). destruct (pan_to_crep.compile_exp ctxt e) as [ces shp]. cbn [FST fst] in IH.
    destruct ces as [|ce ces]; [repeat constructor; apply crok_simple|].
    cbn [FST fst]. apply EVERY_crok, every_inst_ok_less_pan_to_crep_load_shape.
    inversion IH; assumption.
  - specialize (IH H). destruct (pan_to_crep.compile_exp ctxt e) as [ces shp]. cbn [FST fst] in IH.
    destruct ces as [|ce ces]; [repeat constructor; apply crok_simple|].
    destruct shp; try (repeat constructor; apply crok_simple).
    constructor; [|constructor]. apply crok_load32. inversion IH; assumption.
  - specialize (IH H). destruct (pan_to_crep.compile_exp ctxt e) as [ces shp]. cbn [FST fst] in IH.
    destruct ces as [|ce ces]; [repeat constructor; apply crok_simple|].
    destruct shp; try (repeat constructor; apply crok_simple).
    constructor; [|constructor]. apply crok_loadbyte. inversion IH; assumption.
  - destruct (pan_to_crep.cexp_heads _) as [hs|] eqn:Eh; [|repeat constructor; apply crok_simple].
    constructor; [|constructor]. apply crok_op. refine (cexp_heads_Forall _ _ _ Eh).
    apply Forall_map, Forall_map. rewrite Forall_forall in IH, H |- *. intros x Hx. apply IH; [exact Hx|apply H, Hx].
  - destruct H as [Hl H].
    destruct (pan_to_crep.cexp_heads _) as [hs|] eqn:Eh; [|repeat constructor; apply crok_simple].
    constructor; [|constructor]. apply crok_crepop. split.
    + destruct (cexp_heads_some _ _ Eh) as [Hl' _]. rewrite Hl', !LENGTH_length, !length_map.
      rewrite LENGTH_length in Hl. exact Hl.
    + refine (cexp_heads_Forall _ _ _ Eh).
      apply Forall_map, Forall_map. rewrite Forall_forall in IH, H |- *. intros x Hx. apply IH; [exact Hx|apply H, Hx].
  - destruct H as [H1 H2]. specialize (IH1 H1). specialize (IH2 H2).
    destruct (FST (pan_to_crep.compile_exp ctxt e1)) as [|c1 cs1]; [repeat constructor; apply crok_simple|].
    destruct (FST (pan_to_crep.compile_exp ctxt e2)) as [|c2 cs2]; [repeat constructor; apply crok_simple|].
    constructor; [|constructor]. apply crok_cmp. inversion IH1; inversion IH2; split; assumption.
  - destruct H as [H1 H2]. specialize (IH1 H1). specialize (IH2 H2).
    destruct (FST (pan_to_crep.compile_exp ctxt e1)) as [|c1 cs1]; [repeat constructor; apply crok_simple|].
    destruct (FST (pan_to_crep.compile_exp ctxt e2)) as [|c2 cs2]; [repeat constructor; apply crok_simple|].
    constructor; [|constructor]. apply crok_shift. inversion IH1; inversion IH2; split; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_compile_exp" *)
Theorem every_inst_ok_less_pan_to_crep_compile_exp : forall ctxt (e : panLang.exp a) es sh,
  every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) e /\
  pan_to_crep.compile_exp ctxt e = (es, sh) ->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es.
Proof.
  intros ctxt e es sh [H Hc]. apply EVERY_crok.
  pose proof (compile_exp_crok ctxt e H) as Hf. rewrite Hc in Hf. exact Hf.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "exps_of_nested_seq" *)
Theorem exps_of_nested_seq : forall es : list (crepLang.prog a),
  crepProps.exps_of (crepLang.nested_seq es) = FLAT (MAP crepProps.exps_of es).
Proof. induction es as [|e es IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_exps_of_nested_seq" *)
Theorem pan_exps_of_nested_seq : forall es : list (panLang.prog a),
  exps_of (nested_seq es) = FLAT (MAP exps_of es).
Proof. induction es as [|e es IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma EVERY_EVERY_crok {B} (f : B -> list (crepLang.exp a)) (l : list B) :
  is_true (EVERY (fun x => EVERY (crepProps.every_exp
    (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) (f x)) l) <->
  Forall (fun x => Forall crok (f x)) l.
Proof.
  unfold is_true. rewrite EVERY_Forall. split; intros H; eapply Forall_impl; try exact H;
    intros x Hx; apply EVERY_crok, Hx.
Qed.

Lemma stores_crok (e : crepLang.exp a) : forall es a0,
  Forall (fun x => Forall crok (crepProps.exps_of x)) (crepLang.stores e es a0) <->
  (es <> [] -> crok e) /\ Forall crok es.
Proof.
  intros es; induction es as [|e' es IH]; intros a0; cbn [crepLang.stores].
  - split; [intros _; split; [intros C; contradiction C; reflexivity|constructor]|intros _; constructor].
  - assert (Had : forall ad, (crok ad <-> crok e) ->
              (Forall (fun x => Forall crok (crepProps.exps_of x))
                 (crepLang.Store ad e' :: crepLang.stores e es (word_add a0 bytes_in_word)) <->
               (e' :: es <> [] -> crok e) /\ Forall crok (e' :: es))).
    { intros ad Hiff. rewrite Forall_cons_iff, IH. cbn [crepProps.exps_of].
      rewrite !Forall_cons_iff, Hiff. split.
      - intros [[He [He' _]] [_ Hes]]. split; [intros _; exact He|split; assumption].
      - intros [Hn [He' Hes]]. assert (He : crok e) by (apply Hn; discriminate).
        split; [split; [exact He|split; [exact He'|constructor]]|split; [intros _; exact He|exact Hes]]. }
    destruct (decide (a0 = n2w 0)); apply Had; [reflexivity|].
    rewrite crok_op, !Forall_cons_iff. split; [tauto|]. intros He. split; [exact He|split; [apply crok_simple|constructor]].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_stores" *)
Theorem every_inst_ok_less_stores : forall (e : crepLang.exp a) es a0,
  EVERY (fun x => EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
                    (crepProps.exps_of x))
    (crepLang.stores e es a0) <->
  (es <> [] -> crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝) e) /\
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es.
Proof.
  intros e es a0. rewrite EVERY_EVERY_crok, stores_crok, EVERY_crok. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_store_globals" *)
Theorem every_inst_ok_less_store_globals : forall (w : word 5) (es : list (crepLang.exp a)),
  EVERY (fun x => EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
                    (crepProps.exps_of x))
    (crepLang.store_globals w es) <->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝)) es.
Proof.
  intros w es. rewrite EVERY_EVERY_crok, EVERY_crok. revert w.
  induction es as [|e es IH]; intros w; cbn [crepLang.store_globals]; [split; intros; constructor|].
  rewrite !Forall_cons_iff, IH. cbn [crepProps.exps_of]. rewrite Forall_cons_iff.
  split; [intros [[H _] H2]; split; assumption|intros [H H2]; split; [split; [exact H|constructor]|exact H2]].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "load_globals_alt" *)
Theorem load_globals_alt : forall (ad : word 5) n,
  crepLang.load_globals (a := a) ad n = GENLIST (fun n => crepLang.LoadGlob (word_add ad (n2w n))) n.
Proof.
  intros ad n; revert ad. induction n as [|n IH] using N.peano_ind; intros ad; [reflexivity|].
  rewrite (proj2 (crepLang.load_globals_def ad n)), IH.
  rewrite <- N.add_1_r, GENLIST_APPEND.
  change (GENLIST (fun n0 => crepLang.LoadGlob (a := a) (word_add ad (n2w n0))) 1)
    with [crepLang.LoadGlob (a := a) (word_add ad (n2w 0))].
  cbn [app]. f_equal; [f_equal; word_ring|].
  f_equal. apply functional_extensionality. intros t. f_equal.
  rewrite <- word_add_n2w, (WORD_ADD_COMM (n2w t) (n2w 1)), WORD_ADD_ASSOC. reflexivity.
Qed.

End InstOkPan.

Section InstOkPan2.
Context {a : N}.

Lemma LENGTH_GENLIST_k {A} (f : N -> A) n : LENGTH (GENLIST f n) = n.
Proof.
  induction n as [|n IH] using N.peano_ind; [reflexivity|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app, !LENGTH_length, length_app.
  rewrite LENGTH_length in IH. cbn [Datatypes.length]. lia.
Qed.

Lemma LENGTH_cons_k {A} (x : A) l : LENGTH (x :: l) = LENGTH l + 1.
Proof. rewrite !LENGTH_length. cbn [Datatypes.length]. lia. Qed.

Lemma Forall_REPLICATE {A} (P : A -> Prop) n x : P x -> Forall P (REPLICATE n x).
Proof.
  intros H. rewrite REPLICATE_GENLIST. apply Forall_forall. intros y Hy.
  apply In_GENLIST_iff in Hy as (i & _ & ->). exact H.
Qed.

Lemma Forall_crok_Var (ns : list N) : Forall crok (MAP (crepLang.Var (a := a)) ns).
Proof. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (n & <- & _). apply crok_simple. Qed.

Lemma Forall_crok_load_globals ad n : Forall crok (crepLang.load_globals (a := a) ad n).
Proof.
  rewrite load_globals_alt. apply Forall_forall. intros y Hy.
  apply In_GENLIST_iff in Hy as (i & _ & ->). apply crok_simple.
Qed.

Lemma exps_of_MAP2_Assign : forall (xs : list N) (ys : list (crepLang.exp a)),
  Forall crok ys -> Forall (fun x => Forall crok (crepProps.exps_of x)) (MAP2 crepLang.Assign xs ys).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [MAP2]; try constructor.
  - inversion H; subst. constructor; [assumption|constructor].
  - inversion H; subst. apply IH; assumption.
Qed.

Lemma Forall_exps_of_nested_seq (ps : list (crepLang.prog a)) :
  Forall (fun x => Forall crok (crepProps.exps_of x)) ps ->
  Forall crok (crepProps.exps_of (crepLang.nested_seq ps)).
Proof. intros H. rewrite exps_of_nested_seq. apply Forall_concat, Forall_map, H. Qed.

Lemma Forall_exp_hdl {K S} `{EqDecision K} (fm : fmap K (S * list N)) v :
  Forall crok (crepProps.exps_of (pan_to_crep.exp_hdl (a := a) fm v)).
Proof.
  unfold pan_to_crep.exp_hdl. destruct (FLOOKUP fm v) as [[vshp ns]|]; [|constructor].
  apply Forall_exps_of_nested_seq, exps_of_MAP2_Assign, Forall_crok_load_globals.
Qed.

Lemma Forall_FLAT_compile_exps (ctxt : pan_to_crep.context a) es :
  Forall pok es -> Forall crok (FLAT (MAP FST (MAP (pan_to_crep.compile_exp ctxt) es))).
Proof.
  intros H. apply Forall_concat, Forall_map, Forall_map. eapply Forall_impl; [|exact H].
  intros e He. apply compile_exp_crok, He.
Qed.

Lemma crok_head (ctxt : pan_to_crep.context a) e x xs sh :
  pok e -> pan_to_crep.compile_exp ctxt e = (x :: xs, sh) -> crok x /\ Forall crok xs.
Proof.
  intros H E. pose proof (compile_exp_crok ctxt e H) as Hf. rewrite E in Hf. inversion Hf; split; assumption.
Qed.

Ltac pok_split H :=
  repeat match type of H with
         | Forall _ (_ :: _) => apply Forall_cons_iff in H as [?Hp H]
         | Forall _ (_ ++ _) => apply Forall_app in H as [?Hp H]
         end.

Lemma compile_crok : forall (p : panLang.prog a) (ctxt : pan_to_crep.context a),
  Forall pok (exps_of p) -> Forall crok (crepProps.exps_of (pan_to_crep.compile ctxt p)).
Proof.
  intros p. induction p using pan_globalsProof.prog_nested_ind; intros ctxt Hq;
    cbn [pan_to_crep.compile]; cbn [exps_of] in Hq; try (cbn; constructor; fail).
  - (* Dec *)
    apply Forall_cons_iff in Hq as [He Hp].
    pose proof (compile_exp_crok ctxt e He) as Hc.
    destruct (pan_to_crep.compile_exp ctxt e) as [es sh] eqn:Ee. cbn [FST fst] in Hc.
    destruct (decide _) as [Hl|]; [|constructor].
    rewrite exps_of_nested_decs by (rewrite LENGTH_GENLIST_k; exact Hl).
    apply Forall_app. split; [exact Hc|apply IHp, Hp].
  - (* Assign *)
    apply Forall_cons_iff in Hq as [He _].
    destruct vk; [|constructor].
    pose proof (compile_exp_crok ctxt e He) as Hc.
    destruct (pan_to_crep.compile_exp ctxt e) as [es sh] eqn:Ee. cbn [FST fst] in Hc.
    destruct (FLOOKUP _ v) as [[vshp ns]|]; [|constructor].
    destruct (decide _) as [Hl|]; [|constructor].
    destruct (pan_common.distinct_lists _ _).
    + apply Forall_exps_of_nested_seq, exps_of_MAP2_Assign, Hc.
    + rewrite exps_of_nested_decs by (rewrite LENGTH_GENLIST_k; exact Hl).
      apply Forall_app. split; [exact Hc|].
      apply Forall_exps_of_nested_seq, exps_of_MAP2_Assign, Forall_crok_Var.
  - (* Primitive *)
    destruct (FLOOKUP _ v) as [[vshp ns]|]; [|constructor].
    rewrite exps_of_nested_decs by (rewrite LENGTH_GENLIST_k; reflexivity).
    rewrite app_nil_r. apply Forall_FLAT_compile_exps, Hq.
  - (* Store *)
    pok_split Hq.
    destruct (pan_to_crep.compile_exp ctxt e1) as [[|x xs] sh'] eqn:E1; [constructor|].
    destruct (crok_head ctxt e1 x xs sh' Hp E1) as [Hx _].
    pose proof (compile_exp_crok ctxt e2 Hp0) as Hc.
    destruct (pan_to_crep.compile_exp ctxt e2) as [es sh] eqn:E2. cbn [FST fst] in Hc.
    destruct (decide _) as [Hl|]; [|constructor].
    rewrite exps_of_nested_decs
      by (rewrite !LENGTH_cons_k, LENGTH_GENLIST_k, Hl; reflexivity).
    apply Forall_app. split; [constructor; assumption|].
    apply Forall_exps_of_nested_seq, stores_crok. split; [intros _; apply crok_simple|apply Forall_crok_Var].
  - (* Store32 *)
    pok_split Hq.
    destruct (pan_to_crep.compile_exp ctxt e1) as [[|x xs] sh1] eqn:E1; [constructor|].
    destruct (pan_to_crep.compile_exp ctxt e2) as [[|y ys] sh2] eqn:E2; [constructor|].
    destruct (crok_head ctxt e1 x xs sh1 Hp E1) as [Hx _].
    destruct (crok_head ctxt e2 y ys sh2 Hp0 E2) as [Hy _].
    repeat constructor; assumption.
  - (* StoreByte *)
    pok_split Hq.
    destruct (pan_to_crep.compile_exp ctxt e1) as [[|x xs] sh1] eqn:E1; [constructor|].
    destruct (pan_to_crep.compile_exp ctxt e2) as [[|y ys] sh2] eqn:E2; [constructor|].
    destruct (crok_head ctxt e1 x xs sh1 Hp E1) as [Hx _].
    destruct (crok_head ctxt e2 y ys sh2 Hp0 E2) as [Hy _].
    repeat constructor; assumption.
  - (* Seq *)
    apply Forall_app in Hq as [H1 H2]. cbn [crepProps.exps_of]. apply Forall_app.
    split; [apply IHp1, H1|apply IHp2, H2].
  - (* If *)
    apply Forall_cons_iff in Hq as [He Hq]. apply Forall_app in Hq as [H1 H2].
    destruct (pan_to_crep.compile_exp ctxt e) as [[|x xs] sh] eqn:E; [constructor|].
    destruct (crok_head ctxt e x xs sh He E) as [Hx _].
    cbn [crepProps.exps_of]. constructor; [exact Hx|]. apply Forall_app.
    split; [apply IHp1, H1|apply IHp2, H2].
  - (* While *)
    apply Forall_cons_iff in Hq as [He Hq].
    destruct (pan_to_crep.compile_exp ctxt e) as [[|x xs] sh] eqn:E; [constructor|].
    destruct (crok_head ctxt e x xs sh He E) as [Hx _].
    cbn [crepProps.exps_of]. constructor; [exact Hx|]. apply IHp, Hq.
  - (* Call *)
    destruct ct as [[rt hdl]|]; [|exact (Forall_FLAT_compile_exps ctxt args Hq)].
    assert (Hargs : Forall pok args)
      by (destruct hdl as [[eid [evar hp]]|]; [apply Forall_app in Hq; exact (proj1 Hq)|exact Hq]).
    pose proof (Forall_FLAT_compile_exps ctxt args Hargs) as Ha.
    assert (Hdecs : forall rts (q : crepLang.prog a),
               Forall crok (crepProps.exps_of q) ->
               Forall crok (crepProps.exps_of
                 (crepLang.nested_decs rts (REPLICATE (LENGTH rts) (crepLang.Const (n2w 0))) q))).
    { intros rts q Hq'. rewrite exps_of_nested_decs by (rewrite LENGTH_REPLICATE; reflexivity).
      apply Forall_app. split; [apply Forall_REPLICATE, crok_simple|exact Hq']. }
    assert (Hcall : forall rts (o : option (word a * crepLang.prog a)),
               match o with SOME (_, q) => Forall crok (crepProps.exps_of q) | NONE => True end ->
               Forall crok (crepProps.exps_of (crepLang.Call (SOME (rts, o)) f
                 (FLAT (MAP FST (MAP (pan_to_crep.compile_exp ctxt) args)))))).
    { intros rts [[w q]|] Hq'; cbn [crepProps.exps_of]; [apply Forall_app; split; assumption|exact Ha]. }
    destruct hdl as [[eid [evar hp]]|].
    + assert (Hhp : Forall crok (crepProps.exps_of (pan_to_crep.compile ctxt hp)))
        by (apply H; apply Forall_app in Hq; exact (proj2 Hq)).
      assert (Hhdl : Forall crok (crepProps.exps_of
                 (crepLang.Seq (pan_to_crep.exp_hdl (pan_to_crep.vars ctxt) evar)
                               (pan_to_crep.compile ctxt hp))))
        by (cbn [crepProps.exps_of]; apply Forall_app; split; [apply Forall_exp_hdl|exact Hhp]).
      destruct rt as [[rk rv]|].
      * destruct (pan_to_crep.wrap_rt _) as [[sh ns]|];
          destruct (FLOOKUP (pan_to_crep.eids ctxt) eid) as [neid|];
          first [apply (Hcall _ (SOME (neid, _))), Hhdl | apply (Hcall _ NONE), Logic.I | exact Ha].
      * destruct (FLOOKUP (pan_to_crep.eids ctxt) eid) as [neid|]; apply Hdecs;
          [apply (Hcall _ (SOME (neid, _))), Hhdl|apply (Hcall _ NONE), Logic.I].
    + destruct rt as [[rk rv]|].
      * destruct (pan_to_crep.wrap_rt _) as [[sh ns]|]; [apply (Hcall _ NONE), Logic.I|exact Ha].
      * apply Hdecs, (Hcall _ NONE), Logic.I.
  - (* DecCall *)
    apply Forall_app in Hq as [Ha Hp].
    rewrite exps_of_nested_decs by (rewrite LENGTH_REPLICATE; reflexivity).
    apply Forall_app. split; [apply Forall_REPLICATE, crok_simple|].
    cbn [crepProps.exps_of]. apply Forall_app.
    split; [apply Forall_FLAT_compile_exps, Ha|apply IHp, Hp].
  - (* ExtCall *)
    pok_split Hq.
    destruct (pan_to_crep.compile_exp ctxt e1) as [c1 s1] eqn:E1.
    destruct (pan_to_crep.compile_exp ctxt e2) as [c2 s2] eqn:E2.
    destruct (pan_to_crep.compile_exp ctxt e3) as [c3 s3] eqn:E3.
    destruct (pan_to_crep.compile_exp ctxt e4) as [c4 s4] eqn:E4.
    destruct s1, c1 as [|x1 xs1]; try constructor; destruct s2, c2 as [|x2 xs2]; try constructor;
      destruct s3, c3 as [|x3 xs3]; try constructor; destruct s4, c4 as [|x4 xs4]; try constructor.
    all: try (exact (proj1 (crok_head ctxt _ _ _ _ Hp E1))).
    all: cbn [crepProps.exps_of].
    all: repeat constructor.
    all: first [exact (proj1 (crok_head ctxt _ _ _ _ Hp0 E2)) | exact (proj1 (crok_head ctxt _ _ _ _ Hp1 E3))
               | exact (proj1 (crok_head ctxt _ _ _ _ Hp2 E4))].
  - (* Raise *)
    apply Forall_cons_iff in Hq as [He _].
    destruct (FLOOKUP _ eid) as [n|]; [|constructor].
    pose proof (compile_exp_crok ctxt e He) as Hc.
    destruct (pan_to_crep.compile_exp ctxt e) as [es sh] eqn:Ee. cbn [FST fst] in Hc.
    destruct (decide _) as [Hl|]; [|constructor].
    cbn [crepProps.exps_of]. rewrite app_nil_r.
    rewrite exps_of_nested_decs by (rewrite LENGTH_GENLIST_k; exact Hl).
    apply Forall_app. split; [exact Hc|].
    apply Forall_exps_of_nested_seq, EVERY_EVERY_crok, every_inst_ok_less_store_globals, EVERY_crok.
    apply Forall_crok_Var.
  - (* Return *)
    apply Forall_cons_iff in Hq as [He _].
    pose proof (compile_exp_crok ctxt e He) as Hc.
    destruct (pan_to_crep.compile_exp ctxt e) as [es sh] eqn:Ee. cbn [FST fst] in Hc.
    destruct (decide _); cbn [crepProps.exps_of]; [constructor|exact Hc].
  - (* ShMemLoad *)
    apply Forall_cons_iff in Hq as [He _].
    destruct vk; [|constructor].
    destruct (pan_to_crep.compile_exp ctxt e) as [[|x xs] sh] eqn:E; [constructor|].
    destruct (crok_head ctxt e x xs sh He E) as [Hx _].
    destruct (FLOOKUP _ v) as [[? [|r' ?]]|]; cbn; repeat constructor; assumption.
  - (* ShMemStore *)
    pok_split Hq.
    destruct (pan_to_crep.compile_exp ctxt e1) as [[|x xs] sh1] eqn:E1; [constructor|].
    destruct (pan_to_crep.compile_exp ctxt e2) as [[|y ys] sh2] eqn:E2; [constructor|].
    destruct (crok_head ctxt e1 x xs sh1 Hp E1) as [Hx _].
    destruct (crok_head ctxt e2 y ys sh2 Hp0 E2) as [Hy _].
    cbn. repeat constructor; assumption.
Qed.

End InstOkPan2.

Section InstOkPan3.
Context {a : N}.

Lemma EVERY_pok (es : list (panLang.exp a)) :
  is_true (EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) es) <->
  Forall pok es.
Proof. unfold is_true. rewrite EVERY_Forall. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_compile" *)
Theorem every_inst_ok_less_pan_to_crep_compile : forall ctxt (body : panLang.prog a),
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of body) ->
  EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
    (crepProps.exps_of (pan_to_crep.compile ctxt body)).
Proof. intros ctxt body H. apply EVERY_crok, compile_crok, EVERY_pok, H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "good_panops_def" *)
Definition good_panops (d : decl a) : bool :=
  match d with
  | Function fi => EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝))
                     (exps_of (body fi))
  | Decl sh v e => every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) e
  | _ => true
  end.

Lemma good_panops_functions (decls : list (decl a)) :
  is_true (EVERY good_panops decls) ->
  Forall (fun x => Forall pok (exps_of (FST (SND (SND x))))) (functions decls).
Proof.
  induction decls as [|[fi|sh v e|eid sh|nm flds] ds IH]; cbn [EVERY functions]; unfold is_true;
    intros H; try constructor; apply andb_prop in H as [H1 H2]; try exact (IH H2).
  - apply EVERY_pok, H1.
Qed.

Lemma crok_prog_EVERY (code : list (mlstring * (list N * crepLang.prog a))) :
  Forall (fun x => Forall crok (crepProps.exps_of (SND (SND x)))) code ->
  is_true (EVERY (fun '(name, (params, body)) =>
     EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
       (crepProps.exps_of body)) code).
Proof.
  intros H. unfold is_true. rewrite EVERY_Forall. eapply Forall_impl; [|exact H].
  intros [n [ps b]] Hb. apply EVERY_crok, Hb.
Qed.

Lemma EVERY_crok_prog (code : list (mlstring * (list N * crepLang.prog a))) :
  is_true (EVERY (fun '(name, (params, body)) =>
     EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
       (crepProps.exps_of body)) code) ->
  Forall (fun x => Forall crok (crepProps.exps_of (SND (SND x)))) code.
Proof.
  intros H. unfold is_true in H. rewrite EVERY_Forall in H. eapply Forall_impl; [|exact H].
  intros [n [ps b]] Hb. apply EVERY_crok, Hb.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_compile_to_crep" *)
Theorem every_inst_ok_less_pan_to_crep_compile_to_crep : forall pan_code : list (decl a),
  EVERY good_panops pan_code ->
  EVERY (fun '(name, (params, body)) =>
           EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
             (crepProps.exps_of body))
    (pan_to_crep.compile_to_crep pan_code).
Proof.
  intros pan_code H. apply crok_prog_EVERY. unfold pan_to_crep.compile_to_crep. cbv zeta.
  apply Forall_map. eapply Forall_impl; [|exact (good_panops_functions pan_code H)].
  intros [n [ps [b r]]] Hb. cbn [FST SND fst snd] in *. unfold pan_to_crep.comp_func. cbv zeta.
  apply compile_crok, Hb.
Qed.

Lemma ALOOKUP_FILTER_key {K V} {EK : EqDecision K} (P : K -> bool) (l : list (K * V)) k v :
  ALOOKUP (FILTER (fun '(x, y) => P x) l) k = SOME v -> ALOOKUP l k = SOME v.
Proof.
  induction l as [|[x y] l IH]; cbn [List.filter ALOOKUP]; [discriminate|].
  destruct (P x) eqn:Ep; cbn [ALOOKUP].
  - destruct (decide (x = k)); [tauto|exact IH].
  - intros H. destruct (decide (x = k)) as [->|]; [|exact (IH H)].
    exfalso. clear IH. induction l as [|[x' y'] l IH']; cbn [List.filter ALOOKUP] in H; [discriminate|].
    destruct (P x') eqn:Ep'; cbn [ALOOKUP] in H; [|exact (IH' H)].
    destruct (decide (x' = k)) as [->|]; [congruence|exact (IH' H)].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_w_inline" *)
Theorem every_inst_w_inline : forall pan_code : list (decl a),
  EVERY (fun '(name, (params, body)) =>
           EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
             (crepProps.exps_of body))
    (pan_to_crep.compile_to_crep pan_code) ->
  EVERY (fun '(name, (params, body)) =>
           EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
             (crepProps.exps_of body))
    (pan_to_crep.compile_prog pan_code).
Proof.
  intros pan_code H. apply EVERY_crok_prog in H. apply crok_prog_EVERY.
  unfold pan_to_crep.compile_prog, crep_inline.compile_inl_top. cbv zeta.
  set (crep_code := pan_to_crep.compile_to_crep pan_code) in *.
  match goal with |- context [alist_to_fmap (FILTER ?f crep_code)] => set (flt := f) end.
  pose proof (crep_inlineProof.every_inst_crep_inline crep_code (alist_to_fmap (FILTER flt crep_code))) as Hi.
  apply Forall_forall. intros [n [ps b]] Hin. cbn [SND snd].
  refine (proj2 (Forall_forall _ _) _). intros e He.
  refine (Hi _ (n, (ps, b)) _ e _).
  - split.
    + intros [n' [ps' b']] Hm'. apply MEM_In in Hm'. intros e' He'. apply MEM_In in He'.
      rewrite Forall_forall in H. specialize (H _ Hm'). cbn [SND snd] in H.
      rewrite Forall_forall in H. exact (H e' He').
    + intros k v Hk. rewrite FLOOKUP_alist_to_fmap in Hk |- *. unfold flt in Hk.
      exact (ALOOKUP_FILTER_key _ _ _ _ Hk).
  - apply (proj2 (MEM_In _ _)). exact Hin.
  - apply (proj2 (MEM_In _ _)). exact He.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_to_crep_compile_prog" *)
Theorem every_inst_ok_less_pan_to_crep_compile_prog : forall pan_code : list (decl a),
  EVERY good_panops pan_code ->
  EVERY (fun '(name, (params, body)) =>
           EVERY (crepProps.every_exp (fun x => ⌜forall op es, x = crepLang.Crepop op es -> LENGTH es = 2⌝))
             (crepProps.exps_of body))
    (pan_to_crep.compile_prog pan_code).
Proof.
  intros pan_code H. apply every_inst_w_inline, every_inst_ok_less_pan_to_crep_compile_to_crep, H.
Qed.

(** *** [pan_simp] *)

Lemma pok_Var vk v : pok (Var (a := a) vk v).
Proof. unfold pok, is_true. cbn [every_exp]. apply bool_decide_spec. intros ? ? C; discriminate C. Qed.

Lemma exps_of_SmartSeq (p q : panLang.prog a) :
  exps_of (pan_simp.SmartSeq p q) = exps_of p ++ exps_of q.
Proof. unfold pan_simp.SmartSeq. destruct p; cbn; reflexivity. Qed.

Lemma exps_of_seq_assoc : forall (q p : panLang.prog a),
  exps_of (pan_simp.seq_assoc p q) = exps_of p ++ exps_of q.
Proof.
  intros q. induction q using pan_globalsProof.prog_nested_ind; intros p0;
    cbn [pan_simp.seq_assoc]; rewrite ?exps_of_SmartSeq; cbn [exps_of app];
    rewrite ?app_nil_r; try reflexivity.
  - rewrite IHq. reflexivity.
  - rewrite IHq2, IHq1, app_assoc. reflexivity.
  - rewrite IHq1, IHq2. reflexivity.
  - rewrite IHq. reflexivity.
  - destruct ct as [[rv [[eid [ev ep]]|]]|]; rewrite ?exps_of_SmartSeq; cbn [exps_of app]; try reflexivity.
    rewrite H. reflexivity.
  - rewrite IHq. reflexivity.
Qed.

Lemma Forall_exps_of_seq_call_ret (q : panLang.prog a) :
  Forall pok (exps_of (pan_simp.seq_call_ret q)) <-> Forall pok (exps_of q).
Proof.
  unfold pan_simp.seq_call_ret.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; try reflexivity.
  cbn [exps_of]. rewrite Forall_app, Forall_cons_iff. split; [intros H; split; [exact H|split; [apply pok_Var|constructor]]|tauto].
Qed.

Lemma Forall_exps_of_ret_to_tail : forall p : panLang.prog a,
  Forall pok (exps_of (pan_simp.ret_to_tail p)) <-> Forall pok (exps_of p).
Proof.
  intros p. induction p using pan_globalsProof.prog_nested_ind; cbn [pan_simp.ret_to_tail];
    try reflexivity.
  - cbn [exps_of]. rewrite !Forall_cons_iff, IHp. reflexivity.
  - rewrite Forall_exps_of_seq_call_ret. cbn [exps_of]. rewrite !Forall_app, IHp1, IHp2. reflexivity.
  - cbn [exps_of]. rewrite !Forall_cons_iff, !Forall_app, IHp1, IHp2. reflexivity.
  - cbn [exps_of]. rewrite !Forall_cons_iff, IHp. reflexivity.
  - destruct ct as [[rv [[eid [ev ep]]|]]|]; cbn [exps_of]; try reflexivity.
    rewrite !Forall_app, H. reflexivity.
  - cbn [exps_of]. rewrite !Forall_app, IHp. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_ret_to_tail" *)
Theorem every_inst_ok_less_ret_to_tail : forall p : panLang.prog a,
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of (pan_simp.ret_to_tail p)) <->
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of p).
Proof. intros p. rewrite !EVERY_pok. apply Forall_exps_of_ret_to_tail. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_seq_assoc" *)
Theorem every_inst_ok_less_seq_assoc : forall p q : panLang.prog a,
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of (pan_simp.seq_assoc p q)) <->
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of p ++ exps_of q).
Proof. intros p q. rewrite exps_of_seq_assoc. reflexivity. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_simp_compile" *)
Theorem every_inst_ok_less_pan_simp_compile : forall body : panLang.prog a,
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of body) ->
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of (pan_simp.compile body)).
Proof.
  intros body H. unfold pan_simp.compile. cbv zeta. rewrite EVERY_pok in H |- *.
  apply Forall_exps_of_ret_to_tail. rewrite exps_of_seq_assoc. exact H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_simp_compile_prog" *)
Theorem every_inst_ok_less_pan_simp_compile_prog : forall pan_code : list (decl a),
  EVERY good_panops pan_code -> EVERY good_panops (pan_simp.compile_prog pan_code).
Proof.
  unfold pan_simp.compile_prog. intros pan_code.
  induction pan_code as [|[fi|sh v e|eid sh|nm flds] ds IH]; cbn [List.map EVERY]; unfold is_true;
    intros H; try reflexivity; apply andb_prop in H as [H1 H2]; rewrite (IH H2), andb_true_r;
    try exact H1.
  cbn [good_panops body]. apply every_inst_ok_less_pan_simp_compile, H1.
Qed.

End InstOkPan3.

(** ** Instruction side conditions: [pan_structs] and [pan_globals] *)

Section InstOkPan4.
Context {a : N}.
Implicit Types (e : panLang.exp a) (es : list (panLang.exp a)).

Lemma Pp_other (x : panLang.exp a) :
  (forall op es, x <> Panop op es) ->
  ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝ = true.
Proof. intros H. apply bool_decide_spec. intros op es E. exfalso. exact (H op es E). Qed.

Ltac ppk := unfold pok, is_true; cbn [every_exp]; cbv beta;
  rewrite ?Pp_other by (intros ? ? ?Hc; discriminate Hc); cbn [andb].

Lemma pok_simple :
  (forall w, pok (Const (a := a) w)) /\ (forall vk v, pok (Var (a := a) vk v)) /\
  pok (a := a) BaseAddr /\ pok (a := a) TopAddr /\ pok (a := a) BytesInWord.
Proof. repeat split; intros; ppk; reflexivity. Qed.

Lemma pok_list (es : list (panLang.exp a)) :
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) es = true <-> Forall pok es.
Proof. rewrite EVERY_Forall. reflexivity. Qed.

Lemma pok_rstruct es : pok (panLang.RStruct es) <-> Forall (pok (a := a)) es.
Proof. ppk. apply pok_list. Qed.
Lemma pok_rfield i e : pok (RField i e) <-> pok e.
Proof. ppk. reflexivity. Qed.
Lemma pok_load sh e : pok (Load sh e) <-> pok e.
Proof. ppk. reflexivity. Qed.
Lemma pok_load32 e : pok (Load32 e) <-> pok e.
Proof. ppk. reflexivity. Qed.
Lemma pok_loadbyte e : pok (LoadByte e) <-> pok e.
Proof. ppk. reflexivity. Qed.
Lemma pok_op bop es : pok (Op bop es) <-> Forall pok es.
Proof. ppk. apply pok_list. Qed.
Lemma pok_panop op es : pok (Panop op es) <-> LENGTH es = 2 /\ Forall pok es.
Proof.
  unfold pok, is_true. cbn [every_exp]. cbv beta. rewrite andb_true_iff, pok_list, bool_decide_spec.
  split; [intros [H1 H2]; split; [exact (H1 _ _ eq_refl)|exact H2]|].
  intros [H1 H2]; split; [intros op' es' E; injection E as _ <-; exact H1|exact H2].
Qed.
Lemma pok_cmp c e1 e2 : pok (Cmp c e1 e2) <-> pok e1 /\ pok e2.
Proof. ppk. rewrite andb_true_iff. reflexivity. Qed.
Lemma pok_shift s e1 e2 : pok (Shift s e1 e2) <-> pok e1 /\ pok e2.
Proof. ppk. rewrite andb_true_iff. reflexivity. Qed.

Lemma pok_nstruct_inv nm (fes : list (fldname * panLang.exp a)) :
  pok (panLang.NStruct nm fes) -> Forall (fun p => pok (SND p)) fes.
Proof.
  unfold pok, is_true. cbn [every_exp]. intros H. apply andb_prop in H as [_ H].
  rewrite EVERY_Forall in H. exact H.
Qed.

Lemma Forall_MAP_pok (f : panLang.exp a -> panLang.exp a) (es : list (panLang.exp a)) :
  Forall (fun e => pok e -> pok (f e)) es -> Forall pok es -> Forall pok (MAP f es).
Proof.
  intros H1 H2. apply Forall_map. induction H1 as [|e es He H1 IH]; [constructor|].
  inversion H2; subst. constructor; [apply He; assumption|apply IH; assumption].
Qed.

Lemma structs_compile_exps_eq ctxt (es : list (panLang.exp a)) :
  pan_structs.compile_exps ctxt es = MAP (pan_structs.compile_exp ctxt) es.
Proof. induction es as [|e es IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma structs_compile_fields_eq ctxt (flds : list (fldname * panLang.exp a)) :
  MAP SND (pan_structs.compile_fields ctxt flds) = MAP (pan_structs.compile_exp ctxt) (MAP SND flds).
Proof. induction flds as [|[f e] flds IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma structs_exp_pok ctxt : forall e : panLang.exp a, pok e -> pok (pan_structs.compile_exp ctxt e).
Proof.
  intros e. induction e as [w|vk v0|es IH|i e IH|nm es IH|f e IH|sh e IH|e IH|e IH|op es IH|op es IH
                           |cm e1 e2 IH1 IH2|s e1 e2 IH1 IH2| | |]
    using exp_nested_ind; intros H; cbn [pan_structs.compile_exp];
    rewrite ?pan_structs.compile_exps_nested, ?pan_structs.compile_fields_nested, ?structs_compile_exps_eq;
    try exact H.
  - rewrite pok_rstruct in H. apply pok_rstruct, Forall_MAP_pok; assumption.
  - rewrite pok_rfield in H. apply pok_rfield, IH, H.
  - apply pok_nstruct_inv in H. apply pok_rstruct. cbv zeta.
    destruct (ALOOKUP _ nm) as [flds|]; [|constructor].
    apply Forall_concat, Forall_map, Forall_forall. intros [nm' sh] _.
    destruct (ALOOKUP (pan_structs.compile_fields ctxt es) nm') as [e|] eqn:Ea; [|constructor].
    constructor; [|constructor]. apply ALOOKUP_In in Ea.
    assert (Hin : In e (MAP SND (pan_structs.compile_fields ctxt es)))
      by (apply in_map_iff; exists (nm', e); split; [reflexivity|exact Ea]).
    rewrite structs_compile_fields_eq in Hin. apply in_map_iff in Hin as (e0 & <- & Hin).
    apply in_map_iff in Hin as ([f0 e1] & Hf & Hin). cbn [SND snd] in Hf. subst e1.
    rewrite Forall_forall in IH, H. apply (IH (f0, e0) Hin), (H (f0, e0) Hin).
  - cbv zeta. unfold pok, is_true in H |- *. cbn [every_exp] in H |- *. apply andb_prop in H as [_ H].
    rewrite Pp_other by (intros ? ? C; discriminate C). apply IH, H.
  - rewrite pok_load in H. apply pok_load, IH, H.
  - rewrite pok_load32 in H. apply pok_load32, IH, H.
  - rewrite pok_loadbyte in H. apply pok_loadbyte, IH, H.
  - rewrite pok_op in H. apply pok_op, Forall_MAP_pok; assumption.
  - rewrite pok_panop in H; destruct H as [Hl H]. apply pok_panop. split; [rewrite !LENGTH_length, length_map; rewrite LENGTH_length in Hl; exact Hl|].
    apply Forall_MAP_pok; assumption.
  - rewrite pok_cmp in H; destruct H as [H1 H2]. apply pok_cmp. split; [apply IH1, H1|apply IH2, H2].
  - rewrite pok_shift in H; destruct H as [H1 H2]. apply pok_shift. split; [apply IH1, H1|apply IH2, H2].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile_exp" *)
Theorem every_inst_ok_less_pan_structs_compile_exp :
  (forall ctxt (e : panLang.exp a),
     every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) e ->
     every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) (pan_structs.compile_exp ctxt e)) /\
  (forall ctxt (es : list (panLang.exp a)),
     EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) es ->
     EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (pan_structs.compile_exps ctxt es) /\
     LENGTH (pan_structs.compile_exps ctxt es) = LENGTH es) /\
  (forall ctxt (flds : list (fldname * panLang.exp a)),
     EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (MAP SND flds) ->
     EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝))
       (MAP SND (pan_structs.compile_fields ctxt flds))).
Proof.
  split; [exact (structs_exp_pok)|split].
  - intros ctxt es H. rewrite structs_compile_exps_eq. split.
    + apply EVERY_pok. apply EVERY_pok in H. apply Forall_MAP_pok; [|exact H].
      apply Forall_forall. intros e _. apply structs_exp_pok.
    + rewrite !LENGTH_length, length_map. reflexivity.
  - intros ctxt flds H. rewrite structs_compile_fields_eq. apply EVERY_pok. apply EVERY_pok in H.
    apply Forall_MAP_pok; [|exact H]. apply Forall_forall. intros e _. apply structs_exp_pok.
Qed.

Lemma structs_compile_pok : forall (p : panLang.prog a) ctxt,
  Forall pok (exps_of p) -> Forall pok (exps_of (pan_structs.compile ctxt p)).
Proof.
  intros p. induction p using pan_globalsProof.prog_nested_ind; intros ctxt Hq;
    cbn [pan_structs.compile]; cbn [exps_of] in Hq |- *; rewrite ?structs_compile_exps_eq;
    repeat match goal with
           | Hf : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in Hf as [?Hp Hf]
           | Hf : Forall _ (_ ++ _) |- _ => apply Forall_app in Hf as [?Hp Hf]
           end;
    repeat match goal with
           | |- Forall _ (_ :: _) => constructor
           | |- Forall _ (_ ++ _) => apply Forall_app; split
           | |- Forall pok (MAP _ _) => apply Forall_MAP_pok; [apply Forall_forall; intros ? _; apply structs_exp_pok|]
           | |- pok (pan_structs.compile_exp _ _) => apply structs_exp_pok
           end;
    try assumption; try constructor; auto.
  destruct ct as [[tl [[eid [ev ep]]|]]|]; cbn [exps_of] in Hq |- *; rewrite ?structs_compile_exps_eq.
  - apply Forall_app in Hq as [H1 H2]. apply Forall_app. split; [|apply H, H2].
    apply Forall_MAP_pok; [apply Forall_forall; intros ? _; apply structs_exp_pok|exact H1].
  - apply Forall_MAP_pok; [apply Forall_forall; intros ? _; apply structs_exp_pok|exact Hq].
  - apply Forall_MAP_pok; [apply Forall_forall; intros ? _; apply structs_exp_pok|exact Hq].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile" *)
Theorem every_inst_ok_less_pan_structs_compile : forall ctxt (p : panLang.prog a),
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of p) ->
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝))
    (exps_of (pan_structs.compile ctxt p)).
Proof. intros ctxt p H. apply EVERY_pok, structs_compile_pok, EVERY_pok, H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile_decs" *)
Theorem every_inst_ok_less_pan_structs_compile_decs : forall ctxt (pan_code : list (decl a)),
  EVERY good_panops pan_code -> EVERY good_panops (FST (pan_structs.compile_decs ctxt pan_code)).
Proof.
  intros ctxt pan_code; revert ctxt.
  induction pan_code as [|[fi|sh v e|eid sh|nm flds] ds IH]; intros ctxt H; cbn [pan_structs.compile_decs];
    cbn [EVERY] in H; unfold is_true in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]).
  - specialize (IH ctxt H2). destruct (pan_structs.compile_decs ctxt ds) as [ds' c'].
    cbn [FST fst EVERY good_panops body] in *. rewrite IH, andb_true_r.
    apply every_inst_ok_less_pan_structs_compile, H1.
  - match goal with |- context [pan_structs.compile_decs ?c ds] =>
      specialize (IH c H2); destruct (pan_structs.compile_decs c ds) as [ds' c'] end.
    cbn [FST fst EVERY good_panops] in *. rewrite IH, andb_true_r.
    apply (proj1 every_inst_ok_less_pan_structs_compile_exp), H1.
  - specialize (IH ctxt H2). destruct (pan_structs.compile_decs ctxt ds) as [ds' c'].
    cbn [FST fst EVERY good_panops] in *. exact IH.
  - exact (IH ctxt H2).
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_structs_compile_top" *)
Theorem every_inst_ok_less_pan_structs_compile_top : forall (pan_code : list (decl a)),
  EVERY good_panops pan_code -> EVERY good_panops (pan_structs.compile_top pan_code).
Proof.
  intros pan_code H. unfold pan_structs.compile_top. cbv zeta.
  apply every_inst_ok_less_pan_structs_compile_decs, H.
Qed.

End InstOkPan4.

Section InstOkPan5.
Context {a : N}.
Implicit Types (e : panLang.exp a) (es : list (panLang.exp a)).

Lemma pok_topaddr_sub (w : word a) : pok (Op Sub [TopAddr; Const w]).
Proof. apply pok_op. constructor; [apply pok_simple|constructor; [apply pok_simple|constructor]]. Qed.

Lemma globals_exp_pok (ctxt : pan_globals.context a) : forall e, pok e -> pok (pan_globals.compile_exp ctxt e).
Proof.
  intros e. induction e as [w|vk v0|es IH|i e IH|nm es IH|f e IH|sh e IH|e IH|e IH|op es IH|op es IH
                           |cm e1 e2 IH1 IH2|s e1 e2 IH1 IH2| | |]
    using exp_nested_ind; intros H; cbn [pan_globals.compile_exp]; try exact H;
    try (apply pok_simple; fail).
  - destruct vk; [exact H|]. destruct (FLOOKUP _ v0) as [[sh addr]|]; [|apply pok_simple].
    apply pok_load, pok_topaddr_sub.
  - rewrite pok_rstruct in H. apply pok_rstruct, Forall_MAP_pok; assumption.
  - rewrite pok_rfield in H. apply pok_rfield, IH, H.
  - rewrite pok_load in H. apply pok_load, IH, H.
  - rewrite pok_load32 in H. apply pok_load32, IH, H.
  - rewrite pok_loadbyte in H. apply pok_loadbyte, IH, H.
  - rewrite pok_op in H. apply pok_op, Forall_MAP_pok; assumption.
  - rewrite pok_panop in H; destruct H as [Hl H]. apply pok_panop.
    split; [rewrite !LENGTH_length, length_map; rewrite LENGTH_length in Hl; exact Hl|].
    apply Forall_MAP_pok; assumption.
  - rewrite pok_cmp in H; destruct H as [H1 H2]. apply pok_cmp. split; [apply IH1, H1|apply IH2, H2].
  - rewrite pok_shift in H; destruct H as [H1 H2]. apply pok_shift. split; [apply IH1, H1|apply IH2, H2].
  - apply pok_topaddr_sub.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile_exp" *)
Theorem every_inst_ok_less_pan_globals_compile_exp : forall ctxt (e : panLang.exp a),
  every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) e ->
  every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) (pan_globals.compile_exp ctxt e).
Proof. exact globals_exp_pok. Qed.

Lemma shape_val_pok : forall sh, pok (shape_val (a := a) sh).
Proof.
  intros sh. induction sh as [|shs IH|nm] using shape_nested_ind; [apply pok_simple| |apply pok_simple].
  rewrite shape_val_Comb. apply pok_rstruct.
  induction IH as [|sh shs Hs IH' IHl]; cbn [shape_vals]; constructor; assumption.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_shape_val" *)
Theorem every_inst_ok_less_shape_val :
  (forall e : shape, every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝) (shape_val (a := a) e)) /\
  (forall es : list shape, EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (shape_vals (a := a) es)).
Proof.
  split; [exact shape_val_pok|]. intros es. apply EVERY_pok.
  induction es as [|sh shs IH]; cbn [shape_vals]; constructor; [apply shape_val_pok|exact IH].
Qed.

Lemma globals_compile_pok (ctxt : pan_globals.context a) : forall p : panLang.prog a,
  Forall pok (exps_of p) -> Forall pok (exps_of (pan_globals.compile ctxt p)).
Proof.
  intros p. induction p using pan_globalsProof.prog_nested_ind; intros Hq;
    cbn [pan_globals.compile]; cbn [exps_of] in Hq;
    repeat match goal with
           | Hf : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in Hf as [?Hp Hf]
           | Hf : Forall _ (_ ++ _) |- _ => apply Forall_app in Hf as [?Hp Hf]
           end.
  all: try (cbn [exps_of];
    repeat match goal with
           | |- Forall _ (_ :: _) => constructor
           | |- Forall _ (_ ++ _) => apply Forall_app; split
           | |- Forall pok (MAP _ _) => apply Forall_MAP_pok; [apply Forall_forall; intros ? _; apply globals_exp_pok|]
           | |- pok (pan_globals.compile_exp _ _) => apply globals_exp_pok
           end; try assumption; try constructor; auto; fail).
  - (* Assign *)
    destruct vk.
    + cbn [exps_of]. constructor; [apply globals_exp_pok; assumption|constructor].
    + destruct (FLOOKUP _ v) as [[sh addr]|]; cbn [exps_of]; [|constructor].
      constructor; [apply pok_topaddr_sub|constructor; [apply globals_exp_pok; assumption|constructor]].
  - (* Call *)
    assert (Ha : Forall pok (MAP (pan_globals.compile_exp ctxt) args)).
    { apply Forall_MAP_pok; [apply Forall_forall; intros ? _; apply globals_exp_pok|].
      destruct ct as [[tl [[eid [ev ep]]|]]|]; try exact Hq. apply Forall_app in Hq. exact (proj1 Hq). }
    assert (Hh : forall eid ev ep, ct = SOME (ARB, SOME (eid, (ev, ep))) \/ True -> True) by (intros; exact Logic.I).
    clear Hh.
    destruct ct as [[tl hdl]|]; cbn zeta; [|exact Ha].
    assert (Hhp : forall eid ev ep, hdl = SOME (eid, (ev, ep)) ->
              Forall pok (exps_of (pan_globals.compile ctxt ep))).
    { intros eid ev ep ->. apply H. cbn [exps_of] in Hq. apply Forall_app in Hq. exact (proj2 Hq). }
    destruct tl as [[[|] vn]|].
    + destruct hdl as [[eid [ev ep]]|]; cbn [exps_of];
        [apply Forall_app; split; [exact Ha|exact (Hhp _ _ _ eq_refl)]|exact Ha].
    + destruct (FLOOKUP _ vn) as [[sh addr]|].
      * destruct hdl as [[eid [ev ep]]|]; cbv zeta; cbn [exps_of app].
        -- constructor; [apply shape_val_pok|]. constructor; [apply pok_simple|].
           apply Forall_app. split; [apply Forall_app; split; [exact Ha|]|].
           ++ apply Forall_app. split; [exact (Hhp _ _ _ eq_refl)|].
              constructor; [apply pok_simple|constructor].
           ++ constructor; [apply pok_simple|]. constructor; [apply pok_topaddr_sub|].
              constructor; [apply pok_simple|constructor].
        -- apply Forall_app. split; [exact Ha|].
           constructor; [apply pok_topaddr_sub|constructor; [apply pok_simple|constructor]].
      * destruct hdl as [[eid [ev ep]]|]; cbn [exps_of];
          [apply Forall_app; split; [exact Ha|exact (Hhp _ _ _ eq_refl)]|exact Ha].
    + destruct hdl as [[eid [ev ep]]|]; cbn [exps_of];
        [apply Forall_app; split; [exact Ha|exact (Hhp _ _ _ eq_refl)]|exact Ha].
  - (* ShMemLoad *)
    destruct vk.
    + cbn [exps_of]. constructor; [apply globals_exp_pok; assumption|constructor].
    + destruct (FLOOKUP _ v) as [[[| |] addr]|]; cbn [exps_of]; try constructor.
      * apply globals_exp_pok; assumption.
      * constructor; [apply pok_simple|]. cbn [app]. constructor; [apply pok_simple|].
        constructor; [apply pok_topaddr_sub|constructor; [apply pok_simple|constructor]].
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile" *)
Theorem every_inst_ok_less_pan_globals_compile : forall ctxt (code : panLang.prog a),
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of code) ->
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝))
    (exps_of (pan_globals.compile ctxt code)).
Proof. intros ctxt code H. apply EVERY_pok, globals_compile_pok, EVERY_pok, H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile_decs" *)
Theorem every_inst_ok_less_pan_globals_compile_decs : forall ctxt (pan_code : list (decl a)),
  EVERY good_panops pan_code -> EVERY good_panops (FST (SND (pan_globals.compile_decs ctxt pan_code))).
Proof.
  intros ctxt pan_code; revert ctxt.
  induction pan_code as [|[fi|sh v e|eid sh|nm flds] ds IH]; intros ctxt H; cbn [pan_globals.compile_decs];
    cbn [EVERY] in H; unfold is_true in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]);
    try (match goal with |- context [pan_globals.compile_decs ?c ds] =>
           specialize (IH c H2); destruct (pan_globals.compile_decs c ds) as [d1 [f1 [e1 c1]]] end;
         cbn [FST SND fst snd EVERY good_panops body] in *).
  - rewrite IH, andb_true_r. apply every_inst_ok_less_pan_globals_compile, H1.
  - exact IH.
  - exact IH.
  - exact IH.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile_decs_init" *)
Theorem every_inst_ok_less_pan_globals_compile_decs_init : forall ctxt (pan_code : list (decl a)),
  EVERY good_panops pan_code ->
  EVERY (EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)))
    (MAP exps_of (FST (pan_globals.compile_decs ctxt pan_code))).
Proof.
  intros ctxt pan_code; revert ctxt.
  induction pan_code as [|[fi|sh v e|eid sh|nm flds] ds IH]; intros ctxt H; cbn [pan_globals.compile_decs];
    cbn [EVERY] in H; unfold is_true in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]);
    try (match goal with |- context [pan_globals.compile_decs ?c ds] =>
           specialize (IH c H2); destruct (pan_globals.compile_decs c ds) as [d1 [f1 [e1 c1]]] end;
         cbn [FST SND fst snd List.map EVERY good_panops] in *).
  - exact IH.
  - rewrite IH, andb_true_r. change (is_true (EVERY (every_exp
      (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝))
      (exps_of (Store (Op Sub [TopAddr; Const (word_add (pan_globals.globals_size ctxt)
         (word_mul bytes_in_word (n2w (size_of_shape sh))))]) (pan_globals.compile_exp ctxt e))))).
    apply EVERY_pok. cbn [exps_of]. constructor; [apply pok_topaddr_sub|].
    constructor; [apply globals_exp_pok, H1|constructor].
  - exact IH.
  - exact IH.
Qed.

Lemma exps_of_fperm f g : forall p : panLang.prog a, exps_of (pan_globals.fperm f g p) = exps_of p.
Proof.
  intros p. induction p using pan_globalsProof.prog_nested_ind; cbn [pan_globals.fperm exps_of];
    try reflexivity; try congruence.
  destruct ct as [[tl [[eid [ev ep]]|]]|]; cbn [exps_of]; try reflexivity. rewrite H. reflexivity.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_fperm" *)
Theorem every_inst_ok_less_fperm : forall f g (code : panLang.prog a),
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝)) (exps_of code) ->
  EVERY (every_exp (fun x => ⌜forall op es, x = Panop op es -> LENGTH es = 2⌝))
    (exps_of (pan_globals.fperm f g code)).
Proof. intros f g code H. rewrite exps_of_fperm. exact H. Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_fperm_decs" *)
Theorem every_inst_ok_less_fperm_decs : forall f g (pan_code : list (decl a)),
  EVERY good_panops pan_code -> EVERY good_panops (pan_globals.fperm_decs f g pan_code).
Proof.
  intros f g pan_code.
  induction pan_code as [|[fi|sh v e|eid sh|nm flds] ds IH]; cbn [pan_globals.fperm_decs EVERY];
    unfold is_true in *; intros H; try reflexivity; apply andb_prop in H as [H1 H2];
    rewrite (IH H2), andb_true_r; try exact H1.
  cbn [good_panops body] in *. rewrite exps_of_fperm. exact H1.
Qed.

Lemma good_panops_FILTER (q : decl a -> bool) (l : list (decl a)) :
  is_true (EVERY good_panops l) -> is_true (EVERY good_panops (FILTER q l)).
Proof.
  unfold is_true. induction l as [|d l IH]; cbn [List.filter EVERY]; [reflexivity|].
  intros H. apply andb_prop in H as [H1 H2]. destruct (q d); cbn [EVERY]; [rewrite H1|]; apply IH, H2.
Qed.

Lemma good_panops_resort (l : list (decl a)) :
  is_true (EVERY good_panops l) -> is_true (EVERY good_panops (pan_globals.resort_decls l)).
Proof.
  intros H. unfold pan_globals.resort_decls.
  repeat (apply EVERY_app_iff; split); apply good_panops_FILTER, H.
Qed.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "every_inst_ok_less_pan_globals_compile_top" *)
Theorem every_inst_ok_less_pan_globals_compile_top : forall (pan_code : list (decl a)) main,
  EVERY good_panops pan_code -> EVERY good_panops (pan_globals.compile_top pan_code main).
Proof.
  intros pan_code main H. unfold pan_globals.compile_top.
  destruct (ALOOKUP (functions pan_code) main) as [[args [bdy rsh]]|]; [|reflexivity]. cbv zeta.
  pose proof (every_inst_ok_less_fperm_decs main (pan_globals.new_main_name pan_code)
                (pan_globals.resort_decls pan_code) (good_panops_resort pan_code H)) as Hf.
  match goal with |- context [pan_globals.compile_decs ?c ?l] =>
    pose proof (every_inst_ok_less_pan_globals_compile_decs c l Hf) as Hd;
    pose proof (every_inst_ok_less_pan_globals_compile_decs_init c l Hf) as Hi;
    destruct (pan_globals.compile_decs c l) as [decls [funs [exns ctxt]]] eqn:E end.
  cbn [FST SND fst snd] in Hd, Hi.
  rewrite (pan_globalsProof.compile_decs_exns_are_exns _ _ _ _ _ _ E).
  apply EVERY_app_iff. split.
  - unfold is_true. rewrite EVERY_Forall. apply Forall_forall. intros d Hd'.
    apply filter_In in Hd' as [_ Hx]. destruct d; try discriminate Hx. reflexivity.
  - cbn [EVERY]. unfold is_true in *. rewrite Hd, andb_true_r.
    cbn [good_panops panLang.body exps_of]. apply EVERY_pok. apply Forall_app. split.
    + rewrite pan_exps_of_nested_seq. apply Forall_concat. unfold is_true in Hi.
      rewrite EVERY_Forall in Hi. rewrite Forall_map in Hi |- *. eapply Forall_impl; [|exact Hi].
      intros x Hx. apply EVERY_pok, Hx.
    + apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([v s] & <- & _). apply pok_simple.
Qed.

End InstOkPan5.

(** ** The composed side condition *)

Section InstOkTop.
Context {a : N}.

(*! HOL "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_to_word_every_inst_ok_less" *)
Theorem pan_to_word_every_inst_ok_less : forall (c : asm_config a) (pan_code : list (decl a)) wprog0,
  pan_to_word.compile_prog (ISA c) pan_code = wprog0 /\
  byte_offset_ok c (n2w 0) /\ addr_offset_ok c (n2w 0) /\
  EVERY good_panops pan_code ->
  EVERY (fun '(n, (m, p)) => wordConvs.every_inst (wordConvs.inst_ok_less c) p) wprog0.
Proof.
  intros c pan_code wprog0 (<- & Hb & Ha & H). unfold pan_to_word.compile_prog. cbv zeta.
  eapply loop_to_wordProof.loop_to_word_every_inst_ok_less.
  split; [reflexivity|]. split; [exact Hb|]. split; [exact Ha|].
  apply every_inst_ok_less_crep_to_loop_compile_prog, every_inst_ok_less_pan_to_crep_compile_prog,
    every_inst_ok_less_pan_globals_compile_top, every_inst_ok_less_pan_structs_compile_top,
    every_inst_ok_less_pan_simp_compile_prog, H.
Qed.

End InstOkTop.
