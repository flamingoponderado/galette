(** * data_to_word_gcProof: initialization and GC invariants

    PARTIAL port of [cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml].
    Ported: [lsr_lsl], [init_store_ok_def], [word_gc_fun_IMP],
    [gc_fun_const_ok_word_gc_fun], and [gc_fun_ok_word_gc_fun].
    The root-relation and length dependencies are in [word_gcFunctions].
    The remaining heap simulation and GC correctness proofs are not ported. *)

From Galette Require Import Base Classical.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.examples.machine_code.hoare_triple Require Import set_sep.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang data_to_word word_simp.
From Galette.cakeml.compiler.backend.semantics Require Import wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import stack_max.
From Galette.cakeml.compiler.backend.proofs Require Import word_gcFunctions word_simpProof.
Import wordLang.
Open Scope N_scope.
Open Scope word_scope.
Open Scope fmap_scope.
Section GC.
Context {a : N}.
(*! HOL "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lsr_lsl" *)
Theorem lsr_lsl : forall (w : word a) n, aligned n w -> (w >>> n << n)%w = w.
Proof. intros w n H; unfold aligned in H; apply bool_decide_spec in H; rewrite <- align_shift; exact H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "init_store_ok_def" *)
Definition init_store_ok {B : Type} c (store : fmap store_name (word_loc a)) (m : word a -> B) dm
 (code_buffer : buffer a 8) (data_buffer : buffer a a) : Prop :=
 exists (limit : N) (curr : word a),
 (limit <= max_heap_limit a c)%N /\
 FLOOKUP store Globals = SOME (Word (n2w 0)) /\
 FLOOKUP store GlobReal = SOME (Word curr) /\
 FLOOKUP store GenStart = SOME (Word (n2w 0)) /\
 FLOOKUP store CurrHeap = SOME (Word curr) /\
 FLOOKUP store OtherHeap = FLOOKUP store EndOfHeap /\
 FLOOKUP store NextFree = SOME (Word curr) /\
 FLOOKUP store EndOfHeap = SOME (Word (curr + bytes_in_word * n2w limit)) /\
 FLOOKUP store TriggerGC = SOME (Word (match gc_kind c with Generational _ => curr | _ => curr + bytes_in_word * n2w limit end)) /\
 FLOOKUP store HeapLength = SOME (Word (bytes_in_word * n2w limit)) /\
 FLOOKUP store CodeBuffer = SOME (Word (position code_buffer)) /\
 FLOOKUP store CodeBufferEnd = SOME (Word (position code_buffer + n2w (space_left code_buffer))) /\
 FLOOKUP store BitmapBuffer = SOME (Word (position data_buffer)) /\
 FLOOKUP store BitmapBufferEnd = SOME (Word (position data_buffer + bytes_in_word * n2w (space_left data_buffer))) /\
 buffer_buffer code_buffer = [] /\ buffer_buffer data_buffer = [] /\
 word_list_exists curr (limit + limit)%N (fun2set (m,dm)) /\ byte_aligned curr.

(*! HOL "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_fun_const_ok_word_gc_fun" *)
Theorem gc_fun_const_ok_word_gc_fun : forall c, gc_fun_const_ok (@word_gc_fun a c).
Proof.
 intros c [xs [m [dm st]]] [ys [m1 s1]] H.
 pose proof (word_gc_IMP_EVERY2 c xs m dm st ys m1 s1 H) as HR.
 clear H; cbn [FST fst]; induction HR; constructor; auto.
 destruct H as [_ HC]; intros HK; symmetry; apply HC; exact HK.
Qed.


Local Ltac gc_result H :=
 cbn beta iota zeta in H;
 repeat match type of H with
 | context [match ?v with _ => _ end] => destruct v eqn:?; cbn beta iota zeta in H
 | context [if ?b then _ else _] => destruct b eqn:?; cbn beta iota zeta in H
 end; try discriminate; injection H as <- <- <-.
(*! HOL "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_IMP" *)
Theorem word_gc_fun_IMP : forall c (xs : list (word_loc a)) m dm s ys m1 s1,
 word_gc_fun c (xs,(m,(dm,s))) = SOME (ys,(m1,s1)) ->
 FLOOKUP s1 AllocSize = FLOOKUP s AllocSize /\
 FLOOKUP s1 Handler = FLOOKUP s Handler /\
 FLOOKUP s1 CodeBuffer = FLOOKUP s CodeBuffer /\
 FLOOKUP s1 CodeBufferEnd = FLOOKUP s CodeBufferEnd /\
 FLOOKUP s1 BitmapBuffer = FLOOKUP s BitmapBuffer /\
 FLOOKUP s1 BitmapBufferEnd = FLOOKUP s BitmapBufferEnd /\
 FLOOKUP s1 (Temp (n2w 29)) = FLOOKUP s (Temp (n2w 29)) /\
 FLOOKUP s1 HeapLength = FLOOKUP s HeapLength /\ Globals IN FDOM s1.
Proof.
 intros c xs m dm s ys m1 s1 H; unfold word_gc_fun in H.
 destruct (gc_kind c); gc_result H.
 all: repeat split; try (apply FLOOKUP_FUPDATE_LIST_notin; cbn [map fst]; intuition discriminate).
 all: unfold pred_set.IN; apply FDOM_FUPDATE_LIST_iff.
 all: try (right; cbn [MAP FST map fst In]; tauto).
 left; apply bool_decide_spec in Heqb; unfold word_gc_fun_assum in Heqb.
 destruct Heqb as [HD _]. apply HD; unfold pred_set.IN, pred_set.INSERT; tauto.
Qed.


Local Lemma assum_handler c (s : fmap store_name (word_loc a)) h :
 word_gc_fun_assum c (s |+ (Handler,h)) = word_gc_fun_assum c s.
Proof.
 apply propositional_extensionality; unfold word_gc_fun_assum.
 rewrite !FAPPLY_FUPDATE_THM, FDOM_FUPDATE.
 repeat match goal with |- context [decide ?P] => destruct (decide P); try discriminate end.
 unfold pred_set.SUBSET, pred_set.IN, pred_set.INSERT, pred_set.EMPTY; firstorder congruence.
Qed.
Local Lemma partial_handler gens (s : fmap store_name (word_loc a)) h :
 word_gen_gc_can_do_partial gens (s |+ (Handler,h)) = word_gen_gc_can_do_partial gens s.
Proof.
 unfold word_gen_gc_can_do_partial; rewrite !FAPPLY_FUPDATE_THM.
 repeat match goal with |- context [decide ?P] => destruct (decide P); try discriminate end; reflexivity.
Qed.
Local Lemma gc_handler c (xs : list (word_loc a)) m dm s h :
 word_gc_fun c (xs,(m,(dm,s |+ (Handler,h)))) =
 OPTION_MAP (fun '(ys,(m1,s1)) => (ys,(m1,s1 |+ (Handler,h))))
 (word_gc_fun c (xs,(m,(dm,s)))).
Proof.
 unfold word_gc_fun; cbn beta iota zeta.
 assert (HB : ⌜word_gc_fun_assum c (s |+ (Handler,h))⌝ = ⌜word_gc_fun_assum c s⌝).
 { apply Bool.eq_true_iff_eq; rewrite !bool_decide_spec, assum_handler; reflexivity. }
 rewrite HB.
 destruct (gc_kind c); cbn beta iota zeta.
 all: repeat match goal with
 | |- context [@bool_decide ?P ?D] => destruct (@bool_decide P D) eqn:?
 end.
 all: repeat match goal with
 | H : @bool_decide ?P ?D = true |- _ => apply bool_decide_spec in H
 | H : @bool_decide ?P ?D = false |- _ =>
   let HN := fresh "HN" in assert (HN : ~ P) by
     (intros HP; assert (@bool_decide P D = true) by (apply bool_decide_spec; exact HP); congruence);
   clear H
 end.
 all: repeat rewrite partial_handler in *.
 all: try contradiction.
 all: try rewrite !(@FAPPLY_FUPDATE_THM store_name (word_loc a) store_name_eq_dec (@word_loc_inhabited a) s Handler h).
 all: repeat match goal with |- context [decide ?P] => destruct (decide P); try discriminate end.
 all: repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?; cbn beta iota zeta
 | |- context [if ?b then _ else _] => destruct b eqn:?; cbn beta iota zeta
 end.
 all: cbn [OPTION_MAP option_map]; try reflexivity.
 all: rewrite FUPDATE_FUPDATE_LIST_COMMUTES; [reflexivity|]; cbn [MAP FST map fst In]; intuition discriminate.
Qed.
(*! HOL "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "gc_fun_ok_word_gc_fun" *)
Theorem gc_fun_ok_word_gc_fun : forall c1, gc_fun_ok (@word_gc_fun a c1).
Proof.
 intros c1 wl m d s wl1 m1 s1 [HD H].
 pose proof (word_gc_fun_LENGTH c1 wl m d (s \\ Handler) wl1 m1 s1 H) as HL.
 pose proof (word_gc_fun_IMP c1 wl m d (s \\ Handler) wl1 m1 s1 H) as HI.
 destruct HI as [_ [HH _]].
 repeat split; [exact HL| |].
 - unfold pred_set.IN, FDOM; rewrite HH, DOMSUB_FLOOKUP_THM.
   destruct (decide (Handler = Handler)); [cbn; tauto|contradiction].
 - assert (HS : (s \\ Handler) |+ (Handler, FAPPLY s Handler) = s).
   { apply fmap_ext; intros k; rewrite FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM.
     destruct (decide (Handler = k)); [subst k|reflexivity].
     unfold pred_set.IN, FDOM in HD; destruct (FLOOKUP s Handler) eqn:E; [|contradiction].
     unfold FAPPLY; rewrite E; reflexivity. }
   rewrite <- HS at 1; rewrite gc_handler, H; reflexivity.
Qed.
End GC.
