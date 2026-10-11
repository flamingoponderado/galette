(** * CakeML [word_to_stackProof]: the state relation

    Part of the port of
    [cakeml/compiler/backend/proofs/word_to_stackProofScript.sml] (HOL lines
    700-1340): [abs_stack], [stack_rel], [stack_size_rel] and [state_rel],
    and the bitmap, sorting and list lemmas that follow them.

    Notes:
    - HOL's [sorting$SORTED] is not in [theories/HOL/src/sort/sorting.v]
      yet (adding it there would rebuild the whole compiler); the
      Galette-only [SORTED] below has HOL's [SORTED_DEF] clauses (a [Prop]).
    - [stack_rel_aux] is [Prop]-valued (it quantifies); [is_handler_frame]
      and [handler_val] are functions.
    - HOL's [EVERY sorted_env] and [EVERY ((<>) x o FST)] are written
      [EVERY (fun f => ⌜sorted_env f⌝)] and [EVERY (fun p => negb (x =? FST p))].
    - HOL's word-state field [stack_size] is [wordSem.state_stack_size], the
      data buffer's [buffer] field is [buffer_buffer].
    - [store_consts_stub_location] is wordLang's (as in [word_to_stack]).
    - HOL's [ac] word-state compiler type is [num # 'c]: the word state is
      [wordSem.state a (N * c) ffi_t].
    - HOL declares [evaluate_SeqStackFree] twice (lines 960 and 3286); the
      first ([local]) one is [evaluate_SeqStackFree_local] here.
    - [total_key_val_compare] unfolds HOL's [total] (not ported);
      [env_to_list_K_I_IMP] uses Rocq's [Permutation] for HOL's [PERM] (not
      ported) and is untagged; [SORTS_SORT_key_val_compare] (stated with
      [SORTS] and [PERM]) is not ported: [env_to_list_K_I_IMP] is proved
      directly from the Galette-only sortedness of [mergesort_tail]
      ([msN_sorted]).  [LENGTH_write_bitmap] is commented out in HOL; the
      ML binding [MEM_SORT] is not a theorem. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Permutation Sorting.Sorted.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.rich_list Require Import lastn.
From Galette.HOL.src.list.src.list Require Import extra list_to_set.
From Galette.HOL.src.sort Require Import mergesort.
From Galette.HOL.src.relation Require relation.
From Galette.cakeml.basis.pure Require mllist.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words bitstring.
From Galette.HOL.src.n_bit.words Require Import lemmas fcp_defs.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import finite_map alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.backend Require Import backend_common stackLang.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend Require Import word_to_stack.
From Galette.cakeml.compiler.backend.semantics Require Import wordConvs.
From Galette.cakeml.compiler.backend.semantics Require wordSem.
From Galette.cakeml.compiler.backend.semantics.wordProps Require Import stack_max.
From Galette.cakeml.compiler.backend.semantics Require Import stackSem stackProps.
From Galette.cakeml.compiler.backend.proofs.word_to_stackProof Require Import basic compile_props.
Import wordLang (word_loc, Word, Loc).
Import wordSem (stack_frame, StackFrame).
Open Scope N_scope.

#[global] Instance stack_frame_inhabited {a} : Inhabited (stack_frame a) :=
  StackFrame NONE [] [] NONE.

(** HOL [sorting$SORTED] (Galette-only copy, see the header). *)
Fixpoint SORTED {A} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: rst => match rst with [] => True | y :: _ => R x y /\ SORTED R rst end
  end.

Section Defs.
Context {a : N}.

Abbreviation abs_frame := (option (word_loc a * word_loc a) * (list bool * list (word_loc a)))%type.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_def" *)
Fixpoint abs_stack (bitmaps : list (word a)) (frames : list (stack_frame a))
    (stack : list (word_loc a)) (lens : list N) {struct frames} : option (list abs_frame) :=
  match frames, stack, lens with
  | [], stack, [] => if decide (stack = [Word (n2w 0)]) then SOME [] else NONE
  | StackFrame n l0 l NONE :: xs, w :: stack, len :: lens =>
      match full_read_bitmap bitmaps w with
      | NONE => NONE
      | SOME bits =>
          if negb (LENGTH bits =? len) then NONE else
          if LENGTH stack <? len then NONE else
            let frame := TAKE len stack in
            let rest := DROP len stack in
            match abs_stack bitmaps xs rest lens with
            | NONE => NONE
            | SOME ys => SOME ((NONE, (bits, frame)) :: ys)
            end
      end
  | StackFrame n l0 l (SOME _) :: xs, w :: stack, len :: lens =>
      if negb (bool_decide (w = Word (n2w 1))) then NONE
      else
        match stack with
        | loc :: hv :: w :: stack =>
            match full_read_bitmap bitmaps w with
            | NONE => NONE
            | SOME bits =>
                if negb (LENGTH bits =? len) then NONE else
                if LENGTH stack <? len then NONE else
                  let frame := TAKE len stack in
                  let rest := DROP len stack in
                  match abs_stack bitmaps xs rest lens with
                  | NONE => NONE
                  | SOME ys => SOME ((SOME (loc, hv), (bits, frame)) :: ys)
                  end
            end
        | _ => NONE
        end
  | _, _, _ => NONE
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FST_def" *)
Definition MAP_FST {A B C} (f : A -> C) (xs : list (A * B)) : list (C * B) :=
  MAP (fun '(x, y) => (f x, y)) xs.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "adjust_names_def" *)
Definition adjust_names (n : N) : N := n DIV 2.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "handler_val_def" *)
Fixpoint handler_val (stack : list abs_frame) : N :=
  match stack with
  | [] => 1
  | (NONE, (_, frame)) :: stack => 1 + LENGTH frame + handler_val stack
  | (SOME _, (_, frame)) :: stack => 4 + LENGTH frame + handler_val stack
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "is_handler_frame_def" *)
Definition is_handler_frame (f : stack_frame a) : bool :=
  match f with
  | StackFrame n l0 l NONE => false
  | _ => true
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_def" *)
Fixpoint stack_rel_aux (k len : N) (frames : list (stack_frame a)) (stack : list abs_frame) : Prop :=
  match frames, stack with
  | [], [] => True
  | StackFrame n l0 l NONE :: xs, (NONE, (bits, frame)) :: stack =>
      (forall n v,
        ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ->
        adjust_names n < k + LENGTH bits /\
        oEL (k + LENGTH bits - (adjust_names n + 1)) bits = SOME false /\
        ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l, []) /\
      the (LENGTH frame + 1) n = LENGTH frame + 1 /\
      stack_rel_aux k len xs stack
  | StackFrame n l0 l (SOME (h1, (l1, l2))) :: xs, (SOME (loc, hv), (bits, frame)) :: stack =>
      (h1 < LENGTH stack /\
       is_handler_frame (EL (LENGTH stack - (h1 + 1)) xs) ->
       hv = Word (n2w (len - handler_val (LASTN (h1 + 1) stack)))) /\
      loc = Loc l1 l2 /\
      (forall n v,
        ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ->
        adjust_names n < k + LENGTH bits /\
        oEL (k + LENGTH bits - (adjust_names n + 1)) bits = SOME false /\
        ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l, []) /\
      the (LENGTH frame + 1) n = LENGTH frame + 1 /\
      stack_rel_aux k len xs stack
  | _, _ => False
  end.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "sorted_env_def" *)
Definition sorted_env (f : stack_frame a) : Prop :=
  let '(StackFrame n l0 l _) := f in SORTED (fun x y => FST x > FST y) l.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_def" *)
Definition stack_rel (k s_handler : N) (s_stack : list (stack_frame a))
    (t_handler : option (word_loc a)) (t_rest_of_stack : list (word_loc a))
    (t_stack_length : N) (t_bitmaps : list (word a)) (lens : list N) : Prop :=
  EVERY (fun f => ⌜sorted_env f⌝) s_stack /\
  exists stack,
    abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack /\
    (s_handler < LENGTH s_stack /\
     is_handler_frame (EL (LENGTH s_stack - (s_handler + 1)) s_stack) ->
     t_handler = SOME (Word (n2w (t_stack_length - handler_val (LASTN (s_handler + 1) stack))))) /\
    stack_rel_aux k t_stack_length s_stack stack.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_size_rel_def" *)
Definition stack_size_rel (f : N) (s_locals_size : option N) (s_stack_limit : N)
    (s_stack_max : option N) (s_stack : list (stack_frame a))
    (t_stack : list (word_loc a)) (t_stack_space : N) (extra : N) : Prop :=
  (f <> 0 -> the f s_locals_size = f) /\
  s_stack_limit = LENGTH t_stack /\
  forall sm, s_stack_max = SOME sm ->
    LENGTH t_stack - t_stack_space - f - extra <= sm /\
    IS_SOME s_locals_size /\
    (exists ss, wordSem.stack_size s_stack = SOME ss /\
      ss = LENGTH t_stack - t_stack_space - f - extra).

End Defs.

Section StateRel.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_def" *)
Definition state_rel (ac : asm_config a) (k f f' : N) (s : wordSem.state a (N * c) ffi_t)
    (t : stackSem.state a c ffi_t) (lens : list N) (extra : N) : Prop :=
  wordSem.clock s = stackSem.clock t /\ wordSem.gc_fun s = stackSem.gc_fun t /\
  wordSem.permute s = K I /\
  stackSem.ffi t = wordSem.ffi s /\ use_stack t /\ use_store t /\ use_alloc t /\
  stackSem.memory t = wordSem.memory s /\ stackSem.mdomain t = wordSem.mdomain s /\ 4 < k /\
  stackSem.sh_mdomain t = wordSem.sh_mdomain s /\
  wordSem.store s = (stackSem.store t \\ Handler) /\ gc_fun_ok (stackSem.gc_fun t) /\
  wordSem.termdep s = 0 /\
  stackSem.be t = wordSem.be s /\ stackSem.ffi t = wordSem.ffi s /\
  Handler IN FDOM (stackSem.store t) /\
  stackSem.fp_regs t = wordSem.fp_regs s /\
  stackSem.data_buffer t = wordSem.data_buffer s /\
  stackSem.code_buffer t = wordSem.code_buffer s /\
  wordSem.compile s = (fun '(bm0, cfg) progs =>
    let '(progs, (fs, bm)) := compile_word_to_stack ac false k progs (Nil, bm0) in
    OPTION_MAP (fun '(bytes, cfg) => (bytes, (append (FST bm), (SND bm, cfg))))
      (stackSem.compile t cfg progs)) /\
  stackSem.compile_oracle t = (fun n =>
    let '((bm0, cfg), progs) := wordSem.compile_oracle s n in
    let '(progs, (fs, bm)) := compile_word_to_stack ac false k progs (Nil, bm0) in
    (cfg, (progs, append (FST bm)))) /\
  (forall n, let '((bm0, cfg), progs) := wordSem.compile_oracle s n in
    EVERY (fun p => post_alloc_conventions k (SND (SND p))) progs /\
    EVERY (fun p => flat_exp_conventions (SND (SND p))) progs /\
    EVERY (fun p => negb (wordLang.raise_stub_location =? FST p)) progs /\
    EVERY (fun p => negb (wordLang.store_consts_stub_location =? FST p)) progs /\
    (n = 0 -> bm0 = LENGTH (bitmaps t))) /\
  domain (stackSem.code t) =
    wordLang.raise_stub_location INSERT wordLang.store_consts_stub_location INSERT
      domain (wordSem.code s) /\
  (forall n word_prog arg_count,
     lookup n (wordSem.code s) = SOME (arg_count, word_prog) ->
     post_alloc_conventions k word_prog /\
     flat_exp_conventions word_prog /\
     exists bs i bs2 i2 f stack_prog,
       compile_prog ac false word_prog arg_count k (bs, i) = (stack_prog, (f, (bs2, i2))) /\
       LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH (bitmaps t) /\
       isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) (bitmaps t)) /\
       lookup n (stackSem.code t) = SOME stack_prog /\
       the f (lookup n (wordSem.state_stack_size s)) = f) /\
  lookup wordLang.raise_stub_location (stackSem.code t) = SOME (raise_stub false k) /\
  lookup wordLang.store_consts_stub_location (stackSem.code t) = SOME (store_consts_stub k) /\
  good_dimindex a /\ 8 <= dimindex a /\
  LENGTH (bitmaps t) + LENGTH (wordSem.buffer_buffer (wordSem.data_buffer s)) +
    wordSem.space_left (wordSem.data_buffer s) + 1 < dimword a /\
  1 <= LENGTH (bitmaps t) /\ HD (bitmaps t) = n2w 4 /\
  stack_space t + f <= LENGTH (stackSem.stack t) /\ LENGTH (stackSem.stack t) < dimword a /\
  (if f' =? 0 then f = 0 else f = f' + 1) /\
  wf (wordSem.locals s) /\
  stack_size_rel f (wordSem.locals_size s) (wordSem.stack_limit s) (wordSem.stack_max s)
    (wordSem.stack s) (stackSem.stack t) (stack_space t) extra /\
  let stack := DROP (stack_space t + extra) (stackSem.stack t) in
  let current_frame := TAKE f stack in
  let rest_of_stack := DROP f stack in
    stack_rel k (wordSem.handler s) (wordSem.stack s) (FLOOKUP (stackSem.store t) Handler)
      rest_of_stack (LENGTH (stackSem.stack t)) (bitmaps t) lens /\
    (forall n v,
      lookup n (wordSem.locals s) = SOME v ->
      EVEN n /\
      if n DIV 2 <? k then FLOOKUP (regs t) (n DIV 2) = SOME v
      else oEL (f - 1 - (n DIV 2 - k)) current_frame = SOME v /\ n DIV 2 < k + f').

End StateRel.

(** Galette-only: destruct a [state_rel] hypothesis into its 39 components,
    and split a [state_rel] goal into the same components (in order). *)
Ltac sr_destr H :=
  unfold state_rel in H; cbv zeta in H;
  let Hclock := fresh "Hclock" in let Hgc := fresh "Hgc" in let Hperm := fresh "Hperm" in
  let Hffi := fresh "Hffi" in let Hus := fresh "Hus" in let Hust := fresh "Hust" in
  let Hua := fresh "Hua" in let Hmem := fresh "Hmem" in let Hmd := fresh "Hmd" in
  let Hk := fresh "Hk" in let Hshmd := fresh "Hshmd" in let Hstore := fresh "Hstore" in
  let Hgcok := fresh "Hgcok" in let Htd := fresh "Htd" in let Hbe := fresh "Hbe" in
  let Hffi2 := fresh "Hffi2" in let HH := fresh "HH" in let Hfp := fresh "Hfp" in
  let Hdb := fresh "Hdb" in let Hcb := fresh "Hcb" in let Hcomp := fresh "Hcomp" in
  let Hco := fresh "Hco" in let Hcon := fresh "Hcon" in let Hdom := fresh "Hdom" in
  let Hcode := fresh "Hcode" in let Hraise := fresh "Hraise" in let Hsc := fresh "Hsc" in
  let Hgd := fresh "Hgd" in let H8 := fresh "H8" in let Hlen := fresh "Hlen" in
  let Hbm1 := fresh "Hbm1" in let Hhd := fresh "Hhd" in let Hsp := fresh "Hsp" in
  let Hsl := fresh "Hsl" in let Hff := fresh "Hff" in let Hwf := fresh "Hwf" in
  let Hssr := fresh "Hssr" in let Hsr := fresh "Hsr" in let Hloc := fresh "Hloc" in
  destruct H as (Hclock & Hgc & Hperm & Hffi & Hus & Hust & Hua & Hmem & Hmd & Hk & Hshmd & Hstore &
    Hgcok & Htd & Hbe & Hffi2 & HH & Hfp & Hdb & Hcb & Hcomp & Hco & Hcon & Hdom & Hcode & Hraise &
    Hsc & Hgd & H8 & Hlen & Hbm1 & Hhd & Hsp & Hsl & Hff & Hwf & Hssr & Hsr & Hloc).

(** Galette-only: unfold the field updates and projections of wordSem's
    states. *)
Ltac ws_fields :=
  cbn [wordSem.set_locals wordSem.set_locals_size wordSem.set_fp_regs wordSem.set_store_field
    wordSem.set_stack wordSem.set_stack_limit wordSem.set_stack_max wordSem.set_stack_size
    wordSem.set_memory wordSem.set_mdomain wordSem.set_sh_mdomain wordSem.set_permute
    wordSem.set_compile wordSem.set_compile_oracle wordSem.set_code_buffer wordSem.set_data_buffer
    wordSem.set_gc_fun wordSem.set_handler wordSem.set_clock wordSem.set_termdep wordSem.set_code
    wordSem.set_be wordSem.set_ffi
    wordSem.locals wordSem.locals_size wordSem.fp_regs wordSem.store wordSem.stack wordSem.stack_limit
    wordSem.stack_max wordSem.state_stack_size wordSem.memory wordSem.mdomain wordSem.sh_mdomain
    wordSem.permute wordSem.compile wordSem.compile_oracle wordSem.code_buffer wordSem.data_buffer
    wordSem.gc_fun wordSem.handler wordSem.clock wordSem.termdep wordSem.code wordSem.be wordSem.ffi] in *.

Ltac sr_split :=
  unfold state_rel; cbv zeta; repeat match goal with |- _ /\ _ => split end.

(** ** Galette-only: stackLang evaluation equations *)

Section EvalEqs.
Context {a : N} {c ffi_t : Type}.
Implicit Types X Y : stackSem.state a c ffi_t.

Lemma ev_seq (p1 p2 : prog a) X :
  evaluate (Seq p1 p2, X) =
  let '(res, s1) := evaluate (p1, X) in match res with NONE => evaluate (p2, s1) | _ => (res, s1) end.
Proof. destruct (@evaluate_def a c ffi_t) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). apply H. Qed.

Lemma ev_seq_none (p1 p2 : prog a) X Y :
  evaluate (p1, X) = (NONE, Y) -> evaluate (Seq p1 p2, X) = evaluate (p2, Y).
Proof. intros H; rewrite ev_seq, H; reflexivity. Qed.

Lemma ev_skip X : evaluate (Skip, X) = (NONE, X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackfree n X :
  evaluate (StackFree n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if LENGTH (stackSem.stack X) <? stack_space X + n then (SOME Error, empty_env X) else
    (NONE, set_stack_space (stack_space X + n) X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackalloc n X :
  evaluate (StackAlloc n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if stack_space X <? n then (SOME (Halt (Word (n2w 2))), empty_env X) else
    (NONE, set_stack_space (stack_space X - n) X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_inst (i : asm.inst a) X :
  evaluate (Inst i, X) = match inst i X with SOME s1 => (NONE, s1) | NONE => (SOME Error, X) end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackstore r n X :
  evaluate (StackStore r n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if LENGTH (stackSem.stack X) <=? stack_space X + n then (SOME Error, empty_env X) else
  match stackSem.get_var r X with
  | NONE => (SOME Error, empty_env X)
  | SOME v => (NONE, set_stack (LUPDATE v (stack_space X + n) (stackSem.stack X)) X)
  end.
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma ev_stackload r n X :
  evaluate (StackLoad r n, X) =
  if negb (use_stack X) then (SOME Error, X) else
  if stack_space X + n <? LENGTH (stackSem.stack X)
  then (NONE, stackSem.set_var r (EL (stack_space X + n) (stackSem.stack X)) X)
  else (SOME Error, empty_env X).
Proof. rewrite evaluate_eqn; reflexivity. Qed.

Lemma inst_const r w X : inst (asm.Const r w) X = SOME (stackSem.set_var r (Word w) X).
Proof. reflexivity. Qed.

End EvalEqs.

(** ** Lemmas of the state-relation section (HOL lines 960-1340) *)

Section StateRelLemmas.
Context {a : N} {c ffi_t : Type}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_SeqStackFree" 960 *)
Theorem evaluate_SeqStackFree_local : forall f (p : prog a) (t : stackSem.state a c ffi_t),
  use_stack t /\ stack_space t <= LENGTH (stackSem.stack t) ->
  evaluate (SeqStackFree f p, t) = evaluate (Seq (StackFree f) p, t).
Proof.
  intros f p t [Hu Hl]. unfold SeqStackFree. destruct (N.eqb_spec f 0) as [->|Hf]; [|reflexivity].
  rewrite ev_seq, ev_stackfree. unfold is_true in Hu. rewrite Hu. cbn [negb].
  replace (LENGTH (stackSem.stack t) <? stack_space t + 0) with false by (symmetry; apply N.ltb_ge; lia).
  rewrite N.add_0_r. destruct t; reflexivity.
Qed.

End StateRelLemmas.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_list_LUPDATE_lemma" *)
Theorem DROP_list_LUPDATE_lemma : forall {A} n (ys xs : list A),
  DROP n (list_LUPDATE ys n xs) = list_LUPDATE ys 0 (DROP n xs).
Proof. intros A n ys xs. rewrite DROP_list_LUPDATE by lia. rewrite N.sub_diag. reflexivity. Qed.

Section Bits.
Context {a : N}.
Local Open Scope word_scope.

Lemma fcp_bits_to_word_cons b (bs : list bool) i : (i < dimindex a)%N ->
  (@bits_to_word a (b :: bs)) ' i = if (i =? 0)%N then b else (@bits_to_word a bs) ' (i - 1)%N.
Proof.
  intros Hi. pose proof (@dimindex_pos a) as Hd.
  destruct b; cbn [bits_to_word].
  - rewrite fcp_index_word_or, fcp_index_word_lsl, fcp_index_n2w by exact Hi.
    destruct (N.eqb_spec i 0) as [->|Hn].
    + cbn. reflexivity.
    + replace (1 <=? i)%N with true by (symmetry; apply N.leb_le; lia). cbn [andb].
      rewrite BIT_testbit. replace (N.testbit 1 i) with false; [apply orb_false_r|].
      symmetry. destruct i as [|p]; [lia|]. reflexivity.
  - rewrite fcp_index_word_lsl by exact Hi. destruct (N.eqb_spec i 0) as [->|Hn]; [reflexivity|].
    replace (1 <=? i)%N with true by (symmetry; apply N.leb_le; lia). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bits_to_word_bit" *)
Theorem bits_to_word_bit : forall (bs : list bool) i,
  (i < dimindex a)%N /\ (i < LENGTH bs)%N -> (@bits_to_word a bs) ' i = EL i bs.
Proof.
  induction bs as [|b bs IH]; intros i [Hi Hl]; [cbn in Hl; lia|].
  rewrite fcp_bits_to_word_cons by exact Hi. rewrite LENGTH_cons' in Hl.
  destruct (N.eqb_spec i 0) as [->|Hn]; [reflexivity|].
  replace i with (SUC (i - 1)%N) at 2 by lia. rewrite EL_SUC. apply IH. split; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bits_to_word_miss" *)
Theorem bits_to_word_miss : forall (bs : list bool) i,
  (i < dimindex a)%N /\ (LENGTH bs <= i)%N -> ~ is_true ((@bits_to_word a bs) ' i).
Proof.
  induction bs as [|b bs IH]; intros i [Hi Hl].
  - cbn [bits_to_word]. rewrite fcp_index_n2w by exact Hi. rewrite BIT_testbit, N.bits_0. discriminate.
  - rewrite fcp_bits_to_word_cons by exact Hi. rewrite LENGTH_cons' in Hl.
    replace (i =? 0)%N with false by (symmetry; apply N.eqb_neq; lia). apply IH. split; lia.
Qed.

Lemma fcp_bits_to_word (bs : list bool) i : (i < dimindex a)%N ->
  (@bits_to_word a bs) ' i = ((i <? LENGTH bs)%N && EL i bs)%bool.
Proof.
  intros Hi. destruct (N.ltb_spec i (LENGTH bs)) as [Hl|Hl]; cbn [andb].
  - apply bits_to_word_bit. split; assumption.
  - destruct ((@bits_to_word a bs) ' i) eqn:E; [|reflexivity].
    exfalso. apply (bits_to_word_miss bs i (conj Hi Hl)). exact E.
Qed.

Lemma EL_app_N {A} `{Inhabited A} (l1 l2 : list A) i :
  EL i (l1 ++ l2) = if (i <? LENGTH l1)%N then EL i l1 else EL (i - LENGTH l1)%N l2.
Proof.
  rewrite !EL_nth', LENGTH_length. destruct (N.ltb_spec i (N.of_nat (length l1))).
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bits_to_word_SNOC" *)
Theorem bits_to_word_SNOC : forall (bs : list bool) b,
  @bits_to_word a (SNOC b bs) = ((if b then n2w 1 else n2w 0) << LENGTH bs || bits_to_word bs).
Proof.
  intros bs b. apply word_bit_ext. intros i Hi.
  rewrite fcp_index_word_or, fcp_index_word_lsl, !fcp_bits_to_word by exact Hi.
  rewrite SNOC_app, LENGTH_app', EL_app_N. change (LENGTH [b]) with 1%N.
  destruct (N.ltb_spec i (LENGTH bs)) as [H1|H1];
  destruct (N.ltb_spec i (LENGTH bs + 1)) as [H2|H2];
  destruct (N.leb_spec (LENGTH bs) i) as [H3|H3]; try lia; cbn [andb orb]; rewrite ?orb_false_r.
  - reflexivity.
  - assert (E : i = LENGTH bs) by lia. subst i. rewrite N.sub_diag.
    destruct b; rewrite fcp_index_n2w by lia; rewrite BIT_testbit; reflexivity.
  - destruct b; rewrite fcp_index_n2w by lia; rewrite BIT_testbit; [|rewrite N.bits_0; reflexivity].
    destruct (i - LENGTH bs)%N eqn:E; [lia|]. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bits_to_word_bitstring_reverse" *)
Theorem bits_to_word_bitstring_reverse : forall (xs : list bool),
  @bits_to_word a xs = v2w (REVERSE xs).
Proof.
  intros xs. apply word_bit_ext. intros i Hi. unfold v2w. rewrite fcp_index_FCP by exact Hi.
  rewrite fcp_bits_to_word by exact Hi. unfold testbit. cbv zeta.
  rewrite !LENGTH_length, length_rev. destruct (N.ltb_spec i (N.of_nat (length xs))); [|reflexivity].
  cbn [andb]. rewrite !EL_nth', rev_nth by lia. f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "GENLIST_bits_to_word_alt" *)
Theorem GENLIST_bits_to_word_alt : forall (xs ys : list bool),
  (LENGTH (xs ++ ys) <= dimindex a)%N ->
  GENLIST (fun i => (@bits_to_word a (xs ++ ys)) ' i) (LENGTH xs) = xs.
Proof.
  intros xs ys H. rewrite <- (GENLIST_EL_id xs) at 2. rewrite !GENLIST_seq. apply map_ext_in.
  intros j Hj. apply in_seq in Hj. rewrite LENGTH_app' in H.
  rewrite bits_to_word_bit by (rewrite LENGTH_app'; rewrite LENGTH_length, Nat2N.id in *; lia).
  rewrite EL_app_N. replace (N.of_nat j <? LENGTH xs)%N with true by (symmetry; apply N.ltb_lt; rewrite LENGTH_length, Nat2N.id in *; lia).
  reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "GENLIST_bits_to_word" *)
Theorem GENLIST_bits_to_word : forall (qs' : list bool),
  (LENGTH qs' + 1 < dimindex a)%N ->
  GENLIST (fun i => (@bits_to_word a (qs' ++ [true])) ' i) (LENGTH qs') = qs'.
Proof. intros qs' H. apply GENLIST_bits_to_word_alt. rewrite LENGTH_app'. cbn. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "bit_length_bits_to_word" *)
Theorem bit_length_bits_to_word : forall (qs : list bool),
  (LENGTH qs + 1 < dimindex a)%N ->
  bit_length (@bits_to_word a (qs ++ [true])) = (LENGTH qs + 1)%N.
Proof.
  intros qs H. unfold bit_length.
  assert (Ht : N.testbit (w2n (@bits_to_word a (qs ++ [true]))) (LENGTH qs) = true).
  { rewrite <- fcp_index_testbit, fcp_bits_to_word by lia. rewrite LENGTH_app', EL_app_N.
    replace (LENGTH qs <? LENGTH qs + LENGTH [true])%N with true by (symmetry; apply N.ltb_lt; cbn; lia).
    replace (LENGTH qs <? LENGTH qs)%N with false by (symmetry; apply N.ltb_ge; lia).
    rewrite N.sub_diag. reflexivity. }
  assert (Hn : w2n (@bits_to_word a (qs ++ [true])) <> 0%N).
  { intros E. rewrite E in Ht. rewrite N.bits_0 in Ht. discriminate. }
  rewrite N.size_log2 by exact Hn. rewrite N.add_1_r. f_equal.
  apply N.log2_bits_unique; [exact Ht|]. intros m Hm.
  rewrite <- fcp_index_testbit. destruct (N.ltb_spec m (dimindex a)) as [Hd|Hd].
  - rewrite fcp_bits_to_word by exact Hd. rewrite LENGTH_app'. change (LENGTH [true]) with 1%N.
    replace (m <? LENGTH qs + 1)%N with false by (symmetry; apply N.ltb_ge; lia). reflexivity.
  - apply fcp_index_high. exact Hd.
Qed.

Lemma bits_to_word_nonzero (bs : list bool) i :
  (i < dimindex a)%N -> (i < LENGTH bs)%N -> EL i bs = true -> @bits_to_word a bs <> n2w 0.
Proof.
  intros Hi Hl He E. pose proof (bits_to_word_bit bs i (conj Hi Hl)) as B. rewrite E, He in B.
  rewrite fcp_index_n2w, BIT_testbit, N.bits_0 in B by exact Hi. discriminate.
Qed.

Lemma TAKE_app_le {A} n (l1 l2 : list A) : (n <= LENGTH l1)%N -> TAKE n (l1 ++ l2) = TAKE n l1.
Proof. intros H. rewrite !TAKE_firstn, firstn_app. rewrite LENGTH_length in H.
  replace (N.to_nat n - length l1)%nat with O by lia. rewrite app_nil_r. reflexivity. Qed.

Lemma DROP_app_le {A} n (l1 l2 : list A) : (n <= LENGTH l1)%N -> DROP n (l1 ++ l2) = DROP n l1 ++ l2.
Proof. intros H. rewrite !DROP_skipn, skipn_app. rewrite LENGTH_length in H.
  replace (N.to_nat n - length l1)%nat with O by lia. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_word_list" *)
Theorem read_bitmap_word_list : forall (qs : list bool) (xs : list (word a)),
  (8 <= dimindex a)%N ->
  read_bitmap (word_list (qs ++ [true]) (dimindex a - 1) ++ xs) = SOME qs.
Proof.
  intros qs. remember (length qs) as n eqn:En. revert qs En.
  induction n as [n IH] using (well_founded_induction lt_wf). intros qs En xs Hd.
  rewrite word_list_def. replace (dimindex a - 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
  rewrite orb_false_r. rewrite LENGTH_app'. change (LENGTH [true]) with 1%N.
  destruct (N.leb_spec (LENGTH qs + 1) (dimindex a - 1)) as [H|H].
  - cbn [app read_bitmap]. rewrite word_msb_def.
    replace ((@bits_to_word a (qs ++ [true])) ' (dimindex a - 1)%N) with false.
    2:{ symmetry. destruct ((@bits_to_word a (qs ++ [true])) ' (dimindex a - 1)%N) eqn:E; [|reflexivity].
        exfalso. apply (bits_to_word_miss (qs ++ [true]) (dimindex a - 1)); [|exact E].
        rewrite LENGTH_app'. cbn. split; lia. }
    rewrite bit_length_bits_to_word by lia. rewrite N.add_sub. rewrite GENLIST_bits_to_word by lia.
    reflexivity.
  - assert (Hq : (dimindex a - 1 <= LENGTH qs)%N) by lia.
    rewrite TAKE_app_le, DROP_app_le by exact Hq. cbn [app read_bitmap].
    rewrite word_msb_def.
    assert (HL : LENGTH (TAKE (dimindex a - 1) qs) = (dimindex a - 1)%N).
    { rewrite TAKE_firstn, LENGTH_length, length_firstn. rewrite LENGTH_length in Hq. lia. }
    replace ((@bits_to_word a (TAKE (dimindex a - 1) qs ++ [true])) ' (dimindex a - 1)%N) with true.
    2:{ symmetry. rewrite bits_to_word_bit by (rewrite LENGTH_app', HL; cbn; lia).
        rewrite EL_app_N, HL. replace (dimindex a - 1 <? dimindex a - 1)%N with false by (symmetry; apply N.ltb_ge; lia).
        rewrite N.sub_diag. reflexivity. }
    rewrite (IH (length (DROP (dimindex a - 1) qs))); [| |reflexivity|exact Hd].
    + f_equal. assert (G := GENLIST_bits_to_word_alt (TAKE (dimindex a - 1) qs) [true]
        ltac:(rewrite LENGTH_app', HL; cbn; lia)). rewrite HL in G. rewrite G.
      rewrite !TAKE_firstn, !DROP_skipn, firstn_skipn. reflexivity.
    + rewrite DROP_skipn, length_skipn. rewrite LENGTH_length in *. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_write_bitmap" *)
Theorem read_bitmap_write_bitmap : forall names k f',
  (8 <= dimindex a)%N ->
  read_bitmap (@write_bitmap a names k f') =
  SOME (GENLIST (fun x => MEM x (MAP (fun '(r, y) => f' - 1 - (r DIV 2 - k)) (toAList names)))%N f').
Proof.
  intros names k f' H. unfold write_bitmap. cbv zeta.
  pose proof (read_bitmap_word_list
    (GENLIST (fun x => MEM x (MAP (fun '(r, y) => f' - 1 - (r DIV 2 - k)) (toAList names)))%N f') [] H) as R.
  rewrite app_nil_r in R. exact R.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "list_LUPDATE_write_bitmap_NOT_NIL" *)
Theorem list_LUPDATE_write_bitmap_NOT_NIL : forall names k f' (xs : list (word_loc a)),
  (8 <= dimindex a)%N ->
  list_LUPDATE (MAP Word (@write_bitmap a names k f')) 0 xs <> [Word (n2w 0)].
Proof.
  intros names k f' xs H. destruct xs as [|x xs]; [rewrite list_LUPDATE_NIL; discriminate|].
  unfold write_bitmap. cbv zeta.
  set (qs := GENLIST _ f'). rewrite word_list_def.
  replace (dimindex a - 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia). rewrite orb_false_r.
  rewrite LENGTH_app'. change (LENGTH [true]) with 1%N.
  destruct (LENGTH qs + 1 <=? dimindex a - 1)%N eqn:E; cbn [MAP List.map]; rewrite list_LUPDATE_0_CONS;
    intros C; injection C as C _; revert C.
  - apply N.leb_le in E. apply (bits_to_word_nonzero _ (LENGTH qs)); [lia|rewrite LENGTH_app'; cbn; lia|].
    rewrite EL_app_N. replace (LENGTH qs <? LENGTH qs)%N with false by (symmetry; apply N.ltb_ge; lia).
    rewrite N.sub_diag. reflexivity.
  - apply N.leb_gt in E.
    assert (HL : LENGTH (TAKE (dimindex a - 1) (qs ++ [true])) = (dimindex a - 1)%N).
    { rewrite TAKE_firstn, LENGTH_length, length_firstn, length_app. rewrite LENGTH_length in E. cbn [length] in *. lia. }
    apply (bits_to_word_nonzero _ (dimindex a - 1)); [lia|rewrite LENGTH_app', HL; cbn; lia|].
    rewrite EL_app_N, HL. replace (dimindex a - 1 <? dimindex a - 1)%N with false by (symmetry; apply N.ltb_ge; lia).
    rewrite N.sub_diag. reflexivity.
Qed.

End Bits.

(** ** More list lemmas *)

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "APPEND_LEMMA" *)
Theorem APPEND_LEMMA : forall {A} n1 n2 n3 (xs : list A),
  n1 + n2 + n3 <= LENGTH xs ->
  exists xs2 xs3, DROP n1 xs = xs2 ++ xs3 /\ n2 = LENGTH xs2.
Proof.
  intros A n1 n2 n3 xs H. exists (TAKE n2 (DROP n1 xs)), (DROP n2 (DROP n1 xs)). split.
  - rewrite !TAKE_firstn, !DROP_skipn, firstn_skipn. reflexivity.
  - rewrite TAKE_firstn, DROP_skipn, LENGTH_length, length_firstn, length_skipn. rewrite LENGTH_length in H. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_SND_MAP_FST" *)
Theorem MAP_SND_MAP_FST : forall {A B C} (xs : list (A * B)) (f : A -> C), MAP SND (MAP_FST f xs) = MAP SND xs.
Proof. intros A B C xs f. induction xs as [|[x y] xs IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "isPREFIX_DROP" *)
Theorem isPREFIX_DROP : forall {A} `{EqDecision A} (s t : list A) i,
  isPREFIX s t -> isPREFIX (DROP i s) (DROP i t).
Proof.
  intros A HA s t i H. apply isPREFIX_iff in H as [l ->]. apply isPREFIX_iff.
  rewrite !DROP_skipn, skipn_app. destruct (Nat.le_ge_cases (N.to_nat i) (length s)).
  - exists l. replace (N.to_nat i - length s)%nat with O by lia. reflexivity.
  - exists (skipn (N.to_nat i - length s) l). rewrite (List.skipn_all2 s) by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LLOOKUP_cons_SUC" *)
Theorem LLOOKUP_cons_SUC : forall {A} m n (h : A) xs,
  m < n -> oEL (n - m) (h :: xs) = oEL (n - (m + 1)) xs.
Proof.
  intros A m n h xs H. cbn [oEL]. replace (n - m =? 0) with false by (symmetry; apply N.eqb_neq; lia).
  f_equal. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVEN_DIV2_INJ" *)
Theorem EVEN_DIV2_INJ : forall x y, EVEN x /\ EVEN y /\ x DIV 2 = y DIV 2 -> x = y.
Proof.
  intros x y (Hx & Hy & H). apply N.even_spec in Hx as [p ->]. apply N.even_spec in Hy as [q ->].
  rewrite !(N.mul_comm 2), !N.div_mul in H by lia. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVEN_GT" *)
Theorem EVEN_GT : forall a0 b, EVEN a0 /\ EVEN b /\ a0 > b -> a0 DIV 2 > b DIV 2.
Proof.
  intros x y (Hx & Hy & H). apply N.even_spec in Hx as [p ->]. apply N.even_spec in Hy as [q ->].
  rewrite !(N.mul_comm 2), !N.div_mul by lia. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "transitive_GT" *)
Theorem transitive_GT : relation.transitive (fun x y : N => x > y).
Proof. intros x y z [H1 H2]. lia. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_size_rel_iff" *)
Theorem stack_size_rel_iff : forall {a} f s_locals_size s_stack_limit s_stack_max (s_stack : list (stack_frame a))
    t_stack t_stack_space extra,
  stack_size_rel f s_locals_size s_stack_limit s_stack_max s_stack t_stack t_stack_space extra <->
  (f <> 0 -> the f s_locals_size = f) /\
  s_stack_limit = LENGTH t_stack /\
  LENGTH t_stack - t_stack_space - f - extra <= the (LENGTH t_stack - t_stack_space - f - extra) s_stack_max /\
  (IS_SOME s_stack_max -> IS_SOME (wordSem.stack_size s_stack)) /\
  (IS_SOME s_stack_max -> IS_SOME s_locals_size) /\
  (IS_SOME s_stack_max -> the (LENGTH t_stack - t_stack_space - f - extra) (wordSem.stack_size s_stack) =
     LENGTH t_stack - t_stack_space - f - extra).
Proof.
  intros a f sl sli sm ss ts tsp extra. unfold stack_size_rel. split.
  - intros (H1 & H2 & H3). repeat split; auto.
    + destruct sm as [m|]; cbn; [apply (H3 m eq_refl)|lia].
    + intros Hs. destruct sm as [m|]; [|discriminate]. destruct (H3 m eq_refl) as (_ & _ & ss' & E & _).
      rewrite E. reflexivity.
    + intros Hs. destruct sm as [m|]; [|discriminate]. apply (H3 m eq_refl).
    + intros Hs. destruct sm as [m|]; [|discriminate]. destruct (H3 m eq_refl) as (_ & _ & ss' & E & E2).
      rewrite E. cbn. exact E2.
  - intros (H1 & H2 & H3 & H4 & H5 & H6). split; [exact H1|]. split; [exact H2|].
    intros m Em. subst sm. cbn in *. split; [exact H3|]. split; [apply H5; reflexivity|].
    specialize (H4 eq_refl). specialize (H6 eq_refl). destruct (wordSem.stack_size ss) as [z|]; [|discriminate].
    exists z. split; [reflexivity|exact H6].
Qed.

(** ** Bitmap reading *)

Section ReadBitmap.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_append_extra" *)
Theorem read_bitmap_append_extra : forall (l1 l2 : list (word a)) bits,
  read_bitmap l1 = SOME bits -> read_bitmap (l1 ++ l2) = SOME bits.
Proof.
  induction l1 as [|w l1 IH]; intros l2 bits H; [discriminate|]. cbn [read_bitmap app] in *.
  destruct (word_msb w); [|exact H].
  destruct (read_bitmap l1) as [bs|] eqn:E; [|discriminate]. rewrite (IH l2 bs eq_refl). exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "full_read_bitmap_append" *)
Theorem full_read_bitmap_append : forall (bitmaps : list (word a)) w bits more_bitmaps,
  full_read_bitmap bitmaps w = SOME bits -> full_read_bitmap (bitmaps ++ more_bitmaps) w = SOME bits.
Proof.
  intros bitmaps w bits more H. unfold full_read_bitmap in *. destruct w as [w|]; [|discriminate].
  destruct (bool_decide _); [discriminate|].
  rewrite DROP_skipn in *. rewrite skipn_app. destruct (Nat.le_ge_cases (N.to_nat (w2n (word_sub w (n2w 1)))) (length bitmaps)).
  - replace (N.to_nat (w2n (word_sub w (n2w 1))) - length bitmaps)%nat with O by lia.
    apply read_bitmap_append_extra. exact H.
  - rewrite (List.skipn_all2 bitmaps) in H by lia. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_bitmaps_prefix" *)
Theorem abs_stack_bitmaps_prefix : forall (bitmaps : list (word a)) frames stack lens more_bitmaps result,
  abs_stack bitmaps frames stack lens = SOME result ->
  abs_stack (bitmaps ++ more_bitmaps) frames stack lens = SOME result.
Proof.
  intros bitmaps frames; induction frames as [|[n l0 l h] frames IH]; intros stack lens more result H.
  - destruct lens; [exact H|discriminate].
  - destruct stack as [|w stack]; [destruct h; discriminate|]. destruct lens as [|len lens]; [destruct h; discriminate|].
    destruct h as [hh|]; cbn [abs_stack] in *.
    + destruct (negb _); [discriminate|]. destruct stack as [|loc [|hv [|w2 stack]]]; try discriminate.
      destruct (full_read_bitmap bitmaps w2) as [bits|] eqn:E; [|discriminate].
      rewrite (full_read_bitmap_append _ _ _ _ E).
      destruct (negb _); [discriminate|]. destruct (_ <? _); [discriminate|]. cbv zeta in *.
      destruct (abs_stack bitmaps frames _ lens) as [ys|] eqn:E2; [|discriminate].
      rewrite (IH _ _ _ _ E2). exact H.
    + destruct (full_read_bitmap bitmaps w) as [bits|] eqn:E; [|discriminate].
      rewrite (full_read_bitmap_append _ _ _ _ E).
      destruct (negb _); [discriminate|]. destruct (_ <? _); [discriminate|]. cbv zeta in *.
      destruct (abs_stack bitmaps frames _ lens) as [ys|] eqn:E2; [|discriminate].
      rewrite (IH _ _ _ _ E2). exact H.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_IMP_LENGTH" *)
Theorem abs_stack_IMP_LENGTH : forall (bs : list (word a)) wstack sstack lens stack,
  abs_stack bs wstack sstack lens = SOME stack ->
  LENGTH stack = LENGTH wstack /\ LENGTH lens = LENGTH wstack.
Proof.
  intros bs wstack; induction wstack as [|[n l0 l h] frames IH]; intros sstack lens stack H.
  - destruct lens; [|discriminate]. cbn in H. destruct (decide _); [|discriminate].
    injection H as <-. split; reflexivity.
  - destruct sstack as [|w sstack]; [destruct h; discriminate|]. destruct lens as [|len lens]; [destruct h; discriminate|].
    destruct h as [hh|]; cbn [abs_stack] in *.
    + destruct (negb _); [discriminate|]. destruct sstack as [|loc [|hv [|w2 sstack]]]; try discriminate.
      destruct (full_read_bitmap bs w2) as [bits|]; [|discriminate].
      destruct (negb _); [discriminate|]. destruct (_ <? _); [discriminate|]. cbv zeta in *.
      destruct (abs_stack bs frames _ lens) as [ys|] eqn:E2; [|discriminate].
      injection H as <-. destruct (IH _ _ _ E2). rewrite !LENGTH_cons'. lia.
    + destruct (full_read_bitmap bs w) as [bits|]; [|discriminate].
      destruct (negb _); [discriminate|]. destruct (_ <? _); [discriminate|]. cbv zeta in *.
      destruct (abs_stack bs frames _ lens) as [ys|] eqn:E2; [|discriminate].
      injection H as <-. destruct (IH _ _ _ E2). rewrite !LENGTH_cons'. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_insert_bitmap" *)
Theorem read_bitmap_insert_bitmap : forall (bm : list (word a)) bs n bs' n' i (cur : list (word a)),
  i < dimword a /\ IS_SOME (read_bitmap bm) /\
  n = LENGTH cur + LENGTH (append bs) /\
  insert_bitmap bm (bs, n) = ((bs', n'), i) ->
  read_bitmap (DROP (i MOD dimword a) (cur ++ append bs')) = read_bitmap bm.
Proof.
  intros bm bs n bs' n' i cur (Hi & _ & -> & E). cbn [insert_bitmap] in E. injection E as <- <- <-.
  rewrite N.mod_small by exact Hi.
  rewrite (proj1 (append_thm _ _ [])), (proj1 (proj2 (append_thm bs bs bm))).
  replace (LENGTH cur + LENGTH (append bs)) with (LENGTH (cur ++ append bs)) by (rewrite LENGTH_app'; reflexivity).
  rewrite app_assoc, DROP_skipn, LENGTH_length, Nat2N.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

End ReadBitmap.

(** ** Sorting *)

Section SortedLemmas.

Lemma SORTED_Sorted {A} (R : A -> A -> Prop) l : SORTED R l <-> Sorted R l.
Proof.
  induction l as [|x [|y l] IH]; cbn [SORTED].
  - split; constructor.
  - split; [repeat constructor|constructor].
  - rewrite IH. split.
    + intros [H1 H2]. constructor; [exact H2|constructor; exact H1].
    + intros H. apply Sorted_inv in H as [H1 H2]. apply HdRel_inv in H2. split; assumption.
Qed.

Lemma SORTED_StronglySorted {A} (R : A -> A -> Prop) l :
  (forall x y z, R x y -> R y z -> R x z) -> SORTED R l -> StronglySorted R l.
Proof. intros T H. apply SORTED_Sorted in H. apply Sorted_StronglySorted; [exact T|exact H]. Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_FST_LESS_IMP" *)
Theorem SORTED_FST_LESS_IMP : forall {B} `{EqDecision B} (xs : list (N * B)) x,
  SORTED (fun x y => FST x > FST y) (x :: xs) ->
  SORTED (fun x y => FST x > FST y) xs /\ ~ is_true (MEM x xs) /\
  (forall y, MEM y xs -> FST x > FST y).
Proof.
  intros B HB xs x H. apply SORTED_StronglySorted in H; [|intros; lia].
  apply StronglySorted_inv in H as [H F]. rewrite Forall_forall in F. split; [|split].
  - apply SORTED_Sorted, StronglySorted_Sorted, H.
  - unfold is_true. rewrite MEM_In. intros Hin. specialize (F x Hin). lia.
  - intros y Hy. unfold is_true in Hy. rewrite MEM_In in Hy. apply F, Hy.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_IMP_EQ_LISTS" *)
Theorem SORTED_IMP_EQ_LISTS : forall {B} `{EqDecision B} (xs ys : list (N * B)),
  SORTED (fun x y => FST x > FST y) ys /\
  SORTED (fun x y => FST x > FST y) xs /\
  (forall x, is_true (MEM x ys) <-> is_true (MEM x xs)) ->
  xs = ys.
Proof.
  intros B HB xs ys (H1 & H2 & H3).
  apply SORTED_StronglySorted in H1; [|intros; lia]. apply SORTED_StronglySorted in H2; [|intros; lia].
  assert (H : forall x, In x ys <-> In x xs) by (intros x; rewrite <- !MEM_In; apply H3). clear H3.
  revert ys H1 H. induction xs as [|x xs IH]; intros [|y ys] H1 H.
  - reflexivity.
  - exfalso. apply (H y). left; reflexivity.
  - exfalso. apply (H x). left; reflexivity.
  - apply StronglySorted_inv in H1 as [H1 F1]. apply StronglySorted_inv in H2 as [H2 F2].
    rewrite Forall_forall in F1, F2.
    assert (Exy : x = y).
    { destruct (proj2 (H x) (or_introl eq_refl)) as [E|Hx]; [symmetry; exact E|].
      destruct (proj1 (H y) (or_introl eq_refl)) as [E|Hy]; [exact E|].
      specialize (F1 x Hx). specialize (F2 y Hy). lia. }
    subst y. f_equal. apply IH; [exact H2|exact H1|].
    intros z. split; intros Hz.
    + destruct (proj1 (H z) (or_intror Hz)) as [E|E]; [subst z; specialize (F1 x Hz); lia|exact E].
    + destruct (proj2 (H z) (or_intror Hz)) as [E|E]; [subst z; specialize (F2 x Hz); lia|exact E].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_weaken2" *)
Theorem SORTED_weaken2 : forall {A} `{EqDecision A} (R R' : A -> A -> Prop) (ls : list A),
  SORTED R ls /\ ALL_DISTINCT ls /\
  (forall x y, is_true (MEM x ls) /\ is_true (MEM y ls) /\ x <> y /\ R x y -> R' x y) ->
  SORTED R' ls.
Proof.
  intros A HA R R' ls. induction ls as [|x ls IH]; intros (H1 & H2 & H3); [exact Logic.I|].
  destruct ls as [|y ls]; [exact Logic.I|]. cbn [SORTED] in *. destruct H1 as [Hr H1].
  cbn [ALL_DISTINCT] in H2. unfold is_true in H2. apply andb_true_iff in H2 as [Hn H2].
  split.
  - apply H3. cbn [MEM]. unfold is_true. repeat split.
    + rewrite orb_true_iff. left. apply bool_decide_spec. reflexivity.
    + rewrite !orb_true_iff. right. left. apply bool_decide_spec. reflexivity.
    + intros E. subst y. apply negb_true_iff in Hn. cbn [MEM] in Hn.
      rewrite orb_false_iff in Hn. destruct Hn as [Hn _]. apply bool_decide_false in Hn. apply Hn. reflexivity.
    + exact Hr.
  - apply IH. split; [exact H1|]. split; [exact H2|]. intros u v (Hu & Hv & Huv & R0).
    apply H3. repeat split; try assumption; cbn [MEM]; unfold is_true in *; rewrite orb_true_iff; right; assumption.
Qed.

End SortedLemmas.

(*! HOL "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "transitive_key_val_compare" *)
Theorem transitive_key_val_compare : forall {a},
  relation.transitive (fun x y => is_true (@wordSem.key_val_compare a x y)).
Proof.
  intros a [k1 v1] [k2 v2] [k3 v3] [H1 H2]. unfold wordSem.key_val_compare, is_true in *.
  rewrite !orb_true_iff, !andb_true_iff in *. rewrite !N.ltb_lt, !N.eqb_eq in *.
  destruct H1 as [H1|[-> H1]]; destruct H2 as [H2|[-> H2]]; try (left; lia); right; split; [reflexivity|].
  destruct v1 as [w1|p1 q1], v2 as [w2|p2 q2], v3 as [w3|p3 q3]; try discriminate; try reflexivity.
  - rewrite word_le_Zs in *. apply Z.leb_le in H1, H2. apply Z.leb_le. lia.
  - rewrite !orb_true_iff, !andb_true_iff, !N.ltb_lt, !N.eqb_eq, !N.leb_le in *. lia.
Qed.

(** HOL's [total_key_val_compare] states [total key_val_compare]; [relation$total]
    is not ported, so its definition is unfolded here. *)
Theorem total_key_val_compare : forall {a} (x y : N * word_loc a),
  wordSem.key_val_compare x y \/ wordSem.key_val_compare y x.
Proof.
  intros a [k1 v1] [k2 v2]. unfold wordSem.key_val_compare, is_true.
  destruct (N.lt_trichotomy k1 k2) as [H|[<-|H]].
  - right. apply orb_true_iff. left. apply N.ltb_lt. exact H.
  - rewrite N.ltb_irrefl, N.eqb_refl. cbn [orb andb].
    destruct v1 as [w1|p1 q1], v2 as [w2|p2 q2]; auto.
    + rewrite !word_le_Zs. destruct (Z.le_ge_cases (Zs w1) (Zs w2)); [left|right]; apply Z.leb_le; lia.
    + destruct (N.lt_trichotomy p1 p2) as [H|[<-|H]].
      * right. apply orb_true_iff. left. apply N.ltb_lt. exact H.
      * rewrite N.ltb_irrefl, N.eqb_refl. cbn [orb andb].
        destruct (N.le_ge_cases q1 q2); [right|left]; apply N.leb_le; lia.
      * left. apply orb_true_iff. left. apply N.ltb_lt. exact H.
  - left. apply orb_true_iff. left. apply N.ltb_lt. exact H.
Qed.

Lemma bdf {P : Prop} `{Decision P} : bool_decide P = false -> ~ P.
Proof. intros E Hp. apply (bool_decide_spec P) in Hp. congruence. Qed.

Lemma SS_app {A} (r : A -> A -> Prop) l1 l2 :
  StronglySorted r l1 -> StronglySorted r l2 -> (forall u v, In u l1 -> In v l2 -> r u v) ->
  StronglySorted r (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 H; [exact H2|]. apply StronglySorted_inv in H1 as [H1 F].
  cbn. constructor; [apply IH; auto; intros u v Hu Hv; apply H; [right|]; auto|].
  apply Forall_app; split; [exact F|]. apply Forall_forall. intros v Hv. apply H; [left|]; auto.
Qed.

Section MS.
Context {A : Type} (R : A -> A -> bool) (key : A -> N) (S : list A).
Hypothesis HR : forall x y, In x S -> In y S -> key x <> key y -> (R x y = true <-> key y < key x).

Definition ord (neg : bool) (x y : A) : Prop := if neg then key x < key y else key y < key x.

Fixpoint mergeN (neg : bool) (l1 : list A) : list A -> list A :=
  fix aux (l2 : list A) : list A :=
    match l1, l2 with
    | [], [] => []
    | l, [] => l
    | [], l => l
    | x :: l1', y :: l2' =>
        if bool_decide (R x y <> neg) then x :: mergeN neg l1' (y :: l2') else y :: aux l2'
    end.

Lemma merge_tail_mergeN neg l1 : forall l2 acc,
  merge_tail neg R l1 l2 acc = rev_append (mergeN neg l1 l2) acc.
Proof.
  induction l1 as [|x l1 IH]; intros l2; induction l2 as [|y l2 IH2]; intros acc; try reflexivity.
  cbn [merge_tail mergeN]. destruct (bool_decide (R x y <> neg)).
  - rewrite IH. reflexivity.
  - rewrite IH2. reflexivity.
Qed.

Lemma mergeN_perm neg l1 : forall l2, Permutation (mergeN neg l1 l2) (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2; induction l2 as [|y l2 IH2]; cbn [mergeN app];
    rewrite ?app_nil_r; try reflexivity.
  destruct (bool_decide (R x y <> neg)).
  - constructor. apply IH.
  - rewrite IH2. apply Permutation_middle.
Qed.

Lemma ord_trans neg x y z : ord neg x y -> ord neg y z -> ord neg x z.
Proof. unfold ord; destruct neg; lia. Qed.

Lemma ord_choose neg x y : In x S -> In y S -> key x <> key y ->
  (bool_decide (R x y <> neg) = true -> ord neg x y) /\
  (bool_decide (R x y <> neg) = false -> ord neg y x).
Proof.
  intros Hx Hy Hk. pose proof (HR x y Hx Hy Hk) as H. unfold ord.
  split; intros E; [apply bool_decide_spec in E|apply bdf in E];
    destruct neg, (R x y) eqn:ER; try tauto; try (destruct H as [H1 H2]; specialize (H1 eq_refl); lia);
    try (destruct H as [H1 H2]; assert (~ key y < key x) by (intros C; specialize (H2 C); discriminate); lia).
Qed.

Lemma mergeN_sorted neg l1 : forall l2,
  incl l1 S -> incl l2 S -> NoDup (List.map key (l1 ++ l2)) ->
  StronglySorted (ord neg) l1 -> StronglySorted (ord neg) l2 ->
  StronglySorted (ord neg) (mergeN neg l1 l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2; induction l2 as [|y l2 IH2]; intros H1 H2 Hd S1 S2;
    cbn [mergeN]; rewrite ?app_nil_r in *; auto.
  assert (Hxy : key x <> key y).
  { intros E. rewrite map_app in Hd. cbn in Hd. apply NoDup_cons_iff in Hd as [Hn _].
    apply Hn. apply in_or_app. right. left. auto. }
  destruct (ord_choose neg x y (H1 x (or_introl eq_refl)) (H2 y (or_introl eq_refl)) Hxy) as [C1 C2].
  apply StronglySorted_inv in S1 as [S1 F1]. apply StronglySorted_inv in S2 as [S2 F2].
  destruct (bool_decide (R x y <> neg)) eqn:E.
  - constructor.
    + apply IH; auto.
      * intros z Hz; apply H1; right; exact Hz.
      * cbn in Hd. inversion Hd; assumption.
      * constructor; auto.
    + apply Forall_forall. intros z Hz. apply (Permutation_in _ (mergeN_perm neg l1 (y :: l2))) in Hz.
      apply in_app_or in Hz as [Hz|Hz].
      * rewrite Forall_forall in F1. apply F1, Hz.
      * destruct Hz as [<-|Hz]; [apply C1; reflexivity|].
        rewrite Forall_forall in F2. eapply ord_trans; [apply C1; reflexivity|apply F2, Hz].
  - constructor.
    + apply IH2; auto.
      * intros z Hz; apply H2; right; exact Hz.
      * rewrite map_app in *. cbn in Hd |- *. apply NoDup_cons_iff in Hd as [Hn Hd]. constructor.
        { intros C. apply Hn. apply in_or_app. apply in_app_or in C as [C|C]; [left|right; right]; auto. }
        apply NoDup_remove_1 with (a := key y). exact Hd.
      * constructor; auto.
    + apply Forall_forall. intros z Hz.
      assert (Hz' : In z (x :: l1 ++ l2)).
      { pose proof (mergeN_perm neg (x :: l1) l2) as P. cbn [app] in P.
        cbn [mergeN] in Hz. exact (Permutation_in _ P Hz). }
      destruct Hz' as [<-|Hz'].
      * apply C2. reflexivity.
      * apply in_app_or in Hz' as [Hz'|Hz'].
        -- rewrite Forall_forall in F1. eapply ord_trans; [apply C2; reflexivity|apply F1, Hz'].
        -- rewrite Forall_forall in F2. apply F2, Hz'.
Qed.


Lemma StronglySorted_rev_ord neg l :
  StronglySorted (ord neg) l -> StronglySorted (ord (negb neg)) (rev l).
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. apply StronglySorted_inv in H as [H F].
  cbn [rev]. apply SS_app; [apply IH, H|repeat constructor|].
  intros u v Hu Hv. destruct Hv as [<-|[]]. apply in_rev in Hu. rewrite Forall_forall in F.
  specialize (F u Hu). unfold ord in *. destruct neg; cbn [negb]; lia.
Qed.

Lemma incl_take_drop (l : list A) n m : incl (TAKE n (DROP m l)) (TAKE (m + n) l).
Proof.
  rewrite <- TAKE_DROP_add. intros z Hz. apply in_or_app. right. exact Hz.
Qed.

Lemma msN_sorted : forall fuel negate n l, (N.to_nat n < fuel)%nat ->
  incl (TAKE n l) S -> NoDup (List.map key (TAKE n l)) ->
  StronglySorted (ord negate) (mergesortN_tail_f fuel negate R n l).
Proof.
  induction fuel as [|fuel IH]; intros negate n l hf Hi Hd; [lia|]; cbn [mergesortN_tail_f].
  destruct (N.lt_ge_cases n 4) as [hn|hn].
  - rewrite TAKE_firstn in Hi, Hd.
    assert (h : n = 0 \/ n = 1 \/ n = 2 \/ n = 3) by lia.
    destruct h as [-> | [-> | [-> | ->]]]; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
    + constructor.
    + destruct l; repeat constructor.
    + destruct l as [|x [|y l]]; try (repeat constructor; fail). cbn in Hi, Hd.
      assert (Hxy : key x <> key y) by (intros E; inversion Hd; subst; apply H1; left; auto).
      destruct (ord_choose negate x y (Hi x (or_introl eq_refl)) (Hi y (or_intror (or_introl eq_refl))) Hxy) as [C1 C2].
      unfold sort2_tail. destruct (bool_decide (R x y <> negate)) eqn:E;
        repeat constructor; auto.
    + destruct l as [|x [|y [|z l]]]; try (repeat constructor; fail); cbn in Hi, Hd.
      * assert (Hxy : key x <> key y) by (intros E; inversion Hd; subst; apply H1; left; auto).
        destruct (ord_choose negate x y (Hi x (or_introl eq_refl)) (Hi y (or_intror (or_introl eq_refl))) Hxy) as [C1 C2].
        unfold sort2_tail. destruct (bool_decide (R x y <> negate)) eqn:E; repeat constructor; auto.
      * inversion Hd as [|? ? Hn1 Hd1]; subst. inversion Hd1 as [|? ? Hn2 Hd2]; subst.
        assert (Hxy : key x <> key y) by (intros E; apply Hn1; left; auto).
        assert (Hxz : key x <> key z) by (intros E; apply Hn1; right; left; auto).
        assert (Hyz : key y <> key z) by (intros E; apply Hn2; left; auto).
        assert (Ix : In x S) by (apply Hi; left; auto).
        assert (Iy : In y S) by (apply Hi; right; left; auto).
        assert (Iz : In z S) by (apply Hi; right; right; left; auto).
        destruct (ord_choose negate x y Ix Iy Hxy) as [A1 A2].
        destruct (ord_choose negate y z Iy Iz Hyz) as [B1 B2].
        destruct (ord_choose negate x z Ix Iz Hxz) as [D1 D2].
        unfold sort3_tail.
        destruct (bool_decide (R x y <> negate)) eqn:E1, (bool_decide (R y z <> negate)) eqn:E2,
          (bool_decide (R x z <> negate)) eqn:E3; cbn;
          repeat constructor; auto; eapply ord_trans; eauto.
  - assert (e1 : n DIV 2 < n) by (apply N.div_lt; lia).
    assert (e2 : n - n DIV 2 < n) by (assert (0 < n DIV 2) by (apply N.div_str_pos; lia); lia).
    assert (HT : TAKE n l = TAKE (n DIV 2) l ++ TAKE (n - n DIV 2) (DROP (n DIV 2) l)).
    { rewrite TAKE_DROP_add. f_equal. lia. }
    rewrite HT in Hi, Hd.
    assert (S1 := IH (negb negate) (n DIV 2) l ltac:(lia)
      (fun z Hz => Hi z (in_or_app _ _ _ (or_introl Hz)))
      (NoDup_app_remove_r _ _ ltac:(rewrite <- map_app; exact Hd))).
    assert (S2 := IH (negb negate) (n - n DIV 2) (DROP (n DIV 2) l) ltac:(lia)
      (fun z Hz => Hi z (in_or_app _ _ _ (or_intror Hz)))
      (NoDup_app_remove_l _ _ ltac:(rewrite <- map_app; exact Hd))).
    assert (M : StronglySorted (ord (negb negate))
       (mergeN (negb negate) (mergesortN_tail_f fuel (negb negate) R (n DIV 2) l)
                (mergesortN_tail_f fuel (negb negate) R (n - n DIV 2) (DROP (n DIV 2) l)))).
    { assert (P1 := mergesortN_tail_f_perm fuel (negb negate) R (n DIV 2) l ltac:(lia)).
      assert (P2 := mergesortN_tail_f_perm fuel (negb negate) R (n - n DIV 2) (DROP (n DIV 2) l) ltac:(lia)).
      apply mergeN_sorted; auto.
      - intros z Hz. apply (Permutation_in _ P1) in Hz.
        apply Hi, in_or_app. left. exact Hz.
      - intros z Hz. apply (Permutation_in _ P2) in Hz.
        apply Hi, in_or_app. right. exact Hz.
      - eapply Permutation_NoDup; [|exact Hd]. apply Permutation_map.
        apply Permutation_sym, Permutation_app; assumption. }
    apply StronglySorted_rev_ord in M. rewrite Bool.negb_involutive in M.
    destruct n as [|p]; [lia|].
    destruct p as [[[p|p|]|[p|p|]|]|[[p|p|]|[p|p|]|]|]; try lia;
      cbv zeta; rewrite merge_tail_mergeN, rev_append_rev, app_nil_r; exact M.
Qed.

End MS.


Lemma StronglySorted_SORTED {A} (R R' : A -> A -> Prop) l :
  (forall x y, R x y -> R' x y) -> StronglySorted R l -> SORTED R' l.
Proof.
  intros HR H. induction H as [|x l H IH F]; [exact Logic.I|].
  destruct l as [|y l]; [exact Logic.I|]. cbn [SORTED]. split; [|exact IH].
  apply HR. inversion F; assumption.
Qed.

Lemma mergesort_tail_sorted {A} (R : A -> A -> bool) (key : A -> N) (l : list A) :
  (forall x y, In x l -> In y l -> key x <> key y -> (R x y = true <-> key y < key x)) ->
  NoDup (List.map key l) ->
  StronglySorted (ord key false) (mergesort_tail R l).
Proof.
  intros HR Hd. unfold mergesort_tail, mergesortN_tail.
  apply (msN_sorted R key l HR); [lia| |]; rewrite TAKE_firstn, LENGTH_length, Nat2N.id, firstn_all.
  - intros z Hz; exact Hz.
  - exact Hd.
Qed.

(** HOL's [env_to_list_K_I_IMP] with Rocq's [Permutation] for HOL's [PERM]
    (not ported); hence untagged. *)
Lemma env_to_list_K_I_IMP {a} (env : num_map (word_loc a)) l oracle :
  wordSem.env_to_list env (K I) = (l, oracle) ->
  SORTED (fun x y => FST x > FST y) l /\ oracle = K I /\ Permutation (toAList env) l.
Proof.
  intros E. unfold wordSem.env_to_list in E. cbv zeta in E. injection E as El Eo.
  replace (K I 0) with (@I N) in El by reflexivity. rewrite list_rearrange_I in El. unfold I in El.
  subst l oracle. split; [|split].
  - eapply StronglySorted_SORTED; [|apply (mergesort_tail_sorted _ FST)].
    + intros x y H. unfold ord in H. lia.
    + intros [k1 v1] [k2 v2] _ _ Hk. cbn [FST fst] in *. unfold wordSem.key_val_compare.
      replace (k1 =? k2) with false by (symmetry; apply N.eqb_neq; exact Hk).
      rewrite andb_false_l, orb_false_r. apply N.ltb_lt.
    + pose proof (ALL_DISTINCT_MAP_FST_toAList env) as Hd. unfold is_true in Hd.
      rewrite ALL_DISTINCT_NoDup_list in Hd. exact Hd.
  - apply functional_extensionality. intros n. reflexivity.
  - symmetry. apply mergesort_tail_perm.
Qed.
