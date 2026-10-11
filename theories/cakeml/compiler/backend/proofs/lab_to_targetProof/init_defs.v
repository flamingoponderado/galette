(** * CakeML [lab_to_targetProof]: the initial state and shared-memory information

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 9596-10133): [set_bytes], [make_word], [make_init],
    [compiler_oracle_ok], [mc_conf_ok], and the description of
    [get_shmem_info] through [line_to_info] with its consequences.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [make_init] is generic in the type [c] of compiler configurations
      (HOL's ['c]).
    - [MEM_get_shmem_info] states membership with [In] ([shmem_info_num]
      has no decidable equality, which [MEM] needs).
    - [asm_fetch_NOT_ffi_entry_pcs]: HOL's free variable [ffi_names] (an
      argument of [all_enc_ok]) is [ffis], [ffi_names] being the field of
      the machine configuration here.
    - HOL's record updates [rec with <|entry_pc := ..; exit_pc := ..|>] are
      written as full records.
    - Not ported: the ML binding [IMP_LEMMA] (an ML theorem used to build
      [semantics_make_init]). *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.num.extra_theories Require Import bit.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.relation Require Import relation.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.HOL.src.coalgebras Require Import llist.
From Galette.HOL.examples.pl_semantics.lprefix_lub Require Import lprefix_lub.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.semantics.proofs Require Import evaluateProps.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target.
From Galette.cakeml.compiler.backend Require wordLang.
From Galette.cakeml.compiler.backend.semantics Require wordSem backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs Require lab_filterProof.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes inst compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute rl_remove
  code_props pos_props shmem cc_setup cc_asm cc_jump cc_ffi cc_install cc_share compile_correct
  sem_machine.
Import wordLang (word_loc, Word, Loc).
Import wordSem (mem_load_byte_aux, mem_store_byte_aux, write_bytearray, mem_load_32,
  mem_store_32, buffer, position, buffer_buffer, space_left).
Import ByteBits.
Open Scope N_scope.




Section MakeInit.
Context {a : N} {B C Ffi : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "set_bytes_def" *)
Fixpoint set_bytes (a0 : word a) (be : bool) (l : list word8) : word a :=
  match l with
  | [] => n2w 0
  | b :: bs => byte.set_byte a0 b (set_bytes (a0 + n2w 1)%w be bs) be
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_word_def" *)
Definition make_word (be : bool) (m : word a -> word8) (a0 : word a) : word_loc a :=
  if dimindex a =? 32 then
    Word (set_bytes a0 be [m a0; m (a0 + n2w 1)%w; m (a0 + n2w 2)%w; m (a0 + n2w 3)%w])
  else
    Word (set_bytes a0 be [m a0; m (a0 + n2w 1)%w; m (a0 + n2w 2)%w; m (a0 + n2w 3)%w;
                           m (a0 + n2w 4)%w; m (a0 + n2w 5)%w; m (a0 + n2w 6)%w; m (a0 + n2w 7)%w]).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_init_def" *)
Definition make_init {c} (mc_conf : machine_config a B C) (ffi : ffi_state Ffi) (t : asm_state a)
    (m : word a -> word_loc a) (dm sdm : word a -> Prop) (ms : B) (code : list (sec a))
    (comp : c -> list (sec a) -> option (list word8 * c)) (cbpos : word a) (cbspace : N)
    (coracle : N -> c * list (sec a)) : labSem.state a c Ffi :=
  mk_state (fun k => Word (asmSem.regs t k)) (asmSem.fp_regs t) m dm sdm 0
    (big_endian (asmProps.config mc_conf.(target))) ffi
    (target_io_regs mc_conf ffi ms) (target_cc_regs mc_conf ffi ms)
    (target_io_fp_regs mc_conf ffi ms) (target_cc_fp_regs mc_conf ffi ms)
    code comp coracle (wordSem.mk_buffer cbpos [] cbspace) 0 false
    mc_conf.(targetSem.ptr_reg) mc_conf.(targetSem.len_reg)
    mc_conf.(targetSem.ptr2_reg) mc_conf.(targetSem.len2_reg)
    (match asm.link_reg (asmProps.config mc_conf.(target)) with SOME n => n | NONE => 0 end).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_make_init" *)
Theorem oracle_tie_make_init : forall {c} (mc_conf : machine_config a B C) ms ffi t m dm sdm code
    (cmp : c -> list (sec a) -> option (list word8 * c)) cbpos cbspace coracle,
  oracle_tie mc_conf ms (make_init mc_conf ffi t m dm sdm ms code cmp cbpos cbspace coracle).
Proof. intros. unfold oracle_tie, make_init. repeat split. Qed.

End MakeInit.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "compiler_oracle_ok_def" *)
Definition compiler_oracle_ok {a} (coracle : N -> config * list (sec a)) (init_labs : spt (spt N))
    (init_pos : N) (c : asm_config a) (ffis : list ffiname) : Prop :=
  (forall k, let '(cfg, code) := coracle k in
             good_code c cfg.(labels) code /\ no_share_mem_inst code) /\
  (let '(cfg, code) := coracle 0 in
   cfg.(labels) = init_labs /\
   cfg.(pos) = init_pos /\
   cfg.(lab_to_target.ffi_names) = SOME ffis).

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "mc_conf_ok_def" *)
Definition mc_conf_ok {a B C} (mc_conf : machine_config a B C) : Prop :=
  good_dimindex a /\
  encoder_correct mc_conf.(target) /\
  reg_ok mc_conf.(targetSem.ptr_reg) (asmProps.config mc_conf.(target)) /\
  reg_ok mc_conf.(targetSem.len_reg) (asmProps.config mc_conf.(target)) /\
  reg_ok mc_conf.(targetSem.ptr2_reg) (asmProps.config mc_conf.(target)) /\
  reg_ok mc_conf.(targetSem.len2_reg) (asmProps.config mc_conf.(target)) /\
  reg_ok (match asm.link_reg (asmProps.config mc_conf.(target)) with NONE => 0 | SOME n => n end)
    (asmProps.config mc_conf.(target)) /\
  enc_ok (asmProps.config mc_conf.(target)).

Section ShmemInfo.
Context {a : N}.

(** One step of [get_shmem_info] on a line (Galette helper). *)
Definition shmem_rec (pos : N) (m : memop) (r : N) (ad : asm.addr a) (bytes : list word8) : shmem_info_num :=
  {| entry_pc := pos;
     nbytes := snd (get_memop_info m);
     addr_reg := match ad with Addr r off => r end;
     addr_off := match ad with Addr r off => w2n off end;
     reg := r;
     exit_pc := pos + LENGTH bytes |}.

Lemma get_shmem_info_step k (y : line a) ys xs pos fn info :
  get_shmem_info (Section_ k (y :: ys) :: xs) pos fn info =
  match y with
  | Label _ _ _ => get_shmem_info (Section_ k ys :: xs) pos fn info
  | Asm (ShareMem m r ad) bytes _ =>
      get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes)
        (fn ++ [SharedMem (fst (get_memop_info m))]) (info ++ [shmem_rec pos m r ad bytes])
  | Asm _ bytes _ => get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes) fn info
  | LabAsm _ _ bytes _ => get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes) fn info
  end.
Proof.
  destruct y as [| [i|r1 r2|m r ad] bytes l|]; try reflexivity.
  change (get_shmem_info (Section_ k (Asm (ShareMem m r ad) bytes l :: ys) :: xs) pos fn info)
    with (let '(name, nb) := get_memop_info m in
          get_shmem_info (Section_ k ys :: xs) (pos + LENGTH bytes)
            (fn ++ [SharedMem name])
            (info ++
             [{| entry_pc := pos;
                 nbytes := nb;
                 addr_reg := match ad with Addr r off => r end;
                 addr_off := match ad with Addr r off => w2n off end;
                 reg := r;
                 exit_pc := pos + LENGTH bytes |}])).
  unfold shmem_rec. destruct (get_memop_info m); reflexivity.
Qed.

Lemma get_shmem_info_acc : forall (secs : list (sec a)) pos f1 f2 i1 i2,
  get_shmem_info secs pos (f1 ++ f2) (i1 ++ i2) =
  (f1 ++ fst (get_shmem_info secs pos f2 i2), i1 ++ snd (get_shmem_info secs pos f2 i2)).
Proof.
  intros secs. induction secs as [|k ys IH|k y ys xs IH] using code_ind; intros pos f1 f2 i1 i2.
  - reflexivity.
  - exact (IH pos f1 f2 i1 i2).
  - rewrite !get_shmem_info_step.
    destruct y as [| [i|r1 r2|m r ad] bytes l|]; try apply IH.
    rewrite <- !app_assoc. apply IH.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_APPEND" *)
Theorem get_shmem_info_APPEND : forall (secs : list (sec a)) pos ffi_names (shmem_info : list shmem_info_num)
    ffis1 ffis2 info1 info2 new_ffi_names new_shmem_info,
  get_shmem_info secs pos ffi_names shmem_info = (new_ffi_names, new_shmem_info) /\
  ffi_names = ffis1 ++ ffis2 /\
  shmem_info = info1 ++ info2 ->
  new_ffi_names = ffis1 ++ FST (get_shmem_info secs pos ffis2 info2) /\
  new_shmem_info = info1 ++ SND (get_shmem_info secs pos ffis2 info2).
Proof.
  intros secs pos ffi_names shmem_info ffis1 ffis2 info1 info2 nf ns (H & -> & ->).
  rewrite get_shmem_info_acc in H. injection H as <- <-. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_PREPEND" *)
Theorem get_shmem_info_PREPEND : forall (secs : list (sec a)) pos ffi_names (shmem_info : list shmem_info_num)
    new_ffi_names new_shmem_info,
  get_shmem_info secs pos ffi_names shmem_info = (new_ffi_names, new_shmem_info) ->
  new_ffi_names = ffi_names ++ FST (get_shmem_info secs pos [] []) /\
  new_shmem_info = shmem_info ++ SND (get_shmem_info secs pos [] []).
Proof.
  intros secs pos fn si nf ns H. apply (get_shmem_info_APPEND secs pos fn si fn [] si [] nf ns).
  rewrite !app_nil_r. auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_to_info_def" *)
Definition line_to_info (secs : list (sec a)) (p : N) (x : N * option (line a))
    : list (ffiname * shmem_info_num) :=
  match SND x with
  | SOME (Asm (ShareMem m r ad) bytes l) =>
      let '(name, nb) := get_memop_info m in
      [(SharedMem name,
        {| entry_pc := pos_val (FST x) p secs;
           nbytes := nb;
           addr_reg := match ad with Addr r off => r end;
           addr_off := match ad with Addr r off => w2n off end;
           reg := r;
           exit_pc := pos_val (FST x) p secs + LENGTH bytes |})]
  | _ => []
  end.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_to_info_next" *)
Theorem line_to_info_next : forall k1 a1 b bytes1 len1 xs1 rest1 p1 i1 l1
    k2 c2 bytes2 len2 xs2 rest2 p2 i2 l2,
  line_to_info (Section_ k1 (LabAsm a1 b bytes1 len1 :: xs1) :: rest1) p1 (i1 + 1, l1) =
    line_to_info (Section_ k1 xs1 :: rest1) (p1 + LENGTH bytes1) (i1, l1) /\
  line_to_info (Section_ k2 (Asm c2 bytes2 len2 :: xs2) :: rest2) p2 (i2 + 1, l2) =
    line_to_info (Section_ k2 xs2 :: rest2) (p2 + LENGTH bytes2) (i2, l2).
Proof.
  intros. unfold line_to_info. cbn [SND snd FST fst].
  rewrite !(proj2 (proj2 (pos_val_def _ _ _ _ _ _))). cbn [is_Label line_length].
  rewrite !(proj2 (N.eqb_neq _ _)) by lia. rewrite !N.add_sub. split; reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_to_info_hd_empty" *)
Theorem line_to_info_hd_empty : forall k rest p t,
  line_to_info (Section_ k [] :: rest) p t = line_to_info rest p t.
Proof. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_to_info_hd_Label" *)
Theorem line_to_info_hd_Label : forall k a0 b xs rest p t,
  line_to_info (Section_ k (Label a0 b 0 :: xs) :: rest) p t =
  line_to_info (Section_ k xs :: rest) p t.
Proof.
  intros. unfold line_to_info. rewrite !(proj2 (proj2 (pos_val_def _ _ _ _ _ _))).
  cbn [is_Label line_length N.eqb]. rewrite N.add_0_r. reflexivity.
Qed.

Lemma UNZIP_MAP {X Y} (l : list (X * Y)) : UNZIP l = (MAP fst l, MAP snd l).
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [UNZIP MAP map]. rewrite IH. reflexivity. Qed.

(** The shared-memory entries of a program (Galette helper). *)
Definition shmem_entries (secs : list (sec a)) (p : N) : list (ffiname * shmem_info_num) :=
  FLAT (MAP (line_to_info secs p) (GENLIST (fun i => (i, asm_fetch_aux i secs)) (num_pcs secs))).

Lemma map_ext_in_gen {X Y} (f g : X -> Y) l : (forall x, In x l -> f x = g x) -> MAP f l = MAP g l.
Proof. apply List.map_ext_in. Qed.

Lemma shmem_entries_thm : forall c labs ffis (secs : list (sec a)) p fn info p',
  all_enc_ok c labs ffis p' secs ->
  get_shmem_info secs p fn info =
  (fn ++ MAP fst (shmem_entries secs p), info ++ MAP snd (shmem_entries secs p)).
Proof.
  intros c labs ffis secs. induction secs as [|k ys IH|k y ys xs IH] using code_ind;
    intros p fn info p' H.
  - unfold shmem_entries. cbn. rewrite !app_nil_r. reflexivity.
  - destruct H as [_ H]. exact (IH p fn info p' H).
  - destruct H as [Hy H]. rewrite get_shmem_info_step. unfold shmem_entries.
    destruct (is_Label y) eqn:Hl.
    + destruct y as [l1 l2 len| |]; try discriminate. destruct Hy as [_ ->].
      rewrite (IH p fn info _ H). unfold shmem_entries.
      change (num_pcs (Section_ k (Label l1 l2 0 :: ys) :: xs)) with (num_pcs (Section_ k ys :: xs)).
      assert (Eg : GENLIST (fun i => (i, asm_fetch_aux i (Section_ k (Label l1 l2 0 :: ys) :: xs)))
                     (num_pcs (Section_ k ys :: xs)) =
                   GENLIST (fun i => (i, asm_fetch_aux i (Section_ k ys :: xs))) (num_pcs (Section_ k ys :: xs)))
        by reflexivity.
      rewrite Eg. rewrite (map_ext_in_gen (line_to_info (Section_ k (Label l1 l2 0 :: ys) :: xs) p)
                             (line_to_info (Section_ k ys :: xs) p)) by (intros x _; apply line_to_info_hd_Label).
      reflexivity.
    + assert (Hnl : ~ is_Label y) by (rewrite Hl; discriminate).
      set (tail := Section_ k ys :: xs).
      assert (En : num_pcs (Section_ k (y :: ys) :: xs) = num_pcs tail + 1).
      { unfold tail. rewrite (proj2 (proj2 (num_pcs_def k y ys xs))), Hl. lia. }
      rewrite En, GENLIST_asm_fetch_aux_next by exact Hnl.
      cbn [MAP map FLAT concat].
      rewrite MAP_GENLIST_aux.
      assert (Hlen : line_length y = LENGTH (line_bytes y)).
      { destruct y; [discriminate|reflexivity|reflexivity]. }
      assert (Enext : forall i, line_to_info (Section_ k (y :: ys) :: xs) p (i + 1, asm_fetch_aux i tail) =
                                line_to_info tail (p + LENGTH (line_bytes y)) (i, asm_fetch_aux i tail)).
      { intros i. unfold line_to_info. cbn [SND snd FST fst].
        rewrite (proj2 (proj2 (pos_val_def _ _ k xs y ys))), Hl.
        rewrite (proj2 (N.eqb_neq _ _)) by lia. rewrite N.add_sub, Hlen. reflexivity. }
      rewrite (GENLIST_ext_lt _ (fun i => line_to_info tail (p + LENGTH (line_bytes y)) (i, asm_fetch_aux i tail)))
        by (intros i _; apply Enext).
      rewrite <- (MAP_GENLIST_aux (line_to_info tail (p + LENGTH (line_bytes y)))).
      fold (shmem_entries tail (p + LENGTH (line_bytes y))).
      assert (Ehd : line_to_info (Section_ k (y :: ys) :: xs) p (0, SOME y) =
                    match y with
                    | Asm (ShareMem m r ad) bytes _ => [(SharedMem (fst (get_memop_info m)), shmem_rec p m r ad bytes)]
                    | _ => []
                    end).
      { unfold line_to_info. cbn [SND snd FST fst]. rewrite (proj2 (proj2 (pos_val_def _ _ _ _ _ _))), Hl.
        cbn [N.eqb]. destruct y as [| [i|r1 r2|m r ad] bytes l|]; try reflexivity; try discriminate.
        unfold shmem_rec. destruct (get_memop_info m); reflexivity. }
      rewrite Ehd.
      destruct y as [| [i|r1 r2|m r ad] bytes l|x w bytes l]; try discriminate;
        cbn [line_bytes line_length] in *;
        (rewrite (IH _ _ _ (p' + LENGTH bytes) H); cbn [app MAP map]; rewrite <- ?app_assoc; reflexivity).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_thm" *)
Theorem get_shmem_info_thm : forall c labs ffis (secs : list (sec a)) p ffi_names shmem_info p',
  all_enc_ok c labs ffis p' secs ->
  get_shmem_info secs p ffi_names shmem_info =
    let '(new_ffis, new_info) :=
      UNZIP (FLAT (MAP (line_to_info secs p)
                     (GENLIST (fun i => (i, asm_fetch_aux i secs)) (num_pcs secs)))) in
    (ffi_names ++ new_ffis, shmem_info ++ new_info).
Proof.
  intros c labs ffis secs p fn info p' H. rewrite (shmem_entries_thm c labs ffis secs p fn info p' H).
  rewrite UNZIP_MAP. reflexivity.
Qed.

End ShmemInfo.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "FILTER_NOT_MEM_Mapped" *)
Theorem FILTER_NOT_MEM_Mapped : forall l : list string,
  ~ MEM "MappedRead"%hstring
      (FILTER (fun x => ⌜x <> "MappedRead"%hstring /\ x <> "MappedWrite"%hstring⌝) l) /\
  ~ MEM "MappedWrite"%hstring
      (FILTER (fun x => ⌜x <> "MappedRead"%hstring /\ x <> "MappedWrite"%hstring⌝) l).
Proof.
  intros l. split; intros H; unfold is_true in H; rewrite MEM_In, filter_In in H;
    destruct H as [_ H]; apply bool_decide_spec in H; tauto.
Qed.

Lemma FILTER_EVERY_id {X} (P : X -> bool) l : EVERY P l -> FILTER P l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn [EVERY] in H.
  apply Bool.andb_true_iff in H as [H1 H2]. cbn [filter]. rewrite H1, IH by exact H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "mmio_pcs_min_index_APPEND_thm" *)
Theorem mmio_pcs_min_index_APPEND_thm : forall (l ffis : list ffiname),
  EVERY (fun x => ⌜forall s, x <> ExtCall s⌝) l /\
  EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis ->
  mmio_pcs_min_index (ffis ++ l) = SOME (LENGTH ffis).
Proof.
  intros l ffis [Hl Hf].
  pose proof (FILTER_mmio_pcs_min_index l ffis) as X.
  rewrite (FILTER_EVERY_id _ ffis Hf) in X. apply X.
  unfold is_true in *. rewrite EVERY_Forall, List.Forall_forall in *. intros x Hx.
  apply (proj2 (bool_decide_spec _)). apply (proj2 (Sh_not_Ext x)). apply (proj1 (bool_decide_spec _)), Hl, Hx.
Qed.

Section ShmemInfo2.
Context {a : N}.

Lemma ZIP_MAP_fst_snd {X Y} (l : list (X * Y)) : ZIP (MAP fst l, MAP snd l) = l.
Proof. induction l as [|[x y] l IH]; [reflexivity|]. cbn [MAP map]. unfold ZIP in *. cbn [fst snd]. cbn. f_equal. exact IH. Qed.

Lemma In_GENLIST {X} (f : N -> X) n i : i < n -> In (f i) (GENLIST f n).
Proof.
  revert i. induction n as [|n IH] using N.peano_ind; intros i Hi; [lia|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app. apply in_app_iff.
  destruct (N.eq_dec i n) as [->|Hne]; [right; left; reflexivity|left; apply IH; lia].
Qed.

Lemma In_GENLIST_inv {X} (f : N -> X) n x : In x (GENLIST f n) -> exists i, i < n /\ x = f i.
Proof.
  induction n as [|n IH] using N.peano_ind; intros H; [contradiction|].
  rewrite (proj2 (GENLIST_thm f n)), SNOC_app in H. apply in_app_iff in H as [H|[<-|[]]].
  - destruct (IH H) as (i & Hi & ->). exists i. split; [lia|reflexivity].
  - exists n. split; [lia|reflexivity].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "MEM_get_shmem_info" *)
Theorem MEM_get_shmem_info : forall c labs ffis p' (code2 : list (sec a)) pc op re a0 inst' len q r p,
  all_enc_ok c labs ffis p' code2 /\
  asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a0) inst' len) /\
  get_memop_info op = (q, r) ->
  In (SharedMem q,
      {| entry_pc := pos_val pc p code2;
         nbytes := r;
         addr_reg := match a0 with Addr r0 off => r0 end;
         addr_off := match a0 with Addr r0 off => w2n off end;
         reg := re;
         exit_pc := pos_val pc (p + LENGTH inst') code2 |})
    (ZIP (get_shmem_info code2 p [] [])).
Proof.
  intros c labs ffis p' code2 pc op re a0 inst' len q r p (Hok & Hf & Hm).
  rewrite (shmem_entries_thm c labs ffis code2 p [] [] p' Hok). cbn [app]. rewrite ZIP_MAP_fst_snd.
  unfold shmem_entries. apply in_concat.
  exists (line_to_info code2 p (pc, asm_fetch_aux pc code2)). split.
  - apply in_map. apply (In_GENLIST (fun i => (i, asm_fetch_aux i code2))).
    exact (asm_fetch_SOME_IMP_LESS_num_pcs _ _ _ Hf).
  - unfold line_to_info. cbn [SND snd FST fst]. rewrite Hf, Hm. left.
    rewrite <- (pos_val_acc_sum pc (p + LENGTH inst') code2 (LENGTH inst') p) by lia.
    rewrite (N.add_comm (LENGTH inst')). reflexivity.
Qed.

End ShmemInfo2.

Section ShmemInfo3.
Context {a : N}.

Lemma EL_MAP_lt {X Y} `{Inhabited X} `{Inhabited Y} (f : X -> Y) n (l : list X) :
  n < LENGTH l -> EL n (MAP f l) = f (EL n l).
Proof.
  revert n; induction l as [|x l IH]; intros n Hn; cbn [LENGTH] in Hn; [lia|].
  destruct (N.zero_or_succ n) as [->|[m ->]]; [reflexivity|].
  cbn [MAP map]. rewrite !EL_cons_succ. apply IH. lia.
Qed.

Lemma LENGTH_MAP' {X Y} (f : X -> Y) l : LENGTH (MAP f l) = LENGTH l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [MAP map LENGTH]. rewrite IH. reflexivity. Qed.

Lemma find_index_NoDup {X} `{EqDecision X} `{Inhabited X} (l : list X) j k :
  NoDup l -> j < LENGTH l -> find_index (EL j l) l k = SOME (k + j).
Proof.
  revert j k. induction l as [|x l IH]; intros j k Hnd Hj; cbn [LENGTH] in Hj; [lia|].
  inversion Hnd as [|? ? Hx Hnd']; subst. cbn [find_index].
  destruct (N.zero_or_succ j) as [->|[m ->]].
  - cbn [EL]. change (EL 0 (x :: l)) with x. destruct (decide (x = x)); [f_equal; lia|congruence].
  - rewrite EL_cons_succ. destruct (decide (x = EL m l)) as [E|].
    + exfalso. apply Hx. rewrite E. apply EL_In_lt. lia.
    + rewrite IH by (auto; lia). f_equal. lia.
Qed.

(** The entry addresses of [shmem_entries] (Galette helper). *)
Lemma shmem_entries_entry (code2 : list (sec a)) p x :
  In x (shmem_entries code2 p) ->
  exists j op re a0 bytes len,
    asm_fetch_aux j code2 = SOME (Asm (ShareMem op re a0) bytes len) /\
    j < num_pcs code2 /\
    x = (SharedMem (fst (get_memop_info op)),
         {| entry_pc := pos_val j p code2;
            nbytes := snd (get_memop_info op);
            addr_reg := match a0 with Addr r0 off => r0 end;
            addr_off := match a0 with Addr r0 off => w2n off end;
            reg := re;
            exit_pc := pos_val j p code2 + LENGTH bytes |}).
Proof.
  unfold shmem_entries. intros H. apply in_concat in H as (l & Hl & Hx).
  apply in_map_iff in Hl as ([j o] & <- & Hj). apply In_GENLIST_inv in Hj as (i & Hi & E).
  injection E as -> ->. unfold line_to_info in Hx. cbn [SND snd FST fst] in Hx.
  destruct (asm_fetch_aux i code2) as [[| [ii|r1 r2|op re a0] bytes len|]|] eqn:Ef; try contradiction.
  destruct (get_memop_info op) as [q r] eqn:Em. destruct Hx as [<-|[]].
  exists i, op, re, a0, bytes, len. rewrite Em. auto.
Qed.

Lemma shmem_entries_sorted c labs ffis p' (code2 : list (sec a)) p :
  all_enc_ok c labs ffis p' code2 -> enc_ok c ->
  NoDup (MAP (fun x => entry_pc (snd x)) (shmem_entries code2 p)).
Proof.
  intros Hok Hc. unfold shmem_entries.
  assert (G : forall n, n <= num_pcs code2 ->
    NoDup (MAP (fun x => entry_pc (snd x))
             (FLAT (MAP (line_to_info code2 p) (GENLIST (fun i => (i, asm_fetch_aux i code2)) n)))) /\
    (forall x, In x (FLAT (MAP (line_to_info code2 p) (GENLIST (fun i => (i, asm_fetch_aux i code2)) n))) ->
       entry_pc (snd x) < pos_val n p code2 \/ n = 0)).
  { intros n. induction n as [|n IH] using N.peano_ind; intros Hn.
    - split; [constructor|]. intros x []. 
    - destruct (IH ltac:(lia)) as [IH1 IH2].
      rewrite (proj2 (GENLIST_thm _ n)), SNOC_app, map_app, concat_app, map_app. cbn [MAP map FLAT concat].
      rewrite app_nil_r.
      assert (Hl : forall y, In y (line_to_info code2 p (n, asm_fetch_aux n code2)) ->
                     entry_pc (snd y) = pos_val n p code2).
      { intros y Hy. unfold line_to_info in Hy. cbn [SND snd FST fst] in Hy.
        destruct (asm_fetch_aux n code2) as [[| [ii|r1 r2|op re a0] bytes len|]|]; try contradiction.
        destruct (get_memop_info op). destruct Hy as [<-|[]]. reflexivity. }
      assert (Hlt : forall x, In x (FLAT (MAP (line_to_info code2 p) (GENLIST (fun i => (i, asm_fetch_aux i code2)) n))) ->
                      entry_pc (snd x) < pos_val n p code2).
      { intros x Hx. destruct (IH2 x Hx) as [H| ->]; [exact H|exfalso].
        rewrite (proj1 (GENLIST_thm _ 0)) in Hx. exact Hx. }
      split.
      + apply NoDup_app; [exact IH1| |].
        * unfold line_to_info. cbn [SND snd FST fst].
          destruct (asm_fetch_aux n code2) as [[| [ii|r1 r2|op re a0] bytes len|]|]; try constructor.
          destruct (get_memop_info op). cbn. constructor; [intros []|constructor].
        * intros y Hy1 Hy2. apply in_map_iff in Hy1 as (x1 & <- & Hx1). apply in_map_iff in Hy2 as (x2 & E & Hx2).
          pose proof (Hlt _ Hx1). rewrite (Hl _ Hx2) in E. lia.
      + intros x Hx. left. apply in_app_iff in Hx as [Hx|Hx].
        * pose proof (Hlt _ Hx). pose proof (pos_val_mono n p code2 (N.succ n) p' c labs ffis
                                    (conj (N.lt_succ_diag_r n) (conj Hn (conj Hok Hc)))). lia.
        * rewrite (Hl _ Hx). exact (pos_val_mono n p code2 (N.succ n) p' c labs ffis
                                    (conj (N.lt_succ_diag_r n) (conj Hn (conj Hok Hc)))). }
  apply (proj1 (G (num_pcs code2) (N.le_refl _))).
Qed.

End ShmemInfo3.

Section ShmemInfo4.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_ALL_DISTINCT" *)
Theorem get_shmem_info_ALL_DISTINCT : forall c labs ffis p' (code2 : list (sec a)) p,
  LENGTH (prog_to_bytes code2) < dimword a /\
  enc_ok c /\
  all_enc_ok c labs ffis p' code2 ->
  ALL_DISTINCT (MAP (fun rec => entry_pc rec) (SND (get_shmem_info code2 p [] []))).
Proof.
  intros c labs ffis p' code2 p (_ & Hc & Hok). rewrite (shmem_entries_thm c labs ffis code2 p [] [] p' Hok).
  cbn [SND snd app]. rewrite map_map. apply ALL_DISTINCT_NoDup_list.
  exact (shmem_entries_sorted c labs ffis p' code2 p Hok Hc).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_EMPTY_LENGTH_EQ" *)
Theorem get_shmem_info_EMPTY_LENGTH_EQ : forall c labs ffis p' (code2 : list (sec a)) p,
  all_enc_ok c labs ffis p' code2 ->
  LENGTH (FST (get_shmem_info code2 p [] [])) = LENGTH (SND (get_shmem_info code2 p [] [])).
Proof.
  intros c labs ffis p' code2 p Hok. rewrite (shmem_entries_thm c labs ffis code2 p [] [] p' Hok).
  cbn [FST SND fst snd app]. rewrite !LENGTH_MAP'. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_to_info_offset_FST_eq" *)
Theorem line_to_info_offset_FST_eq : forall (code : list (sec a)) p accum,
  MAP FST (line_to_info code p accum) = MAP FST (line_to_info code 0 accum).
Proof.
  intros code p [i o]. unfold line_to_info. cbn [SND snd FST fst].
  destruct o as [[| [ii|r1 r2|op re a0] bytes len|]|]; try reflexivity.
  destruct (get_memop_info op); reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_to_info_offset_SND_eq" *)
Theorem line_to_info_offset_SND_eq : forall (code : list (sec a)) p accum,
  MAP SND (line_to_info code p accum) =
  MAP (fun x => {| entry_pc := p + entry_pc (SND x); nbytes := nbytes (SND x);
                   addr_reg := addr_reg (SND x); addr_off := addr_off (SND x);
                   reg := reg (SND x); exit_pc := p + exit_pc (SND x) |})
    (line_to_info code 0 accum).
Proof.
  intros code p [i o]. unfold line_to_info. cbn [SND snd FST fst].
  destruct o as [[| [ii|r1 r2|op re a0] bytes len|]|]; try reflexivity.
  destruct (get_memop_info op). cbn. rewrite <- (pos_val_acc_0 i p code). do 2 f_equal; lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_init_pc_offset" *)
Theorem get_shmem_info_init_pc_offset : forall c labs ffis p' (code : list (sec a)) p,
  all_enc_ok c labs ffis p' code ->
  FST (get_shmem_info code 0 [] []) = FST (get_shmem_info code p [] []) /\
  MAP (fun rec => {| entry_pc := p + entry_pc rec; nbytes := nbytes rec; addr_reg := addr_reg rec;
                     addr_off := addr_off rec; reg := reg rec; exit_pc := p + exit_pc rec |})
    (SND (get_shmem_info code 0 [] [])) =
  SND (get_shmem_info code p [] []).
Proof.
  intros c labs ffis p' code p Hok.
  rewrite !(shmem_entries_thm c labs ffis code _ [] [] p' Hok). cbn [FST SND fst snd app].
  unfold shmem_entries. rewrite !concat_map, !map_map. split.
  - f_equal. apply map_ext. intros x. symmetry. apply line_to_info_offset_FST_eq.
  - f_equal. apply map_ext. intros x.
    rewrite (line_to_info_offset_SND_eq code p x), !map_map. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "mmio_pcs_min_index_get_shmem_info_ok" *)
Theorem mmio_pcs_min_index_get_shmem_info_ok : forall c labs ffis' p' (code2 : list (sec a)) p ffis
    new_ffi_names new_shmem_info,
  all_enc_ok c labs ffis' p' code2 /\
  enc_ok c /\ EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis /\
  get_shmem_info code2 p ffis [] = (new_ffi_names, new_shmem_info) ->
  mmio_pcs_min_index new_ffi_names = SOME (LENGTH ffis).
Proof.
  intros c labs ffis' p' code2 p ffis nf ns (_ & _ & He & H).
  destruct (get_shmem_info_PREPEND _ _ _ _ _ _ H) as [-> _].
  destruct (get_shmem_info code2 p [] []) as [f0 i0] eqn:E0.
  destruct (get_shmem_info_MappedRead_or_MappedWrite code2 p [] [] f0 i0 E0) as (l & -> & Hl).
  cbn [FST fst app]. apply mmio_pcs_min_index_APPEND_thm. split; [|exact He].
  unfold is_true in *. rewrite EVERY_Forall, List.Forall_forall in *. intros x Hx.
  apply (proj2 (bool_decide_spec _)). apply (proj1 (Sh_not_Ext x)). apply (proj1 (bool_decide_spec _)), Hl, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "genlist_line_to_info_entry_pc_max" *)
Theorem genlist_line_to_info_entry_pc_max : forall c labs ffis p' (code2 : list (sec a)),
  all_enc_ok c labs ffis p' code2 /\ enc_ok c ->
  EVERY (fun x => ⌜entry_pc (SND x) < pos_val (num_pcs code2) 0 code2⌝)
    (FLAT (GENLIST (fun i => line_to_info code2 0 (i, asm_fetch_aux i code2)) (num_pcs code2))).
Proof.
  intros c labs ffis p' code2 (Hok & Hc).
  rewrite <- (MAP_GENLIST_aux (line_to_info code2 0)). fold (shmem_entries code2 0).
  unfold is_true. rewrite EVERY_Forall, List.Forall_forall. intros x Hx.
  apply bool_decide_spec. apply shmem_entries_entry in Hx as (j & op & re & a0 & bytes & len & _ & Hj & ->).
  cbn [SND snd entry_pc]. exact (pos_val_mono j 0 code2 (num_pcs code2) p' c labs ffis
                                   (conj Hj (conj (N.le_refl _) (conj Hok Hc)))).
Qed.

End ShmemInfo4.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_subset_refl" *)
Theorem list_subset_refl : forall {A} `{EqDecision A} (xs : list A), list_subset xs xs.
Proof.
  intros A HA xs. unfold list_subset, is_true. rewrite EVERY_Forall, List.Forall_forall.
  intros x Hx. apply MEM_In, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_subset_TAKE" *)
Theorem list_subset_TAKE : forall {A} `{EqDecision A} i (xs : list A), list_subset (TAKE i xs) xs.
Proof.
  intros A HA i xs. unfold list_subset, is_true. rewrite EVERY_Forall, List.Forall_forall.
  intros x Hx. apply MEM_In. rewrite TAKE_firstn in Hx. rewrite <- (firstn_skipn (N.to_nat i) xs).
  apply in_app_iff. left. exact Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_subset_trans" *)
Theorem list_subset_trans : forall {A} `{EqDecision A} (a0 b c : list A),
  list_subset a0 b /\ list_subset b c -> list_subset a0 c.
Proof.
  intros A HA a0 b c [H1 H2]. unfold list_subset, is_true in *. rewrite EVERY_Forall, List.Forall_forall in *.
  intros x Hx. apply H2. apply MEM_In, H1, Hx.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_index_MAP_w2n" *)
Theorem find_index_MAP_w2n : forall {a} (l : list (word a)) (x : word a) n,
  find_index (w2n x) (MAP w2n l) n = find_index x l n.
Proof.
  intros a l. induction l as [|y l IH]; intros x n; [reflexivity|]. cbn [MAP map find_index].
  destruct (decide (w2n y = w2n x)) as [E|E]; destruct (decide (y = x)) as [E'|E']; subst;
    try reflexivity; try congruence; try apply IH.
  exfalso. apply E'. apply (proj1 (w2n_11 y x)), E.
Qed.

Section AsmFetchFfi.
Context {a : N} {B C : Type}.

Lemma MEM_TAKE_EL {X} `{EqDecision X} `{Inhabited X} : forall i (l : list X) x,
  is_true (MEM x (TAKE i l)) -> exists k, k < i /\ k < LENGTH l /\ EL k l = x.
Proof.
  intros n0 l x. revert n0. induction l as [|y l IH]; intros n0 Hm; cbn [TAKE] in Hm; [discriminate|].
  destruct (N.eqb_spec n0 0) as [E0|Hi]; [subst n0; discriminate|].
  cbn [MEM] in Hm. apply Bool.orb_true_iff in Hm as [Hm|Hm].
  - apply bool_decide_spec in Hm. subst. exists 0. cbn [LENGTH]. split; [lia|split; [lia|reflexivity]].
  - destruct (IH _ Hm) as (k & Hk1 & Hk2 & Hk3). exists (N.succ k). cbn [LENGTH].
    rewrite EL_cons_succ. split; [lia|split; [lia|exact Hk3]].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "asm_fetch_NOT_ffi_entry_pcs" *)
Theorem asm_fetch_NOT_ffi_entry_pcs : forall (mc_conf : machine_config a B C) (code2 : list (sec a)) i labs ffis
    (ms : B) (t : asm_state a) dm pos line a0,
  LENGTH (prog_to_bytes code2) < dimword a /\
  mmio_pcs_min_index mc_conf.(ffi_names) = SOME i /\
  LENGTH mc_conf.(ffi_names) = LENGTH mc_conf.(ffi_entry_pcs) /\
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffis 0 code2 /\
  enc_ok (asmProps.config mc_conf.(target)) /\
  (forall index,
     index < i ->
     (- n2w (ffi_offset * (index + 3)) + get_pc mc_conf.(target) ms)%w NOTIN mc_conf.(prog_addresses) /\
     (- n2w (ffi_offset * (index + 3)) + get_pc mc_conf.(target) ms)%w NOTIN mc_conf.(shared_addresses) /\
     (- n2w (ffi_offset * (index + 3)) + get_pc mc_conf.(target) ms)%w <> mc_conf.(halt_pc) /\
     (- n2w (ffi_offset * (index + 3)) + get_pc mc_conf.(target) ms)%w <> mc_conf.(ccache_pc) /\
     find_index (- n2w (ffi_offset * (index + 3)) + get_pc mc_conf.(target) ms)%w
       mc_conf.(ffi_entry_pcs) 0 = SOME index) /\
  bytes_in_mem (get_pc mc_conf.(target) ms) (prog_to_bytes code2) (asmSem.mem t)
    mc_conf.(prog_addresses) dm /\
  asm_fetch_aux pos code2 = SOME line /\
  a0 < LENGTH (line_bytes line) ->
  ~ MEM (get_pc mc_conf.(target) ms + n2w a0 + n2w (pos_val pos 0 code2))%w (TAKE i mc_conf.(ffi_entry_pcs)).
Proof.
  intros mc_conf code2 i labs ffis ms t dm pos line a0 (Hl & Hi & Hlen & Hok & Hc & Hidx & Hbm & Hf & Ha) Hm.
  apply MEM_TAKE_EL in Hm as (k & Hk & Hkl & Hel).
  destruct (Hidx k Hk) as (Hnp & _ & _ & _ & Hfind).
  pose proof (find_index_EL _ _ _ _ Hfind) as E. rewrite N.sub_0_r, Hel in E.
  apply Hnp. rewrite <- E.
  pose proof (asm_fetch_aux_pos_val_SUC pos 0 code2 0 _ _ _ line (conj Hok Hf)) as Hs.
  pose proof (pos_val_bound (pos + 1) 0 code2 _ _ _ _ Hok) as Hb.
  rewrite <- WORD_ADD_ASSOC, word_add_n2w.
  apply (bytes_in_memory_in_domain _ (prog_to_bytes code2) (asmSem.mem t)).
  split; [exact (bytes_in_mem_IMP _ _ _ _ _ Hbm)|lia].
Qed.

End AsmFetchFfi.

Section OkLemma.
Context {a : N}.

Lemma In_EL_ex {X} `{Inhabited X} (l : list X) x : In x l -> exists j, j < LENGTH l /\ EL j l = x.
Proof.
  induction l as [|y l IH]; intros Hin; [contradiction|]. destruct Hin as [<-|Hin].
  - exists 0. cbn [LENGTH]. split; [lia|reflexivity].
  - destruct (IH Hin) as (j & Hj & E). exists (N.succ j). cbn [LENGTH]. rewrite EL_cons_succ. split; [lia|exact E].
Qed.

#[local] Instance shmem_info_num_inhabited : Inhabited shmem_info_num :=
  {| entry_pc := 0; nbytes := n2w 0; addr_reg := 0; addr_off := 0; reg := 0; exit_pc := 0 |}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "get_shmem_info_ok_lemma" *)
Theorem get_shmem_info_ok_lemma : forall c labs ffis' p' (code2 : list (sec a)) p ffis
    new_ffi_names new_shmem_info,
  all_enc_ok c labs ffis' p' code2 /\
  enc_ok c /\
  LENGTH (prog_to_bytes code2) < dimword a /\
  EVERY (fun x => ⌜exists s, x = ExtCall s⌝) ffis /\
  get_shmem_info code2 p ffis [] = (new_ffi_names, new_shmem_info) ->
  (forall pc op re a0 inst len i,
     asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a0) inst len) /\
     mmio_pcs_min_index new_ffi_names = SOME i ->
     exists index,
       find_index (p + pos_val pc 0 code2) (MAP (fun rec => entry_pc rec) new_shmem_info) 0 = SOME index /\
       (let '(name, nb) := get_memop_info op in
        EL (index + i) new_ffi_names = SharedMem name /\
        EL index new_shmem_info =
          {| entry_pc := entry_pc (EL index new_shmem_info);
             nbytes := nb;
             addr_reg := match a0 with Addr r off => r end;
             addr_off := match a0 with Addr r off => w2n off end;
             reg := re;
             exit_pc := p + (pos_val pc 0 code2 + len) |})) /\
  (forall pc line,
     asm_fetch_aux pc code2 = SOME line /\
     (forall op re a0 inst len, line <> Asm (ShareMem op re a0) inst len) ->
     DISJOINT (set (MAP (fun rec => entry_pc rec) new_shmem_info))
       (fun x => exists a0, x = p + a0 + pos_val pc 0 code2 /\ a0 < LENGTH (line_bytes line))).
Proof.
  intros c labs ffis' p' code2 p ffis nf ns (Hok & Hc & Hlen & He & H).
  pose proof (mmio_pcs_min_index_get_shmem_info_ok c labs ffis' p' code2 p ffis nf ns
                (conj Hok (conj Hc (conj He H)))) as Hm.
  rewrite (shmem_entries_thm c labs ffis' code2 p ffis [] p' Hok) in H. injection H as <- <-.
  cbn [app] in *. set (E := shmem_entries code2 p) in *.
  pose proof (shmem_entries_sorted c labs ffis' p' code2 p Hok Hc) as ND. fold E in ND.
  rewrite map_map. split.
  - intros pc op re a0 inst len i (Hfa & Hi). rewrite Hm in Hi. injection Hi as <-.
    assert (Hin : In (SharedMem (fst (get_memop_info op)), shmem_rec (pos_val pc p code2) op re a0 inst) E).
    { unfold E, shmem_entries. apply in_concat.
      exists (line_to_info code2 p (pc, asm_fetch_aux pc code2)). split.
      - apply in_map. apply (In_GENLIST (fun i => (i, asm_fetch_aux i code2))).
        exact (asm_fetch_SOME_IMP_LESS_num_pcs _ _ _ Hfa).
      - unfold line_to_info. cbn [SND snd FST fst]. rewrite Hfa. unfold shmem_rec.
        destruct (get_memop_info op). left. reflexivity. }
    destruct (In_EL_ex E _ Hin) as (j & Hj & Ej).
    exists j. split.
    + assert (Ee : EL j (MAP (fun x => entry_pc (snd x)) E) = p + pos_val pc 0 code2).
      { rewrite EL_MAP_lt by exact Hj. rewrite Ej. cbn. rewrite pos_val_acc_0. reflexivity. }
      rewrite <- Ee. rewrite (find_index_NoDup _ j 0 ND) by (rewrite LENGTH_MAP'; exact Hj). reflexivity.
    + pose proof (all_enc_ok_asm_fetch_aux_IMP_line_ok _ _ _ _ _ _ _ (conj Hok Hfa)) as Hl.
      destruct (get_memop_info op) as [name nb] eqn:Em. split.
      * rewrite N.add_comm, EL_app_ge by lia. replace (LENGTH ffis + j - LENGTH ffis) with j by lia. rewrite EL_MAP_lt by exact Hj. rewrite Ej. reflexivity.
      * rewrite EL_MAP_lt by exact Hj. rewrite Ej. unfold shmem_rec. try rewrite Em. cbn.
        cbn [line_ok] in Hl. destruct Hl as (_ & Hl & _). rewrite Hl, <- pos_val_acc_0. f_equal. lia.
  - intros pc line (Hfa & Hnot). rewrite IN_DISJOINT. intros (x & Hx1 & (a0 & -> & Ha)).
    apply IN_set in Hx1. apply in_map_iff in Hx1 as (y & Ey & Hy).
    apply shmem_entries_entry in Hy as (j & op & re & a1 & bytes & len & Hfj & Hj & ->).
    cbn in Ey. destruct (N.eq_dec j pc) as [->|Hne].
    + rewrite Hfa in Hfj. injection Hfj as ->. exact (Hnot _ _ _ _ _ eq_refl).
    + apply (pos_val_asm_fetch_aux_distinct c labs ffis' p' code2 pc line a0 j p).
      * split; [exact Hok|]. split; [exact Hc|]. split; [exact Hfa|]. split; [exact Ha|]. split; [exact Hlen|exact Hne].
      * rewrite <- (pos_val_acc_0 pc p code2). lia.
Qed.

End OkLemma.
