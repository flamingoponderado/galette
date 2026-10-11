(** * CakeML [lab_to_targetProof]: properties of the assembled code

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 6269-6569): lengths of [prog_to_bytes], [loc_to_pc] and
    [pos_val] on appended code and their bounds, [find_ffi_names] on
    appended code, alignment of [pos_val] and [read_ffi_bytearrays] under
    machine-configuration updates.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [loc_to_pc_append]: HOL quantifies the unused variables [conf],
      [labs], [ffis] and [pos]; they are left out.
    - HOL's [len_no_lab o Section_lines] is written as a [fun] ([len_no_lab]
      is an abbreviation); [SUM o MAP line_length o Section_lines] is
      written with [∘].
    - HOL's [mc with next_interfer := foo] and [mc with ffi_interfer :=
      ffi] are [set_next_interfer foo mc] and [set_ffi_interfer ffi mc].
    - HOL's [local] theorems are ported as ordinary theorems. *)

From Galette Require Import Base Classical.
From Stdlib Require Import Setoid.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.list.src.list Require Import list_to_set.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.combin Require Import combin.
From Galette.HOL.src.n_bit Require Import words alignment byte.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.semantics.ffi Require Import ffi.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.backend Require Import labLang lab_to_target lab_filter.
From Galette.cakeml.compiler.backend.semantics Require backendProps.
From Galette.cakeml.compiler.backend.semantics Require Import targetSem targetProps.
From Galette.cakeml.compiler.backend.semantics Require Import labSem labProps.
From Galette.cakeml.compiler.backend.proofs.lab_to_targetProof Require Import
  basic bytes compile_lemmas rl_syntax rl_invariants rl_nop rl_labels rl_compute.
Import backendProps (restrict_zero, restrict_nonzero).
Open Scope N_scope.

Open Scope N_scope.

Section CodeProps.
Context {a : N}.

Lemma prog_to_bytes_cons k (ys : list (line a)) xs :
  prog_to_bytes (Section_ k ys :: xs) = FLAT (MAP line_bytes ys) ++ prog_to_bytes xs.
Proof. rewrite !prog_to_bytes_MAP. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_line_byte_length" *)
Theorem line_ok_line_byte_length : forall (c : asm_config a) labs ffi n (l : line a),
  line_ok c labs ffi n l ->
  LENGTH (line_bytes l) = line_length l.
Proof.
  intros c labs ffi n [k1 k2 len|b bytes len|x w bytes len] H; cbn [line_bytes line_length];
    [|reflexivity|reflexivity].
  destruct H as [_ ->]. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_ok_MAP_line_byte_length" *)
Theorem lines_ok_MAP_line_byte_length : forall (ls : list (line a)) c labs ffi n,
  lines_ok c labs ffi n ls ->
  MAP LENGTH (MAP line_bytes ls) = MAP line_length ls.
Proof.
  induction ls as [|l ls IH]; intros c labs ffi n H; [reflexivity|].
  destruct H as [H1 H2]. cbn [MAP map]. rewrite (line_ok_line_byte_length _ _ _ _ _ H1), (IH _ _ _ _ H2).
  reflexivity.
Qed.

Lemma lines_ok_LENGTH_FLAT (c : asm_config a) labs ffi n (ls : list (line a)) :
  lines_ok c labs ffi n ls -> LENGTH (FLAT (MAP line_bytes ls)) = SUM (MAP line_length ls).
Proof.
  revert n. induction ls as [|l ls IH]; intros n H; [reflexivity|].
  destruct H as [H1 H2]. cbn [MAP map FLAT concat SUM]. rewrite LENGTH_app, (IH _ H2).
  rewrite (line_ok_line_byte_length _ _ _ _ _ H1). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "LENGTH_prog_to_bytes" *)
Theorem LENGTH_prog_to_bytes : forall (code : list (sec a)) n c labs ffi pos,
  all_enc_ok c labs ffi pos code ->
  FOLDL (fun pos sec => sec_length (Section_lines sec) pos) n code =
  LENGTH (prog_to_bytes code) + n.
Proof.
  induction code as [|[k lines] rest IH]; intros n c labs ffi pos H; [reflexivity|].
  apply all_enc_ok_cons in H as (H1 & _ & H3).
  cbn [FOLDL fold_left Section_lines]. rewrite (IH _ _ _ _ _ H1), prog_to_bytes_cons, LENGTH_app.
  rewrite sec_length_sum_line_len, (lines_ok_LENGTH_FLAT _ _ _ _ _ H3), (lines_ok_SUM _ _ _ _ _ H3).
  lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "LENGTH_prog_to_bytes2" *)
Theorem LENGTH_prog_to_bytes2 : forall (code : list (sec a)) (n : N) c labs ffi pos,
  all_enc_ok c labs ffi pos code ->
  SUM (MAP (SUM ∘ MAP line_length ∘ Section_lines) code) =
  LENGTH (prog_to_bytes code).
Proof.
  induction code as [|[k lines] rest IH]; intros n c labs ffi pos H; [reflexivity|].
  apply all_enc_ok_cons in H as (H1 & _ & H3).
  cbn [MAP map SUM Section_lines]. rewrite (IH n _ _ _ _ H1), prog_to_bytes_cons, LENGTH_app.
  rewrite (lines_ok_LENGTH_FLAT _ _ _ _ _ H3). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "prog_to_bytes_APPEND" *)
Theorem prog_to_bytes_APPEND : forall (c1 c2 : list (sec a)),
  prog_to_bytes (c1 ++ c2) = prog_to_bytes c1 ++ prog_to_bytes c2.
Proof. intros c1 c2. rewrite !prog_to_bytes_MAP, map_app, concat_app. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_prog_to_bytes_EVEN" *)
Theorem all_enc_ok_prog_to_bytes_EVEN : forall (code : list (sec a)) (n : N) c labs ffi pos,
  EVEN pos /\
  all_enc_ok c labs ffi pos code ->
  EVEN (LENGTH (prog_to_bytes code)).
Proof.
  induction code as [|[k lines] rest IH]; intros n c labs ffi pos (He & H); [reflexivity|].
  apply all_enc_ok_cons in H as (H1 & H2 & H3).
  rewrite prog_to_bytes_cons, LENGTH_app, (lines_ok_LENGTH_FLAT _ _ _ _ _ H3).
  specialize (IH n _ _ _ _ (conj H2 H1)). rewrite N.even_add, IH.
  rewrite N.even_add, He in H2. destruct (EVEN (SUM (MAP line_length lines))); [reflexivity|discriminate].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "loc_to_pc_append" *)
Theorem loc_to_pc_append : forall l1 l2 (c1 c2 : list (sec a)),
  EVERY sec_labels_ok (c1 ++ c2) ->
  loc_to_pc l1 l2 (c1 ++ c2) =
  match loc_to_pc l1 l2 c1 with
  | SOME x => SOME x
  | NONE =>
      match loc_to_pc l1 l2 c2 with
      | SOME x => SOME (x + SUM (MAP (fun s => len_no_lab (Section_lines s)) c1))
      | NONE => NONE
      end
  end.
Proof.
  intros l1 l2 c1; induction c1 as [|[k lines] c1 IH]; intros c2 H.
  - cbn [app]. rewrite (proj1 loc_to_pc_def). cbn [MAP map SUM].
    destruct (loc_to_pc l1 l2 c2); [rewrite N.add_0_r|]; reflexivity.
  - rewrite <- app_comm_cons. rewrite (loc_to_pc_thm l1 l2 (Section_ k lines :: c1 ++ c2)) by exact H.
    rewrite (loc_to_pc_thm l1 l2 (Section_ k lines :: c1)).
    2:{ cbn [app EVERY] in H |- *. apply Bool.andb_true_iff in H as [H1 H2].
        rewrite EVERY_app in H2. apply Bool.andb_true_iff in H2 as [H2 _]. rewrite H1, H2. reflexivity. }
    cbn [app EVERY] in H. apply Bool.andb_true_iff in H as [_ H].
    rewrite (IH _ H). cbn [MAP map SUM Section_lines].
    destruct (l1 =? k); [destruct (sec_loc_to_pc l2 lines); [reflexivity|]|];
      (destruct (loc_to_pc l1 l2 c1); [reflexivity|]);
      (destruct (loc_to_pc l1 l2 c2); [cbn; f_equal; lia|reflexivity]).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_append" *)
Theorem all_enc_ok_append : forall conf labs ffi n (c1 c2 : list (sec a)),
  all_enc_ok conf labs ffi n c1 /\
  all_enc_ok conf labs ffi (n + LENGTH (prog_to_bytes c1)) c2 ->
  all_enc_ok conf labs ffi n (c1 ++ c2).
Proof.
  intros conf labs ffi n c1; revert n. induction c1 as [|[k lines] c1 IH]; intros n c2 (H1 & H2).
  - cbn in H2. rewrite N.add_0_r in H2. exact H2.
  - rewrite <- app_comm_cons. apply all_enc_ok_cons in H1 as (H1a & H1b & H1c).
    apply all_enc_ok_cons. split; [|split; assumption].
    apply IH. split; [exact H1a|].
    rewrite prog_to_bytes_cons, LENGTH_app, (lines_ok_LENGTH_FLAT _ _ _ _ _ H1c), N.add_assoc in H2.
    exact H2.
Qed.

Lemma sec_loc_to_pc_extract_labels k l2 (lines : list (line a)) :
  is_true (MEM (k, l2) (extract_labels lines)) -> exists y, sec_loc_to_pc l2 lines = SOME y.
Proof.
  induction lines as [|z zs IH]; intros H; [discriminate|].
  rewrite sec_loc_to_pc_cons.
  destruct (bool_decide (l2 = 0 \/ (exists n1 k0, z = Label n1 l2 k0))) eqn:E; [eauto|].
  assert (Hz : ~ exists n1 k0, z = Label n1 l2 k0).
  { intros Hc. rewrite (proj2 (bool_decide_spec _) (or_intror Hc)) in E. discriminate. }
  assert (Hm : is_true (MEM (k, l2) (extract_labels zs))).
  { destruct z as [m1 m2 ml| |]; cbn [extract_labels] in H; [|exact H|exact H].
    cbn [MEM] in H. apply Bool.orb_true_iff in H as [H|H]; [|exact H].
    apply bool_decide_spec in H. injection H as -> ->. exfalso. apply Hz. eauto. }
  destruct (IH Hm) as [y ->]. eexists. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "extract_labels_loc_to_pc" *)
Theorem extract_labels_loc_to_pc : forall l1 l2 (code : list (sec a)),
  EVERY sec_labels_ok code /\
  MEM (l1, l2) (FLAT (MAP (extract_labels ∘ Section_lines) code)) ->
  exists y, loc_to_pc l1 l2 code = SOME y.
Proof.
  intros l1 l2 code; induction code as [|[k lines] rest IH]; intros (Hok & Hm); [discriminate|].
  rewrite loc_to_pc_thm by exact Hok.
  cbn [EVERY sec_labels_ok] in Hok. apply Bool.andb_true_iff in Hok as [Hok1 Hok].
  cbn [MAP map FLAT concat Section_lines] in Hm. unfold is_true in Hm. rewrite MEM_In, in_app_iff in Hm.
  destruct Hm as [Hm|Hm].
  - pose proof (sec_label_ok_extract_labels k lines l1 l2) as Hs.
    assert (Hm' : is_true (MEM (l1, l2) (extract_labels lines))) by (apply MEM_In; exact Hm).
    destruct (Hs (conj Hok1 Hm')) as [-> _]. rewrite N.eqb_refl.
    destruct (sec_loc_to_pc_extract_labels k l2 lines Hm') as [y ->]. eauto.
  - assert (Hm' : is_true (MEM (l1, l2) (FLAT (MAP (extract_labels ∘ Section_lines) rest))))
      by (apply MEM_In; exact Hm).
    destruct (IH (conj Hok Hm')) as [y ->].
    destruct (l1 =? k); [destruct (sec_loc_to_pc l2 lines)|]; eexists; reflexivity.
Qed.

Lemma line_ok_labs_mono (conf : asm_config a) labs labs2 ffi n (y : line a) :
  (forall l1 l2 x, lab_lookup l1 l2 labs = SOME x -> lab_lookup l1 l2 labs2 = SOME x) ->
  line_ok conf labs ffi n y -> line_ok conf labs2 ffi n y.
Proof.
  intros Hm. destruct y as [k1 k2 l|b bytes l|x w bytes l]; cbn [line_ok]; [tauto|tauto|].
  destruct x as [[l1 l2]|cc r ri [l1 l2]|v|r [l1 l2]|s| |]; cbn [get_label]; try tauto;
    destruct (lab_lookup l1 l2 labs) as [t|] eqn:E; try contradiction; rewrite (Hm _ _ _ E); tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_labs_mono" *)
Theorem all_enc_ok_labs_mono : forall conf labs ffi n (c : list (sec a)) labs2,
  (forall l1 l2 x,
     lab_lookup l1 l2 labs = SOME x ->
     lab_lookup l1 l2 labs2 = SOME x) /\
  all_enc_ok conf labs ffi n c ->
  all_enc_ok conf labs2 ffi n c.
Proof.
  intros conf labs ffi n c labs2 (Hm & H). revert n H.
  induction c as [|k ys IH|k y ys xs IH] using code_ind; intros n H.
  - exact Logic.I.
  - destruct H as [He H]. split; [exact He|]. apply IH, H.
  - destruct H as [Hy H]. split; [exact (line_ok_labs_mono _ _ _ _ _ _ Hm Hy)|]. apply IH, H.
Qed.

Lemma sec_pos_val_lt i pos (l : list (line a)) :
  i < len_no_lab l -> exists x, sec_pos_val i pos l = SOME x.
Proof.
  revert i pos. induction l as [|y ys IH]; intros i pos H; cbn [FILTER LENGTH] in H; [lia|].
  cbn [sec_pos_val]. cbn [FILTER] in H. destruct (is_Label y); cbn [negb LENGTH] in H.
  - apply IH, H.
  - destruct (N.eqb_spec i 0); [eauto|]. apply IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_append" *)
Theorem pos_val_append : forall (c1 : list (sec a)) i pos c2,
  EVERY sec_label_zero c2 ->
  pos_val i pos (c1 ++ c2) =
  if i <=? SUM (MAP (fun s => len_no_lab (Section_lines s)) c1) then
    pos_val i pos c1
  else
    pos_val (i - SUM (MAP (fun s => len_no_lab (Section_lines s)) c1))
      (pos + SUM (MAP (SUM ∘ MAP line_length ∘ Section_lines) c1)) c2.
Proof.
  induction c1 as [|[k l] c1 IH]; intros i pos c2 Hz.
  - cbn [app MAP map SUM]. destruct (N.leb_spec i 0).
    + assert (i = 0) as -> by lia. rewrite sec_label_zero_pos_val_0 by exact Hz. reflexivity.
    + rewrite N.sub_0_r, N.add_0_r. reflexivity.
  - rewrite <- app_comm_cons. rewrite !(proj2 (pos_val_thm _ _ _ _ _)).
    cbn [MAP map SUM Section_lines].
    destruct (sec_pos_val i pos l) as [x|] eqn:E.
    + assert (Hi : i < len_no_lab l).
      { destruct (N.lt_ge_cases i (len_no_lab l)) as [Hi|Hi]; [exact Hi|].
        rewrite sec_pos_val_too_big in E by exact Hi. discriminate. }
      rewrite (proj2 (N.leb_le _ _)) by lia. reflexivity.
    + assert (Hi : len_no_lab l <= i).
      { destruct (N.lt_ge_cases i (len_no_lab l)) as [Hi|Hi]; [|exact Hi].
        destruct (sec_pos_val_lt i pos l Hi) as [x Hx]. rewrite Hx in E. discriminate. }
      rewrite IH by exact Hz.
      destruct (N.leb_spec (i - len_no_lab l) (SUM (MAP (fun s => len_no_lab (Section_lines s)) c1)));
        destruct (N.leb_spec i (len_no_lab l + SUM (MAP (fun s => len_no_lab (Section_lines s)) c1)));
        first [lia | reflexivity | f_equal; lia].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_pos_val_acc" *)
Theorem sec_pos_val_acc : forall (l : list (line a)) n i,
  len_no_lab l <= i ->
  sec_pos_val i n l = NONE.
Proof. intros l n i H. apply sec_pos_val_too_big, H. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_acc" *)
Theorem pos_val_acc : forall (ls : list (sec a)) n,
  pos_val (SUM (MAP (fun s => len_no_lab (Section_lines s)) ls)) n ls =
  n + SUM (MAP (SUM ∘ MAP line_length ∘ Section_lines) ls).
Proof.
  induction ls as [|[k l] ls IH]; intros n.
  - cbn. lia.
  - rewrite (proj2 (pos_val_thm _ _ _ _ _)). cbn [MAP map SUM Section_lines].
    rewrite sec_pos_val_acc by lia.
    replace (len_no_lab l + SUM (MAP (fun s => len_no_lab (Section_lines s)) ls) - len_no_lab l)
      with (SUM (MAP (fun s => len_no_lab (Section_lines s)) ls)) by lia.
    rewrite IH. lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pos_val_bound" *)
Theorem pos_val_bound : forall i pos (code : list (sec a)) conf labs ffi n,
  all_enc_ok conf labs ffi n code ->
  pos_val i pos code <= pos + LENGTH (prog_to_bytes code).
Proof.
  intros i pos code conf labs ffi. revert i pos.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros i pos n H.
  - cbn. lia.
  - destruct H as [_ H]. exact (IH i pos n H).
  - destruct H as [Hy H]. rewrite (proj2 (proj2 (pos_val_def i pos k xs y ys))).
    rewrite (proj2 (proj2 (prog_to_bytes_def k y ys xs))), LENGTH_app,
      (line_ok_line_byte_length _ _ _ _ _ Hy).
    specialize (IH (i - 1) (pos + line_length y) _ H) as IH1.
    specialize (IH i (pos + line_length y) _ H) as IH2.
    destruct (is_Label y); [lia|]. destruct (i =? 0); lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "sec_loc_to_pc_bound" *)
Theorem sec_loc_to_pc_bound : forall n (xs : list (line a)) x,
  sec_loc_to_pc n xs = SOME x ->
  x <= len_no_lab xs.
Proof.
  intros n xs; induction xs as [|z zs IH]; intros x H.
  - cbn in H. destruct (n =? 0); [injection H as <-; cbn; lia|discriminate].
  - rewrite sec_loc_to_pc_cons in H. destruct (bool_decide _); [injection H as <-; lia|].
    cbn [FILTER]. destruct (is_Label z); cbn [negb LENGTH].
    + destruct (sec_loc_to_pc n zs) as [y|] eqn:E; [|discriminate]. injection H as <-. apply IH. reflexivity.
    + destruct (sec_loc_to_pc n zs) as [y|] eqn:E; [|discriminate]. injection H as <-.
      specialize (IH _ eq_refl). lia.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "loc_to_pc_bound" *)
Theorem loc_to_pc_bound : forall (code : list (sec a)) l1 l2 x,
  EVERY sec_labels_ok code /\
  loc_to_pc l1 l2 code = SOME x ->
  x <= SUM (MAP (fun s => len_no_lab (Section_lines s)) code).
Proof.
  induction code as [|[k lines] rest IH]; intros l1 l2 x (Hok & H).
  - rewrite (proj1 loc_to_pc_def) in H. discriminate.
  - rewrite loc_to_pc_thm in H by exact Hok.
    cbn [EVERY sec_labels_ok] in Hok. apply Bool.andb_true_iff in Hok as [_ Hok].
    cbn [MAP map SUM Section_lines].
    assert (Hr : forall y, loc_to_pc l1 l2 rest = SOME y -> y <= SUM (MAP (fun s => len_no_lab (Section_lines s)) rest))
      by (intros y Hy; exact (IH _ _ _ (conj Hok Hy))).
    destruct (l1 =? k); [destruct (sec_loc_to_pc l2 lines) as [y|] eqn:E|].
    + injection H as <-. pose proof (sec_loc_to_pc_bound _ _ _ E). lia.
    + destruct (loc_to_pc l1 l2 rest) as [y|]; [|discriminate]. injection H as <-.
      specialize (Hr _ eq_refl). lia.
    + destruct (loc_to_pc l1 l2 rest) as [y|]; [|discriminate]. injection H as <-.
      specialize (Hr _ eq_refl). lia.
Qed.

Definition ffi_step (x : line a) (acc : list ffiname) : list ffiname :=
  match x with
  | LabAsm (CallFFI s) _ _ _ => list_add_if_fresh (ExtCall s) acc
  | _ => acc
  end.

Lemma find_ffi_names_app_fold (c1 c2 : list (sec a)) :
  find_ffi_names (c1 ++ c2) = fold_right ffi_step (find_ffi_names c2) (FLAT (MAP Section_lines c1)).
Proof.
  induction c1 as [|[k lines] c1 IH]; [reflexivity|].
  cbn [app MAP map FLAT concat Section_lines]. rewrite fold_right_app, <- IH.
  induction lines as [|x xs IHl]; [reflexivity|]. cbn [fold_right]. rewrite <- IHl. reflexivity.
Qed.

Lemma MEM_iff {X} `{EqDecision X} (x : X) l : is_true (MEM x l) <-> In x l.
Proof. apply MEM_In. Qed.

Lemma fold_ffi_step acc (xs : list (line a)) :
  fold_right ffi_step acc xs =
  acc ++ FILTER (fun n => negb (MEM n acc)) (fold_right ffi_step [] xs).
Proof.
  induction xs as [|x xs IH]; [cbn; rewrite app_nil_r; reflexivity|].
  cbn [fold_right]. rewrite IH. set (R := fold_right ffi_step [] xs).
  destruct x as [| |y w bytes len]; cbn [ffi_step]; try reflexivity.
  destruct y; cbn [ffi_step]; try reflexivity.
  rewrite !list_add_if_fresh_thm. set (e := ExtCall m).
  set (F := FILTER (fun n => negb (MEM n acc)) R).
  assert (HF : forall n, In n F <-> In n R /\ ~ In n acc).
  { intros n. unfold F. rewrite filter_In, Bool.negb_true_iff, <- Bool.not_true_iff_false, MEM_In.
    reflexivity. }
  destruct (MEM e (acc ++ F)) eqn:E1; destruct (MEM e R) eqn:E2.
  - reflexivity.
  - apply MEM_In in E1. rewrite filter_app. cbn [filter].
    destruct (MEM e acc) eqn:E3; cbn [negb].
    + rewrite app_nil_r. reflexivity.
    + exfalso. apply in_app_iff in E1 as [E1|E1].
      * apply MEM_In in E1. rewrite E1 in E3. discriminate.
      * apply HF in E1 as [E1 _]. apply MEM_In in E1. rewrite E1 in E2. discriminate.
  - exfalso. apply Bool.not_true_iff_false in E1. apply E1. apply MEM_In. apply in_app_iff. right.
    apply HF. split; [apply MEM_In, E2|]. intros Hc. apply E1, MEM_In, in_app_iff. left. exact Hc.
  - rewrite filter_app. cbn [filter]. destruct (MEM e acc) eqn:E3.
    + exfalso. apply Bool.not_true_iff_false in E1. apply E1, MEM_In, in_app_iff. left. apply MEM_In, E3.
    + cbn [negb]. rewrite app_assoc. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_ffi_names_append" *)
Theorem find_ffi_names_append : forall (l1 l2 : list (sec a)),
  find_ffi_names (l1 ++ l2) =
  find_ffi_names l2 ++
  FILTER (fun n => negb (MEM n (find_ffi_names l2))) (find_ffi_names l1).
Proof.
  intros l1 l2. rewrite find_ffi_names_app_fold, fold_ffi_step.
  rewrite <- (app_nil_r l1), find_ffi_names_app_fold, app_nil_r. reflexivity.
Qed.

End CodeProps.

Section MachineConfig.
Context {a : N} {B C : Type}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_aligned_pos_val" *)
Theorem all_enc_ok_aligned_pos_val : forall (mc_conf : machine_config a B C) labs (code2 : list (sec a))
    pc ffi_names,
  all_enc_ok (asmProps.config mc_conf.(target)) labs ffi_names 0 code2 /\
  (has_odd_inst code2 -> code_alignment (asmProps.config mc_conf.(target)) = 0) /\
  encoder_correct mc_conf.(target) ->
  aligned (code_alignment (asmProps.config mc_conf.(target))) (n2w (pos_val pc 0 code2) : word a).
Proof.
  intros mc_conf labs code2 pc ffi_names (H1 & H2 & H3). apply MOD_0_aligned.
  apply (pos_val_MOD_0 mc_conf labs ffi_names). auto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "read_ffi_bytearrays_with_next_interfer" *)
Theorem read_ffi_bytearrays_with_next_interfer : forall (mc : machine_config a B C) foo,
  read_ffi_bytearrays (set_next_interfer foo mc) =
  read_ffi_bytearrays mc.
Proof. intros mc foo. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "read_ffi_bytearrays_shift_interfer" *)
Theorem read_ffi_bytearrays_shift_interfer : forall x (y : machine_config a B C),
  read_ffi_bytearrays (shift_interfer x y) = read_ffi_bytearrays y.
Proof. intros x y. reflexivity. Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "read_ffi_bytearrays_ffi_interfer" *)
Theorem read_ffi_bytearrays_ffi_interfer : forall (mc : machine_config a B C) ffi,
  read_ffi_bytearrays (set_ffi_interfer ffi mc) = read_ffi_bytearrays mc.
Proof. intros mc ffi. reflexivity. Qed.

End MachineConfig.
