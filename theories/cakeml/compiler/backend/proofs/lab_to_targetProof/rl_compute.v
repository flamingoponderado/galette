(** * CakeML [lab_to_targetProof]: syntactic properties of [remove_labels] (5)

    Part of the port of
    [cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml] (HOL
    lines 5415-5921): sections ending with labels, [compute_labels_alt]
    under re-encoding and padding, the label positions it computes
    ([ALOOKUP_section_labels], [lab_lookup_compute_labels_test]),
    preservation of [all_enc_ok_pre], and code alignment of odd-length
    instructions.

    Notes:
    - Naming conventions as in [lab_to_targetProof/basic.v].
    - [enc_lines_again_simp_ends_with_label] states HOL's [¬NULL ls] as
      [~ NULL ls] (on [bool]).
    - [lab_lookup_compute_labels_test]: HOL quantifies an unused variable
      [nop]; it is left out.
    - HOL's [local] theorems are ported as ordinary theorems.
    - Not ported: the evaluation snippets inside HOL comments
      ([val code], [EVAL ...]). *)

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
  basic bytes rl_syntax rl_invariants rl_nop rl_labels.
Import backendProps (restrict_zero, restrict_nonzero).
Open Scope N_scope.

Open Scope N_scope.

(** ** Sections ending with a label *)

Section EndsWithLabel.
Context {a : N}.

Lemma line_similar_is_Label (x y : line a) : line_similar x y -> is_Label x = is_Label y.
Proof. destruct x, y; cbn; tauto. Qed.

Lemma LIST_REL_line_similar_ends (l1 l2 : list (line a)) :
  LIST_REL line_similar l1 l2 ->
  (negb (NULL l1) && is_Label (LAST l1)) = (negb (NULL l2) && is_Label (LAST l2)).
Proof.
  intros H. induction H as [|x y l1 l2 Hxy Hl IH]; [reflexivity|].
  destruct Hl as [|x' y' l1' l2' Hxy' Hl'].
  - cbn [NULL negb andb LAST]. apply line_similar_is_Label, Hxy.
  - change (LAST (x :: x' :: l1')) with (LAST (x' :: l1')).
    change (LAST (y :: y' :: l2')) with (LAST (y' :: l2')). exact IH.
Qed.

Lemma code_similar_ends_with_label (c1 c2 : list (sec a)) :
  code_similar c1 c2 -> EVERY sec_ends_with_label c1 = EVERY sec_ends_with_label c2.
Proof.
  revert c2. induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H; try contradiction.
  - reflexivity.
  - destruct H as (Hc & Hl & ->). cbn [EVERY sec_ends_with_label].
    rewrite (IH _ Hc), (LIST_REL_line_similar_ends _ _ Hl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "upd_lab_len_ends_with_label" *)
Theorem upd_lab_len_ends_with_label : forall pos (ss : list (sec a)),
  EVERY sec_ends_with_label ss ->
  EVERY sec_ends_with_label (upd_lab_len pos ss).
Proof.
  intros pos ss H. rewrite (code_similar_ends_with_label (upd_lab_len pos ss) ss); [exact H|].
  apply code_similar_upd_lab_len, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_lookup_compute_labels_alt_ignore" *)
Theorem lab_lookup_compute_labels_alt_ignore : forall n1 n2 pos (secs : list (sec a)) acc,
  ~ MEM n1 (MAP Section_num secs) ->
  lab_lookup n1 n2 (compute_labels_alt pos secs acc) = lab_lookup n1 n2 acc.
Proof.
  intros n1 n2 pos secs; revert pos. induction secs as [|[k lines] rest IH]; intros pos acc Hm;
    [reflexivity|].
  unfold is_true in Hm. rewrite MEM_In in Hm. cbn [MAP map Section_num In] in Hm.
  cbn [compute_labels_alt]. destruct (section_labels pos lines []) as [np sl].
  rewrite IH by (unfold is_true; rewrite MEM_In; tauto).
  unfold lab_lookup. rewrite lookup_insert. destruct (decide (n1 = k)); [|reflexivity].
  exfalso. apply Hm. left. congruence.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "ALOOKUP_section_labels" *)
Theorem ALOOKUP_section_labels : forall n1 n2 pos (lines : list (line a)) acc pc,
  EVERY (sec_label_ok n1) lines /\
  EVERY line_length_ok lines /\
  EVERY label_zero lines /\
  ALL_DISTINCT (extract_labels lines) /\
  sec_loc_to_pc n2 lines = SOME pc /\
  n2 <> 0 ->
  exists i,
    ALOOKUP (SND (section_labels pos lines acc)) n2 = SOME i /\
    ((sec_pos_val pc pos lines = NONE /\
      i = pos + SUM (MAP line_length lines) /\
      pc = LENGTH (FILTER (negb ∘ is_Label) lines)) \/
     sec_pos_val pc pos lines = SOME i).
Proof.
  intros n1 n2 pos lines; revert pos.
  induction lines as [|y ys IH]; intros pos acc pc (Hok & Hlen & Hz & Hd & Hpc & Hn2).
  { cbn [sec_loc_to_pc] in Hpc. rewrite (proj2 (N.eqb_neq _ _) Hn2) in Hpc. discriminate. }
  cbn [EVERY] in Hok, Hlen, Hz.
  apply Bool.andb_true_iff in Hok as [Hoky Hok]. apply Bool.andb_true_iff in Hlen as [Hleny Hlen].
  apply Bool.andb_true_iff in Hz as [Hzy Hz].
  rewrite sec_loc_to_pc_cons in Hpc.
  destruct y as [k1 k2 l|x1 x2 l|x w bytes l].
  - cbn [label_zero] in Hzy. apply N.eqb_eq in Hzy. subst l.
    cbn [sec_label_ok] in Hoky. apply Bool.andb_true_iff in Hoky as [Hk1 Hk2].
    apply N.eqb_eq in Hk1. subst k1.
    cbn [extract_labels ALL_DISTINCT] in Hd. apply Bool.andb_true_iff in Hd as [Hdy Hd].
    cbn [section_labels sec_pos_val is_Label FILTER MAP map SUM line_length].
    rewrite N.eqb_refl. cbn [negb]. rewrite !N.add_0_r.
    destruct (N.eqb_spec k2 n2) as [->|Hk].
    + rewrite (proj2 (bool_decide_spec _)) in Hpc by (right; eauto). injection Hpc as <-.
      rewrite (proj2 (N.eqb_neq _ _) Hn2).
      rewrite ALOOKUP_section_labels_ignore.
      2:{ unfold is_true. rewrite MEM_In. intros Hin. apply in_map_iff in Hin as ([m1 m2] & Em & Hin).
          cbn in Em. subst m2. apply Bool.negb_true_iff in Hdy.
          pose proof (sec_label_ok_extract_labels n1 ys m1 n2) as Hs.
          assert (Hmem : is_true (MEM (m1, n2) (extract_labels ys))) by (apply MEM_In; exact Hin).
          destruct (Hs (conj Hok Hmem)) as [-> _]. unfold is_true in Hmem. rewrite Hmem in Hdy.
          discriminate. }
      cbn [ALOOKUP]. destruct (decide (n2 = n2)) as [_|]; [|congruence].
      exists pos. split; [reflexivity|].
      destruct (EVERY is_Label ys) eqn:Hall.
      * left. split; [apply EVERY_is_Label_sec_pos_val; exact Hall|].
        assert (Hs : SUM (MAP line_length ys) = 0 /\ LENGTH (FILTER (negb ∘ is_Label) ys) = 0).
        { clear -Hall Hz. induction ys as [|[k1 k2 l|x1 x2 l|x w bytes l] ys IH]; [split; reflexivity| |discriminate|discriminate].
          cbn [EVERY] in Hall, Hz. apply Bool.andb_true_iff in Hz as [Hl Hz]. cbn [label_zero] in Hl.
          apply N.eqb_eq in Hl. subst l. cbn [MAP map SUM line_length FILTER is_Label negb N.eqb].
          cbn [is_Label andb] in Hall. exact (IH Hz Hall). }
        destruct Hs as [-> ->]. split; [lia|reflexivity].
      * right. apply sec_pos_val_0. split; [rewrite Hall; discriminate|exact Hz].
    + rewrite bool_decide_false in Hpc.
      2:{ intros [Hc|(m1 & m2 & Hc)]; [contradiction|injection Hc; intros; congruence]. }
      cbn [is_Label] in Hpc. destruct (sec_loc_to_pc n2 ys) as [pc'|] eqn:Hpc'; [|discriminate].
      cbn [OPTION_MAP option_map I] in Hpc. injection Hpc as <-.
      destruct (k2 =? 0);
        (edestruct IH as (i & Hi & Hdisj); [split; [exact Hok|split; [exact Hlen|split; [exact Hz|split; [exact Hd|split; [first [exact Hpc'|reflexivity]|exact Hn2]]]]]|];
         exists i; split; [exact Hi|exact Hdisj]).
  - rewrite bool_decide_false in Hpc.
    2:{ intros [Hc|(m1 & m2 & Hc)]; [contradiction|discriminate]. }
    cbn [is_Label] in Hpc. destruct (sec_loc_to_pc n2 ys) as [pc'|] eqn:Hpc'; [|discriminate].
    cbn [OPTION_MAP option_map] in Hpc. injection Hpc as <-.
    cbn [extract_labels] in Hd. unfold line_length_ok, is_true in Hleny. apply N.eqb_eq in Hleny.
    cbn [line_bytes line_len] in Hleny. subst l.
    edestruct (IH (pos + LENGTH x2) acc pc') as (i & Hi & Hdisj);
      [split; [exact Hok|split; [exact Hlen|split; [exact Hz|split; [exact Hd|split; [first [exact Hpc'|reflexivity]|exact Hn2]]]]]|].
    exists i. split; [exact Hi|].
    cbn [sec_pos_val is_Label FILTER negb MAP map SUM line_length LENGTH].
    rewrite (proj2 (N.eqb_neq _ _)) by lia. replace (N.succ pc' - 1) with pc' by lia.
    destruct Hdisj as [(H1 & H2 & H3)|H1]; [left|right; exact H1].
    split; [exact H1|split; [rewrite H2; lia|cbn [length]; lia]].
  - rewrite bool_decide_false in Hpc.
    2:{ intros [Hc|(m1 & m2 & Hc)]; [contradiction|discriminate]. }
    cbn [is_Label] in Hpc. destruct (sec_loc_to_pc n2 ys) as [pc'|] eqn:Hpc'; [|discriminate].
    cbn [OPTION_MAP option_map] in Hpc. injection Hpc as <-.
    cbn [extract_labels] in Hd. unfold line_length_ok, is_true in Hleny. apply N.eqb_eq in Hleny.
    cbn [line_bytes line_len] in Hleny. subst l.
    edestruct (IH (pos + LENGTH bytes) acc pc') as (i & Hi & Hdisj);
      [split; [exact Hok|split; [exact Hlen|split; [exact Hz|split; [exact Hd|split; [first [exact Hpc'|reflexivity]|exact Hn2]]]]]|].
    exists i. split; [exact Hi|].
    cbn [sec_pos_val is_Label FILTER negb MAP map SUM line_length LENGTH].
    rewrite (proj2 (N.eqb_neq _ _)) by lia. replace (N.succ pc' - 1) with pc' by lia.
    destruct Hdisj as [(H1 & H2 & H3)|H1]; [left|right; exact H1].
    split; [exact H1|split; [rewrite H2; lia|cbn [length]; lia]].
Qed.

End EndsWithLabel.

Section ComputeLabels.
Context {a : N}.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lab_lookup_compute_labels_test" *)
Theorem lab_lookup_compute_labels_test : forall pos (sec_list : list (sec a)) acc l1 l2 x2 c labs ffis,
  EVERY sec_labels_ok sec_list /\
  ALL_DISTINCT (MAP Section_num sec_list) /\
  EVERY (fun s => ALL_DISTINCT (extract_labels (Section_lines s))) sec_list /\
  EVERY sec_label_zero sec_list /\
  all_enc_ok c labs ffis pos sec_list /\
  loc_to_pc l1 l2 sec_list = SOME x2 ->
  lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
  SOME (pos_val x2 pos sec_list).
Proof.
  intros pos sec_list; revert pos.
  induction sec_list as [|[k lines] rest IH]; intros pos acc l1 l2 x2 c labs ffis
    (Hok & Hd & Hdl & Hz & Henc & Hpc).
  { rewrite (proj1 loc_to_pc_def) in Hpc. discriminate. }
  pose proof Henc as Henc0.
  rewrite loc_to_pc_thm in Hpc by exact Hok.
  cbn [EVERY sec_labels_ok sec_label_zero Section_lines] in Hok, Hdl, Hz.
  apply Bool.andb_true_iff in Hok as [Hok1 Hok]. apply Bool.andb_true_iff in Hdl as [Hdl1 Hdl].
  apply Bool.andb_true_iff in Hz as [Hz1 Hz].
  cbn [MAP map Section_num ALL_DISTINCT] in Hd. apply Bool.andb_true_iff in Hd as [Hk Hd].
  apply Bool.negb_true_iff in Hk.
  apply all_enc_ok_cons in Henc as (Henc & Hev & Hlines).
  pose proof (lines_ok_SUM _ _ _ _ _ Hlines) as Hsum.
  rewrite (proj2 (pos_val_thm x2 pos k lines rest)).
  cbn [compute_labels_alt]. destruct (section_labels pos lines []) as [np sl] eqn:Es.
  pose proof (section_labels_sec_length pos lines []) as Hp. rewrite Es in Hp. cbn [FST fst] in Hp.
  assert (Hnp : np = pos + SUM (MAP line_length lines)).
  { rewrite Hp, sec_length_sum_line_len, Hsum. lia. }
  assert (Hrest : forall x2', loc_to_pc l1 l2 rest = SOME x2' ->
            lab_lookup l1 l2 (compute_labels_alt np rest (insert k (fromAList ((0, pos) :: sl)) acc)) =
            SOME (match sec_pos_val (len_no_lab lines + x2') pos lines with
                  | NONE => pos_val (len_no_lab lines + x2' - len_no_lab lines)
                              (pos + SUM (MAP line_length lines)) rest
                  | SOME x => x end)).
  { intros x2' Hx2'. rewrite sec_pos_val_too_big by lia.
    replace (len_no_lab lines + x2' - len_no_lab lines) with x2' by lia. rewrite <- Hnp.
    apply (IH _ _ _ _ _ c labs ffis). repeat split; try assumption. rewrite Hnp. exact Henc. }
  destruct (N.eqb_spec l1 k) as [->|Hne].
  - destruct (sec_loc_to_pc l2 lines) as [pc|] eqn:Hsl.
    + injection Hpc as <-.
      rewrite lab_lookup_compute_labels_alt_ignore by (rewrite Hk; discriminate).
      unfold lab_lookup. rewrite lookup_insert. destruct (decide (k = k)) as [_|]; [|congruence].
      rewrite lookup_fromAList. cbn [ALOOKUP]. destruct (decide (0 = l2)) as [<-|Hl2].
      * assert (pc = 0) as -> by (clear -Hsl; destruct lines; simpl in Hsl; congruence).
        rewrite <- (proj2 (pos_val_thm 0 pos k lines rest)). f_equal. symmetry.
        exact (pos_val_0 _ _ _ _ _ Henc0).
      * pose proof (lines_enc_with_nop_length_ok _ _ _ _ _ (lines_ok_lines_enc_with_nop _ _ _ _ _ Hlines))
          as Hlen.
        destruct (ALOOKUP_section_labels k l2 pos lines [] pc) as (i & Hi & Hdisj).
        { repeat split; try assumption. congruence. }
        rewrite Es in Hi. cbn [SND snd] in Hi. rewrite Hi.
        destruct Hdisj as [(H1 & H2 & H3)|H1]; rewrite H1; [|reflexivity].
        rewrite H3, N.sub_diag, (pos_val_0 _ _ _ _ _ Henc). f_equal. exact H2.
    + destruct (loc_to_pc k l2 rest) as [x2'|] eqn:Hx2'; [|discriminate].
      cbn [OPTION_MAP option_map] in Hpc. injection Hpc as <-. exact (Hrest _ eq_refl).
  - destruct (loc_to_pc l1 l2 rest) as [x2'|] eqn:Hx2'; [|discriminate].
    cbn [OPTION_MAP option_map] in Hpc. injection Hpc as <-. exact (Hrest _ eq_refl).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_simp_ends_with_label" *)
Theorem enc_lines_again_simp_ends_with_label : forall labs ffis pos enc (ls res : list (line a)) ok,
  enc_lines_again_simp labs ffis pos enc ls = (res, ok) /\
  ~ NULL ls /\ is_Label (LAST ls) ->
  ~ NULL res /\ is_Label (LAST res).
Proof.
  intros labs ffis pos enc ls res ok (H & Hn & Hl).
  pose proof (enc_lines_again_simp_EQ labs ffis pos enc ls [] true) as E. rewrite H in E.
  pose proof (enc_lines_again_IMP_similar labs ffis pos enc ls [] true _ _ [] E (LIST_REL_nil _)) as Hs.
  cbn [rev app] in Hs. pose proof (LIST_REL_line_similar_ends _ _ Hs) as Hends.
  apply Bool.not_true_iff_false in Hn. rewrite Hn, Hl in Hends. cbn in Hends.
  symmetry in Hends. apply Bool.andb_true_iff in Hends as [H1 H2].
  apply Bool.negb_true_iff in H1. split; [rewrite H1; discriminate|exact H2].
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_ends_with_label" *)
Theorem enc_secs_again_ends_with_label : forall pos labs ffis enc (lines res : list (sec a)) ok,
  enc_secs_again pos labs ffis enc lines = (res, ok) /\
  EVERY sec_ends_with_label lines ->
  EVERY sec_ends_with_label res.
Proof.
  intros pos labs ffis enc lines res ok (H & He).
  rewrite <- (code_similar_ends_with_label lines res); [exact He|].
  exact (enc_secs_again_IMP_similar _ _ _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_sec_list_ends_with_label" *)
Theorem enc_sec_list_ends_with_label : forall enc (code : list (sec a)),
  EVERY sec_ends_with_label code ->
  EVERY sec_ends_with_label (enc_sec_list enc code).
Proof.
  intros enc code H. rewrite (code_similar_ends_with_label _ code); [exact H|].
  apply code_similar_enc_sec_list, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_even_labels_append" *)
Theorem lines_even_labels_append : forall (l1 l2 : list (line a)) pos,
  lines_even_labels pos (l1 ++ l2) <->
  lines_even_labels pos l1 /\
  lines_even_labels (pos + SUM (MAP line_len l1)) l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 pos.
  - cbn. rewrite N.add_0_r. tauto.
  - cbn [app lines_even_labels MAP map SUM]. rewrite IH, N.add_assoc. tauto.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_zero_pos_ok_lines_even_labels" *)
Theorem label_zero_pos_ok_lines_even_labels : forall pos (ls : list (line a)),
  EVERY label_zero ls /\
  lab_len_pos_ok pos ls ->
  lines_even_labels pos ls.
Proof.
  intros pos ls; revert pos. induction ls as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos (Hz & Hp);
    [exact Logic.I| | |]; cbn [EVERY lab_len_pos_ok] in Hz, Hp;
    apply Bool.andb_true_iff in Hz as [Hz1 Hz]; apply Bool.andb_true_iff in Hp as [Hp1 Hp];
    (split; [|apply IH; split; assumption]).
  - intros _. cbn [label_zero] in Hz1. apply N.eqb_eq in Hz1. subst l. cbn [line_lab_len_pos_ok] in Hp1.
    destruct (EVEN pos); [reflexivity|discriminate].
  - intros Hc; discriminate.
  - intros Hc; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "label_zero_pos_ok_even_labels" *)
Theorem label_zero_pos_ok_even_labels : forall pos (code : list (sec a)),
  EVERY sec_label_zero code /\
  all_lab_len_pos_ok pos code ->
  even_labels pos code.
Proof.
  intros pos code; revert pos. induction code as [|[k ls] code IH]; intros pos (Hz & Hp); [exact Logic.I|].
  cbn [EVERY sec_label_zero all_lab_len_pos_ok] in Hz, Hp.
  apply Bool.andb_true_iff in Hz as [Hz1 Hz]. apply Bool.andb_true_iff in Hp as [Hp1 Hp].
  apply even_labels_alt. split; [apply label_zero_pos_ok_lines_even_labels; split; assumption|].
  apply IH. split; [exact Hz|]. rewrite sec_length_sum_line_len, N.add_0_r in Hp. exact Hp.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_code_ends_with_label" *)
Theorem pad_code_ends_with_label : forall nop (ls : list (sec a)),
  EVERY sec_ends_with_label ls ->
  EVERY sec_ends_with_label (pad_code nop ls).
Proof.
  intros nop ls H. rewrite <- (code_similar_ends_with_label ls); [exact H|].
  apply code_similar_pad_code, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_section_labels" *)
Theorem enc_lines_again_section_labels : forall labs ffis pos enc (lines res : list (line a)) acc,
  enc_lines_again_simp labs ffis pos enc lines = (res, true) ->
  section_labels pos lines acc = section_labels pos res acc.
Proof.
  intros labs ffis pos enc lines. revert pos.
  induction lines as [|[k1 k2 l|x1 x2 l|x w bytes l] xs IH]; intros pos res acc H;
    cbn [enc_lines_again_simp] in H.
  - injection H as <-. reflexivity.
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. cbn [section_labels]. destruct (k2 =? 0); apply IH; exact E.
  - destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
    injection H as <- ->. cbn [section_labels]. apply IH; exact E.
  - cbv zeta in H. destruct (decide _).
    + destruct (enc_lines_again_simp labs ffis (pos + l) enc xs) as [rest ok] eqn:E.
      injection H as <- ->. cbn [section_labels]. apply IH; exact E.
    + destruct (enc_lines_again_simp labs ffis _ enc xs) as [rest ok] eqn:E.
      injection H as <- Hok. apply Bool.andb_true_iff in Hok as [Hl ->].
      apply N.eqb_eq in Hl. cbn [section_labels]. rewrite Hl in E |- *. apply IH; exact E.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_compute_labels" *)
Theorem enc_secs_again_compute_labels : forall pos labs ffis enc (secs res : list (sec a)) acc,
  enc_secs_again pos labs ffis enc secs = (res, true) ->
  compute_labels_alt pos res acc =
  compute_labels_alt pos secs acc.
Proof.
  intros pos labs ffis enc secs; revert pos.
  induction secs as [|[k lines] rest IH]; intros pos res acc H; cbn [enc_secs_again] in H.
  - injection H as <-. reflexivity.
  - destruct (enc_lines_again labs ffis pos enc lines ([], true)) as [lines1 [pos1 ok1]] eqn:E1.
    destruct (enc_secs_again pos1 labs ffis enc rest) as [rest1 ok2] eqn:E2.
    injection H as <- Hok. apply Bool.andb_true_iff in Hok as [-> ->].
    destruct (enc_lines_again_simp_of _ _ _ _ _ _ _ _ E1) as [Es ->].
    cbn [compute_labels_alt].
    rewrite <- (enc_lines_again_section_labels _ _ _ _ _ _ [] Es).
    pose proof (section_labels_sec_length pos lines []) as Hp.
    destruct (section_labels pos lines []) as [np sl]. cbn [FST fst] in Hp.
    assert (Hl : sec_length lines1 pos = np).
    { rewrite Hp, !sec_length_sum_line_len, (enc_lines_again_simp_len _ _ _ _ _ _ Es). reflexivity. }
    rewrite Hl in E2. apply IH. exact E2.
Qed.

End ComputeLabels.

(** ** Labels of the padded code *)

Section PadLabels.
Context {a : N}.

Lemma section_labels_nonlabel pos (y : line a) rest acc :
  ~ is_Label y -> section_labels pos (y :: rest) acc = section_labels (pos + line_len y) rest acc.
Proof. destruct y; cbn; [intros H; exfalso; apply H; reflexivity|reflexivity|reflexivity]. Qed.

Lemma section_labels_nop_shift pos (y y' : line a) l1 l2 xs acc :
  ~ is_Label y -> ~ is_Label y' -> line_len y' = line_len y + 1 ->
  section_labels pos (y' :: Label l1 l2 0 :: xs) acc =
  section_labels pos (y :: Label l1 l2 1 :: xs) acc.
Proof.
  intros Hy Hy' Hl. rewrite (section_labels_nonlabel pos y') by exact Hy'.
  rewrite (section_labels_nonlabel pos y) by exact Hy. cbn [section_labels].
  rewrite Hl. replace (pos + (line_len y + 1) + 0) with (pos + line_len y + 1) by lia. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_section_labels" *)
Theorem pad_section_labels : forall nop (lines aux : list (line a)) pos labs,
  lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines /\
  lab_len_pos_ok pos (REVERSE aux) /\ EVERY label_zero aux /\
  (~ NULL lines /\ is_Label (HD lines) /\ line_len (HD lines) = 1 ->
   ~ NULL aux /\ ~ is_Label (HD aux)) ->
  section_labels pos (pad_section nop lines aux) labs =
  section_labels pos (REVERSE aux ++ lines) labs.
Proof.
  intros nop lines. induction lines as [|[k1 k2 len|x1 x2 l|y w bytes l] xs IH];
    intros aux pos labs (H1 & H2 & H3 & H4); cbn [pad_section].
  - rewrite app_nil_r. reflexivity.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len] in H1. apply Bool.andb_true_iff in H1 as [Hl H1].
    set (P := pos + SUM (MAP line_len aux)) in *.
    destruct (EVEN P) eqn:EP; apply N.eqb_eq in Hl; subst len.
    + rewrite N.eqb_refl. rewrite IH.
      * cbn [rev]. rewrite <- app_assoc. reflexivity.
      * split; [|split; [|split]].
        -- cbn [MAP map SUM line_len]. rewrite N.add_0_l. rewrite N.add_0_r in H1. exact H1.
        -- cbn [rev]. rewrite lab_len_pos_ok_append, H2. cbn [lab_len_pos_ok line_lab_len_pos_ok line_len].
           rewrite map_rev, SUM_rev. fold P. rewrite EP. reflexivity.
        -- cbn [EVERY label_zero N.eqb]. exact H3.
        -- intros (Hn & Hh & Hhl). exfalso. destruct xs as [|z zs]; [apply Hn; reflexivity|].
           destruct z as [m1 m2 ml| |]; try discriminate. cbn [HD line_len] in Hhl. subst ml.
           rewrite N.add_0_r in H1. cbn [lab_len_pos_ok line_lab_len_pos_ok line_len] in H1.
           rewrite EP in H1. discriminate.
    + assert (Hnn : ~ is_true (NULL (Label k1 k2 1 :: xs))) by (cbn; discriminate).
      specialize (H4 (conj Hnn (conj eq_refl eq_refl))). destruct H4 as [Hna Hh].
      destruct aux as [|h t]; [exfalso; apply Hna; reflexivity|]. cbn [HD] in Hh.
      destruct (add_nop_nonlabel_head nop h t Hh) as (h' & E & Hh' & Hlen & Hz & Hp).
      cbn [N.eqb Pos.eqb]. rewrite E. rewrite IH.
      * cbn [rev]. rewrite <- !app_assoc. cbn [app].
        rewrite !section_labels_append. apply section_labels_nop_shift; assumption.
      * split; [|split; [|split]].
        -- cbn [MAP map SUM line_len] in *. rewrite Hlen.
           replace (pos + (0 + (line_len h + 1 + SUM (MAP line_len t)))) with (P + 1) by (unfold P; lia).
           exact H1.
        -- cbn [rev] in H2 |- *. rewrite !lab_len_pos_ok_append in *.
           apply Bool.andb_true_iff in H2 as [H2a H2b]. rewrite H2a.
           cbn [lab_len_pos_ok] in H2b |- *. rewrite Hp.
           apply Bool.andb_true_iff in H2b as [H2b _]. rewrite H2b. cbn [andb line_lab_len_pos_ok].
           rewrite !map_app, !SUM_app, !map_rev, !SUM_rev. cbn [MAP map SUM]. rewrite Hlen.
           replace (pos + (SUM (MAP line_len t) + (line_len h + 1 + 0))) with (P + 1)
             by (unfold P; cbn [MAP map SUM]; lia).
           rewrite N.even_add, EP. reflexivity.
        -- cbn [EVERY label_zero N.eqb andb] in H3 |- *. rewrite Hz. exact H3.
        -- intros (Hn & Hhd & Hhl). exfalso. destruct xs as [|z zs]; [apply Hn; reflexivity|].
           destruct z as [m1 m2 ml| |]; try discriminate. cbn [HD line_len] in Hhl. subst ml.
           cbn [lab_len_pos_ok line_lab_len_pos_ok line_len] in H1.
           replace (P + 1) with (P + 1) in H1 by reflexivity.
           rewrite N.even_add, EP in H1. discriminate.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb] in H1. rewrite IH.
    + cbn [rev]. rewrite <- app_assoc. cbn [app]. rewrite !section_labels_append. reflexivity.
    + split; [|split; [|split]].
      * cbn [MAP map SUM line_len]. replace (pos + (l + SUM (MAP line_len aux))) with
          (pos + SUM (MAP line_len aux) + l) by lia. exact H1.
      * cbn [rev]. rewrite lab_len_pos_ok_append, H2. reflexivity.
      * exact H3.
      * intros _. split; discriminate.
  - cbn [lab_len_pos_ok line_lab_len_pos_ok line_len andb] in H1. rewrite IH.
    + cbn [rev]. rewrite <- app_assoc. cbn [app]. rewrite !section_labels_append. reflexivity.
    + split; [|split; [|split]].
      * cbn [MAP map SUM line_len]. replace (pos + (l + SUM (MAP line_len aux))) with
          (pos + SUM (MAP line_len aux) + l) by lia. exact H1.
      * cbn [rev]. rewrite lab_len_pos_ok_append, H2. reflexivity.
      * exact H3.
      * intros _. split; discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "pad_code_compute_labels" *)
Theorem pad_code_compute_labels : forall nop pos (code : list (sec a)) acc,
  EVERY sec_label_one code /\
  (LENGTH nop <> 1 -> EVERY sec_label_zero code) /\
  EVERY sec_label_prefix_zero code /\
  all_lab_len_pos_ok pos code ->
  compute_labels_alt pos (pad_code nop code) acc =
  compute_labels_alt pos code acc.
Proof.
  intros nop pos code; revert pos. induction code as [|[k lines] rest IH]; intros pos acc (H1 & H2 & H3 & H4);
    [reflexivity|].
  cbn [EVERY sec_label_one sec_label_prefix_zero all_lab_len_pos_ok] in H1, H3, H4.
  apply Bool.andb_true_iff in H1 as [H1a H1b]. apply Bool.andb_true_iff in H3 as [H3a H3b].
  apply Bool.andb_true_iff in H4 as [H4a H4b]. apply bool_decide_spec in H3a.
  cbn [pad_code compute_labels_alt].
  rewrite (pad_section_labels nop lines [] pos []).
  2:{ split; [cbn; rewrite N.add_0_r; exact H4a|split; [reflexivity|split; [reflexivity|]]].
      intros (Hn & Hh & Hl). exfalso. destruct lines as [|z zs]; [apply Hn; reflexivity|].
      destruct z as [m1 m2 ml| |]; try discriminate. cbn [HD line_len] in Hl. subst ml.
      apply lpz_Label in H3a as [Hc _]. discriminate. }
  cbn [rev app]. pose proof (section_labels_sec_length pos lines []) as Hp.
  destruct (section_labels pos lines []) as [np sl]. cbn [FST fst] in Hp. subst np.
  apply IH. split; [exact H1b|split; [|split; [exact H3b|]]].
  - intros Hn. specialize (H2 Hn). cbn [EVERY] in H2. apply Bool.andb_true_iff in H2 as [_ H2]. exact H2.
  - rewrite sec_length_sum_line_len. rewrite sec_length_sum_line_len, N.add_0_r in H4b.
    rewrite N.add_comm. exact H4b.
Qed.

End PadLabels.

(** ** Preservation of [all_enc_ok_pre] *)

Section EncOkPre.
Context {a : N}.

Lemma line_similar_line_ok_pre (c : asm_config a) (x y : line a) :
  line_similar x y -> line_ok_pre c x = line_ok_pre c y.
Proof. destruct x, y; cbn; intros H; try contradiction; try reflexivity. subst. reflexivity. Qed.

Lemma LIST_REL_line_ok_pre (c : asm_config a) (l1 l2 : list (line a)) :
  LIST_REL line_similar l1 l2 -> EVERY (line_ok_pre c) l1 = EVERY (line_ok_pre c) l2.
Proof. apply LIST_REL_EVERY_eq, line_similar_line_ok_pre. Qed.

Lemma code_similar_all_enc_ok_pre (c : asm_config a) (c1 c2 : list (sec a)) :
  code_similar c1 c2 -> all_enc_ok_pre c c1 = all_enc_ok_pre c c2.
Proof.
  revert c2. induction c1 as [|[k1 l1] c1 IH]; intros [|[k2 l2] c2] H; cbn in H; try contradiction.
  - reflexivity.
  - destruct H as (Hc & Hl & ->). cbn [EVERY sec_ok_pre].
    rewrite (IH _ Hc), (LIST_REL_line_ok_pre _ _ _ Hl). reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_lines_again_all_enc_ok_pre" *)
Theorem enc_lines_again_all_enc_ok_pre : forall labs ffis pos enc (lines : list (line a)) acc ok
    res ok' c,
  enc_lines_again labs ffis pos enc lines (acc, ok) = (res, ok') /\
  EVERY (line_ok_pre c) lines /\ EVERY (line_ok_pre c) acc ->
  EVERY (line_ok_pre c) res.
Proof.
  intros labs ffis pos enc lines acc ok res ok' c (H & H1 & H2).
  pose proof (enc_lines_again_IMP_similar labs ffis pos enc lines acc ok res ok' (REVERSE acc) H
                ltac:(apply LIST_REL_refl, line_similar_refl)) as Hs.
  rewrite <- (LIST_REL_line_ok_pre c _ _ Hs), EVERY_app, EVERY_rev, H1, H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "enc_secs_again_all_enc_ok_pre" *)
Theorem enc_secs_again_all_enc_ok_pre : forall pos labs ffis enc (ls res : list (sec a)) ok c,
  enc_secs_again pos labs ffis enc ls = (res, ok) /\ all_enc_ok_pre c ls ->
  all_enc_ok_pre c res.
Proof.
  intros pos labs ffis enc ls res ok c (H & H1).
  rewrite <- (code_similar_all_enc_ok_pre c ls res); [exact H1|].
  exact (enc_secs_again_IMP_similar _ _ _ _ _ _ _ H).
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_pre_add_nop" *)
Theorem line_ok_pre_add_nop : forall (c : asm_config a) nop (xs : list (line a)),
  EVERY (line_ok_pre c) xs ->
  EVERY (line_ok_pre c) (add_nop nop xs).
Proof.
  intros c nop xs H. rewrite <- (LIST_REL_line_ok_pre c xs); [exact H|].
  apply line_similar_add_nop_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_pre_pad_section" *)
Theorem line_ok_pre_pad_section : forall nop (xs acc : list (line a)) c,
  EVERY (line_ok_pre c) xs /\ EVERY (line_ok_pre c) acc ->
  EVERY (line_ok_pre c) (pad_section nop xs acc).
Proof.
  intros nop xs acc c (H1 & H2).
  rewrite <- (LIST_REL_line_ok_pre c (REVERSE acc ++ xs)); [|apply pad_section_similar].
  rewrite EVERY_app, EVERY_rev, H1, H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_pre_pad_code" *)
Theorem all_enc_ok_pre_pad_code : forall nop (code : list (sec a)) c,
  all_enc_ok_pre c code ->
  all_enc_ok_pre c (pad_code nop code).
Proof.
  intros nop code c H. rewrite <- (code_similar_all_enc_ok_pre c code); [exact H|].
  apply code_similar_pad_code, code_similar_refl.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_pre_lines_upd_lab_len" *)
Theorem all_enc_ok_pre_lines_upd_lab_len : forall (c : asm_config a) n (lines acc : list (line a)),
  EVERY (line_ok_pre c) lines /\
  EVERY (line_ok_pre c) acc ->
  EVERY (line_ok_pre c) (FST (lines_upd_lab_len n lines acc)).
Proof.
  intros c n lines acc (H1 & H2).
  rewrite (LIST_REL_line_ok_pre c _ (REVERSE acc ++ lines)); [|apply lines_upd_lab_len_similar].
  rewrite EVERY_app, EVERY_rev, H1, H2. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "all_enc_ok_pre_upd_lab_len" *)
Theorem all_enc_ok_pre_upd_lab_len : forall (c : asm_config a) n (code : list (sec a)),
  all_enc_ok_pre c code ->
  all_enc_ok_pre c (upd_lab_len n code).
Proof.
  intros c n code H. rewrite (code_similar_all_enc_ok_pre c _ code); [exact H|].
  apply code_similar_upd_lab_len, code_similar_refl.
Qed.

End EncOkPre.

(** ** Code alignment *)

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "EXP_IMP_ZERO_LT" *)
Theorem EXP_IMP_ZERO_LT : forall y x, 2 ^ y = x -> 0 < x.
Proof. intros y x <-. apply N.neq_0_lt_0, N.pow_nonzero. discriminate. Qed.

Section Alignment.
Context {a : N}.

Lemma enc_with_nop_EVEN (c : asm_config a) (i : asm.asm a) bytes :
  enc_ok c -> code_alignment c <> 0 -> enc_with_nop (encode c) i bytes -> EVEN (LENGTH bytes).
Proof.
  intros Hc Ha H. apply enc_with_nop_thm in H as [n ->].
  rewrite LENGTH_app, LENGTH_FLAT_REPLICATE, N.even_add, N.even_mul,
    !(enc_ok_EVEN c) by assumption.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "line_ok_alignment" *)
Theorem line_ok_alignment : forall (c : asm_config a) labs ffis pos (line : line a),
  enc_ok c /\
  line_ok c labs ffis pos line /\
  ODD (line_length line) ->
  code_alignment c = 0.
Proof.
  intros c labs ffis pos line (Hc & Hl & Ho).
  destruct (N.eq_dec (code_alignment c) 0) as [E|Ha]; [exact E|exfalso].
  assert (He : EVEN (line_length line)).
  { destruct line as [k1 k2 l|b bytes l|x w bytes l]; cbn [line_ok line_length] in Hl |- *.
    - destruct Hl as [_ ->]. reflexivity.
    - destruct Hl as (He & _). exact (enc_with_nop_EVEN _ _ _ Hc Ha He).
    - destruct x as [[l1 l2]|cc r ri [l1 l2]|v|r [l1 l2]|s| |]; cbn [get_label] in Hl; cbv zeta in Hl;
        try contradiction;
        try (destruct (lab_lookup l1 l2 labs); [|contradiction]);
        destruct Hl as (He & _); exact (enc_with_nop_EVEN _ _ _ Hc Ha He). }
  rewrite <- N.negb_even, He in Ho. discriminate.
Qed.

(*! HOL "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "has_odd_inst_alignment" *)
Theorem has_odd_inst_alignment : forall (c : asm_config a) labs ffis pos (code : list (sec a)),
  enc_ok c /\
  all_enc_ok c labs ffis pos code /\
  has_odd_inst code ->
  code_alignment c = 0.
Proof.
  intros c labs ffis pos code. revert pos.
  induction code as [|k ys IH|k y ys xs IH] using code_ind; intros pos (Hc & Hok & Ho).
  - discriminate.
  - destruct Hok as [_ Hok]. exact (IH pos (conj Hc (conj Hok Ho))).
  - destruct Hok as [Hy Hok]. rewrite (proj2 (proj2 (has_odd_inst_def k xs y ys))) in Ho.
    apply Bool.orb_true_iff in Ho as [Ho|Ho].
    + apply (line_ok_alignment c labs ffis pos y). split; [exact Hc|split; [exact Hy|]].
      rewrite <- N.negb_even. exact Ho.
    + exact (IH _ (conj Hc (conj Hok Ho))).
Qed.

End Alignment.
