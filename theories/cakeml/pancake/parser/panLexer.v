(** * Pancake [panLexer]: the lexer

    Port of [cakeml/pancake/parser/panLexerScript.sml].

    - HOL [int] is [Z], [num] is [N], [string] is [list ascii] (literals in
      [hol_string_scope]); [«...»] mlstring literals are [strlit "..."].
    - HOL's [case x of #"\n" => ...] on characters is a [decide] test.
    - [next_atom] and [pancake_lex_aux] are well-founded recursions on the
      length of the input; they are defined with [Function] on that measure
      (the termination proofs are HOL's [next_atom_LESS]/[next_token_LESS]),
      so the extracted code recurses directly without any fuel.
      [pancake_lex_aux] is computed by the tail-recursive
      [pancake_lex_acc] (a deep non-tail recursion over hundreds of
      thousands of tokens makes OCaml's minor collections scan a deep
      stack); HOL's defining equation is the tagged
      [pancake_lex_aux_def].
    - HOL's [f ## I] (pair map) in [safe_pancake_lex] is written as the
      corresponding lambda. *)

From Stdlib Require Import Recdef.
From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option pair.
From Galette.HOL.src.string Require Import string ASCIInumbers.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.misc Require Import misc.
From Galette.HOL.examples.formal_languages.context_free Require Import location.
Open Scope N_scope.
Open Scope hol_string_scope.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "keyword" *)
Inductive keyword : Type :=
  SkipK | StK | StwK | St8K | St16K | St32K | IfK | ElseK | WhileK
| BrK | ContK | ThrowK | RetK | TicK | VarK | TryK | CatchK | BiwK | NamedK
| LdsK | Ld8K | LdwK | Ld16K | Ld32K | BaseK | TopK | InK | FunK | ExportK | TrueK | FalseK
| InlineK | ExceptionK.

#[global] Instance keyword_eq_dec : EqDecision keyword.
Proof. intros x y; unfold Decision; decide equality. Defined.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "token" *)
Inductive token : Type :=
  AndT | OrT | BoolAndT | BoolOrT | XorT | NotT | ArrowT
| EqT | NeqT | LessT | GreaterT | GeqT | LeqT | LowerT | HigherT | HigheqT | LoweqT
| PlusT | MinusT | DotT | StarT
| LslT | LsrT | AsrT | RorT
| IntT (i : Z) | IdentT (s : string) | ForeignIdent (s : string)
| LParT | RParT | CommaT | SemiT | ColonT | AddrT
| LBrakT | RBrakT | LCurT | RCurT
| AssignT
| StaticT
| NoinlineT
| DefaultShT
| KeywordT (k : keyword)
| AnnotCommentT (s : string)
| LexErrorT (m : mlstring).

#[global] Instance token_eq_dec : EqDecision token.
Proof.
  intros x y; unfold Decision.
  decide equality; apply decide; typeclasses eauto.
Defined.

#[global] Instance token_inhabited : Inhabited token := AndT.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "atom" *)
Inductive atom : Type :=
| NumberA (i : Z) | WordA (s : string) | SymA (s : string) | ErrA (m : mlstring)
| AnnotCommentA (s : string).

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "isAtom_singleton_def" *)
Definition isAtom_singleton (c : ascii) : bool := MEM c "+-^*().,;:[]{}".

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "isAtom_begin_group_def" *)
Definition isAtom_begin_group (c : ascii) : bool := MEM c "#=><!&|".

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "isAtom_in_group_def" *)
Definition isAtom_in_group (c : ascii) : bool := MEM c "=<>|&+".

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "isAlphaNumOrWild_def" *)
Definition isAlphaNumOrWild (c : ascii) : bool := isAlphaNum c || bool_decide (c = "_"%char).

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "isLexErrorT_def" *)
Definition isLexErrorT (t : token) : bool :=
  match t with LexErrorT _ => true | _ => false end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "dest_lexErrorT_def" *)
Definition destLexErrorT (t : token) : option mlstring :=
  match t with LexErrorT msg => SOME msg | _ => NONE end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "get_token_def" *)
Definition get_token (s : string) : token :=
  if decide (s = "&&") then BoolAndT else
  if decide (s = "||") then BoolOrT else
  if decide (s = "&") then AndT else
  if decide (s = "|") then OrT else
  if decide (s = "^") then XorT else
  if decide (s = "==") then EqT else
  if decide (s = "=>") then ArrowT else
  if decide (s = "!=") then NeqT else
  if decide (s = "<") then LessT else
  if decide (s = ">") then GreaterT else
  if decide (s = ">=") then GeqT else
  if decide (s = "<=") then LeqT else
  if decide (s = "<+") then LowerT else
  if decide (s = ">+") then HigherT else
  if decide (s = ">=+") then HigheqT else
  if decide (s = "<=+") then LoweqT else
  if decide (s = "!") then NotT else
  if decide (s = "+") then PlusT else
  if decide (s = "-") then MinusT else
  if decide (s = "*") then StarT else
  if decide (s = ".") then DotT else
  if decide (s = "<<") then LslT else
  if decide (s = ">>>") then LsrT else
  if decide (s = ">>") then AsrT else
  if decide (s = "#>>") then RorT else
  if decide (s = "(") then LParT else
  if decide (s = ")") then RParT else
  if decide (s = ",") then CommaT else
  if decide (s = ";") then SemiT else
  if decide (s = ":") then ColonT else
  if decide (s = "[") then LBrakT else
  if decide (s = "]") then RBrakT else
  if decide (s = "{") then LCurT else
  if decide (s = "}") then RCurT else
  if decide (s = "=") then AssignT else
  LexErrorT (concat [strlit "Unrecognised symbolic token: "; implode s]).

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "get_keyword_def" *)
Definition get_keyword (s : string) : token :=
  if decide (s = "skip") then (KeywordT SkipK) else
  if decide (s = "st") then (KeywordT StK) else
  if decide (s = "stw") then (KeywordT StwK) else
  if decide (s = "st8") then (KeywordT St8K) else
  if decide (s = "st16") then (KeywordT St16K) else
  if decide (s = "st32") then (KeywordT St32K) else
  if decide (s = "if") then (KeywordT IfK) else
  if decide (s = "else") then (KeywordT ElseK) else
  if decide (s = "while") then (KeywordT WhileK) else
  if decide (s = "break") then (KeywordT BrK) else
  if decide (s = "continue") then (KeywordT ContK) else
  if decide (s = "throw") then (KeywordT ThrowK) else
  if decide (s = "return") then (KeywordT RetK) else
  if decide (s = "tick") then (KeywordT TicK) else
  if decide (s = "var") then (KeywordT VarK) else
  if decide (s = "in") then (KeywordT InK) else
  if decide (s = "try") then (KeywordT TryK) else
  if decide (s = "catch") then (KeywordT CatchK) else
  if decide (s = "lds") then (KeywordT LdsK) else
  if decide (s = "ldw") then (KeywordT LdwK) else
  if decide (s = "ld8") then (KeywordT Ld8K) else
  if decide (s = "ld16") then (KeywordT Ld16K) else
  if decide (s = "ld32") then (KeywordT Ld32K) else
  if decide (s = "@base") then (KeywordT BaseK) else
  if decide (s = "@top") then (KeywordT BaseK) else
  if decide (s = "@biw") then (KeywordT BiwK) else
  if decide (s = "true") then (KeywordT TrueK) else
  if decide (s = "false") then (KeywordT FalseK) else
  if decide (s = "fun") then (KeywordT FunK) else
  if decide (s = "export") then (KeywordT ExportK) else
  if decide (s = "inline") then (KeywordT InlineK) else
  if decide (s = "exception") then (KeywordT ExceptionK) else
  if decide (s = "struct") then (KeywordT NamedK) else
  if decide (s = "") then LexErrorT (strlit "Expected keyword, found empty string") else
  if (2 <=? LENGTH s) && bool_decide (EL 0 s = "@"%char) then ForeignIdent (DROP 1 s)
  else IdentT s.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "token_of_atom_def" *)
Definition token_of_atom (a : atom) : token :=
  match a with
  | NumberA i => IntT i
  | WordA s => get_keyword s
  | SymA s => get_token s
  | ErrA s => LexErrorT s
  | AnnotCommentA s => AnnotCommentT s
  end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "read_while_def" *)
Fixpoint read_while (P : ascii -> bool) (input : string) (s : string) : string * string :=
  match input with
  | [] => (IMPLODE (REVERSE s), [])
  | c :: cs => if P c then read_while P cs (c :: s) else (IMPLODE (REVERSE s), c :: cs)
  end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "read_while_thm" *)
Theorem read_while_thm : forall P input s s' rest,
  read_while P input s = (s', rest) -> LENGTH rest <= LENGTH input.
Proof.
  intros P input; induction input as [|c cs IH]; intros s s' rest h; cbn in h.
  - injection h as _ <-; lia.
  - destruct (P c).
    + apply IH in h; cbn; lia.
    + injection h as _ <-; lia.
Qed.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "next_loc_def" *)
Definition next_loc (n : N) (l : locn) : locn :=
  match l with POSN r c => POSN r (c + n) | x => x end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "next_line_def" *)
Definition next_line (l : locn) : locn :=
  match l with POSN r c => POSN (r + 1) 0 | x => x end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "loc_row_def" *)
Definition loc_row (n : N) : locn := POSN n 1.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "skip_comment_def" *)
Fixpoint skip_comment (s : string) (loc : locn) (i : N) : option (locn * N) :=
  match s with
  | [] => NONE
  | x :: xs =>
      if decide (x = "010"%char) then SOME (next_line loc, i + 1)
      else skip_comment xs (next_loc 1 loc) (i + 1)
  end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "skip_block_comment_def" *)
Fixpoint skip_block_comment (s : string) (loc : locn) (i : N) : option (locn * (N * N)) :=
  match s with
  | [] => NONE
  | [_] => NONE
  | x :: ((y :: xs) as rest) =>
      if decide ((x = "*"%char /\ y = "/"%char) \/ (x = "@"%char /\ y = "/"%char)) then
        SOME (next_loc 2 loc, (i, i + 2))
      else if decide (x = "010"%char) then
        skip_block_comment rest (next_line loc) (i + 1)
      else
        skip_block_comment rest (next_loc 1 loc) (i + 1)
  end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "unhex_alt_def" *)
Definition unhex_alt (x : ascii) : N := if isHexDigit x then UNHEX x else 0.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "num_from_dec_string_alt_def" *)
Definition num_from_dec_string_alt : string -> N := s2n 10 unhex_alt.

Lemma length_DROP {A} n (l : list A) : (length (DROP n l) <= length l)%nat.
Proof. rewrite DROP_skipn, length_skipn; lia. Qed.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "next_atom_def" *)
Function next_atom (input : string) (loc : locn) {measure length input}
    : option (atom * (locs * string)) :=
  match input with
  | [] => NONE
  | c :: cs =>
    if decide (c = "010"%char) then (* Skip Newline *)
      next_atom cs (next_line loc)
    else if isSpace c then
      next_atom cs (next_loc 1 loc)
    else if isDigit c then
      let (n, cs') := read_while isDigit cs [c] in
        SOME (NumberA (Z.of_N (num_from_dec_string_alt n)),
              (Locs loc (next_loc (LENGTH n) loc), cs'))
    else if bool_decide (c = "-"%char /\ cs <> "") && isDigit (HD cs) then
      let (n, rest) := read_while isDigit cs [] in
      SOME (NumberA (0 - Z.of_N (num_from_dec_string_alt n)),
            (Locs loc (next_loc (LENGTH n) loc), rest))
    else if isPREFIX "//" (c :: cs) then (* comment *)
      match skip_comment (TL cs) (next_loc 2 loc) 0 with
      | NONE => SOME (ErrA (strlit "Malformed comment"), (Locs loc (next_loc 2 loc), ""))
      | SOME (loc', len) => next_atom (DROP (len + 1) cs) loc'
      end
    else if isPREFIX "/@" (c :: cs) then (* annotation block comment *)
      match skip_block_comment (TL cs) (next_loc 3 loc) 0 with
      | NONE => SOME (ErrA (strlit "Malformed comment"), (Locs loc (next_loc 3 loc), ""))
      | SOME (loc', (i, len)) => SOME (AnnotCommentA (TAKE i (TL cs)),
           (Locs loc loc', DROP (len + 1) cs))
      end
    else if isPREFIX "/*" (c :: cs) then (* block comment *)
      match skip_block_comment (TL cs) (next_loc 2 loc) 0 with
      | NONE => SOME (ErrA (strlit "Malformed comment"), (Locs loc (next_loc 2 loc), ""))
      | SOME (loc', (_, len)) => next_atom (DROP (len + 1) cs) loc'
      end
    else if isAtom_singleton c then
      SOME (SymA (STRING c []), (Locs loc loc, cs))
    else if isAtom_begin_group c then
      let (n, rest) := read_while isAtom_in_group cs [c] in
      SOME (SymA n, (Locs loc (next_loc (LENGTH n - 1) loc), rest))
    else if isAlpha c || bool_decide (c = "@"%char) || bool_decide (c = "_"%char) then
      (* read identifier *)
      let (n, rest) := read_while isAlphaNumOrWild cs [c] in
      SOME (WordA n, (Locs loc (next_loc (LENGTH n) loc), rest))
    else (* input not recognised *)
      SOME (ErrA (concat [strlit "Unrecognised symbol: "; chr_to_str c]), (Locs loc loc, cs))
  end.
Proof.
  all: intros; cbn; try lia.
  all: pose proof (length_DROP (len + 1) cs); lia.
Defined.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "next_atom_LESS" *)
Theorem next_atom_LESS : forall input l s l' rest,
  next_atom input l = SOME (s, (l', rest)) -> LENGTH rest < LENGTH input.
Proof.
  intros input l; functional induction (next_atom input l); intros s0 l0 rest0 h;
    try discriminate; try (apply IHo in h; cbn in *; lia);
    try (injection h as <- <- <-).
  all: rewrite ?LENGTH_length in *; cbn [length] in *; try lia.
  all: repeat match goal with
       | H : read_while _ _ _ = (_, _) |- _ =>
           apply read_while_thm in H; rewrite ?LENGTH_length in H; cbn [length] in H
       end; try lia.
  all: try (pose proof (length_DROP (len + 1) cs); lia).
  all: apply IHo in h; rewrite ?LENGTH_length in *; pose proof (length_DROP (len + 1) cs);
    cbn in *; lia.
Qed.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "next_token_def" *)
Definition next_token (input : string) (loc : locn) : option (token * (locs * string)) :=
  match next_atom input loc with
  | NONE => NONE
  | SOME (atom, (locs, rest)) => SOME (token_of_atom atom, (locs, rest))
  end.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "next_token_LESS" *)
Theorem next_token_LESS : forall s l l' rest input,
  next_token input l = SOME (s, (l', rest)) -> LENGTH rest < LENGTH input.
Proof.
  intros s l l' rest input; unfold next_token.
  destruct (next_atom input l) as [[a [ls r]]|] eqn:E; [|discriminate].
  intros h; injection h as _ <- <-; eapply next_atom_LESS, E.
Qed.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "init_loc_def" *)
Definition init_loc : locn := POSN 1 1.

(** [pancake_lex_acc input loc acc] is [REVERSE acc ++ pancake_lex_aux
    input loc], computed tail-recursively (a token list can be long);
    [rev_append acc []] is [REVERSE acc] computed in linear time. *)
Function pancake_lex_acc (input : string) (loc : locn) (acc : list (token * locs))
    {measure length input} : list (token * locs) :=
  match next_token input loc with
  | NONE => rev_append acc []
  | SOME (token, (Locs locB locE, rest)) =>
      pancake_lex_acc rest locE ((token, Locs locB locE) :: acc)
  end.
Proof.
  intros; apply next_token_LESS in teq; rewrite !LENGTH_length in teq; lia.
Defined.

Definition pancake_lex_aux (input : string) (loc : locn) : list (token * locs) :=
  pancake_lex_acc input loc [].

Lemma pancake_lex_acc_app input loc acc :
  pancake_lex_acc input loc acc = REVERSE acc ++ pancake_lex_acc input loc [].
Proof.
  revert loc acc; induction input as [input IH] using
    (well_founded_induction (well_founded_ltof _ (@length ascii))); intros loc acc.
  rewrite (pancake_lex_acc_equation input loc acc), (pancake_lex_acc_equation input loc []).
  destruct (next_token input loc) as [[token [[locB locE] rest]]|] eqn:E.
  - assert (hlt : (length rest < length input)%nat).
    { apply next_token_LESS in E; rewrite !LENGTH_length in E; lia. }
    rewrite (IH rest hlt locE ((token, Locs locB locE) :: acc)), (IH rest hlt locE [_]).
    cbn; rewrite <- app_assoc; reflexivity.
  - rewrite <- !rev_alt; cbn; rewrite app_nil_r; reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "pancake_lex_aux_def" *)
Theorem pancake_lex_aux_def : forall input loc,
  pancake_lex_aux input loc =
  match next_token input loc with
  | NONE => []
  | SOME (token, (Locs locB locE, rest)) =>
      (token, Locs locB locE) :: pancake_lex_aux rest locE
  end.
Proof.
  intros input loc; unfold pancake_lex_aux.
  rewrite pancake_lex_acc_equation.
  destruct (next_token input loc) as [[token [[locB locE] rest]]|]; [|reflexivity].
  rewrite pancake_lex_acc_app; reflexivity.
Qed.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "pancake_lex_def" *)
Definition pancake_lex (input : string) : list (token * locs) :=
  pancake_lex_aux input init_loc.

(*! HOL "cakeml/pancake/parser/panLexerScript.sml" "safe_pancake_lex_def" *)
Definition safe_pancake_lex (input : string)
    : list (token * locs) + list (mlstring * locs) :=
  let output := pancake_lex input in
  match FILTER (fun p => isLexErrorT (FST p)) output with
  | [] => inl output
  | xs => inr (MAP (fun p => (the (strlit "") (destLexErrorT (FST p)), SND p)) xs)
  end.
