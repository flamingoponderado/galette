(* HOL term -> Rocq printer for L3-generated theories (Galette).
   Usage (inside hol, after loading the theory):
     Gen.run {thy, script, hol_path, defs, out}                      *)

structure Gen = struct
open HolKernel boolLib

fun die s = raise Fail s
val concatS = String.concat
fun joinWith sep l = String.concatWith sep l

(* ---------- configuration (set by run) ---------- *)
val THY = ref "arm8"
val theory_consts : string list ref = ref []     (* names of constants defined so far *)
val type_names : string list ref = ref []
val ty_rename : (string * string) list ref = ref []

(* ---------- identifiers ---------- *)
val reserved =
  ["fun","match","with","end","let","in","if","then","else","as","return",
   "for","at","forall","exists","Type","Prop","Set","struct","fix","cofix",
   "IF","is","mod","land","lor","lxor","Definition","Inductive","Record",
   "Proof","Qed","from","using","where","SProp","exists2","S","O","Some",
   "None","true","false","nil","cons","pair","tt","inl","inr","Eq","Lt","Gt",
   "N0","Npos","Z0","Zpos","Zneg","xH","xO","xI","N","Z","ARB","K","I","T",
   "F","word","list","option","bool","unit","ascii","string","fst","snd",
   "value","sub","len","dimindex","Lsl","Lsr","Asr","Ror","Add","Sub","And",
   "Or","Xor","Load","Store","Skip","Equal","Less","Lower","Test","NotLess",
   "NotLower","NotEqual","NotTest","Reg","Imm","Addr","Mem","Inst","Jump",
   "Call","Loc","JumpCmp","JumpReg","Halt","Arith","Const","Binop","Shift",
   "Div","LongMul","LongDiv","AddCarry","AddOverflow","SubOverflow","FP"]

fun ident s =
  let
    fun tr c =
      if Char.isAlphaNum c orelse c = #"_" orelse c = #"'" then String.str c
      else if c = #"@" then "_" else "_"
  in String.translate tr s end

(* variables: avoid keywords, constructors, and theory constant names *)
fun varname s =
  let val s' = ident s
  in if mem s' reserved orelse mem s' (!theory_consts) orelse mem s' (!type_names)
     then s' ^ "'" else s' end

fun tyvarname ty =
  let val s = dest_vartype ty   (* 'N *)
  in ident (String.extract (s, 1, NONE)) ^ "w" end

fun constname s =
  if String.isPrefix "recordtype." s then
    (case String.tokens (fn c => c = #".") s of
       [_, t, _, f] => ident (t ^ "_" ^ f)
     | [_, t] => "Build_" ^ ident t
     | _ => ident s)
  else ident s
fun tyname s = case assoc1 s (!ty_rename) of SOME (_, r) => r | NONE => ident s

(* ---------- types ---------- *)
fun subtypes ty =
  if is_vartype ty then [ty]
  else ty :: List.concat (map subtypes (#Args (dest_thy_type ty)))
fun all_types tm = List.concat (map (subtypes o type_of) (find_terms (K true) tm))
fun numty n =
  if is_vartype n then tyvarname n
  else Arbnum.toString (fcpSyntax.dest_numeric_type n)

fun pty ty =
  if is_vartype ty then ident (String.extract (dest_vartype ty, 1, NONE)) ^ "T"
  else
  let val {Thy, Tyop, Args} = dest_thy_type ty
  in case (Thy, Tyop, Args) of
       ("min", "bool", []) => "bool"
     | ("num", "num", []) => "N"
     | ("integer", "int", []) => "Z"
     | ("one", "one", []) => "unit"
     | ("string", "char", []) => "ascii"
     | ("min", "fun", [a, b]) => "(" ^ pty a ^ " -> " ^ pty b ^ ")"
     | ("pair", "prod", [a, b]) => "(" ^ pty a ^ " * " ^ pty b ^ ")"
     | ("fcp", "cart", [b, n]) =>
         if b = bool then
           (let val w = numty n
            in if mem w ["1","2","3","4","5","6","7","8","12","13","16","20","21","32","64"]
               then "word" ^ w else "(word " ^ w ^ ")" end)
         else die "cart over non-bool"
     | ("list", "list", [a]) => "(list " ^ pty a ^ ")"
     | ("option", "option", [a]) => "(option " ^ pty a ^ ")"
     | (t, n, []) => if t = !THY then tyname n else die ("unknown type " ^ t ^ "$" ^ n)
     | (t, n, _) => die ("unknown type " ^ t ^ "$" ^ n)
  end

fun word_width ty = (* SOME width string if ty is a word type *)
  (case dest_thy_type ty of
     {Thy = "fcp", Tyop = "cart", Args = [b, n]} => if b = bool then SOME (numty n) else NONE
   | _ => NONE) handle HOL_ERR _ => NONE

(* ---------- polymorphism ---------- *)
fun sort_tyvars tvs = Listsort.sort (fn (a, b) => String.compare (dest_vartype a, dest_vartype b)) tvs

(* implicit-width parameters of a constant defined in this theory *)
fun const_params name =
  let val c = prim_mk_const {Thy = !THY, Name = name}
  in sort_tyvars (type_vars (type_of c)) end

(* ---------- terms ---------- *)
val used_vars = ref (HOLset.empty Term.compare)
fun with_used body f =
  let val old = !used_vars
      val _ = used_vars := HOLset.addList (old, free_vars body)
      val r = f ()
  in used_vars := old; r end
fun par s = "(" ^ s ^ ")"

fun is_lit t =
  numSyntax.is_numeral t orelse wordsSyntax.is_word_literal t orelse
  intSyntax.is_int_literal t orelse stringSyntax.is_string_literal t orelse
  stringSyntax.is_char_literal t

(* bound variables may need renaming: we keep a simple global policy *)
fun pvar v = varname (fst (dest_var v))

fun strlit t =
  let val s = stringSyntax.fromHOLstring t
  in "\"" ^ String.translate (fn #"\"" => "\"\"" | c => String.str c) s ^ "\"" end

fun list_elems t =
  if listSyntax.is_nil t then SOME []
  else if listSyntax.is_cons t then
    let val (h, tl) = listSyntax.dest_cons t
    in case list_elems tl of SOME l => SOME (h :: l) | NONE => NONE end
  else NONE

fun undetermined c args =
  (* does the result type of [c args] mention type variables of c's generic
     type that the argument types do not determine? *)
  let
    val {Thy, Name, Ty} = dest_thy_const c
    val gen = type_of (prim_mk_const {Thy = Thy, Name = Name})
    fun peel ty 0 acc = (rev acc, ty)
      | peel ty n acc = (let val (a, b) = dom_rng ty in peel b (n - 1) (a :: acc) end
                         handle HOL_ERR _ => (rev acc, ty))
    val (gargs, gres) = peel gen (length args) []
    val argtvs = List.concat (map type_vars gargs)
    val restvs = type_vars gres
  in List.exists (fn v => not (mem v argtvs)) restvs end

fun ascribe s ty = "(" ^ s ^ " : " ^ pty ty ^ ")"

fun binop_sym thy name =
  case (thy, name) of
    ("arithmetic", "+") => SOME "+" | ("arithmetic", "-") => SOME "-"
  | ("arithmetic", "*") => SOME "*" | ("arithmetic", "DIV") => SOME "/"
  | ("arithmetic", "MOD") => SOME "mod" | ("arithmetic", "EXP") => SOME "^"
  | ("prim_rec", "<") => SOME "<?" | ("arithmetic", "<=") => SOME "<=?"
  | ("bool", "/\\") => SOME "&&" | ("bool", "\\/") => SOME "||"
  | _ => NONE

fun zbin name =
  case name of
    "int_add" => SOME "Z.add" | "int_sub" => SOME "Z.sub" | "int_mul" => SOME "Z.mul"
  | "int_lt" => SOME "Z.ltb" | "int_le" => SOME "Z.leb" | _ => NONE

(* conditions and bindings for matching a pattern against an expression
   string (only tuples / literals / variables / wildcards) *)
fun pat_conds pat e =
  if is_var pat then ([], [(pat, e)])
  else if is_lit pat then (["bool_decide (" ^ e ^ " = " ^ pt pat ^ ")"], [])
  else if pairSyntax.is_pair pat then
    let val (a, b) = pairSyntax.dest_pair pat
        val (c1, b1) = pat_conds a ("(fst " ^ e ^ ")")
        val (c2, b2) = pat_conds b ("(snd " ^ e ^ ")")
    in (c1 @ c2, b1 @ b2) end
  else if aconv pat T then (["(" ^ e ^ ")"], [])
  else if aconv pat F then (["(negb " ^ e ^ ")"], [])
  else die ("pat_conds: " ^ term_to_string pat)

and ppat p =
  if is_var p then (if HOLset.member (!used_vars, p) then pvar p else "_" ^ pvar p)
  else if is_lit p then pt p
  else if pairSyntax.is_pair p then
    let val (a, b) = pairSyntax.dest_pair p in "(" ^ ppat a ^ ", " ^ ppat b ^ ")" end
  else if aconv p T then "true" else if aconv p F then "false"
  else if listSyntax.is_nil p then "[]"
  else if listSyntax.is_cons p then
    let val (h, tl) = listSyntax.dest_cons p in "(" ^ ppat h ^ " :: " ^ ppat tl ^ ")" end
  else
    let val (f, args) = strip_comb p
        val {Name, Thy, ...} = dest_thy_const f
        val n = case (Thy, Name) of
                  ("option", "SOME") => "Some" | ("option", "NONE") => "None"
                | _ => constname Name
    in if null args then n else "(" ^ n ^ " " ^ joinWith " " (map ppat args) ^ ")" end

and has_lit p =
  is_lit p orelse
  (pairSyntax.is_pair p andalso
     let val (a, b) = pairSyntax.dest_pair p in has_lit a orelse has_lit b end) orelse
  ((is_comb p) andalso not (pairSyntax.is_pair p) andalso
     List.exists has_lit (snd (strip_comb p)))

and pcase t =
  let val (scrut, rows) = TypeBase.strip_case t
  in
    if List.exists (fn (p, _) => has_lit p orelse aconv p T orelse aconv p F) rows
       andalso not (type_of scrut = bool)
    then
      (* HOL's first-match semantics over literal patterns: an if-chain *)
      let
        val sv = "scrut'"
        fun go [] = "ARB"
          | go ((p, r) :: rest) =
              let val (cs, bs) = pat_conds p sv
                  val body = List.foldr (fn ((v, e), acc) =>
                                "(let " ^ pvar v ^ " := " ^ e ^ " in " ^ acc ^ ")")
                               (pt r) bs
              in if null cs then body
                 else "(if " ^ joinWith " && " cs ^ " then " ^ body ^ " else " ^ go rest ^ ")"
              end
      in "(let " ^ sv ^ " := " ^ pt scrut ^ " in " ^ go rows ^ ")" end
    else
      "(match " ^ pt scrut ^ " with" ^
      concatS (map (fn (p, r) => "\n | " ^ with_used r (fn () => ppat p) ^ " => " ^ pt r) rows) ^ "\n end)"
  end

and pabs_s t =
  if pairSyntax.is_pabs t andalso not (is_abs t) then
    let val (p, b) = pairSyntax.dest_pabs t
    in "(fun '(" ^ with_used b (fn () => ppat_tuple p) ^ " : " ^ pty (type_of p) ^ ") => " ^ pt b ^ ")" end
  else
    let val (v, b) = dest_abs t
    in "(fun (" ^ pvar v ^ " : " ^ pty (type_of v) ^ ") => " ^ pt b ^ ")" end

and ppat_tuple p =  (* without outer parens around the whole tuple *)
  if pairSyntax.is_pair p then
    let val (a, b) = pairSyntax.dest_pair p in ppat a ^ ", " ^ ppat b end
  else ppat p

and plet t =
  let val (f, arg) = boolSyntax.dest_let t
  in
    if is_abs f then
      let val (v, b) = dest_abs f
      in "(let " ^ pvar v ^ " := " ^ pt arg ^ " in\n " ^ pt b ^ ")" end
    else
      let val (p, b) = pairSyntax.dest_pabs f
      in "(let '(" ^ with_used b (fn () => ppat_tuple p) ^ ") := " ^ pt arg ^ " in\n " ^ pt b ^ ")" end
  end

and pt t =
  if is_var t then pvar t
  else if aconv t T then "true" else if aconv t F then "false"
  else if numSyntax.is_numeral t then Arbnum.toString (numSyntax.dest_numeral t)
  else if wordsSyntax.is_word_literal t then
    "(n2w " ^ Arbnum.toString (wordsSyntax.dest_word_literal t) ^ " : " ^ pty (type_of t) ^ ")"
  else if intSyntax.is_int_literal t then
    (let val i = intSyntax.int_of_term t
          in "(" ^ (if Arbint.< (i, Arbint.zero) then "-" ^ Arbnum.toString (Arbint.toNat (Arbint.~ i))
                    else Arbnum.toString (Arbint.toNat i)) ^ ")%Z" end)
  else if stringSyntax.is_string_literal t then strlit t
  else if fcpSyntax.is_dimindex t then "(dimindex " ^ numty (fcpSyntax.dest_dimindex t) ^ ")"
  else if boolSyntax.is_let t then plet t
  else if boolSyntax.is_cond t then
    let val (c, a, b) = boolSyntax.dest_cond t
    in "(if " ^ pt c ^ " then " ^ pt a ^ " else " ^ pt b ^ ")" end
  else if TypeBase.is_case t then pcase t
  else if is_abs t orelse pairSyntax.is_pabs t then pabs_s t
  else if pairSyntax.is_pair t then
    let val (a, b) = pairSyntax.dest_pair t in "(" ^ pt a ^ ", " ^ pt b ^ ")" end
  else if is_eq t then
    let val (a, b) = dest_eq t in "(bool_decide (" ^ pt a ^ " = " ^ pt b ^ "))" end
  else if boolSyntax.is_neg t then "(negb " ^ pt (boolSyntax.dest_neg t) ^ ")"
  else if boolSyntax.is_imp_only t then
    let val (a, b) = boolSyntax.dest_imp t in "(implb " ^ pt a ^ " " ^ pt b ^ ")" end
  else if listSyntax.is_cons t orelse listSyntax.is_nil t then
    (case list_elems t of
       SOME [] => "[]"
     | SOME l => "[" ^ joinWith "; " (map pt l) ^ "]"
     | NONE => let val (h, tl) = listSyntax.dest_cons t in "(" ^ pt h ^ " :: " ^ pt tl ^ ")" end)
  else
    let val (f, args) = strip_comb t
    in
      if is_var f then "(" ^ joinWith " " (pvar f :: map pt args) ^ ")"
      else if is_abs f then "(" ^ joinWith " " (pt f :: map pt args) ^ ")"
      else papp f args t
    end

and papp f args t =
  let
    val {Thy, Name, Ty} = dest_thy_const f
    fun app n = if null args then n else "(" ^ joinWith " " (n :: map pt args) ^ ")"
  in
    case (Thy, Name, args) of
      ("bool", "ARB", []) => "ARB"
    | ("one", "one", []) => "tt"
    | ("state_transformer", "FOR", x :: rest) =>
        (* state_transformer's FOR takes Galette's left-nested triple *)
        let val (i, r) = pairSyntax.dest_pair x
            val (j, a) = pairSyntax.dest_pair r
            val h = "(FOR (" ^ pt i ^ ", " ^ pt j ^ ", " ^ pt a ^ "))"
        in if null rest then h else "(" ^ joinWith " " (h :: map pt rest) ^ ")" end
    | ("option", "SOME", _) => app "Some"
    | ("option", "NONE", []) => "None"
    | ("option", "THE", _) => app "THE"
    | ("option", "IS_SOME", _) => app "IS_SOME"
    | ("pair", "FST", _) => app "fst"
    | ("pair", "SND", _) => app "snd"
    | ("combin", "K", [x]) => "(fun _ => " ^ pt x ^ ")"
    | ("combin", "K", [x, _]) => pt x
    | ("combin", "UPDATE", _) => app "UPDATE"
    | ("combin", "o", [g, h]) => "(" ^ pt g ^ " ∘ " ^ pt h ^ ")"
    | ("list", "APPEND", [a, b]) => "(" ^ pt a ^ " ++ " ^ pt b ^ ")"
    | ("list", n, _) => app n
    | ("integer", "int_of_num", _) => app "Z.of_N"
    | ("integer", "Num", _) => app "Z.to_N"
    | ("integer", "int_neg", _) => app "Z.opp"
    | ("integer", n, [a, b]) =>
        (case zbin n of SOME z => "(" ^ z ^ " " ^ pt a ^ " " ^ pt b ^ ")"
                      | NONE => die ("integer op " ^ n))
    | ("arithmetic", "MIN", _) => app "N.min"
    | ("arithmetic", "MAX", _) => app "N.max"
    | ("arithmetic", ">", [a, b]) => "(" ^ pt b ^ " <? " ^ pt a ^ ")"
    | ("arithmetic", ">=", [a, b]) => "(" ^ pt b ^ " <=? " ^ pt a ^ ")"
    | ("pred_set", "EMPTY", []) => "{}"
    | ("bool", "IN", [a, b]) => "(bool_decide (" ^ pt a ^ " IN " ^ pt b ^ "))"
    | ("pred_set", "INSERT", [a, b]) => "(" ^ pt a ^ " INSERT " ^ pt b ^ ")"
    | ("bool", "literal_case", _) => die "literal_case"
    | (thy, n, [a, b]) =>
        (case binop_sym thy n of
           SOME s => "(" ^ pt a ^ " " ^ s ^ " " ^ pt b ^ ")"
         | NONE => gen_app f args t)
    | _ => gen_app f args t
  end

and gen_app f args t =
  let
    val {Thy, Name, Ty} = dest_thy_const f
    val head =
      if Thy = !THY then
        let val ps = const_params Name handle HOL_ERR _ => []
        in if null ps then constname Name
           else
             let val gen = type_of (prim_mk_const {Thy = Thy, Name = Name})
                 val s = match_type gen Ty
                 fun is_width v = List.exists (fn t => (case dest_thy_type t of
                                {Thy = "fcp", Tyop = "cart", Args = [_, n]} => n = v | _ => false)
                                handle HOL_ERR _ => false) (subtypes gen)
             fun inst v =
               let val ty = case subst_assoc (fn x => x = v) s of SOME ty => ty | NONE => v
               in if is_width v then "(" ^ tyvarname v ^ ":=" ^ numty ty ^ ")"
                  else "(" ^ pty v ^ ":=" ^ pty ty ^ ")" end
             in "(" ^ constname Name ^ " " ^ joinWith " " (map inst ps) ^ ")" end
        end
      else constname Name
    val s = if null args then head else "(" ^ joinWith " " (head :: map pt args) ^ ")"
  in
    if Thy <> !THY andalso undetermined f args then ascribe s (type_of t) else s
  end

(* ---------- definitions ---------- *)

fun hol_tag hol_path name = "(*! HOL \"" ^ hol_path ^ "\" \"" ^ name ^ "\" *)\n"

fun pdef hol_path (defname, th) =
  let
    val eqs = strip_conj (concl th)
    val eq = case eqs of [e] => e | _ => die ("multi-clause " ^ defname)
    val (_, eq) = strip_forall eq
    val (lhs, rhs) = dest_eq eq
    val (c, largs) = strip_comb lhs
    val {Name, ...} = dest_thy_const c
    val ps = const_params Name
    fun width_var v = List.exists (fn t => (case dest_thy_type t of
                          {Thy = "fcp", Tyop = "cart", Args = [_, n]} => n = v | _ => false)
                          handle HOL_ERR _ => false) (all_types (concl th))
    val implicits = concatS (map (fn v => if width_var v then " {" ^ tyvarname v ^ " : N}"
                       else " {" ^ pty v ^ " : Type} `{Inhabited " ^ pty v ^ "}") ps)
    fun parg a =
      if is_var a then " (" ^ pvar a ^ " : " ^ pty (type_of a) ^ ")"
      else if pairSyntax.is_pair a then " '((" ^ with_used rhs (fn () => ppat_tuple a) ^ ") : " ^ pty (type_of a) ^ ")"
      else if aconv a oneSyntax.one_tm then " (_ : unit)"
      else die ("lhs arg " ^ term_to_string a)
    val recursive = List.exists (fn x => same_const x c) (find_terms is_const rhs)
    val body = pt rhs
    val txt =
      hol_tag hol_path defname ^
      (if recursive then "(* RECURSIVE: needs hand translation *)\n" else "") ^
      "Definition " ^ constname Name ^ implicits ^ concatS (map parg largs) ^
      " : " ^ pty (type_of rhs) ^ " :=\n  " ^ body ^ ".\n"
  in
    theory_consts := constname Name :: !theory_consts;
    txt
  end
  handle Fail s => "(* FAILED " ^ defname ^ ": " ^ s ^ " *)\n"
       | e => "(* FAILED " ^ defname ^ ": " ^ General.exnMessage e ^ " *)\n"

(* ---------- datatypes ---------- *)
fun is_record ty = not (null (TypeBase.fields_of ty)) handle HOL_ERR _ => false

fun has_fun_type ty =
  (is_vartype ty andalso false) orelse
  (not (is_vartype ty) andalso
   let val {Tyop, Thy, Args} = dest_thy_type ty
   in (Thy = "min" andalso Tyop = "fun") orelse List.exists has_fun_type Args end)

fun pdatatype hol_path tname =
  let
    val ty = mk_thy_type {Thy = !THY, Tyop = tname, Args = []}
    val rn = tyname tname
  in
    if is_record ty then
      let
        val fs = TypeBase.fields_of ty
        val flds = map (fn (f, {ty = fty, ...}) => (tname ^ "_" ^ f, fty)) fs
        val decl =
          hol_tag hol_path tname ^
          "(** HOL record type [" ^ tname ^ "] (L3 [Record]); fields are named after HOL's\n" ^
          "    accessor constants. *)\n" ^
          "Record " ^ rn ^ " : Type := {\n" ^
          concatS (map (fn (f, fty) => "  " ^ constname f ^ " : " ^ pty fty ^ ";\n") flds) ^ "}.\n"
        val inh =
          "#[global] Instance " ^ rn ^ "_inhabited : Inhabited " ^ rn ^ " :=\n  {| " ^
          joinWith "; " (map (fn (f, _) => constname f ^ " := inhabitant _") flds) ^ " |}.\n"
        val fupds = concatS (map (fn (f, fty) =>
            "Definition " ^ constname f ^ "_fupd (g : " ^ pty fty ^ " -> " ^ pty fty ^ ") (r : " ^ rn ^
            ") : " ^ rn ^ " :=\n  {| " ^
            joinWith "; " (map (fn (f', _) =>
               constname f' ^ " := " ^ (if f' = f then "g (" ^ constname f ^ " r)" else constname f' ^ " r")) flds) ^
            " |}.\n") flds)
        val eqd = if List.exists (fn (_, t) => has_fun_type t) flds then ""
                  else "#[global] Instance " ^ rn ^ "_eq_dec : EqDecision " ^ rn ^ ".\n" ^
                       "Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.\n"
      in (decl ^ inh, fupds, eqd, map fst flds) end
    else
      let
        val cs = TypeBase.constructors_of ty
        fun pc c =
          let val (n, cty) = dest_const c
              val (argtys, _) = strip_fun cty
          in "| " ^ constname n ^ " : " ^ concatS (map (fn a => pty a ^ " -> ") argtys) ^ rn ^ "\n" end
        val decl =
          hol_tag hol_path tname ^
          "(** HOL datatype [" ^ tname ^ "] (L3 [Construct]). *)\n" ^
          "Inductive " ^ rn ^ " : Type :=\n" ^ concatS (map pc cs) ^ ".\n"
        val c0 = hd cs
        val (n0, t0) = dest_const c0
        val inh = "#[global] Instance " ^ rn ^ "_inhabited : Inhabited " ^ rn ^ " := " ^
                  (if null (fst (strip_fun t0)) then constname n0
                   else constname n0 ^ " (inhabitant _)") ^ ".\n"
        val eqd = "#[global] Instance " ^ rn ^ "_eq_dec : EqDecision " ^ rn ^ ".\n" ^
                  "Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.\n"
      in (decl ^ inh, "", eqd, map (constname o fst o dest_const) cs) end
  end

fun enum_helpers tname =
  let
    val ty = mk_thy_type {Thy = !THY, Tyop = tname, Args = []}
    val cs = TypeBase.constructors_of ty
    val rn = tyname tname
    val n = length cs
    val idx = List.tabulate (n, fn i => (i, constname (fst (dest_const (List.nth (cs, i))))))
  in
    if List.exists (fn c => not (null (fst (strip_fun (type_of c))))) cs then ""
    else
      "Definition " ^ tname ^ "2num (x : " ^ rn ^ ") : N :=\n  match x with\n" ^
      concatS (map (fn (i, c) => "  | " ^ c ^ " => " ^ Int.toString i ^ "\n") idx) ^ "  end.\n" ^
      "Definition num2" ^ tname ^ " (n : N) : " ^ rn ^ " :=\n  " ^
      concatS (map (fn (i, c) => "if n =? " ^ Int.toString i ^ " then " ^ c ^ "\n  else ") idx) ^ "ARB.\n"
  end

end
