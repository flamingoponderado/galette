(* Driver: print the Rocq translation of HOL's arm8Theory (L3 ARMv8 model).
   Run by regen-arm8.sh, which sets L3GEN (this directory) and L3OUT (a
   scratch directory holding types.txt and defs.txt). *)
val _ = load "arm8Theory";
val _ = app load ["intSyntax", "stringSyntax", "fcpSyntax", "wordsSyntax", "listSyntax", "oneSyntax"];
val L3GEN = valOf (OS.Process.getEnv "L3GEN");
val L3OUT = valOf (OS.Process.getEnv "L3OUT");
use (L3GEN ^ "/gen.sml");
fun lines f = String.tokens (fn c => c = #"\n") (let val is = TextIO.openIn f in TextIO.inputAll is before TextIO.closeIn is end);
val tys = lines (L3OUT ^ "/types.txt");
val defs = lines (L3OUT ^ "/defs.txt");
val hol_path = "HOL/examples/l3-machine-code/arm8/model/arm8Script.sml";
val allconsts = map (fn c => #1 (dest_const c)) (constants "arm8");
val _ = Gen.THY := "arm8";
val _ = Gen.ty_rename := List.mapPartial (fn t => if mem t allconsts then SOME (t, t ^ "_ty") else NONE) tys;
val _ = Gen.type_names := map Gen.tyname tys;
val dts = map (Gen.pdatatype hol_path) tys;
val _ = Gen.theory_consts := List.concat (map #4 dts);
val used = HOLset.listItems (List.foldl (fn (n,s) => HOLset.addList (s, map (#1 o dest_const) (find_terms (fn t => is_const t andalso #Thy (dest_thy_const t) = "arm8") (concl (DB.fetch "arm8" n))))) (HOLset.empty String.compare) defs);
val enums = List.filter (fn t => mem (t ^ "2num") used orelse mem ("num2" ^ t) used) tys;
val body_defs = map (fn n => Gen.pdef hol_path (n, DB.fetch "arm8" n)) defs;
val out = TextIO.openOut (L3OUT ^ "/arm8.v.body");
val _ = TextIO.output (out, "(** ** Datatypes *)\n\n" ^ String.concatWith "\n" (map #1 dts) ^
   "\n(** ** Decidable equality (Galette infrastructure) *)\n\n" ^ String.concat (map #3 dts) ^
   "\n(** ** Record field updates (HOL [t_f_fupd]) *)\n\n" ^ String.concat (map #2 dts) ^
   "\n(** ** Enumerations as numbers (HOL [t2num], [num2t]) *)\n\n" ^ String.concatWith "\n" (map Gen.enum_helpers enums) ^
   "\n(** ** Definitions *)\n\n" ^ String.concatWith "\n" body_defs);
val _ = TextIO.closeOut out;
