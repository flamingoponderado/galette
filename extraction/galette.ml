(* Galette: command-line driver for the extracted Pancake compiler.

   Mirrors the [main] function of CakeML's compiler64ProgScript.sml for
   [full_compile_64]: the command-line arguments (without the program name)
   and the whole of stdin are passed to [Galette_compiler.galette_main]
   (see Extract.v), which returns the stdout text (as a list of chunks, the
   flattened app_list), the stderr text, and whether the stderr text is an
   error message ([compiler$is_error_msg]).  On error CakeML's runtime
   reports "Program exited with nonzero exit code." on stderr and exits
   with code 1. *)

let explode s = List.init (String.length s) (String.get s)

let implode_to buf l = List.iter (Buffer.add_char buf) l

let () =
  set_binary_mode_in stdin true;
  set_binary_mode_out stdout true;
  set_binary_mode_out stderr true;
  let args = List.tl (Array.to_list Sys.argv) in
  let input = In_channel.input_all stdin in
  let ((out, err), is_err) =
    Galette_compiler.galette_main (List.map explode args) (explode input) in
  let buf = Buffer.create 65536 in
  List.iter (implode_to buf) out;
  print_string (Buffer.contents buf);
  flush stdout;
  let ebuf = Buffer.create 1024 in
  implode_to ebuf err;
  prerr_string (Buffer.contents ebuf);
  if is_err then begin
    prerr_string "Program exited with nonzero exit code.\n";
    flush stderr;
    exit 1
  end
