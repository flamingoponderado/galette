let () =
  List.iter (fun z -> print_string (Z.to_string z ^ " ")) Galette_smoke.smoke;
  print_newline ()
