(* Type-checks OCaml expressions without compiling or running them. Used by OCamlTyper.

   Reads one expression per line on stdin and answers each with a line, "ok" or "err". The
   arguments are extra directories to look for compiled interfaces in, besides the standard
   library's.

   Only the expression is typed, never bound, so the value restriction can't get in the way:
   ungeneralized type variables are never generalized or exported. *)
let () =
  Clflags.include_dirs := List.tl (Array.to_list Sys.argv);
  ignore (Warnings.parse_options false "-a");
  Compmisc.init_path ();
  let env = Compmisc.initial_env () in
  let check line =
    match Typecore.type_expression env (Parse.expression (Lexing.from_string line)) with
    | _ -> "ok"
    | exception _ -> "err"
  in
  try
    while true do
      print_endline (check (input_line stdin))
    done
  with End_of_file -> ()
