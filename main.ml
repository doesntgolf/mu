let main () =
  let cmd =
    match Sys.argv.(1) with
    | "-h"
    | "--help" -> `Usage
    | "-v"
    | "--version" -> `Version
    | "-"
    | "--" ->`Prog In_channel.(input_all stdin)
    | "-e"
    | "--eval" -> `Prog Sys.argv.(2)
    | fname -> `Prog In_channel.(with_open_bin fname input_all)
    | exception (Invalid_argument _) -> `Usage
  in
  match cmd with
  | `Usage ->
    let bin_name = Sys.argv.(0) in
    Printf.printf {|usage: %s [command]
Available commands are:
  -h or --help		Print this help text.
  -e or --eval 'code'	Parse, typecheck, and evaluate 'code'.
  -v or --version	Show version information.
  - or --		Parse, typecheck, and evaluate code from stdin.
  'filename'		Parse, typecheck, and evaluate code from file 'filename'
|} bin_name;
    0

  | `Version ->
    print_endline "Mu 0.0.0 alpha";
    0

  | `Prog code ->
    match Bootstrap.run code with
    | Ok out -> print_endline out; 0
    | Error msg -> print_endline msg; 1

let () = exit (main ())
