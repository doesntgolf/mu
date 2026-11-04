(* The workspace in the browser. For now, it evaluates the program in a
   textarea as it's edited. *)
open Js_of_ocaml

let () =
  let input =
    Option.get (Dom_html.getElementById_coerce "input" Dom_html.CoerceTo.textarea)
  in
  let output = Dom_html.getElementById "output" in
  let update () =
    let text = match Bootstrap.run (Js.to_string input##.value) with Ok s | Error s -> s in
    output##.textContent := Js.some (Js.string text)
  in
  input##.oninput := Dom_html.handler (fun _ -> update (); Js._true);
  update ()
