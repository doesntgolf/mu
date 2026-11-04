(* The workspace: a structure editor for Mu programs, in the browser.

   The program is kept as source text, and shown as the syntax tree parsed
   from it, with a cell for each node. In normal mode, a cursor moves between
   cells. Editing a cell edits its text, and accepting the edit splices it
   into the source and parses the whole program again. *)
open Js_of_ocaml
open Bootstrap

let doc = Dom_html.document

type state = {
  mutable source : string;
  mutable parsed : Parsing.result;
  mutable cursor : int list; (* the selected node's path of child indices *)
  mutable editing : Dom_html.textAreaElement Js.t option;
  mutable message : string;
  mutable undo : string list;
}

(* Saved in the browser, so a reload doesn't lose the program *)
let storage_key = Js.string "mu-workspace"

let load () =
  try
    Js.Optdef.to_option Dom_html.window##.localStorage
    |> Fun.flip Option.bind (fun s -> Js.Opt.to_option (s##getItem storage_key))
    |> Option.map Js.to_string
  with _ -> None

let save source =
  try
    Js.Optdef.iter Dom_html.window##.localStorage (fun s ->
        s##setItem storage_key (Js.string source))
  with _ -> ()

let rec find (node : Syntax.t) = function
  | [] -> Some node
  | i :: path -> Option.bind (List.nth_opt node.children i) (fun child -> find child path)

(* The outermost node with the span, other than the whole program *)
let rec path_to start stop (node : Syntax.t) =
  let within () =
    List.find_mapi (fun i (child : Syntax.t) ->
        if child.start <= start && stop <= child.stop then
          Option.map (List.cons i) (path_to start stop child)
        else None)
      node.children
  in
  match node.start = start && node.stop = stop, node.form with
  | true, "program" -> Some (Option.value (within ()) ~default:[])
  | true, _ -> Some []
  | false, _ -> within ()

(* The longest prefix of a path that's still in the tree *)
let valid root path =
  let rec go node acc = function
    | i :: path ->
      begin match List.nth_opt node.Syntax.children i with
        | Some child -> go child (i :: acc) path
        | None -> List.rev acc
      end
    | [] -> List.rev acc
  in
  go root [] path

let selected st = Option.get (find st.parsed.syntax st.cursor)

let problem (node : Syntax.t) =
  match node.info with
  | Expr {expr = Error {msg; _}; _} | Pat {pat = Error {msg; _}; _} -> Some msg
  | _ -> None

let type_of (node : Syntax.t) =
  match node.info with
  | Expr e -> Some e.ty
  | Pat p -> Some p.ty
  | Other -> None

(* Layout. Blocks span several lines; everything else is inline. *)
let rec is_block (node : Syntax.t) =
  match node.form with
  | "let" | "abstract" | "recur" -> true
  | "match" -> List.length node.children > 2 || List.exists is_block node.children
  | _ -> List.exists is_block node.children

(* Where a block's lines break. Keywords like `in` and `->` end a line, and
   separators start one, so a list in brackets is laid out as
     { a
     , b
     }
   Each break is before a child, or before the closing bracket. *)
type break = Ends_line of bool | Starts_line of bool (* whether it's indented *)

let line_break (node : Syntax.t) i (child : Syntax.t) =
  let last = i = List.length node.children - 1 in
  let when_ cond break = if cond then Some break else None in
  match node.form with
  | "let" | "abstract" -> when_ last (Ends_line false)
  | "recur" -> when_ last (Ends_line true)
  | "match" -> when_ (i > 0) (Starts_line true)
  | "record" | "variant" | "parens" -> when_ (i > 0) (Starts_line false)
  | "apply" -> when_ (i > 1) (Starts_line false)
  (* Other blocks can start on the same line, and break within *)
  | _ -> when_ (last && List.mem child.form ["let"; "abstract"]) (Ends_line true)

let closing_break (node : Syntax.t) =
  match node.form with
  | "match" -> Some (Starts_line true)
  | "record" | "variant" | "parens" | "apply" -> Some (Starts_line false)
  | _ -> None

(* The source between nodes, with whitespace and comments collapsed *)
let between source start stop =
  let buf = Buffer.create 16 in
  let rec go pos =
    if pos < stop then begin
      let next = min stop (Parsing.skip source pos) in
      if next > pos then begin
        Buffer.add_char buf ' ';
        go next
      end else begin
        Buffer.add_char buf source.[pos];
        go (pos + 1)
      end
    end
  in
  go start;
  Buffer.contents buf

let text s = (doc##createTextNode (Js.string s) :> Dom.node Js.t)

let trim_end s =
  let n = ref (String.length s) in
  while !n > 0 && s.[!n - 1] = ' ' do decr n done;
  String.sub s 0 !n

(* Set below, once drawing the whole workspace is defined *)
let redraw = ref (fun () -> ())

let rec render st path (node : Syntax.t) : Dom.node Js.t =
  match st.editing with
  | Some area when path = st.cursor -> (area :> Dom.node Js.t)
  | _ ->
    let block = is_block node in
    (* Inline, even for blocks, whose lines are divs within *)
    let el = Dom_html.createSpan doc in
    let classes = ["node"; "form-" ^ node.form] in
    let classes = if path = st.cursor then "selected" :: classes else classes in
    let classes = if problem node <> None then "error" :: classes else classes in
    el##.className := Js.string (String.concat " " classes);
    Option.iter (fun msg -> el##.title := Js.string msg) (problem node);
    el##.onclick := Dom_html.handler (fun ev ->
        Dom_html.stopPropagation ev;
        if st.editing = None then begin
          st.cursor <- path;
          st.message <- "";
          !redraw ()
        end;
        Js._false);
    el##.ondblclick := Dom_html.handler (fun ev ->
        Dom_html.stopPropagation ev;
        st.cursor <- path;
        edit st;
        Js._false);
    let line = ref (el :> Dom.node Js.t) in
    let new_line indent =
      let div = Dom_html.createDiv doc in
      div##.className := Js.string (if indent then "line indent" else "line");
      Dom.appendChild el div;
      line := (div :> Dom.node Js.t)
    in
    (* The text before a break, which is put on one side of it. After a block,
       it's on a line of its own. *)
    let after_block = ref false in
    let put gap = function
      | Some (Ends_line indent) ->
        let gap = if !after_block then String.trim gap else trim_end gap in
        if gap <> "" then Dom.appendChild !line (text gap);
        new_line indent
      | Some (Starts_line indent) ->
        new_line indent;
        Dom.appendChild !line (text (String.trim gap ^ " "))
      | None -> Dom.appendChild !line (text gap)
    in
    let breaks =
      List.mapi (fun i child -> if block then line_break node i child else None) node.children
    in
    (* Brackets go on their own lines only when what's between them does *)
    let bracketed = List.exists (fun b -> b <> None) breaks && closing_break node <> None in
    let pos = ref node.start in
    List.iteri (fun i (child : Syntax.t) ->
        let gap = between st.source !pos child.start in
        let break = List.nth breaks i in
        (* Space after an opening bracket, to line up with the separators *)
        let gap =
          if i = 0 && bracketed && String.trim gap <> "" then String.trim gap ^ " " else gap
        in
        put gap break;
        Dom.appendChild !line (render st (path @ [i]) child);
        after_block := is_block child;
        pos := child.stop)
      node.children;
    let gap = between st.source !pos node.stop in
    if bracketed then put (String.trim gap) (closing_break node) else put gap None;
    (el :> Dom.node Js.t)

and edit st =
  let node = selected st in
  let area = Dom_html.createTextarea doc in
  area##.className := Js.string "cell";
  area##.value := Js.string (String.sub st.source node.start (node.stop - node.start));
  let fit () =
    let lines = String.split_on_char '\n' (Js.to_string area##.value) in
    area##.rows := List.length lines;
    area##.cols := List.fold_left (fun n l -> max n (String.length l + 1)) 4 lines
  in
  fit ();
  area##.oninput := Dom_html.handler (fun _ -> fit (); Js._true);
  st.editing <- Some area;
  st.message <- "";
  !redraw ();
  area##focus;
  area##select

(* The source with each span replaced by its text, if it parses *)
let reparse st edits =
  (* Last first, so the earlier spans stay put *)
  let edits = List.sort (fun (a, _, _) (b, _, _) -> Int.compare b a) edits in
  let source =
    List.fold_left (fun source (start, stop, text) ->
        String.sub source 0 start ^ text ^ String.sub source stop (String.length source - stop))
      st.source edits
  in
  match Parsing.parse source with
  | parsed -> Ok (source, parsed)
  | exception Compile_error msg -> Error msg

let commit st (source, (parsed : Parsing.result)) cursor =
  st.undo <- st.source :: st.undo;
  st.source <- source;
  st.parsed <- parsed;
  st.cursor <- valid parsed.syntax cursor;
  st.message <- "";
  save source

(* Moves the cursor to the node with the span [select] in the result *)
let rewrite st edits (start, stop) =
  match reparse st edits with
  | Ok ((_, parsed) as result) ->
    commit st result (Option.value (path_to start stop parsed.syntax) ~default:st.cursor);
    true
  | Error msg ->
    st.message <- msg;
    false

(* Replaces the selected node's text and stops editing, if the result parses
   with a node in its place. If it doesn't fit as is, it may with a hole for
   the body of a let (which is edited next), or in parentheses. *)
let accept st text =
  let node = selected st in
  let text = if String.trim text = "" then "_" else text in
  let attempt text =
    Result.bind (reparse st [node.start, node.stop, text]) (fun (source, parsed) ->
        match path_to node.start (node.start + String.length text) parsed.syntax with
        | Some path -> Ok ((source, parsed), path)
        | None -> Error "that doesn't fit here")
  in
  let finish ((_, parsed) as result, path) hole =
    st.editing <- None;
    match Option.bind hole (fun pos -> path_to pos (pos + 1) parsed.Parsing.syntax) with
    | Some hole -> commit st result hole; edit st
    | None -> commit st result path
  in
  (* The hole is the last character of the text *)
  let with_hole text = text, Some (node.start + String.length text - 1) in
  let rec first msg = function
    | [] -> st.message <- msg
    | (text, hole) :: rest ->
      match attempt text with
      | Ok result -> finish result hole
      | Error _ -> first msg rest
  in
  match attempt text with
  | Ok result -> finish result None
  | Error msg ->
    let trimmed = String.trim text in
    first msg [with_hole (trimmed ^ " in _"); with_hole (trimmed ^ " _"); "(" ^ text ^ ")", None]

(* Rows are a record's entries, a match's clauses, and the bindings of a
   chain of lets, which can be rearranged *)
let is_row (node : Syntax.t) = List.mem node.form ["entry"; "clause"; "binding"]

let split_last path =
  match List.rev path with
  | last :: rest -> List.rev rest, last
  | [] -> invalid_arg "split_last"

let node_at st path = Option.get (find st.parsed.syntax path)

let text_of st (node : Syntax.t) = String.sub st.source node.start (node.stop - node.start)

(* The innermost row at or around the cursor *)
let enclosing_row st =
  let rec go path =
    if is_row (node_at st path) then Some path
    else if path = [] then None
    else go (fst (split_last path))
  in
  go st.cursor

(* The paths of the rows before and after one. A binding's are the bindings
   of the lets around and within its own. *)
let neighbours st path =
  let node = node_at st path in
  let parent_path, i = split_last path in
  let parent = node_at st parent_path in
  let last_child (node : Syntax.t) = List.length node.children - 1 in
  match node.form with
  | "binding" ->
    let before =
      if parent_path = [] then None
      else
        let outer_path, j = split_last parent_path in
        let outer = node_at st outer_path in
        if outer.form = "let" && j = last_child outer then Some (outer_path @ [0]) else None
    in
    let body = last_child parent in
    let after =
      if (List.nth parent.children body).form = "let" then Some (parent_path @ [body; 0]) else None
    in
    before, after
  | _ ->
    let rows =
      List.concat (List.mapi (fun j (child : Syntax.t) ->
          if child.form = node.form then [j] else [])
          parent.children)
    in
    let before = List.fold_left (fun acc j -> if j < i then Some j else acc) None rows in
    let after = List.find_opt (fun j -> j > i) rows in
    Option.map (fun j -> parent_path @ [j]) before, Option.map (fun j -> parent_path @ [j]) after

(* Swaps the row around the cursor with the one before or after it *)
let move_row st up =
  match enclosing_row st with
  | None -> st.message <- "not in a row"
  | Some path ->
    let before, after = neighbours st path in
    match if up then before else after with
    | None -> ()
    | Some other ->
      let node = node_at st path and other = node_at st other in
      let a, b = if up then other, node else node, other in
      let length (n : Syntax.t) = n.stop - n.start in
      (* Where the moved row ends up *)
      let start = if up then a.start else a.start + length b + (b.start - a.stop) in
      ignore (rewrite st
                [a.start, a.stop, text_of st b; b.start, b.stop, text_of st a]
                (start, start + length node))

(* Deletes a row. An entry or clause goes with the comma on one side of it,
   and a binding with the rest of its let, leaving the let's body. *)
let delete_row st path =
  let node = node_at st path in
  let parent_path, i = split_last path in
  match node.form with
  | "binding" ->
    let parent = node_at st parent_path in
    let body = List.nth parent.children (List.length parent.children - 1) in
    ignore (rewrite st [parent.start, parent.stop, text_of st body]
              (parent.start, parent.start + body.stop - body.start))
  | _ ->
    let source = st.source in
    let after = Parsing.skip source node.stop in
    let rec back pos =
      if pos > 0 && String.contains " \t\r\n" source.[pos - 1] then back (pos - 1) else pos
    in
    let start, stop =
      if after < String.length source && source.[after] = ',' then
        node.start, Parsing.skip source (after + 1)
      else
        let before = back node.start in
        if before > 0 && source.[before - 1] = ',' then before - 1, node.stop
        else node.start, node.stop
    in
    match reparse st [start, stop, ""] with
    | Error msg -> st.message <- msg
    | Ok ((_, parsed) as result) ->
      (* The next row, which takes its place, or else the one before *)
      let is_row path =
        match find parsed.syntax path with
        | Some n -> n.form = node.form
        | None -> false
      in
      let cursor = List.find_opt is_row [path; parent_path @ [i - 1]] in
      commit st result (Option.value cursor ~default:parent_path)

(* Inserts a row of holes before or after the one around the cursor, and
   edits it *)
let insert_row st after =
  match enclosing_row st with
  | None -> st.message <- "not in a row"
  | Some path ->
    let node = node_at st path in
    let template = match node.form with "clause" -> "_ -> _" | "binding" -> "_ = _" | _ -> "_" in
    let pos, text, offset =
      match node.form with
      | "binding" ->
        let parent = node_at st (fst (split_last path)) in
        let body = List.nth parent.children (List.length parent.children - 1) in
        (if after then body.start else parent.start), "let " ^ template ^ " in ", 4
      | _ -> if after then node.stop, ", " ^ template, 2 else node.start, template ^ ", ", 0
    in
    if rewrite st [pos, pos, text] (pos + offset, pos + offset + String.length template) then
      edit st

let parse_or_hole source =
  match Parsing.parse source with
  | parsed -> source, parsed
  | exception Compile_error _ -> "_", Parsing.parse "_"

let output st =
  let {Parsing.expr; errors; _} = st.parsed in
  let value =
    match Runtime.eval [] expr with
    | value -> Runtime.show value
    | exception e -> "evaluation failed: " ^ Printexc.to_string e
  in
  String.concat "\n"
    (Printf.sprintf "the %s %s" (Type.show expr.ty) value
     :: List.map (fun (pos, msg) -> Parsing.describe st.source pos msg) errors)

let status st =
  let node = selected st in
  let ty = Option.fold ~none:"" ~some:(fun ty -> " : " ^ Type.show ty) (type_of node) in
  let problem = Option.fold ~none:"" ~some:(fun msg -> " - " ^ msg) (problem node) in
  let message = if st.message = "" then "" else "\n" ^ st.message in
  node.form ^ ty ^ problem ^ message

let draw st =
  let editor = Dom_html.getElementById "editor" in
  editor##.innerHTML := Js.string "";
  Dom.appendChild editor (render st [] st.parsed.syntax);
  let set id s = (Dom_html.getElementById id)##.textContent := Js.some (Js.string s) in
  set "status" (status st);
  set "output" (output st);
  set "source" st.source

let move st path =
  match find st.parsed.syntax path with
  | Some _ -> st.cursor <- path
  | None -> ()

let normal_key st key =
  let last = List.length st.cursor - 1 in
  let sibling d =
    if last >= 0 then
      move st (List.mapi (fun i x -> if i = last then x + d else x) st.cursor)
  in
  match key with
  | "ArrowLeft" | "h" -> sibling (-1); true
  | "ArrowRight" | "l" -> sibling 1; true
  | "ArrowUp" | "k" ->
    if last >= 0 then st.cursor <- List.filteri (fun i _ -> i < last) st.cursor;
    true
  | "ArrowDown" | "j" -> move st (st.cursor @ [0]); true
  | "Enter" | "i" -> edit st; true
  | "d" | "Delete" | "Backspace" ->
    if is_row (selected st) then delete_row st st.cursor else accept st "_";
    true
  | "K" -> move_row st true; true
  | "J" -> move_row st false; true
  | "o" -> insert_row st true; true
  | "O" -> insert_row st false; true
  | "u" ->
    begin match st.undo with
      | source :: rest ->
        let source, parsed = parse_or_hole source in
        st.source <- source;
        st.parsed <- parsed;
        st.undo <- rest;
        st.cursor <- valid parsed.syntax st.cursor
      | [] -> st.message <- "nothing to undo"
    end;
    true
  | _ -> false

let () =
  let source, parsed =
    parse_or_hole (Option.value (load ()) ~default:"let id(x) = x in id(#hello)")
  in
  let st = {source; parsed; cursor = []; editing = None; message = ""; undo = []} in
  st.cursor <- valid parsed.syntax [0];
  redraw := (fun () -> draw st);
  doc##.onkeydown := Dom_html.handler (fun ev ->
      let key = Js.Optdef.case ev##.key (fun () -> "") Js.to_string in
      let modified = Js.to_bool ev##.ctrlKey || Js.to_bool ev##.metaKey || Js.to_bool ev##.altKey in
      let handled =
        match st.editing with
        | Some area ->
          begin match key with
            | "Enter" when not (Js.to_bool ev##.shiftKey) ->
              accept st (Js.to_string area##.value);
              true
            | "Escape" -> st.editing <- None; st.message <- ""; true
            | _ -> false
          end
        | None -> not modified && normal_key st key
      in
      if handled then begin
        draw st;
        Option.iter (fun area -> area##focus) st.editing;
        Js._false
      end else Js._true);
  draw st
