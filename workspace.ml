(* The workspace: a structure editor for Mu programs, in the browser.

   The program is kept as source text, and shown as the syntax tree parsed
   from it. In normal mode, a cursor moves between nodes. In editing mode, a
   cell of raw text sits in a hole, or after a node, and as each token typed
   in it is finished, it's turned into structure: it's put in the source,
   which is parsed with whatever it's missing filled in, like the holes and
   closing tokens of a construct, and the cell moves on into the next hole. *)
open Js_of_ocaml
open Bootstrap

let doc = Dom_html.document

(* The prelude, or if it doesn't load, an empty one and why *)
let prelude, prelude_error =
  match load_prelude Prelude.source with
  | Ok prelude -> prelude, ""
  | Error msg -> {vars = []; env = []}, msg

let parse source = Parsing.parse ~vars:prelude.vars source

(* The cell being edited is raw text at a span of the source. The span holds
   the text if it parses there as a node, or else [fallback], which does: a
   hole, or nothing for a cell after a node. *)
type cell = {
  mutable start : int;
  mutable stop : int;
  mutable fallback : string;
  mutable text : string;
  mutable anchor : int; (* the selection in the text, from anchor to caret *)
  mutable caret : int;
  before : string; (* the source when editing began, for undo *)
}

type state = {
  mutable source : string;
  mutable parsed : Parsing.result;
  mutable cursor : int list; (* the selected node's path of child indices *)
  mutable editing : cell option;
  mutable message : string;
  mutable undo : string list;
  area : Dom_html.element Js.t; (* the cell's element, kept across redraws *)
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

(* The innermost node that ends at a position *)
let rec ending_at pos path (node : Syntax.t) =
  let within =
    List.find_mapi (fun i (child : Syntax.t) ->
        if child.start < pos && pos <= child.stop then ending_at pos (path @ [i]) child else None)
      node.children
  in
  if within = None && node.stop = pos && path <> [] then Some path else within

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

let node_at st path = Option.get (find st.parsed.syntax path)

let text_of st (node : Syntax.t) = String.sub st.source node.start (node.stop - node.start)

let problem (node : Syntax.t) =
  match node.info with
  | Expr {expr = Error {msg; _}; _} | Pat {pat = Error {msg; _}; _} -> Some msg
  | _ -> None

let type_of (node : Syntax.t) =
  match node.info with
  | Expr e -> Some e.ty
  | Pat p -> Some p.ty
  | Other -> None

(* Holes, and wildcards, which are what's missing from a pattern *)
let is_hole (node : Syntax.t) = node.form = "hole" || node.form = "wildcard"

(* The start of each hole, in order *)
let holes st =
  let rec go (node : Syntax.t) = if is_hole node then [node.start] else List.concat_map go node.children in
  go st.parsed.syntax

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

(* Editing. Each change to the source must leave it parsing. *)

let splice source start stop text =
  String.sub source 0 start ^ text ^ String.sub source stop (String.length source - stop)

(* What stands in for a node whose text doesn't parse *)
let fallback_for (node : Syntax.t) =
  match node.form with
  | "binding" -> "_ = _"
  | "clause" -> "_ -> _"
  | _ -> "_"

(* Puts [text] at the cell's span, if the source then parses, with a node
   there unless the text is empty *)
let place st cell text =
  let source = splice st.source cell.start cell.stop text in
  let stop = cell.start + String.length text in
  match parse source with
  | parsed when text = "" || path_to cell.start stop parsed.syntax <> None ->
    st.source <- source;
    st.parsed <- parsed;
    cell.stop <- stop;
    true
  | _ -> false
  | exception Parsing.Syntax_error _ -> false

(* Puts the cell's text at its span if it fits, or else its fallback.
   Returns whether nothing is left that doesn't fit. *)
let settle st cell =
  let text = String.trim cell.text in
  (text <> "" && place st cell text) || (ignore (place st cell cell.fallback); text = "")

(* The tokens of some text, as spans, up to any that doesn't tokenize *)
let tokens text =
  let rec go pos acc =
    match Parsing.tokenize text pos with
    | Parsing.EOF, _ -> List.rev acc
    | token, next -> go next ((token, Parsing.skip text pos, next) :: acc)
    | exception Parsing.Syntax_error _ -> List.rev acc
  in
  go 0 []

let token_at source pos =
  match Parsing.tokenize source pos with
  | found -> Some found
  | exception Parsing.Syntax_error _ -> None

(* The last token that ends by a position *)
let token_before source pos =
  List.fold_left (fun found ((_, _, stop) as token) -> if stop <= pos then Some token else found)
    None (tokens source)

(* Whether typing more could make it a different token *)
let extendable : Parsing.token -> bool = function
  | Ident _ | Field _ | Tag _ | TypeVar _ | Dep _ | Dot | Underscore
  | Let | In | Fun | Using | Abstract | The | Rec | Recur | Do | Or -> true
  | _ -> false

(* Whether some text is only holes and the tokens around them, which
   repairing would put back *)
let refillable text =
  let found = tokens text in
  let stop = List.fold_left (fun _ (_, _, stop) -> stop) 0 found in
  Parsing.skip text stop = String.length text
  && List.for_all (fun (token, _, _) ->
      match (token : Parsing.token) with
      | Underscore | RightParen | RightCurly | RightSquare | Comma | Equal | Arrow | LeftArrow
      | In | Do -> true
      | _ -> false)
    found

(* The space before a token at a position, as programs are usually written *)
let space_before source pos token =
  let prev = if pos > 0 then source.[pos - 1] else ' ' in
  if String.contains " \t\n({[&" prev then ""
  else if prev = ',' then " "
  else if String.contains ")}],(." token.[0] then ""
  else " "

(* Parses the source, inserting whatever it's missing at [caret], like a hole
   or the token that finishes a construct, until it does *)
let repair source caret =
  let rec go source caret n =
    match parse source with
    | parsed -> Some (source, parsed)
    | exception Parsing.Syntax_error {pos; expected = Some token; _}
      when n < 100 && pos = Parsing.skip source caret ->
      let space = space_before source caret token in
      go (splice source caret caret (space ^ token)) (caret + String.length space + String.length token) (n + 1)
    | exception Parsing.Syntax_error _ -> None
  in
  go source caret 0

(* Moves the cell to the hole right after a position, if there's one, or else
   to the position itself *)
let arrive st cell pos =
  match token_at st.source pos with
  | Some (Underscore, next) ->
    cell.start <- next - 1;
    cell.stop <- next;
    cell.fallback <- "_"
  | _ ->
    cell.start <- pos;
    cell.stop <- pos;
    cell.fallback <- ""

(* Puts finished text at the cell, which moves past it. A token that's
   already next is stepped over instead, taking an empty hole before it with
   it, and the comma before that. *)
let step st cell ?token text =
  let source = st.source in
  match token, token_at source cell.stop with
  | Some token, Some (next, after) when next = token ->
    let removals =
      if cell.fallback <> "_" then []
      else
        match token_before source cell.start with
        | Some (Comma, comma, _) -> [comma, cell.stop; cell.start, cell.stop]
        | _ -> [cell.start, cell.stop]
    in
    let removed =
      List.find_map (fun (start, stop) ->
          let source = splice source start stop "" in
          match parse source with
          | parsed -> Some (source, parsed, stop - start)
          | exception Parsing.Syntax_error _ -> None)
        removals
    in
    let source, parsed, removed = Option.value removed ~default:(source, st.parsed, 0) in
    st.source <- source;
    st.parsed <- parsed;
    arrive st cell (after - removed);
    true
  | _ ->
    let space = space_before source cell.start text in
    let caret = cell.start + String.length space + String.length text in
    match repair (splice source cell.start cell.stop (space ^ text)) caret with
    | Some (source, parsed) ->
      st.source <- source;
      st.parsed <- parsed;
      arrive st cell caret;
      true
    | None -> false

(* Turns the finished tokens before the cell's caret into structure, one at a
   time, leaving the rest as its text. With [all], the whole text is
   finished. A token that doesn't fit by itself is tried along with the ones
   after it, for `abstract t in` and annotations, which only fit whole.
   Returns whether nothing is left that doesn't fit. *)
let commit st cell ~all =
  let upto = if all then String.length cell.text else cell.caret in
  let prefix = String.sub cell.text 0 upto in
  let finished =
    match List.rev (tokens prefix) with
    | (token, _, stop) :: rest when not all && stop = upto && extendable token -> List.rev rest
    | found -> List.rev found
  in
  (* Space at the start means nothing *)
  let blank = min (Parsing.skip cell.text 0) cell.caret in
  if blank > 0 && finished = [] then begin
    cell.text <- String.sub cell.text blank (String.length cell.text - blank);
    cell.caret <- cell.caret - blank;
    cell.anchor <- cell.caret
  end;
  if finished <> [] then begin
    ignore (place st cell cell.fallback);
    let last = List.fold_left (fun _ (_, _, stop) -> stop) 0 finished in
    let rec go = function
      | [] -> last
      | (token, start, stop) :: rest ->
        if step st cell ~token (String.sub prefix start (stop - start)) then go rest
        else if rest <> [] && step st cell (String.sub prefix start (last - start)) then last
        else start
    in
    let consumed = go finished in
    let rest = String.sub cell.text consumed (String.length cell.text - consumed) in
    let trimmed = Parsing.skip rest 0 in
    cell.text <- String.sub rest trimmed (String.length rest - trimmed);
    cell.caret <- max 0 (cell.caret - consumed - trimmed);
    cell.anchor <- cell.caret
  end;
  settle st cell

(* Backspace at the start of the cell takes apart what's before it. An empty
   item goes with the comma before it, into the end of the item before that.
   Otherwise the token before and the smallest node around it and the cell
   become the cell's text, without the token's last character. *)
let melt st cell =
  ignore (place st cell cell.fallback);
  match token_before st.source cell.start with
  | None -> ()
  | Some (token, start, stop) ->
    let rec around (node : Syntax.t) =
      match List.find_opt (fun (child : Syntax.t) ->
          child.start <= start && cell.stop <= child.stop) node.children with
      | Some child -> around child
      | None -> node
    in
    let node = around st.parsed.syntax in
    let item =
      List.find_opt (fun (child : Syntax.t) ->
          child.start <= cell.start && cell.stop <= child.stop)
        node.children
    in
    let earlier =
      List.fold_left (fun found (child : Syntax.t) -> if child.stop <= start then Some child else found)
        None node.children
    in
    let joined =
      match token, item, earlier with
      | Comma, Some item, Some earlier
        when cell.text = "" && refillable (text_of st item) ->
        let source = splice st.source start item.stop "" in
        begin match parse source with
          | parsed ->
            st.source <- source;
            st.parsed <- parsed;
            cell.start <- earlier.start;
            cell.stop <- earlier.stop;
            cell.fallback <- fallback_for earlier;
            cell.text <- text_of st earlier;
            cell.caret <- String.length cell.text;
            true
          | exception Parsing.Syntax_error _ -> false
        end
      | _ -> false
    in
    if not joined then begin
      let prefix = String.sub st.source node.start (stop - 1 - node.start) in
      let suffix = String.sub st.source cell.stop (node.stop - cell.stop) in
      cell.text <- prefix ^ cell.text ^ (if refillable suffix then "" else suffix);
      cell.caret <- String.length prefix;
      cell.start <- node.start;
      cell.stop <- node.stop;
      cell.fallback <- fallback_for node
    end;
    cell.anchor <- cell.caret;
    ignore (settle st cell)

(* Edits the selected node as text, all selected, so typing replaces it. A
   hole is edited empty. *)
let edit st =
  let node = selected st in
  let text = if text_of st node = "_" then "" else text_of st node in
  st.editing <- Some {
      start = node.start;
      stop = node.stop;
      fallback = fallback_for node;
      text;
      anchor = 0;
      caret = String.length text;
      before = st.source;
    };
  st.message <- ""

(* Moves the cell to the next or previous hole, if there is one *)
let to_hole st cell forward =
  let holes = holes st in
  let target =
    if forward then List.find_opt (fun h -> h >= cell.stop) holes
    else List.fold_left (fun found h -> if h < cell.start then Some h else found) None holes
  in
  Option.iter (fun h ->
      cell.start <- h;
      cell.stop <- h + 1;
      cell.fallback <- "_";
      cell.text <- "";
      cell.anchor <- 0;
      cell.caret <- 0)
    target

(* Stops editing, selecting the node that was edited, or that the cell was
   after. Text that doesn't fit is dropped. *)
let leave st cell =
  if not (commit st cell ~all:true) then begin
    cell.text <- "";
    ignore (settle st cell)
  end;
  st.editing <- None;
  if st.source <> cell.before then begin
    st.undo <- cell.before :: st.undo;
    save st.source
  end;
  let path =
    if cell.start < cell.stop then path_to cell.start cell.stop st.parsed.syntax
    else ending_at cell.start [] st.parsed.syntax
  in
  st.cursor <- valid st.parsed.syntax (Option.value path ~default:st.cursor)

(* Keys while editing, other than typing. Returns whether the key was used. *)
let editing_key st cell key shift =
  let at_start = cell.anchor = 0 && cell.caret = 0 in
  let at_end = cell.anchor = cell.caret && cell.caret = String.length cell.text in
  let finished () =
    commit st cell ~all:true || (st.message <- "this doesn't fit here"; false)
  in
  match key with
  | "Enter" ->
    if finished () then begin
      let before = cell.start in
      to_hole st cell true;
      if cell.start = before then leave st cell
    end;
    true
  | "Tab" -> if finished () then to_hole st cell (not shift); true
  | "ArrowRight" when at_end -> if finished () then to_hole st cell true; true
  | "ArrowLeft" when at_start -> if finished () then to_hole st cell false; true
  | "Backspace" when at_start -> melt st cell; true
  | "Escape" -> leave st cell; true
  | _ -> false

(* Set below, once drawing the whole workspace is defined *)
let redraw = ref (fun () -> ())

(* Each value is shown in the gutter, level with the line its node starts *)
let value (s, title) =
  let el = Dom_html.createSpan doc in
  el##.className := Js.string "value";
  el##.title := Js.string title;
  Dom.appendChild el (text s);
  (el :> Dom.node Js.t)

(* The values to show by path, and whether the cell has been put in yet *)
type context = {values : (int list * (string * string)) list; mutable placed : bool}

let rec render st ctx path (node : Syntax.t) : Dom.node Js.t =
  match st.editing with
  | Some cell
    when not ctx.placed && cell.start < cell.stop && node.start = cell.start && node.stop = cell.stop ->
    ctx.placed <- true;
    (st.area :> Dom.node Js.t)
  | _ ->
    let block = is_block node in
    (* Inline, even for blocks, whose lines are divs within *)
    let el = Dom_html.createSpan doc in
    let classes = ["node"; "form-" ^ node.form] in
    let classes = if path = st.cursor && st.editing = None then "selected" :: classes else classes in
    let classes = if problem node <> None then "error" :: classes else classes in
    el##.className := Js.string (String.concat " " classes);
    Option.iter (fun msg -> el##.title := Js.string msg) (problem node);
    el##.onclick := Dom_html.handler (fun ev ->
        Dom_html.stopPropagation ev;
        Option.iter (leave st) st.editing;
        st.cursor <- valid st.parsed.syntax path;
        st.message <- "";
        !redraw ();
        Js._false);
    el##.ondblclick := Dom_html.handler (fun ev ->
        Dom_html.stopPropagation ev;
        Option.iter (leave st) st.editing;
        st.cursor <- valid st.parsed.syntax path;
        edit st;
        !redraw ();
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
    (* A cell between nodes goes in the gap it's in, where the gap starts if
       it's right after a node, or else where it ends *)
    let put_around start stop gap break =
      let at =
        match st.editing with
        | Some cell when not ctx.placed && cell.start = cell.stop && start <= cell.start && cell.start <= stop ->
          ctx.placed <- true;
          Some (cell.start = start)
        | _ -> None
      in
      if at = Some true then Dom.appendChild !line st.area;
      put gap break;
      if at = Some false then Dom.appendChild !line st.area
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
        put_around !pos child.start gap break;
        Option.iter (fun v -> Dom.appendChild !line (value v)) (List.assoc_opt (path @ [i]) ctx.values);
        Dom.appendChild !line (render st ctx (path @ [i]) child);
        after_block := is_block child;
        pos := child.stop)
      node.children;
    let gap = between st.source !pos node.stop in
    if bracketed then put_around !pos node.stop (String.trim gap) (closing_break node)
    else put_around !pos node.stop gap None;
    (el :> Dom.node Js.t)

(* The source with each span replaced by its text, if it parses *)
let reparse st edits =
  (* Last first, so the earlier spans stay put *)
  let edits = List.sort (fun (a, _, _) (b, _, _) -> Int.compare b a) edits in
  let source = List.fold_left (fun source (start, stop, text) -> splice source start stop text) st.source edits in
  match parse source with
  | parsed -> Ok (source, parsed)
  | exception Parsing.Syntax_error {pos; msg; _} -> Error (Parsing.describe source pos msg)

let change st (source, (parsed : Parsing.result)) cursor =
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
    change st result (Option.value (path_to start stop parsed.syntax) ~default:st.cursor);
    true
  | Error msg ->
    st.message <- msg;
    false

(* Rows are a record's entries, a match's clauses, and the bindings of a
   chain of lets, which can be rearranged *)
let is_row (node : Syntax.t) = List.mem node.form ["entry"; "clause"; "binding"]

let split_last path =
  match List.rev path with
  | last :: rest -> List.rev rest, last
  | [] -> invalid_arg "split_last"

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
      change st result (Option.value cursor ~default:parent_path)

(* Inserts a row of holes before or after the one around the cursor, and
   edits its first hole *)
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
    let start = pos + offset in
    if rewrite st [pos, pos, text] (start, start + 1) then edit st

let parse_or_hole source =
  match parse source with
  | parsed -> source, parsed
  | exception Parsing.Syntax_error _ -> "_", parse "_"

(* The values bound by the program's top-level lets, and the value of the
   whole program, by the paths of the bindings and the final body. Each has
   a tooltip, which for the whole program includes its type. *)
let values st =
  let show_bound env env' =
    let bound = List.filteri (fun i _ -> i < List.length env' - List.length env) env' in
    String.concat ", " (List.rev_map (fun (name, v) -> name ^ " = " ^ Runtime.show v) bound)
  in
  let rec bindings env path (node : Syntax.t) =
    match node.form, node.info with
    | "let", Expr {expr = Let {pat; defn; _}; _} ->
      begin match Runtime.define env pat defn with
        | Some env' -> (path @ [0], show_bound env env') :: bindings env' (path @ [1]) (List.nth node.children 1)
        | None -> []
      end
    | "abstract", _ -> bindings env (path @ [0]) (List.hd node.children)
    | _ -> []
  in
  let rec body path (node : Syntax.t) =
    match node.form with
    | "let" -> body (path @ [1]) (List.nth node.children 1)
    | "abstract" -> body (path @ [0]) (List.hd node.children)
    | _ -> path
  in
  let expr = st.parsed.expr in
  let result =
    match Runtime.show (Runtime.eval prelude.env expr) with
    | value -> value, Printf.sprintf "the %s %s" (Type.show expr.ty) value
    | exception e -> let msg = "evaluation failed: " ^ Printexc.to_string e in msg, msg
  in
  match st.parsed.syntax.children with
  | [program] ->
    let bound = List.filter (fun (_, v) -> v <> "") (bindings prelude.env [0] program) in
    (body [0] program, result) :: List.map (fun (path, v) -> path, (v, v)) bound
  | _ -> []

let output st =
  String.concat "\n" (List.filter (( <> ) "") [prelude_error; describe_errors st.source st.parsed.errors])

(* The selected node, or while editing, the cell's node or the node it's after *)
let status st =
  let path =
    match st.editing with
    | Some cell when cell.start < cell.stop -> path_to cell.start cell.stop st.parsed.syntax
    | Some cell -> ending_at cell.start [] st.parsed.syntax
    | None -> Some st.cursor
  in
  let node = node_at st (Option.value path ~default:[]) in
  let ty = Option.fold ~none:"" ~some:(fun ty -> " : " ^ Type.show ty) (type_of node) in
  let problem = Option.fold ~none:"" ~some:(fun msg -> " - " ^ msg) (problem node) in
  let message = if st.message = "" then "" else "\n" ^ st.message in
  node.form ^ ty ^ problem ^ message

(* The cell's text and selection, as the browser has them *)
let read_cell st cell =
  let text = Js.Opt.case st.area##.textContent (fun () -> "") Js.to_string in
  let length = String.length text in
  let offset (node : Dom.node Js.t) offset =
    let is_text = Js.Opt.case st.area##.firstChild (fun () -> false) (fun child -> child == node) in
    if is_text then min offset length
    else if node == (st.area :> Dom.node Js.t) && offset = 0 then 0
    else length
  in
  let selection = Dom_html.window##getSelection in
  begin match offset selection##.anchorNode selection##.anchorOffset,
              offset selection##.focusNode selection##.focusOffset with
    | anchor, caret -> cell.anchor <- anchor; cell.caret <- caret
    | exception _ -> cell.anchor <- length; cell.caret <- length
  end;
  cell.text <- text

(* Puts the cell's text and selection in the browser, and focuses it *)
let show_cell st cell =
  let current = Js.Opt.case st.area##.textContent (fun () -> "") Js.to_string in
  if current <> cell.text then st.area##.textContent := Js.some (Js.string cell.text);
  st.area##focus;
  let range = doc##createRange in
  let length = String.length cell.text in
  let clamp n = max 0 (min length n) in
  let start = clamp (min cell.anchor cell.caret) and stop = clamp (max cell.anchor cell.caret) in
  begin match Js.Opt.to_option st.area##.firstChild with
    | Some child -> range##setStart child start; range##setEnd child stop
    | None ->
      range##setStart (st.area :> Dom.node Js.t) 0;
      range##setEnd (st.area :> Dom.node Js.t) 0
  end;
  let selection = Dom_html.window##getSelection in
  selection##removeAllRanges;
  selection##addRange range

let draw st =
  let editor = Dom_html.getElementById "editor" in
  editor##.innerHTML := Js.string "";
  let ctx = {values = values st; placed = false} in
  Dom.appendChild editor (render st ctx [] st.parsed.syntax);
  if st.editing <> None && not ctx.placed then Dom.appendChild editor st.area;
  (* The gutter is as wide as the widest value, up to a limit *)
  let values = Dom.list_of_nodeList (editor##querySelectorAll (Js.string ".value")) in
  let width = List.fold_left (fun w (v : Dom_html.element Js.t) -> max w v##.offsetWidth) 0 values in
  List.iter (fun (v : Dom_html.element Js.t) -> v##.style##.width := Js.string (Printf.sprintf "%dpx" width)) values;
  editor##.style##.paddingRight := Js.string (Printf.sprintf "calc(%dpx + 3ch)" width);
  let set id s = (Dom_html.getElementById id)##.textContent := Js.some (Js.string s) in
  set "status" (status st);
  set "output" (output st);
  set "source" st.source;
  Option.iter (show_cell st) st.editing

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
    let node = selected st in
    if is_row node then delete_row st st.cursor
    else ignore (rewrite st [node.start, node.stop, "_"] (node.start, node.start + 1));
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
  let area = Dom_html.createSpan doc in
  area##.className := Js.string "cell";
  area##setAttribute (Js.string "contenteditable") (Js.string "plaintext-only");
  area##setAttribute (Js.string "spellcheck") (Js.string "false");
  let st = {source; parsed; cursor = []; editing = None; message = ""; undo = []; area} in
  st.cursor <- valid parsed.syntax [0];
  redraw := (fun () -> draw st);
  let composing ev = Js.to_bool (Js.Unsafe.coerce ev)##.isComposing in
  (* Typing finishes tokens, but deleting doesn't, so they can be changed *)
  let changed ~typed =
    Option.iter (fun cell ->
        read_cell st cell;
        ignore (if typed then commit st cell ~all:false else settle st cell);
        st.message <- "";
        draw st)
      st.editing
  in
  let listen event f =
    ignore (Dom_html.addEventListener area (Dom_html.Event.make event) (Dom_html.handler f) Js._false)
  in
  listen "input" (fun ev ->
      if not (composing ev) then begin
        let kind = Js.Optdef.case (Js.Unsafe.coerce ev)##.inputType (fun () -> "") Js.to_string in
        changed ~typed:(String.starts_with ~prefix:"insert" kind)
      end;
      Js._true);
  listen "compositionend" (fun _ -> changed ~typed:true; Js._true);
  let inside = Dom_html.handler (fun ev -> Dom_html.stopPropagation ev; Js._true) in
  area##.onclick := inside;
  area##.ondblclick := inside;
  doc##.onkeydown := Dom_html.handler (fun ev ->
      let key = Js.Optdef.case ev##.key (fun () -> "") Js.to_string in
      let modified = Js.to_bool ev##.ctrlKey || Js.to_bool ev##.metaKey || Js.to_bool ev##.altKey in
      let handled =
        match st.editing with
        | Some cell ->
          not (composing ev) && begin
            read_cell st cell;
            editing_key st cell key (Js.to_bool ev##.shiftKey)
          end
        | None -> not modified && normal_key st key
      in
      if handled then begin
        draw st;
        Js._false
      end else Js._true);
  draw st
