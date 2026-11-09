(* The workspace: a structure editor for Mu programs, in the browser.

   The program is a tree, which is checked and drawn from its shape. In
   normal mode, a cursor moves between nodes. In editing mode, a cell of raw
   text sits in place of a node, or before or after it, and as each token
   typed in it is finished, the cell's text is read there, framed by what
   the place needs, with whatever it's missing filled in, like the holes and
   closing tokens of a construct, and the cell moves on into the next hole.
   A cell before a node wraps it in what's typed. *)
open Js_of_ocaml
open Bootstrap

let doc = Dom_html.document

(* The prelude, or if it doesn't load, an empty one and why *)
let prelude, prelude_error =
  match load_prelude Prelude.source with
  | Ok prelude -> prelude, ""
  | Error msg -> {vars = []; env = []}, msg

let ( let* ) = Option.bind

type path = int list

let split path =
  match List.rev path with
  | i :: rest -> Some (List.rev rest, i)
  | [] -> None

(* The nodes of a program as the editor sees them: its expressions, patterns
   and types, and the parts of constructs that hold them, which are items of
   a list or rows the editor can rearrange *)
type ('e, 'p) node =
  | E of 'e
  | P of 'p
  | T of Annot.t
  | Entry of string option * ('e, 'p) node (* of a record, named or positional *)
  | Item of string * ('e, 'p) node (* a named argument, payload field or parameter *)
  | Using of ('e, 'p) node
  | Rest of ('e, 'p) node option (* `..r` in a record, and `..` in a record pattern *)
  | Clause of 'p * 'e
  | Binding of 'p * 'e (* a let's `p = e`, without the body *)
  | Acc of 'p * 'e (* a recur's accumulator, `p = init` *)

(* How to see the shapes of a tree's nodes, checked or not *)
type ('e, 'p) shapes = {of_expr : 'e -> ('e, 'p) Expr.t; of_pat : 'p -> 'p Pat.t}

let untyped = {of_expr = (fun (e : _ Expr.untyped) -> e.expr); of_pat = (fun (p : _ Pat.untyped) -> p.pat)}
let typed = {of_expr = (fun (e : _ Type.expr) -> e.expr); of_pat = (fun (p : _ Type.pat) -> p.pat)}

(* The program, which has no locations *)
type expr = unit Expr.untyped
type pat = unit Pat.untyped
type tree = (expr, pat) node

(* The program checked, located by path *)
type checked = (path Type.expr, path Type.pat) node

(* What's read from text, located in it *)
type fragment = (Parsing.span Expr.untyped, Parsing.span Pat.untyped) node

let hole_expr : expr = {expr = Hole; loc = ()}
let wildcard : pat = {pat = Wildcard; loc = ()}

let rec strip (e : _ Expr.untyped) : expr = {expr = Expr.map strip strip_pat e.expr; loc = ()}
and strip_pat (p : _ Pat.untyped) : pat = {pat = Pat.map strip_pat p.pat; loc = ()}

let rec strip_node : fragment -> tree = function
  | E e -> E (strip e)
  | P p -> P (strip_pat p)
  | T ann -> T ann
  | Entry (name, x) -> Entry (name, strip_node x)
  | Item (name, x) -> Item (name, strip_node x)
  | Using x -> Using (strip_node x)
  | Rest x -> Rest (Option.map strip_node x)
  | Clause (p, e) -> Clause (strip_pat p, strip e)
  | Binding (p, e) -> Binding (strip_pat p, strip e)
  | Acc (p, e) -> Acc (strip_pat p, strip e)

(* Fields, with None for the name of each positional one *)
let named fields =
  let rec go i = function
    | [] -> []
    | (name, x) :: rest when name = label i -> (None, x) :: go (i + 1) rest
    | (name, x) :: rest -> (Some name, x) :: go i rest
  in
  go 0 fields

(* Fields from positional and named ones, whose names can't repeat *)
let unnamed items =
  let rec go i = function
    | [] -> []
    | (None, x) :: rest -> (label i, x) :: go (i + 1) rest
    | (Some name, x) :: rest -> (name, x) :: go i rest
  in
  let fields = go 0 items in
  let names = List.map fst fields in
  if List.length (List.sort_uniq compare names) < List.length names then
    invalid_arg "repeated field";
  fields

(* A let or a named entry whose value is a function, which is written
   `let f(x) = e` or `{.f(x) = e}` *)
let sugar s = function
  | Binding (p, e) ->
    begin match s.of_pat p, s.of_expr e with
      | Var _, Function _ -> true
      | _ -> false
    end
  | Entry (Some _, E e) -> (match s.of_expr e with Function _ -> true | _ -> false)
  | _ -> false

(* Whether a node's [i]th child is a function written `(x) = e` *)
let shows_sugar s node i =
  match node with
  | Binding _ -> i = 1 && sugar s node
  | Entry _ -> i = 0 && sugar s node
  | _ -> false

let rec annotation : Annot.t -> string = function
  | Var name -> "'" ^ name
  | Name name -> name
  | Record row -> "{" ^ annotation_row row ^ "}"
  | Variant {fields; rest} ->
    let tag (name, payload) =
      match payload with
      | Annot.Record {fields = []; rest = None} -> "#" ^ name
      | Annot.Record row -> "#" ^ name ^ "(" ^ annotation_row row ^ ")"
      | ty -> "#" ^ name ^ "(" ^ annotation ty ^ ")"
    in
    let rest = match rest with Some r -> [".." ^ annotation r] | None -> [] in
    "[" ^ String.concat ", " (List.map tag fields @ rest) ^ "]"
  | Function {inputs; deps; output} ->
    let deps = match deps with Some d -> ["using " ^ annotation d] | None -> [] in
    "fun(" ^ String.concat ", " (annotation_items inputs @ deps) ^ ") -> " ^ annotation output
  | Rec (name, body) -> "rec '" ^ name ^ ". " ^ annotation body

and annotation_items ({fields; rest} : Annot.row) =
  List.map (function
      | None, ty -> annotation ty
      | Some name, ty -> "." ^ name ^ " : " ^ annotation ty)
    (named fields)
  @ (match rest with Some r -> [".." ^ annotation r] | None -> [])

and annotation_row row = String.concat ", " (annotation_items row)

(* A node's concrete syntax: its text, and the nodes within it. A function
   can be [sugared], written `(x) = e`. *)
type ('e, 'p) part = Text of string | Part of ('e, 'p) node

let parts ?(sugared = false) s node =
  let sep_by sep groups =
    List.concat (List.mapi (fun i group -> if i = 0 then group else Text sep :: group) groups)
  in
  let parens cond node = if cond then [Text "("; Part node; Text ")"] else [Part node] in
  let items wrap fields =
    List.map (function
        | None, x -> [Part (wrap x)]
        | Some name, x -> [Part (Item (name, wrap x))])
      (named fields)
  in
  let using wrap = function Some x -> [[Part (Using (wrap x))]] | None -> [] in
  let e x = E x and p x = P x in
  let function_parts arrow f =
    match s.of_expr f with
    | Function {params; deps; body} ->
      Text "(" :: sep_by ", " (items p params @ using p deps) @ [Text (") " ^ arrow ^ " "); Part (E body)]
    | _ -> invalid_arg "function_parts"
  in
  (* Operands that need parentheses, to be read back the same: what would
     take in a postfix after it, and a match on the left of a postfix
     operand of `&` or `the`, which would take the match *)
  let open_ended x =
    match s.of_expr x with
    | Let _ | Function _ | Abstract _ | Alias _ | Recur _ -> true
    | _ -> false
  in
  let prefixed x = match s.of_expr x with The _ | Roll _ -> true | _ -> false in
  let rec has_match x =
    match s.of_expr x with
    | Match _ -> true
    | Field (l, _) -> has_match l
    | Apply {f; _} -> has_match f
    | _ -> false
  in
  let rec open_pattern q =
    match s.of_pat q with
    | The _ -> true
    | Roll r -> (match s.of_pat r with Or _ -> false | _ -> open_pattern r)
    | _ -> false
  in
  match node with
  | E x ->
    begin match s.of_expr x with
      | Var name -> [Text name]
      | Hole -> [Text "_"]
      | Dep name -> [Text ("@" ^ name)]
      | Record {fields; rest} ->
        let entries = List.map (fun (name, x) -> [Part (Entry (name, E x))]) (named fields) in
        let rest = match rest with Some r -> [[Part (Rest (Some (E r)))]] | None -> [] in
        Text "{" :: sep_by ", " (entries @ rest) @ [Text "}"]
      | Field (l, name) -> parens (open_ended l || prefixed l) (E l) @ [Text ("." ^ name)]
      | Variant (tag, []) -> [Text ("#" ^ tag)]
      | Variant (tag, fields) -> Text ("#" ^ tag ^ "(") :: sep_by ", " (items e fields) @ [Text ")"]
      | Match (l, clauses) ->
        parens (open_ended l) (E l)
        @ Text " [" :: sep_by ", " (List.map (fun (q, b) -> [Part (Clause (q, b))]) clauses) @ [Text "]"]
      | Function _ when sugared -> function_parts "=" x
      | Function _ -> Text "fun" :: function_parts "->" x
      | Apply {f; args; deps} ->
        let bare = match s.of_expr f with Variant (_, []) -> true | _ -> false in
        parens (open_ended f || prefixed f || bare) (E f)
        @ Text "(" :: sep_by ", " (items e args @ using e deps) @ [Text ")"]
      | Let {pat; defn; body} -> [Text "let "; Part (Binding (pat, defn)); Text " in "; Part (E body)]
      | Roll r -> Text "&" :: parens (has_match r) (E r)
      | Recur {root; input; accs; body; _} ->
        [Text "recur ("; Part (P root); Text " <- "; Part (E input)]
        @ List.concat_map (fun (q, init) -> [Text ", "; Part (Acc (q, init))]) accs
        @ [Text ") do "; Part (E body)]
      | The (ann, r) -> [Text "the "; Part (T ann); Text " "] @ parens (has_match r) (E r)
      | Abstract (name, body) -> [Text ("abstract " ^ name ^ " in "); Part (E body)]
      | Alias (name, ann, body) -> [Text ("type " ^ name ^ " = "); Part (T ann); Text " in "; Part (E body)]
    end
  | P q ->
    begin match s.of_pat q with
      | Var name -> [Text name]
      | Wildcard -> [Text "_"]
      | Record {fields; rest} ->
        let entries = List.map (fun (name, x) -> [Part (Entry (name, P x))]) (named fields) in
        let rest = if rest then [[Part (Rest None)]] else [] in
        Text "{" :: sep_by ", " (entries @ rest) @ [Text "}"]
      | Variant (tag, []) -> [Text ("#" ^ tag)]
      | Variant (tag, fields) -> Text ("#" ^ tag ^ "(") :: sep_by ", " (items p fields) @ [Text ")"]
      | Roll r -> Text "&" :: parens (match s.of_pat r with Or _ -> true | _ -> false) (P r)
      | The (ann, r) -> [Text "the "; Part (T ann); Text " "; Part (P r)]
      | Or (l, r) ->
        parens (match s.of_pat l with Or _ -> true | _ -> open_pattern l) (P l)
        @ [Text " or "; Part (P r)]
    end
  | T ann -> [Text (annotation ann)]
  | Entry (None, x) -> [Part x]
  | Entry (Some name, x) when sugar s node -> [Text ("." ^ name); Part x]
  | Entry (Some name, x) | Item (name, x) -> [Text ("." ^ name ^ " = "); Part x]
  | Using x -> [Text "using "; Part x]
  | Rest (Some x) -> [Text ".."; Part x]
  | Rest None -> [Text ".."]
  | Clause (q, b) -> [Part (P q); Text " -> "; Part (E b)]
  | Binding (q, d) when sugar s node -> [Part (P q); Part (E d)]
  | Binding (q, d) | Acc (q, d) -> [Part (P q); Text " = "; Part (E d)]

let children s node = List.filter_map (function Part n -> Some n | Text _ -> None) (parts s node)

let form s = function
  | E x ->
    begin match s.of_expr x with
      | Record _ -> "record" | Field _ -> "field" | Variant _ -> "variant" | Match _ -> "match"
      | Function _ -> "fun" | Apply _ -> "apply" | Dep _ -> "dep" | Var _ -> "var" | Let _ -> "let"
      | Roll _ -> "roll" | Recur _ -> "recur" | The _ -> "the" | Abstract _ -> "abstract"
      | Alias _ -> "alias"
      | Hole -> "hole"
    end
  | P q ->
    begin match s.of_pat q with
      | Var _ -> "var" | Wildcard -> "wildcard" | Record _ -> "record" | Variant _ -> "variant"
      | Roll _ -> "roll" | The _ -> "the" | Or _ -> "or"
    end
  | T _ -> "type"
  | Entry _ -> "entry"
  | Item _ -> "item"
  | Using _ -> "using"
  | Rest _ -> "rest"
  | Clause _ -> "clause"
  | Binding _ -> "binding"
  | Acc _ -> "accumulator"

(* Holes, and wildcards, which are what's missing from a pattern. An entry of
   a hole is one too, so what's typed in it can name it. *)
let rec is_hole s = function
  | E x -> (match s.of_expr x with Hole -> true | _ -> false)
  | P q -> (match s.of_pat q with Wildcard -> true | _ -> false)
  | Entry (None, x) -> is_hole s x
  | _ -> false

let hole node = is_hole untyped node

let rec find s node = function
  | [] -> Some node
  | i :: path -> Option.bind (List.nth_opt (children s node) i) (fun child -> find s child path)

let get s node path =
  match find s node path with
  | Some node -> node
  | None -> invalid_arg "get"

(* The longest prefix of a path that's in the tree *)
let valid root path =
  let rec go node acc = function
    | i :: path ->
      begin match List.nth_opt (children untyped node) i with
        | Some child -> go child (i :: acc) path
        | None -> List.rev acc
      end
    | [] -> List.rev acc
  in
  go root [] path

(* Text, and where each node within it is, by path *)
let print_spans ?sugared s node =
  let buf = Buffer.create 64 and spans = ref [] in
  let rec go ?sugared path node =
    let start = Buffer.length buf in
    ignore (List.fold_left (fun i -> function
        | Text t -> Buffer.add_string buf t; i
        | Part child -> go ~sugared:(shows_sugar s node i) (path @ [i]) child; i + 1)
        0 (parts ?sugared s node));
    spans := (path, (start, Buffer.length buf)) :: !spans
  in
  go ?sugared [] node;
  Buffer.contents buf, !spans

let print ?sugared s node = fst (print_spans ?sugared s node)

(* Whether the node at a path in the program is a function written
   `(x) = e`, and that node's syntax and text *)
let sugared root path =
  match split path with
  | Some (parent, i) -> shows_sugar untyped (get untyped root parent) i
  | None -> false

let parts_at root path = parts ~sugared:(sugared root path) untyped (get untyped root path)
let print_spans_at root path = print_spans ~sugared:(sugared root path) untyped (get untyped root path)
let print_at root path = fst (print_spans_at root path)

(* A node with new children, which must be the kinds of node it can hold, and
the location [loc], if it has one *)
let rebuild_at (type a l) (loc : l) (node : (a Expr.untyped, a Pat.untyped) node)
    (children : (l Expr.untyped, l Pat.untyped) node list) : (l Expr.untyped, l Pat.untyped) node =
  let bad () = invalid_arg "rebuild" in
  let e = function E x -> x | _ -> bad () in
  let p = function P x -> x | _ -> bad () in
  (* Items, named or positional, then an optional `using` *)
  let items get cs =
    let fields cs = unnamed (List.map (function Item (name, x) -> Some name, get x | x -> None, get x) cs) in
    match List.rev cs with
    | Using x :: rest -> fields (List.rev rest), Some (get x)
    | _ -> fields cs, None
  in
  let plain get cs = match items get cs with fields, None -> fields | _ -> bad () in
  let entries get cs = unnamed (List.map (function Entry (name, x) -> name, get x | _ -> bad ()) cs) in
  let fn cs : (l Expr.untyped, l Pat.untyped) Expr.t =
    match List.rev cs with
    | E body :: rest ->
      let params, deps = items p (List.rev rest) in
      Function {params; deps; body}
    | _ -> bad ()
  in
  match node, children with
  | E x, cs ->
    let shape : (l Expr.untyped, l Pat.untyped) Expr.t =
      match x.expr, cs with
      | Record _, cs ->
        let cs, rest =
          match List.rev cs with
          | Rest (Some r) :: rest -> List.rev rest, Some (e r)
          | _ -> cs, None
        in
        Record {fields = entries e cs; rest}
      | Field (_, name), [l] -> Field (e l, name)
      | Variant (tag, _), cs -> Variant (tag, plain e cs)
      | Match _, l :: cs ->
        Match (e l, List.map (function Clause (q, b) -> q, b | _ -> bad ()) cs)
      | Function _, cs -> fn cs
      | Apply _, f :: cs ->
        let args, deps = items e cs in
        Apply {f = e f; args; deps}
      | Let _, [Binding (pat, defn); body] -> Let {pat; defn; body = e body}
      | Roll _, [r] -> Roll (e r)
      | Recur r, P root :: E input :: cs ->
        begin match List.rev cs with
          | E body :: accs ->
            let accs = List.rev_map (function Acc (q, init) -> q, init | _ -> bad ()) accs in
            Recur {continue = r.continue; forget = r.forget; root; input; accs; body}
          | _ -> bad ()
        end
      | The _, [T ann; r] -> The (ann, e r)
      | Abstract (name, _), [body] -> Abstract (name, e body)
      | Alias (name, _, _), [T ann; body] -> Alias (name, ann, e body)
      | Var name, [] -> Var name
      | Dep name, [] -> Dep name
      | Hole, [] -> Hole
      | _ -> bad ()
    in
    E {expr = shape; loc}
  | P x, cs ->
    let shape : l Pat.untyped Pat.t =
      match x.pat, cs with
      | Record _, cs ->
        let cs, rest =
          match List.rev cs with
          | Rest None :: rest -> List.rev rest, true
          | _ -> cs, false
        in
        Record {fields = entries p cs; rest}
      | Variant (tag, _), cs -> Variant (tag, plain p cs)
      | Roll _, [r] -> Roll (p r)
      | The _, [T ann; r] -> The (ann, p r)
      | Or _, [l; r] -> Or (p l, p r)
      | Var name, [] -> Var name
      | Wildcard, [] -> Wildcard
      | _ -> bad ()
    in
    P {pat = shape; loc}
  | T ann, [] -> T ann
  | Entry (name, _), [x] -> Entry (name, x)
  | Item (name, _), [x] -> Item (name, x)
  | Using _, [x] -> Using x
  | Rest (Some _), [x] -> Rest (Some x)
  | Rest None, [] -> Rest None
  | Clause _, [P q; E b] -> Clause (q, b)
  | Binding _, [P q; E d] -> Binding (q, d)
  | Acc _, [P q; E init] -> Acc (q, init)
  | _ -> bad ()

let rebuild (node : tree) (children : tree list) : tree = rebuild_at () node children

(* The program, with each expression and pattern located by its path, to
   check it *)
let rec locate path node =
  rebuild_at path node (List.mapi (fun i child -> locate (path @ [i]) child) (children untyped node))

let rec update node path f =
  match path with
  | [] -> f node
  | i :: path ->
    let cs = children untyped node in
    if i >= List.length cs then invalid_arg "update";
    rebuild node (List.mapi (fun j child -> if j = i then update child path f else child) cs)

(* Removes the [i]th child of the node at a path *)
let remove root path i =
  update root path (fun node ->
      rebuild node (List.filteri (fun j _ -> j <> i) (children untyped node)))

(* Reading text *)

let tokens text =
  let rec go pos acc =
    match Parsing.tokenize text pos with
    | Parsing.EOF, _ -> List.rev acc
    | token, next -> go next ((token, Parsing.skip text pos, next) :: acc)
    | exception Parsing.Syntax_error _ -> List.rev acc
  in
  go 0 []

(* Whether typing more could make it a different token *)
let extendable : Parsing.token -> bool = function
  | Ident _ | Field _ | Tag _ | TypeVar _ | Dep _ | Dot | Underscore
  | Let | In | Fun | Using | Abstract | Type | The | Rec | Recur | Do | Or -> true
  | _ -> false

(* Whether some text is only holes and the tokens around them, which reading
   would put back *)
let refillable text =
  List.for_all (fun (token, _, _) ->
      match (token : Parsing.token) with
      | Underscore | RightParen | RightCurly | RightSquare | Comma | Equal | Arrow | LeftArrow
      | In | Do -> true
      | _ -> false)
    (tokens text)

(* How text is read in a place in the program: [prefix] and [suffix] frame
   it, so that [parse] reads it as what it stands for there, which is
   [items] of what's read: the children of the node at a path, from child
   [first], or else the whole of it. [standin] reads as one item, or the
   whole. *)
type frame = {
  prefix : string;
  suffix : string;
  parse : string -> fragment;
  standin : string;
  items : fragment -> ((path * int) option * fragment list) option;
}

let parse_expr text = E (Parsing.parse text)
let parse_pat text = P (Parsing.parse_pattern text)

let whole parse = {prefix = ""; suffix = ""; parse; standin = "_"; items = fun read -> Some (None, [read])}
let expr_frame = whole parse_expr
let pat_frame = whole parse_pat
let type_frame = {(whole (fun text -> T (Parsing.parse_type text))) with standin = ""}

let shape_of = function E e -> Some (untyped.of_expr e) | _ -> None
let pat_shape_of = function P p -> Some (untyped.of_pat p) | _ -> None
let all_but_last xs = List.take (List.length xs - 1) xs

(* The frames of lists' items. Around the items are holes. *)
let list_frame prefix suffix parse standin items = {prefix; suffix; parse; standin; items}

let record_frame = list_frame "{" "}" parse_expr "_" (fun read ->
    match shape_of read with Some (Record _) -> Some (Some ([], 0), children untyped read) | _ -> None)

let variant_frame = list_frame "#x(" ")" parse_expr "_" (fun read ->
    match shape_of read with Some (Variant ("x", _)) -> Some (Some ([], 0), children untyped read) | _ -> None)

let params_frame = list_frame "fun(" ") -> _" parse_expr "_" (fun read ->
    match shape_of read with
    | Some (Function {body; _}) when hole (E body) -> Some (Some ([], 0), all_but_last (children untyped read))
    | _ -> None)

let args_frame = list_frame "_(" ")" parse_expr "_" (fun read ->
    match shape_of read with
    | Some (Apply {f; _}) when hole (E f) -> Some (Some ([], 1), List.tl (children untyped read))
    | _ -> None)

let clauses_frame = list_frame "_ [" "]" parse_expr "_ -> _" (fun read ->
    match shape_of read with
    | Some (Match (l, _)) when hole (E l) -> Some (Some ([], 1), List.tl (children untyped read))
    | _ -> None)

let accs_frame = list_frame "recur (_ <- _, " ") do _" parse_expr "_ = _" (fun read ->
    match shape_of read with
    | Some (Recur {root; input; body; _}) when hole (P root) && hole (E input) && hole (E body) ->
      Some (Some ([], 2), all_but_last (List.drop 2 (children untyped read)))
    | _ -> None)

let pat_record_frame = list_frame "{" "}" parse_pat "_" (fun read ->
    match pat_shape_of read with Some (Record _) -> Some (Some ([], 0), children untyped read) | _ -> None)

let pat_variant_frame = list_frame "#x(" ")" parse_pat "_" (fun read ->
    match pat_shape_of read with
    | Some (Variant ("x", _)) -> Some (Some ([], 0), children untyped read)
    | _ -> None)

let binding_frame = list_frame "let " " in _" parse_expr "_ = _" (fun read ->
    match shape_of read, children untyped read with
    | Some (Let {body; _}), [binding; _] when hole (E body) -> Some (Some ([], 0), [binding])
    | _ -> None)

(* A function written `(x) = e`, as a let's *)
let lambda_frame = list_frame "let f" " in _" parse_expr "(_) = _" (fun read ->
    match shape_of read, children untyped read with
    | Some (Let {body; _}), [binding; _] when hole (E body) && sugar untyped binding ->
      Some (Some ([0], 1), [List.nth (children untyped binding) 1])
    | _ -> None)

(* The list a node holds, if it holds one: its frame, and which of its
   children are items, from [first] up to [trailing] from the end *)
let list_of (node : tree) =
  match node with
  | E e ->
    begin match e.expr with
      | Record _ -> Some (record_frame, 0, 0)
      | Variant _ -> Some (variant_frame, 0, 0)
      | Function _ -> Some (params_frame, 0, 1)
      | Apply _ -> Some (args_frame, 1, 0)
      | Match _ -> Some (clauses_frame, 1, 0)
      | Recur _ -> Some (accs_frame, 2, 1)
      | _ -> None
    end
  | P p ->
    begin match p.pat with
      | Record _ -> Some (pat_record_frame, 0, 0)
      | Variant _ -> Some (pat_variant_frame, 0, 0)
      | _ -> None
    end
  | _ -> None

(* How text is read in place of the node at a path, and if it's an item of a
   list, the list's node and the item's index *)
let slot root path =
  let alone () =
    match get untyped root path with
    | P _ -> pat_frame
    | T _ -> type_frame
    | Binding _ -> binding_frame
    | E _ when sugared root path -> lambda_frame
    | _ -> expr_frame
  in
  match split path with
  | Some (parent_path, i) ->
    let parent = get untyped root parent_path in
    begin match list_of parent with
      | Some (frame, first, trailing)
        when first <= i && i < List.length (children untyped parent) - trailing ->
        frame, Some (parent_path, i)
      | _ -> alone (), None
    end
  | None -> alone (), None

(* Reads [src] in a frame, with whatever it's missing filled in at its end,
   and given [inner], at that offset too. What's filled in at the end must
   finish with the frame's suffix, rather than the suffix being taken into
   what's read. Returns the text with what was filled in, and what's read. *)
let read frame ?inner src =
  let token_list text = List.map (fun (token, _, _) -> token) (tokens text) in
  let suffix = token_list frame.suffix in
  let rec go src inner added n =
    match frame.parse src with
    | read ->
      let added = token_list added in
      let extra = List.length added - List.length suffix in
      if extra >= 0 && List.drop extra added = suffix then Some (src, read) else None
    | exception Parsing.Syntax_error {pos; expected = Some token; _} when n < 100 ->
      let token = " " ^ token in
      if pos >= String.length src then go (src ^ token) inner (added ^ token) (n + 1)
      else begin match inner with
        | Some i when Parsing.skip src i = pos ->
          let src = String.sub src 0 i ^ token ^ String.sub src i (String.length src - i) in
          go src (Some (i + String.length token)) added (n + 1)
        | _ -> None
      end
    | exception Parsing.Syntax_error _ -> None
  in
  go src inner "" 0

(* The program with [items] in place of the node at a path *)
let replace root path list items =
  match list, items with
  | Some (parent_path, i), items ->
    update root parent_path (fun parent ->
        let cs = children untyped parent in
        rebuild parent (List.take i cs @ items @ List.drop (i + 1) cs))
  | None, [item] -> update root path (fun _ -> item)
  | None, _ -> invalid_arg "replace"

(* The expressions and patterns of what's read, by path, with their spans *)
let rec located path (node : fragment) =
  let here = match node with E e -> [path, e.loc] | P p -> [path, p.loc] | _ -> [] in
  here @ List.concat (List.mapi (fun i child -> located (path @ [i]) child) (children untyped node))

(* Where the cell is: in place of the node at a path, or after or before it *)
type position = Into of path | After of path | Before of path

let path_of = function Into path | After path | Before path -> path

(* Where the cell goes into a hole. An entry of a hole is the hole, so what's
   typed there can name it. *)
let into root path =
  match split path with
  | Some (parent, _) when (match get untyped root parent with Entry (None, _) -> true | _ -> false) -> parent
  | _ -> path

(* Reads [text] at a position, in place of the node at a path, or after or
   before it, where the node stands for itself. Returns the new program,
   where the cell goes next, and the tokens filled in before it, which typing
   steps over. The cell goes into the next hole if only what was filled in
   comes before it, or for text before a node, stays before it, or else goes
   after the node the text ends. *)
let place root at text =
  let path = path_of at in
  let frame, list = slot root path in
  let original = get untyped root path in
  let standin = match original with E _ | P _ -> "_" | _ -> frame.standin in
  let start = String.length frame.prefix in
  let src, inner, standin_at, caret =
    match at with
    | Into _ -> frame.prefix ^ text, None, None, start + String.length text
    | After _ ->
      frame.prefix ^ standin ^ " " ^ text, None, Some start,
      start + String.length standin + 1 + String.length text
    | Before _ ->
      let caret = start + String.length text in
      frame.prefix ^ text ^ " " ^ standin, Some caret, Some (caret + 1), caret
  in
  let* () = if standin_at = None || standin <> "" then Some () else None in
  let* src, read = read frame ?inner src in
  let* first, items = frame.items read in
  let count = List.length items in
  let* () = if list <> None || count = 1 then Some () else None in
  let nodes = located [] read in
  (* Which item a path in what's read is in, and the path within it *)
  let locate fpath =
    match first with
    | None -> Some (0, fpath)
    | Some (at, first) ->
      let n = List.length at in
      match List.drop n fpath with
      | c :: rest when List.take n fpath = at && c >= first && c - first < count -> Some (c - first, rest)
      | _ -> None
  in
  let hole_at pos =
    List.find_map (fun (fpath, (start, _)) ->
        if start = pos && hole (get untyped read fpath) then locate fpath else None)
      nodes
  in
  let items = Array.of_list (List.map strip_node items) in
  (* The original, in place of the stand-in *)
  let* standin_loc =
    match standin_at with
    | None -> Some None
    | Some pos ->
      let* k, rest = hole_at pos in
      begin match original, get untyped items.(k) rest with
        | (E _, E _ | P _, P _) ->
          items.(k) <- update items.(k) rest (fun _ -> original);
          Some (Some (k, rest))
        | (E _ | P _), _ -> None
        | _ when print untyped items.(k) = standin ->
          items.(k) <- original;
          Some (Some (k, []))
        | _ -> None
      end
  in
  let root = replace root path list (Array.to_list items) in
  let in_program (k, rest) =
    match list with
    | Some (parent, i) -> parent @ [i + k] @ rest
    | None -> path @ rest
  in
  let next_hole =
    let rec next pos filled =
      match Parsing.tokenize src pos with
      | Parsing.Underscore, stop ->
        let* loc = hole_at (stop - 1) in
        if Some (stop - 1) = standin_at then
          Option.map (fun loc -> Before (in_program loc), List.rev filled) standin_loc
        else Some (Into (into root (in_program loc)), List.rev filled)
      | Parsing.EOF, _ -> None
      | token, stop -> next stop (( = ) token :: filled)
      | exception Parsing.Syntax_error _ -> None
    in
    next caret []
  in
  let ending =
    List.filter_map (fun (fpath, (_, stop)) -> if stop = caret then locate fpath else None) nodes
    |> List.fold_left (fun found (k, rest) ->
        match found with
        | Some (_, longest) when List.length longest >= List.length rest -> found
        | _ -> Some (k, rest))
      None
    |> Option.map (fun loc -> After (in_program loc), [])
  in
  let last =
    match list with
    | Some (parent, i) when count > 0 -> parent @ [i + count - 1]
    | Some (parent, _) -> parent
    | None -> path
  in
  let at, filled = Option.value (if next_hole <> None then next_hole else ending) ~default:(After last, []) in
  Some (root, at, filled)

(* Text after or before a node that doesn't fit with it might with what the
   node is the last or first part of *)
let rec around root at text =
  match place root at text with
  | Some placed -> Some placed
  | None ->
    let* parent, i = split (path_of at) in
    let parent_node = get untyped root parent in
    let parts = parts_at root parent in
    let count = List.length (children untyped parent_node) in
    let starts = match parts with Part _ :: _ -> true | _ -> false in
    let ends = match List.rev parts with Part _ :: _ -> true | _ -> false in
    match at with
    | After _ when ends && i = count - 1 -> around root (After parent) text
    | Before _ when starts && i = 0 -> around root (Before parent) text
    | _ -> None

(* Typing a token that's next steps over it, to the node after it, or past
   the construct it ends, taking an empty item the cell was in with it. The
   rest of the tokens between them are returned, for typing to step over. *)
let step_over root at token =
  let* path, empty =
    match at with
    | Into path when hole (get untyped root path) -> Some (path, true)
    | After path -> Some (path, false)
    | Into _ | Before _ -> None
  in
  let rec next path =
    let* parent, i = split path in
    let rec after k = function
      | Part _ :: rest when k = i -> Some rest
      | Part _ :: rest -> after (k + 1) rest
      | Text _ :: rest -> after k rest
      | [] -> None
    in
    let* rest = after 0 (parts_at root parent) in
    let rec texts acc = function
      | Text t :: rest -> texts (acc ^ t) rest
      | rest -> acc, rest <> []
    in
    (* A function written `(x) = e` was typed `(x) -> e` if it's in a record *)
    let is token (t : Parsing.token) =
      t = token
      || t = Equal && token = Arrow && sugared root parent
    in
    let rec rest_after = function
      | t :: rest -> if is token t then Some (List.map (fun t typed -> is typed t) rest) else rest_after rest
      | [] -> None
    in
    match texts "" rest with
    | "", false -> next parent
    | text, more ->
      let* filled = rest_after (List.map (fun (t, _, _) -> t) (tokens text)) in
      Some (parent, i, (if more then Some (i + 1) else None), filled)
  in
  let* parent, i, after, filled = next path in
  match after with
  | Some j ->
    let target = parent @ [j] in
    Some (root, (if hole (get untyped root target) then Into (into root target) else Before target), filled)
  | None ->
    let item = path = parent @ [i] && snd (slot root path) <> None in
    let root = if empty && item then (try remove root parent i with Invalid_argument _ -> root) else root in
    Some (root, After parent, filled)

(* Tokens that change what's before them: `(` after a let's name makes it a
   function's, `let f(_) = e`, with e its body, and after a tag, gives it a
   payload, and `,` after the input of a recur starts its accumulators *)
let special root at (token : Parsing.token) =
  match at, token with
  | After path, Comma ->
    let* parent, i = split path in
    begin match get untyped root parent with
      | E {expr = Recur ({accs = []; _} as r); _} as recur when i = 1 ->
        let acc = wildcard, hole_expr in
        Some (update root parent (fun _ -> match recur with
            | E e -> E {e with expr = Recur {r with accs = [acc]}}
            | _ -> recur),
              Into (parent @ [2; 0]), [])
      | _ -> None
    end
  | After path, LeftParen ->
    begin match get untyped root path, split path with
      | E ({expr = Variant (tag, []); _} as e), _ ->
        Some (update root path (fun _ -> E {e with expr = Variant (tag, [label 0, hole_expr])}), Into (path @ [0]), [])
      | P ({pat = Variant (tag, []); _} as p), _ ->
        Some (update root path (fun _ -> P {p with pat = Variant (tag, [label 0, wildcard])}), Into (path @ [0]), [])
      | _, Some (parent, 0) ->
        begin match get untyped root parent with
          | Binding (({pat = Var _; _} as name), defn) as binding when not (sugar untyped binding) ->
            let defn = {defn with expr = Function {params = [label 0, wildcard]; deps = None; body = defn}} in
            Some (update root parent (fun _ -> Binding (name, defn)), Into (parent @ [1; 0]), [])
          | _ -> None
        end
      | _ -> None
    end
  | _ -> None

(* Editing *)

(* The cell being edited, raw text at a position in the program *)
type cell = {
  mutable at : position;
  mutable text : string;
  mutable anchor : int; (* the selection in the text, from anchor to caret *)
  mutable caret : int;
  mutable filled : (Parsing.token -> bool) list; (* filled in after the cell, which typing steps over *)
  origin : path; (* the node editing began at, which what's typed before wraps *)
  before : expr; (* the program when editing began, for undo *)
}

type state = {
  mutable doc : expr;
  mutable cursor : path; (* the selected node *)
  mutable editing : cell option;
  mutable message : string;
  mutable undo : expr list;
  area : Dom_html.element Js.t; (* the cell's element, kept across redraws *)
}

let root st = E st.doc

let set st = function
  | E e -> st.doc <- e
  | _ -> invalid_arg "set"

(* Saved in the browser as text, so a reload doesn't lose the program *)
let storage_key = Js.string "mu-workspace"

let load () =
  try
    Js.Optdef.to_option Dom_html.window##.localStorage
    |> Fun.flip Option.bind (fun s -> Js.Opt.to_option (s##getItem storage_key))
    |> Option.map Js.to_string
  with _ -> None

let save st =
  try
    Js.Optdef.iter Dom_html.window##.localStorage (fun s ->
        s##setItem storage_key (Js.string (print untyped (root st))))
  with _ -> ()

let attempt f = try f () with Invalid_argument _ | Failure _ | Not_found -> None

(* Puts [text] in place of the node at a path, if it reads as one node there *)
let fill st path text =
  let placed =
    attempt (fun () ->
        let frame, list = slot (root st) path in
        let* read =
          try Some (frame.parse (frame.prefix ^ text ^ frame.suffix))
          with Parsing.Syntax_error _ -> None
        in
        let* _, items = frame.items read in
        match items with
        | [item] -> Some (replace (root st) path list [strip_node item])
        | _ -> None)
  in
  Option.iter (set st) placed;
  placed <> None

(* Puts what stands for nothing in place of the node at a path: a hole, or
   an item of holes *)
let clear st path =
  Option.iter (fun (root, _, _) -> set st root) (attempt (fun () -> place (root st) (Into path) ""))

(* Puts the cell's text in place of its node if it reads as one, or else
   clears it. Returns whether nothing is left that doesn't fit. Text before
   or after a node isn't put there until it's finished. *)
let settle st cell =
  let text = String.trim cell.text in
  match cell.at with
  | Into path -> (text <> "" && fill st path text) || (clear st path; text = "")
  | After _ | Before _ -> text = ""

(* Puts finished text at the cell, which moves on. A token that's already
   next is stepped over instead. *)
let step st cell ?token text =
  let root = root st in
  let stepped =
    match token, cell.filled with
    | Some token, next :: filled when next token -> Some (root, cell.at, filled)
    | Some token, _ ->
      attempt (fun () ->
          match step_over root cell.at token with
          | None -> special root cell.at token
          | stepped -> stepped)
    | None, _ -> None
  in
  let placed () =
    attempt (fun () ->
        match cell.at with
        | Into _ -> place root cell.at text
        | After _ | Before _ -> around root cell.at text)
  in
  match if stepped <> None then stepped else placed () with
  | Some (root, at, filled) ->
    set st root;
    cell.at <- at;
    cell.filled <- filled;
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
    (match cell.at with Into path -> clear st path | After _ | Before _ -> ());
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
   Otherwise the smallest node with text before the cell, from the end of
   which the last character goes, becomes the cell's text, around what's in
   the cell. *)
let melt st cell =
  let root = root st in
  let joined =
    match cell.at with
    | Into path when cell.text = "" ->
      begin match slot root path with
        | _, Some (parent, i) ->
          let first = match list_of (get untyped root parent) with Some (_, first, _) -> first | None -> 0 in
          i > first && refillable (print_at root path)
          && begin match remove root parent i with
            | root ->
              let earlier = parent @ [i - 1] in
              set st root;
              cell.at <- Into earlier;
              cell.filled <- [];
              cell.text <- print_at root earlier;
              cell.caret <- String.length cell.text;
              true
            | exception Invalid_argument _ -> false
          end
        | _, None -> false
      end
    | _ -> false
  in
  if not joined then begin
    let path = path_of cell.at in
    let rec around node_path =
      let text, spans = print_spans_at root node_path in
      let start, stop = List.assoc (List.drop (List.length node_path) path) spans in
      let before, after =
        match cell.at with
        | Into _ -> start, stop
        | Before _ -> start, start
        | After _ -> stop, stop
      in
      let prefix = String.trim (String.sub text 0 before) in
      if prefix <> "" then Some (node_path, text, before, after)
      else Option.bind (split node_path) (fun (parent, _) -> around parent)
    in
    let outer = match cell.at with After _ -> Some path | Into _ | Before _ -> Option.map fst (split path) in
    match Option.bind outer around with
    | None -> ()
    | Some (node_path, text, before, after) ->
      let rec trim_end n = if n > 0 && text.[n - 1] = ' ' then trim_end (n - 1) else n in
      let prefix = String.sub text 0 (trim_end before - 1) in
      let suffix = String.sub text after (String.length text - after) in
      cell.text <- prefix ^ cell.text ^ (if refillable suffix then "" else suffix);
      cell.caret <- String.length prefix;
      cell.at <- Into node_path;
      cell.filled <- []
  end;
  cell.anchor <- cell.caret;
  ignore (settle st cell)

(* Edits the selected node as text, all selected, so typing replaces it. A
   hole is edited empty. *)
let edit st =
  let path = into (root st) st.cursor in
  let node = get untyped (root st) path in
  let text = if hole node then "" else print_at (root st) path in
  st.editing <- Some {at = Into path; text; anchor = 0; caret = String.length text; filled = [];
                      origin = path; before = st.doc};
  st.message <- ""

(* Edits at the start or end of the selected node. What's typed at the start
   wraps it, and at the end, extends it, like with a field or arguments. *)
let insert st ~before =
  let node = get untyped (root st) st.cursor in
  if before && hole node then edit st
  else begin
    (* Around an entry's value *)
    let path = match node with Entry (None, _) -> st.cursor @ [0] | _ -> st.cursor in
    let at = if before then Before path else After path in
    st.editing <- Some {at; text = ""; anchor = 0; caret = 0; filled = []; origin = st.cursor; before = st.doc};
    st.message <- ""
  end

(* The holes, in order *)
let holes root =
  let rec go path node =
    if hole node then [path]
    else List.concat (List.mapi (fun i child -> go (path @ [i]) child) (children untyped node))
  in
  go [] root

let rec is_prefix p q =
  match p, q with
  | [], _ -> true
  | a :: p, b :: q -> a = b && is_prefix p q
  | _ -> false

(* Moves the cell to the next or previous hole, if there is one *)
let to_hole st cell forward =
  let holes = holes (root st) in
  let last p = List.fold_left (fun found h -> if p h then Some h else found) None holes in
  let target =
    match cell.at, forward with
    | Before p, true -> List.find_opt (fun h -> compare h p >= 0) holes
    | (Into p | After p), true -> List.find_opt (fun h -> compare h p > 0 && not (is_prefix p h)) holes
    | (Into p | Before p), false -> last (fun h -> compare h p < 0)
    | After p, false -> last (fun h -> compare h p < 0 || is_prefix p h)
  in
  Option.iter (fun h ->
      cell.at <- Into h;
      cell.filled <- [];
      cell.text <- "";
      cell.anchor <- 0;
      cell.caret <- 0)
    target

(* Stops editing, selecting the node that was edited, or that the cell was
   after, or what the node it was before was wrapped in. Text that doesn't fit
   is dropped. *)
let leave st cell =
  if not (commit st cell ~all:true) then begin
    cell.text <- "";
    ignore (settle st cell)
  end;
  st.editing <- None;
  if st.doc <> cell.before then begin
    st.undo <- cell.before :: st.undo;
    save st
  end;
  let path = match cell.at with Into p | After p -> p | Before _ -> cell.origin in
  st.cursor <- valid (root st) path

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
      let before = cell.at in
      to_hole st cell true;
      if cell.at = before then leave st cell
    end;
    true
  | "Tab" -> if finished () then to_hole st cell (not shift); true
  | "ArrowRight" when at_end -> if finished () then to_hole st cell true; true
  | "ArrowLeft" when at_start -> if finished () then to_hole st cell false; true
  | "Backspace" when at_start -> melt st cell; true
  | "Escape" -> leave st cell; true
  | _ -> false

(* Changes to the program in normal mode *)

let change st root cursor =
  st.undo <- st.doc :: st.undo;
  set st root;
  st.cursor <- valid root cursor;
  st.message <- "";
  save st

(* Rows are a record's entries, a match's clauses, a recur's accumulators,
   and the bindings of a chain of lets, which can be rearranged *)
let is_row = function Entry _ | Clause _ | Binding _ | Acc _ -> true | _ -> false

(* The innermost row at or around the cursor *)
let enclosing_row st =
  let rec go path =
    if is_row (get untyped (root st) path) then Some path
    else Option.bind (split path) (fun (parent, _) -> go parent)
  in
  go st.cursor

(* The paths of the rows before and after one. A binding's are the bindings
   of the lets around and within its own. *)
let neighbours root path =
  let node = get untyped root path in
  let parent_path, i = Option.get (split path) in
  match node with
  | Binding _ ->
    let is_let path = form untyped (get untyped root path) = "let" in
    let before =
      match split parent_path with
      | Some (outer, 1) when is_let outer -> Some (outer @ [0])
      | _ -> None
    in
    let after = if is_let (parent_path @ [1]) then Some (parent_path @ [1; 0]) else None in
    before, after
  | _ ->
    let rows =
      List.concat (List.mapi (fun j child -> if form untyped child = form untyped node then [j] else [])
                     (children untyped (get untyped root parent_path)))
    in
    let before = List.fold_left (fun acc j -> if j < i then Some j else acc) None rows in
    let after = List.find_opt (fun j -> j > i) rows in
    Option.map (fun j -> parent_path @ [j]) before, Option.map (fun j -> parent_path @ [j]) after

(* Swaps the row around the cursor with the one before or after it *)
let move_row st up =
  match enclosing_row st with
  | None -> st.message <- "not in a row"
  | Some path ->
    let root = root st in
    let before, after = neighbours root path in
    match if up then before else after with
    | None -> ()
    | Some other ->
      let a = get untyped root path and b = get untyped root other in
      match update (update root path (fun _ -> b)) other (fun _ -> a) with
      | root -> change st root other
      | exception Invalid_argument _ -> st.message <- "can't move this here"

let expr_of = function E e -> e | _ -> invalid_arg "expr_of"

(* Deletes a row. A binding goes with the rest of its let, leaving the let's
   body. *)
let delete_row st path =
  let root = root st in
  let parent, i = Option.get (split path) in
  let node = get untyped root path in
  match node with
  | Binding _ -> change st (update root parent (fun _ -> get untyped root (parent @ [1]))) parent
  | _ ->
    match remove root parent i with
    | exception Invalid_argument _ -> st.message <- "can't delete this"
    | after ->
      (* The next row, which takes its place, or else the one before *)
      let is_row path = Option.map (form untyped) (find untyped after path) = Some (form untyped node) in
      let cursor = List.find_opt is_row [path; parent @ [i - 1]] in
      change st after (Option.value cursor ~default:parent)

(* An item of holes, for a list read in a frame *)
let template frame =
  let* _, read = read frame (frame.prefix ^ frame.standin) in
  let* _, items = frame.items read in
  match items with [item] -> Some (strip_node item) | _ -> None

(* Inserts a row of holes before or after the one around the cursor, and
   edits its first hole *)
let insert_row st after =
  match enclosing_row st with
  | None -> st.message <- "not in a row"
  | Some path ->
    let root = root st in
    let parent, i = Option.get (split path) in
    let fresh body = E {Expr.expr = Let {pat = wildcard; defn = hole_expr; body = expr_of body}; loc = ()} in
    let inserted =
      attempt (fun () ->
          match get untyped root path with
          | Binding _ ->
            if after then Some (update root (parent @ [1]) fresh, parent @ [1; 0])
            else Some (update root parent fresh, parent @ [0])
          | _ ->
            let* frame, _, _ = list_of (get untyped root parent) in
            let* row = template frame in
            let j = if after then i + 1 else i in
            let root =
              update root parent (fun node ->
                  let cs = children untyped node in
                  rebuild node (List.take j cs @ [row] @ List.drop j cs))
            in
            Some (root, parent @ [j]))
    in
    match inserted with
    | None -> st.message <- "can't insert a row here"
    | Some (root, row) ->
      change st root row;
      Option.iter (fun h -> st.cursor <- h)
        (List.find_opt (is_prefix row) (holes (E st.doc)));
      edit st

(* Replaces the selected node with a hole, or removes it from its list *)
let delete st =
  let root = root st in
  let path = st.cursor in
  match get untyped root path with
  | node when is_row node -> delete_row st path
  | E _ -> change st (update root path (fun _ -> E hole_expr)) path
  | P _ -> change st (update root path (fun _ -> P wildcard)) path
  | Item _ | Using _ | Rest _ ->
    let parent, i = Option.get (split path) in
    begin match remove root parent i with
      | root -> change st root parent
      | exception Invalid_argument _ -> st.message <- "can't delete this"
    end
  | _ -> st.message <- "can't delete this"

(* Drawing *)

(* Layout. Blocks span several lines; everything else is inline. *)
let rec is_block node =
  match form typed node with
  | "let" | "abstract" | "alias" | "recur" -> true
  | "match" -> List.length (children typed node) > 2 || List.exists is_block (children typed node)
  | _ -> List.exists is_block (children typed node)

(* Where a block's lines break. Keywords like `in` and `->` end a line, and
   separators start one, so a list in brackets is laid out as
     { a
     , b
     }
   Each break is before a child, or before the closing bracket. *)
type break = Ends_line of bool | Starts_line of bool (* whether it's indented *)

let line_break node i child =
  let last = i = List.length (children typed node) - 1 in
  let when_ cond break = if cond then Some break else None in
  match form typed node with
  | "let" | "abstract" | "alias" -> when_ last (Ends_line false)
  | "recur" -> when_ last (Ends_line true)
  | "match" -> when_ (i > 0) (Starts_line true)
  | "record" | "variant" -> when_ (i > 0) (Starts_line false)
  | "apply" -> when_ (i > 1) (Starts_line false)
  (* Other blocks can start on the same line, and break within *)
  | _ -> when_ (last && List.mem (form typed child) ["let"; "abstract"; "alias"]) (Ends_line true)

let closing_break node =
  match form typed node with
  | "match" -> Some (Starts_line true)
  | "record" | "variant" | "apply" -> Some (Starts_line false)
  | _ -> None

let text s = (doc##createTextNode (Js.string s) :> Dom.node Js.t)

let trim_end s =
  let n = ref (String.length s) in
  while !n > 0 && s.[!n - 1] = ' ' do decr n done;
  String.sub s 0 !n

(* Set below, once drawing the whole workspace is defined *)
let redraw = ref (fun () -> ())

(* Each value is shown in the gutter, level with the line its node starts *)
let value (s, title) =
  let el = Dom_html.createSpan doc in
  el##.className := Js.string "value";
  el##.title := Js.string title;
  Dom.appendChild el (text s);
  (el :> Dom.node Js.t)

(* A type error, in a block under the line it's on *)
let problem_block indent msg =
  let el = Dom_html.createDiv doc in
  el##.className := Js.string (if indent then "problem indent" else "problem");
  Dom.appendChild el (text msg);
  (el :> Dom.node Js.t)

(* The values and type errors to show by path, and whether the cell has been
   put in yet *)
type context = {
  values : (path * (string * string)) list;
  problems : (path * string) list;
  mutable placed : bool;
}

(* Draws a node, giving [report] its errors and those of the inline nodes
   within it, for the line they're on. A block shows those on each of its own
   lines under it. *)
let rec render st ctx ~report ?sugared path (node : checked) : Dom.node Js.t =
  match st.editing with
  | Some {at = Into p; _} when p = path ->
    ctx.placed <- true;
    (st.area :> Dom.node Js.t)
  | _ ->
    let block = is_block node in
    (* Inline, even for blocks, whose lines are divs within *)
    let el = Dom_html.createSpan doc in
    let classes = ["node"; "form-" ^ form typed node] in
    let classes = if path = st.cursor && st.editing = None then "selected" :: classes else classes in
    let problems = List.filter_map (fun (p, msg) -> if p = path then Some msg else None) ctx.problems in
    let classes = if problems <> [] then "error" :: classes else classes in
    el##.className := Js.string (String.concat " " classes);
    List.iter report problems;
    let select ev =
      Dom_html.stopPropagation ev;
      Option.iter (leave st) st.editing;
      st.cursor <- path;
      st.message <- ""
    in
    el##.onclick := Dom_html.handler (fun ev -> select ev; !redraw (); Js._false);
    el##.ondblclick := Dom_html.handler (fun ev -> select ev; edit st; !redraw (); Js._false);
    let line = ref (el :> Dom.node Js.t) and indented = ref false in
    let pending = ref [] in
    let flush () =
      List.iter (fun msg -> Dom.appendChild el (problem_block !indented msg)) (List.rev !pending);
      pending := []
    in
    let report = if block then (fun msg -> pending := msg :: !pending) else report in
    let new_line indent =
      flush ();
      indented := indent;
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
      | None -> if gap <> "" then Dom.appendChild !line (text gap)
    in
    let cell at =
      match st.editing with
      | Some cell when cell.at = at ->
        ctx.placed <- true;
        Dom.appendChild !line st.area
      | _ -> ()
    in
    let breaks =
      List.mapi (fun i child -> if block then line_break node i child else None) (children typed node)
    in
    (* Brackets go on their own lines only when what's between them does *)
    let bracketed = List.exists Option.is_some breaks && closing_break node <> None in
    let gap = Buffer.create 16 in
    let take () = let g = Buffer.contents gap in Buffer.clear gap; g in
    ignore (List.fold_left (fun i -> function
        | Text t -> Buffer.add_string gap t; i
        | Part child ->
          let g = take () in
          (* Space after an opening bracket, to line up with the separators *)
          let g = if i = 0 && bracketed && String.trim g <> "" then String.trim g ^ " " else g in
          put g (List.nth breaks i);
          let p = path @ [i] in
          cell (Before p);
          Option.iter (fun v -> Dom.appendChild !line (value v)) (List.assoc_opt p ctx.values);
          Dom.appendChild !line (render st ctx ~report ~sugared:(shows_sugar typed node i) p child);
          cell (After p);
          after_block := is_block child;
          i + 1)
        0 (parts ?sugared typed node));
    let g = take () in
    if bracketed then put (String.trim g) (closing_break node) else put g None;
    flush ();
    (el :> Dom.node Js.t)

(* The values bound by the program's top-level lets, and the value of the
   whole program, by the paths of the bindings and the final body. Each has
   a tooltip, which for the whole program includes its type. *)
let values (program : path Type.expr) =
  let show_bound env env' =
    let bound = List.filteri (fun i _ -> i < List.length env' - List.length env) env' in
    String.concat ", " (List.rev_map (fun (name, v) -> name ^ " = " ^ Runtime.show v) bound)
  in
  let rec bindings env path (e : path Type.expr) =
    match e.expr with
    | Let {pat; defn; body} ->
      begin match Runtime.define env pat defn with
        | Some env' -> (path @ [0], show_bound env env') :: bindings env' (path @ [1]) body
        | None -> []
      end
    | Abstract (_, body) -> bindings env (path @ [0]) body
    | Alias (_, _, body) -> bindings env (path @ [1]) body
    | _ -> []
  in
  let rec body path (e : path Type.expr) =
    match e.expr with
    | Let {body = b; _} -> body (path @ [1]) b
    | Abstract (_, b) -> body (path @ [0]) b
    | Alias (_, _, b) -> body (path @ [1]) b
    | _ -> path
  in
  let result =
    match Runtime.show (Runtime.eval prelude.env program) with
    | value -> value, Printf.sprintf "the %s %s" (Type.show program.ty) value
    | exception e -> let msg = "evaluation failed: " ^ Printexc.to_string e in msg, msg
  in
  let bound = List.filter (fun (_, v) -> v <> "") (bindings prelude.env [] program) in
  (body [] program, result) :: List.map (fun (path, v) -> path, (v, v)) bound

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
  let program, errors =
    match locate [] (root st) with
    | E located -> check ~vars:prelude.vars located
    | _ -> invalid_arg "draw"
  in
  let root = E program in
  let editor = Dom_html.getElementById "editor" in
  editor##.innerHTML := Js.string "";
  let problems = List.map (fun (path, problem) -> path, Type.describe problem) errors in
  let ctx = {values = values program; problems; placed = false} in
  let cell at =
    match st.editing with
    | Some cell when cell.at = at ->
      ctx.placed <- true;
      Dom.appendChild editor st.area
    | _ -> ()
  in
  Option.iter (fun v -> Dom.appendChild editor (value v)) (List.assoc_opt [] ctx.values);
  cell (Before []);
  let pending = ref [] in
  Dom.appendChild editor (render st ctx ~report:(fun msg -> pending := msg :: !pending) [] root);
  cell (After []);
  if st.editing <> None && not ctx.placed then Dom.appendChild editor st.area;
  List.iter (fun msg -> Dom.appendChild editor (problem_block false msg)) (List.rev !pending);
  let set id s = (Dom_html.getElementById id)##.textContent := Js.some (Js.string s) in
  (* Why the prelude didn't load, and what's happened in the editor *)
  set "output" (String.concat "\n" (List.filter (( <> ) "") [prelude_error; st.message]));
  set "source" (print untyped (E st.doc));
  Option.iter (show_cell st) st.editing

let move st path = if find untyped (root st) path <> None then st.cursor <- path

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
  | "I" -> insert st ~before:true; true
  | "A" -> insert st ~before:false; true
  | "d" | "Delete" | "Backspace" -> delete st; true
  | "K" -> move_row st true; true
  | "J" -> move_row st false; true
  | "o" -> insert_row st true; true
  | "O" -> insert_row st false; true
  | "u" ->
    begin match st.undo with
      | previous :: rest ->
        st.doc <- previous;
        st.undo <- rest;
        st.cursor <- valid (root st) st.cursor;
        save st
      | [] -> st.message <- "nothing to undo"
    end;
    true
  | _ -> false

let () =
  let program =
    let source = Option.value (load ()) ~default:"let id(x) = x in id(#hello)" in
    try strip (Parsing.parse source) with Parsing.Syntax_error _ -> hole_expr
  in
  let area = Dom_html.createSpan doc in
  area##.className := Js.string "cell";
  area##setAttribute (Js.string "contenteditable") (Js.string "plaintext-only");
  area##setAttribute (Js.string "spellcheck") (Js.string "false");
  let st = {doc = program; cursor = []; editing = None; message = ""; undo = []; area} in
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
