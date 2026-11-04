exception Compile_error of string

(* Fields, environments and rows are association lists keyed by name.
   Positional fields are labelled 1, 2, ... *)
let label i = string_of_int (i + 1)

let show_fields buf ~sep show fields =
  List.iteri (fun i (name, x) ->
      if i <> 0 then
        Buffer.add_string buf ", ";
      if not (String.equal name (label i)) then
        Printf.bprintf buf ".%s %s " name sep;
      show x)
    fields

module Type = struct
  type t =
    | Record of row
    | Variant of row (* each tag's payload is a Record *)
    | Function of {
        inputs : t;
        deps : t;
        exists : abstract list; (* quantified in output, written `exists t.` *)
        output : t
      }
    | Recurs of recurs
    | Var of var ref
    (* An occurrence of an abstract type, with its view of the underlying type.
       The abstract type is parameterized by the variables of its underlying
       type that get generalized, so [view] is an instance of [abs.repr]. *)
    | Rigid of {abs : abstract; view : t}

  and row = {fields : (string * t) list; rest : t option}

  (* A recursive type's binder is the Recurs node itself, so cyclic types are
     cyclic graphs. The index is shared by every layer of a cycle: [empty] when
     absent, and the Rigid of a `recur` while its subterms are recursed on. *)
  and recurs = {mutable body : t; index : t}

  and var =
    | Unbound of {
        id : int;
        mutable level : int;
        mutable fun_level : int
      }
    | Link of t

  and abstract = {
    name : string;
    id : int;
    mutable fun_level : int;
    repr : t
  }

  (***
   * Inference is done by the parser, in a single pass:
   *  - Algorithm J-style, using refs for type vars rather than a Map
   *  - Attaches levels to type vars for generalization rather than scanning the environment:
   *    `let` depth for universal type variables, function depth for existential ones
   **)
  let level = ref 0
  let fun_level = ref 0 (* fun_level(language_design) > 9000 *)
  let generic = max_int
  let counter = ref 0

  let fresh ?(level = !level) () =
    incr counter;
    Var (ref (Unbound {id = !counter; level; fun_level = !fun_level}))

  let abstract name repr =
    incr counter;
    {name; id = !counter; fun_level = !fun_level; repr}

  let rigid name repr = Rigid {abs = abstract name repr; view = repr}

  let empty = Record {fields = []; rest = None}

  let rec prune = function
    | Var {contents = Link ty} -> prune ty
    | ty -> ty

  (* A row's fields through bound row variables, and the rest. Fields repeat
     where a record extends another. *)
  let rec flatten variant {fields; rest} =
    match variant, Option.map prune rest with
    | false, Some (Record r) | true, Some (Variant r) ->
      let more, rest = flatten variant r in
      fields @ more, rest
    | _, rest -> fields, rest

  (* Visits each node, following each cycle once *)
  let iter f ty =
    let recs = ref [] in
    let rec go ty =
      let ty = prune ty in
      f ty;
      match ty with
      | Record r | Variant r ->
        List.iter (fun (_, ty) -> go ty) r.fields;
        Option.iter go r.rest
      | Function fn -> go fn.inputs; go fn.deps; go fn.output
      | Recurs r when not (List.memq r !recs) ->
        recs := r :: !recs;
        go r.index;
        go r.body
      | Rigid r -> go r.view
      | _ -> ()
    in
    go ty

  let contains p ty =
    try iter (fun ty -> if p ty then raise Exit) ty; false
    with Exit -> true

  (* What each of an abstract type's parameters - the generalized variables of
     its underlying type - is in an occurrence's [view]. Row variables aren't
     parameters, since they'd expose the shape of the underlying type. *)
  let args abs view =
    let found = ref [] and recs = ref [] in
    let rec go a b =
      match prune a, prune b with
      | Var ({contents = Unbound {level; _}} as v), b when level = generic ->
        if not (List.mem_assq v !found) then
          found := !found @ [v, b]
      | Record r1, Record r2 | Variant r1, Variant r2 ->
        List.iter (fun (name, a) -> Option.iter (go a) (List.assoc_opt name r2.fields)) r1.fields
      | Function f1, Function f2 -> go f1.inputs f2.inputs; go f1.deps f2.deps; go f1.output f2.output
      | Recurs r1, Recurs r2 when not (List.memq r1 !recs) ->
        recs := r1 :: !recs;
        go r1.index r2.index;
        go r1.body r2.body
      | Rigid r1, Rigid r2 -> go r1.view r2.view
      | _ -> ()
    in
    go abs.repr view;
    List.map snd !found

  let show ty =
    let buf = Buffer.create 32 in
    let count = ref 0 and vars = ref [] and recs = ref [] in
    let next () =
      let n = !count in
      incr count;
      if n < 26 then Printf.sprintf "'%c" (Char.chr (97 + n))
      else Printf.sprintf "'t%i" n
    in
    let rec go ty =
      match prune ty with
      | Var {contents = Unbound {id; _}} ->
        let name =
          match List.assoc_opt id !vars with
          | Some name -> name
          | None ->
            let name = next () in
            vars := (id, name) :: !vars;
            name
        in
        Buffer.add_string buf name
      | Var {contents = Link _} -> assert false

      | Rigid {abs; view} ->
        Buffer.add_string buf abs.name;
        begin match args abs view with
          | [] -> ()
          | args ->
            Buffer.add_char buf '(';
            List.iteri (fun i ty -> if i <> 0 then Buffer.add_string buf ", "; go ty) args;
            Buffer.add_char buf ')'
        end

      | Record r ->
        Buffer.add_char buf '{';
        row false (show_fields buf ~sep:":" go) r;
        Buffer.add_char buf '}'

      | Variant r ->
        Buffer.add_char buf '[';
        row true (List.iteri (fun i (tag, payload) ->
            if i <> 0 then
              Buffer.add_string buf ", ";
            Printf.bprintf buf "#%s" tag;
            match prune payload with
            | Record {fields = []; rest = None} -> ()
            | Record r ->
              Buffer.add_char buf '(';
              row false (show_fields buf ~sep:":" go) r;
              Buffer.add_char buf ')'
            | ty -> go ty))
          r;
        Buffer.add_char buf ']'

      | Function fn ->
        Buffer.add_string buf "fun(";
        let start = Buffer.length buf in
        begin match prune fn.inputs with
          | Record r -> row false (show_fields buf ~sep:":" go) r
          | ty -> go ty
        end;
        begin match prune fn.deps with
          | Var _ | Record {fields = []; rest = None} -> ()
          | deps ->
            if Buffer.length buf > start then
              Buffer.add_string buf ", ";
            Buffer.add_string buf "using ";
            go deps
        end;
        Buffer.add_string buf ") -> ";
        if fn.exists <> [] then
          Printf.bprintf buf "exists %s. "
            (String.concat ", " (List.map (fun abs -> abs.name) fn.exists));
        go fn.output

      | Recurs r ->
        match List.assq_opt r !recs with
        | Some name -> Buffer.add_string buf name
        | None ->
          let cyclic = contains (function Recurs r' -> r' == r | _ -> false) r.body in
          let name = if cyclic then next () else "_" in
          recs := (r, name) :: !recs;
          Buffer.add_string buf "rec ";
          begin match prune r.index with
            | Rigid {abs; _} -> Printf.bprintf buf "[%s] " abs.name
            | _ -> ()
          end;
          Printf.bprintf buf "%s. " name;
          go r.body

    and row variant show_items r =
      let fields, rest = flatten variant r in
      let fields =
        List.fold_left (fun acc (name, ty) ->
            if List.mem_assoc name acc then acc else acc @ [name, ty])
          [] fields
      in
      show_items fields;
      Option.iter (fun rest ->
          if fields <> [] then
            Buffer.add_string buf ", ";
          Buffer.add_string buf "..";
          go rest)
        rest
    in
    go ty;
    Buffer.contents buf

  (* Copies a type, preserving cycles, with [leaf] choosing replacements for
     variables and abstract types. Types copied by one [copy leaf] share their
     copies of recursive types. *)
  let copy leaf =
    let recs = ref [] in
    let rec go ty =
      match prune ty with
      | Record r -> Record (row r)
      | Variant r -> Variant (row r)
      | Function fn ->
        Function {fn with inputs = go fn.inputs; deps = go fn.deps; output = go fn.output}
      | Recurs r ->
        begin match List.assq_opt r !recs with
          | Some r' -> Recurs r'
          | None ->
            let r' = {body = r.body; index = go r.index} in
            recs := (r, r') :: !recs;
            r'.body <- go r.body;
            Recurs r'
        end
      | ty ->
        match leaf ty, ty with
        | Some ty, _ -> ty
        | None, Rigid r -> Rigid {r with view = go r.view}
        | None, ty -> ty
    and row {fields; rest} =
      {fields = List.map (fun (name, ty) -> name, go ty) fields; rest = Option.map go rest}
    in
    go

  let memo () =
    let table = ref [] in
    fun id make ->
      match List.assoc_opt id !table with
      | Some ty -> ty
      | None ->
        let ty = make () in
        table := (id, ty) :: !table;
        ty

  let generalize ty =
    iter (function
        | Var {contents = Unbound u} when u.level > !level -> u.level <- generic
        | _ -> ())
      ty

  (* Copies only when needed, so recursive types keep their identity *)
  let instantiate ty =
    let fresh_for = memo () in
    let is_generic = function Var {contents = Unbound u} -> u.level = generic | _ -> false in
    if not (contains is_generic ty) then ty
    else copy (function
        | Var {contents = Unbound u} when u.level = generic -> Some (fresh_for u.id fresh)
        | _ -> None)
      ty

  (* The abstract types in a type, other than those quantified by a function
     type within it *)
  let abstracts ty =
    let found = ref [] and bound = ref [] in
    iter (function
        | Rigid {abs; _} when not (List.memq abs !found) -> found := !found @ [abs]
        | Function fn -> bound := fn.exists @ !bound
        | _ -> ())
      ty;
    List.filter (fun abs -> not (List.memq abs !bound)) !found

  (* Abstract types introduced within the current function *)
  let existentials ty = List.filter (fun abs -> abs.fun_level > !fun_level) (abstracts ty)

  let mentions abss ty = contains (function Rigid {abs; _} -> List.memq abs abss | _ -> false) ty

  (* At application, each existential gets a fresh abstract type, keeping the
     original underlying type to find its parameters *)
  let open_exists ty =
    match prune ty with
    | Function fn when fn.exists <> [] ->
      let fresh_for = memo () in
      let rec output ty =
        copy (function
            | Rigid r when List.memq r.abs fn.exists ->
              let abs = fresh_for r.abs.id (fun () -> abstract r.abs.name r.abs.repr) in
              Some (Rigid {abs; view = output r.view})
            | _ -> None)
          ty
      in
      Function {fn with exists = []; output = output fn.output}
    | ty -> ty

  (* Undoes the changes made by the current unification, so a failed one
     leaves types as they were *)
  let trail = ref []
  let save undo = trail := undo :: !trail

  (* A type may only contain itself through a recursive type, and not within a
     function's parameters, so recursive types stay strictly positive. Looking
     through abstract types forbids recursion via their underlying types. *)
  let occurs var ty =
    let seen = ref [] in
    let rec go guarded positive ty =
      match prune ty with
      | Var v when v == var ->
        if not (guarded && positive) then raise (Compile_error "infinite type")
      | Record r | Variant r ->
        List.iter (fun (_, ty) -> go guarded positive ty) r.fields;
        Option.iter (go guarded positive) r.rest
      | Function fn ->
        go guarded false fn.inputs;
        go guarded false fn.deps;
        go guarded positive fn.output
      | Recurs r when not (List.exists (fun (r', p) -> r' == r && p = positive) !seen) ->
        seen := (r, positive) :: !seen;
        go guarded positive r.index;
        go true positive r.body
      | Rigid r -> go false false r.view
      | _ -> ()
    in
    go false true ty;
    (* Through underlying types too, so an abstract type can't carry a `recur`
       index out of its scope *)
    match !var with
    | Unbound {level = lv; fun_level = fl; _} ->
      iter (function
          | Var {contents = Unbound u} ->
            let level = u.level and fun_level = u.fun_level in
            save (fun () -> u.level <- level; u.fun_level <- fun_level);
            u.level <- min level lv;
            u.fun_level <- min fun_level fl
          | Rigid {abs; _} ->
            let fun_level = abs.fun_level in
            save (fun () -> abs.fun_level <- fun_level);
            abs.fun_level <- min fun_level fl
          | _ -> ())
        ty
    | Link _ -> ()

  let unify a b =
    let seen = ref [] and renamed = ref [] and binders = ref [] in
    let rec go a b =
      match prune a, prune b with
      | Var v1, Var v2 when v1 == v2 -> ()
      | Var v, ty | ty, Var v ->
        occurs v ty;
        let old = !v in
        save (fun () -> v := old);
        v := Link ty
      | Record r1, Record r2 -> rows false r1 r2
      | Variant r1, Variant r2 -> rows true r1 r2
      | Function f1, Function f2 ->
        if List.compare_lengths f1.exists f2.exists <> 0 then
          raise (Compile_error "functions with different numbers of existential types");
        go f1.inputs f2.inputs;
        go f1.deps f2.deps;
        (* Existentials match up to renaming *)
        let outer = !renamed and outer_binders = !binders in
        if not (List.for_all (fun abs -> List.memq abs f2.exists) f1.exists) then
          binders := (f1.exists, f2.exists) :: outer_binders;
        go f1.output f2.output;
        renamed := outer;
        binders := outer_binders
      | (Recurs r1 as a), (Recurs r2 as b) ->
        if r1 != r2 && not (List.exists (fun (x, y) -> x == r1 && y == r2) !seen) then begin
          seen := (r1, r2) :: !seen;
          (try go r1.index r2.index with Compile_error _ -> mismatch a b);
          go r1.body r2.body
        end
      | Rigid r1, Rigid r2 when r1.abs == r2.abs -> go r1.view r2.view
      (* Renamed existentials are compared by their parameters, so their
         underlying types stay hidden *)
      | (Rigid r1 as a), (Rigid r2 as b) when rename r1.abs r2.abs ->
        let args1 = args r1.abs r1.view and args2 = args r2.abs r2.view in
        if List.compare_lengths args1 args2 <> 0 then mismatch a b;
        List.iter2 go args1 args2
      | a, b -> mismatch a b

    (* Pairs two existentials, one from each function type, the first time
       they meet; each may only be paired once *)
    and rename x y =
      let among (xs, ys) = List.memq x xs && List.memq y ys || List.memq y xs && List.memq x ys in
      let pairs (x', y') = x' == x && y' == y || x' == y && y' == x in
      let either (x', y') = x' == x || x' == y || y' == x || y' == y in
      List.exists pairs !renamed
      || List.exists among !binders && not (List.exists either !renamed)
         && (renamed := (x, y) :: !renamed; true)

    and mismatch a b =
      let why =
        match a, b with
        | Rigid r1, Rigid r2
          when String.equal r1.abs.name r2.abs.name && not (rename r1.abs r2.abs) ->
          ", a different abstract type"
        | _ -> ""
      in
      raise (Compile_error (Printf.sprintf "cannot unify %s with %s%s" (show a) (show b) why))

    (* A row's distinct fields; repeated fields must agree *)
    and fields variant row =
      let fields, rest = flatten variant row in
      begin match rest with
        | Some (Var _) | None -> ()
        | Some ty -> raise (Compile_error ("expected a row, found " ^ show ty))
      end;
      List.fold_left (fun acc (name, ty) ->
          match List.assoc_opt name acc with
          | Some ty' -> go ty ty'; acc
          | None -> acc @ [name, ty])
        [] fields,
      rest

    and rows variant r1 r2 =
      let wrap row = if variant then Variant row else Record row in
      let f1, rest1 = fields variant r1 in
      let f2, rest2 = fields variant r2 in
      List.iter (fun (name, ty) -> Option.iter (go ty) (List.assoc_opt name f2)) f1;
      let extra fs others = List.filter (fun (name, _) -> not (List.mem_assoc name others)) fs in
      let extra1 = extra f1 f2 and extra2 = extra f2 f1 in
      let missing = function
        | [] -> ()
        | (name, _) :: _ ->
          raise (Compile_error ((if variant then "no tag #" else "no field .") ^ name))
      in
      match rest1, rest2 with
      | Some (Var v1), Some (Var v2) when v1 == v2 -> missing extra1; missing extra2
      | _ ->
        let tail = if Option.is_some rest1 && Option.is_some rest2 then Some (fresh ()) else None in
        let extend rest extra =
          match rest with
          | Some rest -> go rest (wrap {fields = extra; rest = tail})
          | None -> missing extra
        in
        extend rest1 extra2;
        extend rest2 extra1
    in
    trail := [];
    try go a b with Compile_error _ as e -> List.iter (fun undo -> undo ()) !trail; raise e

  (* A variant row's tags with their payloads, and its tail variable if it's
     open, which identifies the row *)
  let tags ty =
    match prune ty with
    | Variant r ->
      let fields, rest = flatten true r in
      fields, (match rest with Some (Var v) -> Some v | _ -> None)
    | Var v -> [], Some v
    | _ -> [], None

  (* Closes a variant row by its tail, so it can't take more tags *)
  let close tail = unify (Var tail) (Variant {fields = []; rest = None})
end

module Pat = struct
  type t =
      Var of string
    | Wildcard
    | Record of (string * typed) list
    | Variant of string * (string * typed) list
    | Roll of typed
    | Or of typed * typed
    | Error of {pos : int; msg : string; p : typed} (* a type error *)

  and typed = {
    pat : t;
    ty : Type.t
  }

  type coverage = Exhaustive | Missing of string | Ambiguous

  (* Checks that patterns are exhaustive, following Maranget's usefulness
     algorithm, and closes the open variant rows they must close to be: those
     a match can't be exhaustive without, even with every other row closed.
     Closing a row only removes values, so if closing just those isn't enough,
     there's no single least choice of rows to close, and it's ambiguous. *)
  let check pats =
    let wild = {pat = Wildcard; ty = Type.empty} in
    let rec row_type ty =
      match Type.prune ty with
      | Rigid r -> row_type r.view (* under `the t`, matching t's underlying type *)
      | ty -> ty
    in
    (* Field names in order of first appearance *)
    let names fieldss =
      List.fold_left (fun acc fields ->
          acc @ List.filter (fun name -> not (List.mem name acc)) (List.map fst fields))
        [] fieldss
    in
    let show_fields names ws =
      String.concat ", " (List.mapi (fun i (name, w) ->
          if String.equal name (label i) then w else "." ^ name ^ " = " ^ w)
          (List.combine names ws))
    in
    (* Finds a value, as text, that no row matches, treating the open variant
       rows [closed] picks as closed, and collecting the open rows into [found] *)
    let found = ref [] in
    let rec go closed n rows =
      let rec expand = function
        | {pat = Or (p, q); _} :: rest -> expand (p :: rest) @ expand (q :: rest)
        | row -> [row]
      in
      match List.concat_map expand rows with
      | [] -> Some (List.init n (fun _ -> "_"))
      | _ when n = 0 -> None
      | rows ->
        (* An erroneous pattern doesn't count as missing anything *)
        let is_wild p = match p.pat with Var _ | Wildcard | Error _ -> true | _ -> false in
        let heads = List.map List.hd rows in
        (* Rows whose head is the constructor [sub] picks out, with its k
           subpatterns in place of the head *)
        let specialize k sub rebuild =
          let rows = List.filter_map (function
              | p :: rest when is_wild p -> Some (List.init k (fun _ -> wild) @ rest)
              | p :: rest -> Option.map (fun ps -> ps @ rest) (sub p)
              | [] -> None)
              rows
          in
          Option.map (fun w -> rebuild (List.take k w) :: List.drop k w)
            (go closed (k + n - 1) rows)
        in
        let fields_of names fields =
          List.map (fun name -> Option.value (List.assoc_opt name fields) ~default:wild) names
        in
        match List.find_opt (fun p -> not (is_wild p)) heads with
        | None -> Option.map (fun w -> "_" :: w) (go closed (n - 1) (List.map List.tl rows))

        | Some {pat = Roll _; _} ->
          specialize 1 (function {pat = Roll p; _} -> Some [p] | _ -> None)
            (fun ws -> "&" ^ List.hd ws)

        | Some {pat = Record _; _} ->
          let names = names (List.filter_map (function
              | {pat = Record fields; _} -> Some fields
              | _ -> None)
              heads)
          in
          specialize (List.length names)
            (function {pat = Record fields; _} -> Some (fields_of names fields) | _ -> None)
            (fun ws -> "{" ^ show_fields names ws ^ "}")

        | Some p ->
          let tags, tail = Type.tags (row_type p.ty) in
          Option.iter (fun v -> if not (List.memq v !found) then found := !found @ [v]) tail;
          let open_ = match tail with Some v -> not (closed v) | None -> false in
          let seen = List.filter_map (function
              | {pat = Variant (tag, _); _} -> Some tag
              | _ -> None)
              heads
          in
          let case (tag, payload) =
            let fieldss = List.filter_map (function
                | {pat = Variant (tag', fields); _} when tag' = tag -> Some fields
                | _ -> None)
                heads
            in
            let names = names fieldss in
            specialize (List.length names)
              (function
                | {pat = Variant (tag', fields); _} when tag' = tag -> Some (fields_of names fields)
                | _ -> None)
              (fun ws ->
                 let tag = "#" ^ tag in
                 match ws, Type.prune payload with
                 | [], Record {fields = []; rest = None} -> tag
                 | [], _ -> tag ^ "(..)"
                 | ws, _ -> tag ^ "(" ^ show_fields names ws ^ ")")
          in
          let complete = not open_ && List.for_all (fun (tag, _) -> List.mem tag seen) tags in
          let default () = go closed (n - 1) (List.filter_map (function
              | p :: rest when is_wild p -> Some rest
              | _ -> None)
              rows)
          in
          if complete then List.find_map case tags
          else match default () with
            | None -> None
            | Some w when open_ -> Some ("_" :: w) (* any other tag *)
            | Some _ -> List.find_map case tags
    in
    let missing closed = Option.map List.hd (go closed 1 (List.map (fun p -> [p]) pats)) in
    match missing (fun _ -> true) with
    | Some w -> Missing w
    | None ->
      let forced = List.filter (fun v -> missing (fun v' -> v' != v) <> None) !found in
      match missing (fun v -> List.memq v forced) with
      | None -> List.iter Type.close forced; Exhaustive
      | Some _ -> Ambiguous
end

module Expr = struct
  (* `the` and `abstract` only affect typing, so they don't appear here *)
  type t =
      Record of {fields : (string * typed) list; rest : typed option}
    | Field of typed * string

    | Variant of string * (string * typed) list
    | Match of typed * (Pat.typed * typed) list

    | Function of {
        params : (string * Pat.typed) list;
        deps : Pat.typed option;
        body : typed
      }
    | Apply of {
        f : typed;
        args : (string * typed) list;
        deps : typed option
      }
    | Dep of string

    | Var of string
    | Let of {
        pat : Pat.typed;
        defn : typed;
        body : typed
      }

    | Roll of typed
    (* `recur (p <- e, ...) do body`: [params] start with `&p`, and body sees
       [continue] and [forget] *)
    | Recur of {
        continue : string;
        forget : string;
        params : (string * Pat.typed) list;
        args : (string * typed) list;
        body : typed
      }

    | Hole (* `_` *)
    (* A type error in [e], which makes it evaluate to a hole *)
    | Error of {pos : int; msg : string; e : typed}

  and typed = {
    expr : t;
    ty : Type.t
  }
end

(* The concrete syntax tree, for the editor: each construct's [form], like
   "let" or "match", with the typed node it was checked as, its span in the
   source, and the constructs within it. Keywords and punctuation are in the
   text between the children's spans. The sugar `let f(x) = e` and
   `.f(x) = e` has no node for the function, so its parameters and body are
   the binding's or the field's.

   Some nodes are rows, which the editor can rearrange: a record's entries,
   a match's clauses, and a let's binding, `p = e` without the body. *)
module Syntax = struct
  type t = {
    form : string;
    info : info;
    start : int;
    stop : int;
    children : t list
  }

  and info = Expr of Expr.typed | Pat of Pat.typed | Other
end

module Parsing = struct
  type token =
      Let
    | In
    | Fun
    | Using
    | Abstract
    | The
    | Rec
    | Recur
    | Do
    | Or
    | Underscore
    | LeftParen
    | RightParen
    | LeftCurly
    | RightCurly
    | LeftSquare
    | RightSquare
    | Comma
    | Arrow
    | LeftArrow
    | Equal
    | Colon
    | Dot
    | DotDot
    | Ampersand
    | Ident of string
    | Field of string
    | Tag of string
    | TypeVar of string
    | Dep of string
    | EOF

  let string_of_token = function
    | Let -> "let"
    | In -> "in"
    | Fun -> "fun"
    | Using -> "using"
    | Abstract -> "abstract"
    | The -> "the"
    | Rec -> "rec"
    | Recur -> "recur"
    | Do -> "do"
    | Or -> "or"
    | Underscore -> "_"
    | LeftParen -> "("
    | RightParen -> ")"
    | LeftCurly -> "{"
    | RightCurly -> "}"
    | LeftSquare -> "["
    | RightSquare -> "]"
    | Comma -> ","
    | Arrow -> "->"
    | LeftArrow -> "<-"
    | Equal -> "="
    | Colon -> ":"
    | Dot -> "."
    | DotDot -> ".."
    | Ampersand -> "&"
    | Ident sym -> sym
    | Field sym -> "." ^ sym
    | Tag sym -> "#" ^ sym
    | TypeVar sym -> "'" ^ sym
    | Dep sym -> "@" ^ sym
    | EOF -> "end of input"

  let line_and_col_of_pos input target =
    let rec aux pos line col =
      if Int.equal pos target then
        (line, col)
      else
        match input.[pos] with
        | '\n' -> aux (pos+1) (line+1) 1
        | _    -> aux (pos+1) line (col+1)
    in
    aux 0 1 1

  let describe input pos msg =
    let line, col = line_and_col_of_pos input pos in
    Printf.sprintf "line %i, column %i: %s" line col msg

  let fail input pos msg = raise (Compile_error (describe input pos msg))

  let rec skip input pos =
    match input.[pos] with
    | ' ' | '\b' | '\012'
    | '\t' | '\011'
    | '\n' | '\r' -> skip input (pos+1)
    | ';' ->
      begin match String.index_from_opt input pos '\n' with
        | Some pos -> skip input pos
        | None -> String.length input
      end
    | _ -> pos
    | exception (Invalid_argument _) -> pos

  let is_symbol_char = function
    | 'a'..'z'
    | 'A'..'Z'
    | '0'..'9'
    | '-' | '_' -> true
    | _ -> false

  (* TODO parse numbers, via notation *)
  let tokenize input pos =
    let pos = skip input pos in
    let char pos = if pos < String.length input then input.[pos] else '\000' in

    let symbol start =
      let stop = ref start in
      while is_symbol_char (char !stop) do incr stop done;
      String.sub input start (!stop - start), !stop
    in

    let prefixed token =
      match symbol (pos+1) with
      | _, next when Int.equal next (pos+1) -> fail input pos "expected a name"
      | sym, next -> token sym, next
    in

    match char pos with
    | 'a'..'z'
    | 'A'..'Z'
    | '_' ->
      let sym, next = symbol pos in
      let token =
        match sym with
        | "let" -> Let
        | "in" -> In
        | "fun" -> Fun
        | "using" -> Using
        | "abstract" -> Abstract
        | "the" -> The
        | "rec" -> Rec
        | "recur" -> Recur
        | "do" -> Do
        | "or" -> Or
        | "_" -> Underscore
        | _ -> Ident sym
      in
      token, next

    | '.' when char (pos+1) = '.' -> DotDot, pos+2
    | '.' when is_symbol_char (char (pos+1)) -> prefixed (fun sym -> Field sym)
    | '.' -> Dot, pos+1
    | '#' -> prefixed (fun sym -> Tag sym)
    | '\'' -> prefixed (fun sym -> TypeVar sym)
    | '@' -> prefixed (fun sym -> Dep sym)

    | '-' when char (pos+1) = '>' -> Arrow, pos+2
    | '<' when char (pos+1) = '-' -> LeftArrow, pos+2
    | ',' -> Comma, pos+1
    | '=' -> Equal, pos+1
    | ':' -> Colon, pos+1
    | '&' -> Ampersand, pos+1

    | '(' -> LeftParen, pos+1
    | ')' -> RightParen, pos+1
    | '{' -> LeftCurly, pos+1
    | '}' -> RightCurly, pos+1
    | '[' -> LeftSquare, pos+1
    | ']' -> RightSquare, pos+1

    | '\000' when pos >= String.length input -> EOF, pos
    | c -> fail input pos (Printf.sprintf "unexpected character '%c'" c)

  type scope = {
    vars : (string * Type.t) list;
    types : (string * Type.t) list; (* names bound by `abstract` *)
    deps : Type.t                      (* dependencies of the innermost function *)
  }

  (* For `the T e`, e has type T with each abstract type written in T replaced
     by its underlying type, so T can be a whole signature *)
  let repr ty =
    Type.copy (function
        | Rigid r -> Some r.view
        | _ -> None)
      ty

  let variant_type tag payload =
    Type.Variant {
      fields = [tag, Record {fields = payload; rest = None}];
      rest = Some (Type.fresh ())
    }

  type result = {
    expr : Expr.typed;
    errors : (int * string) list; (* positions and messages, in order *)
    syntax : Syntax.t
  }

  (* Parses and typechecks in a single pass. Syntax errors stop parsing, but
     type errors are marked in the tree, which goes on being checked. *)
  let parse input =
    let tokenize = tokenize input in
    let fail pos = fail input (skip input pos) in

    let unexpected pos =
      let token, _ = tokenize pos in
      fail pos (Printf.sprintf "unexpected %s" (string_of_token token))
    in

    let expect token pos =
      match tokenize pos with
      | found, next when found = token -> next
      | _ -> unexpected pos
    in

    (* Each node adopts the nodes recorded since its start as its children *)
    let nodes = ref [] in
    let node form info start stop =
      let rec adopt children = function
        | (n : Syntax.t) :: rest when n.start >= start -> adopt (n :: children) rest
        | rest -> children, rest
      in
      let children, rest = adopt [] !nodes in
      nodes := {Syntax.form; info; start; stop; children} :: rest
    in
    let enode form start (e, next) = node form (Expr e) start next; e, next in
    let pnode form start (p, next) = node form (Pat p) start next; p, next in

    let errors = ref [] in
    let error pos msg =
      let pos = skip input pos in
      errors := (pos, msg) :: !errors;
      pos
    in
    (* A node is checked before its parent adopts it, so it's found among the
       unadopted nodes, to update *)
    let retag old info =
      let same (n : Syntax.t) =
        match n.info, old with
        | Expr a, Syntax.Expr b -> a == b
        | Pat a, Pat b -> a == b
        | _ -> false
      in
      nodes := List.map (fun (n : Syntax.t) -> if same n then {n with info} else n) !nodes
    in
    let mark pos msg (e : Expr.typed) =
      let marked = {e with expr = Error {pos = error pos msg; msg; e}} in
      retag (Expr e) (Expr marked);
      marked
    in
    let pmark pos msg (p : Pat.typed) =
      let marked = {p with pat = Error {pos = error pos msg; msg; p}} in
      retag (Pat p) (Pat marked);
      marked
    in
    let check pos problem e = Option.fold ~none:e ~some:(fun msg -> mark pos msg e) problem in
    let pcheck pos problem p = Option.fold ~none:p ~some:(fun msg -> pmark pos msg p) problem in

    (* Checks return the problem they find, if any *)
    let unify a b =
      match Type.unify a b with
      | () -> None
      | exception Compile_error msg -> Some msg
    in

    let exhaustive pats =
      match Pat.check pats with
      | Exhaustive -> None
      | Missing w -> Some ("patterns are not exhaustive, missing " ^ w)
      | Ambiguous ->
        Some "patterns are only exhaustive if more variant types are closed, \
              and which ones is ambiguous: add a catch-all clause or a type annotation"
    in

    (* Comma separated, up to [closer]: positional items, `.name <sep> item`,
       `.name(params) <sep> body` given [func], `..rest`, and `using item`.
       Named items are nodes, and given a [row] form, positional ones are too. *)
    let sequence ?func ?rest ?using ?(row = "item") ~sep item closer pos =
      let rec aux i fields tail deps pos =
        let i, fields, tail, deps, pos =
          match tokenize pos, rest, using with
          | (Field name, next), _, _ ->
            if List.mem_assoc name fields then
              fail pos "duplicate field";
            let start = skip input pos in
            let x, pos =
              match tokenize next, func with
              | (LeftParen, _), Some func -> func next
              | _ -> item (expect sep next)
            in
            node row Other start pos;
            i, (name, x) :: fields, tail, deps, pos
          | (DotDot, next), Some rest, _ ->
            let x, pos = rest next in
            i, fields, Some x, deps, pos
          | (Using, next), _, Some using ->
            let x, pos = using next in
            i, fields, tail, Some x, pos
          | _ ->
            let start = skip input pos in
            let x, pos = item pos in
            if row <> "item" then node row Other start pos;
            i+1, (label i, x) :: fields, tail, deps, pos
        in
        match tokenize pos with
        | Comma, next -> aux i fields tail deps next
        | token, next when token = closer -> List.rev fields, tail, deps, next
        | _ -> unexpected pos
      in
      match tokenize pos with
      | token, next when token = closer -> [], None, None, next
      | _ -> aux 0 [] None None pos
    in

    let payload item pos =
      match tokenize pos with
      | LeftParen, next ->
        let fields, _, _, pos = sequence ~sep:Equal item RightParen next in
        fields, pos
      | _ -> [], pos
    in

    (* [vars] holds the annotation's type variables. [binders] holds the
       enclosing `rec` binders, as None where an occurrence would not be
       strictly positive. *)
    let rec type_expr scope vars binders pos =
      let ty = type_expr scope vars binders in
      match tokenize pos with
      | TypeVar name, next ->
        begin match List.assoc_opt name binders with
          | Some (Some ty) -> ty, next
          | Some None ->
            ignore (error pos "recursive type is not strictly positive");
            Type.fresh (), next
          | None ->
            match List.assoc_opt name !vars with
            | Some ty -> ty, next
            | None ->
              let ty = Type.fresh () in
              vars := (name, ty) :: !vars;
              ty, next
        end

      | Ident name, next ->
        begin match List.assoc_opt name scope.types with
          | Some ty -> ty, next
          | None ->
            ignore (error pos ("unknown type " ^ name));
            Type.fresh (), next
        end

      | LeftParen, next ->
        let inner, pos = ty next in
        inner, expect RightParen pos

      | LeftCurly, next ->
        let fields, rest, _, pos = sequence ~rest:ty ~sep:Colon ty RightCurly next in
        Type.Record {fields; rest}, pos

      | LeftSquare, next ->
        let tag pos =
          match tokenize pos with
          | Tag name, next ->
            let fields, rest, _, pos =
              match tokenize next with
              | LeftParen, next -> sequence ~rest:ty ~sep:Colon ty RightParen next
              | _ -> [], None, None, next
            in
            (name, Type.Record {fields; rest}), pos
          | _ -> unexpected pos
        in
        let tags, rest, _, pos = sequence ~rest:ty ~sep:Colon tag RightSquare next in
        Type.Variant {fields = List.map snd tags; rest}, pos

      | Fun, next ->
        let input = type_expr scope vars (List.map (fun (name, _) -> name, None) binders) in
        let fields, rest, deps, pos =
          sequence ~rest:input ~using:input ~sep:Colon input RightParen (expect LeftParen next)
        in
        let output, pos = ty (expect Arrow pos) in
        let deps = Option.value deps ~default:Type.empty in
        Type.Function {inputs = Record {fields; rest}; deps; exists = []; output}, pos

      | Rec, next ->
        begin match tokenize next with
          | TypeVar name, next ->
            let r = {Type.body = Type.empty; index = Type.fresh ()} in
            let body, pos =
              type_expr scope vars ((name, Some (Type.Recurs r)) :: binders) (expect Dot next)
            in
            r.body <- body;
            Type.Recurs r, pos
          | _ -> unexpected next
        end

      | _ -> unexpected pos
    in

    (* An annotation with an error is ignored *)
    let annotation scope pos =
      let before = !errors and start = skip input pos in
      let ty, pos = type_expr scope (ref []) [] pos in
      node "type" Other start pos;
      (if !errors == before then ty else Type.fresh ()), pos
    in

    let rec pattern scope binds pos =
      let left = ref [] and start = skip input pos in
      let p, pos = atomic_pattern scope left pos in
      let p, pos =
        match tokenize pos with
        | Or, next ->
          let right = ref [] in
          let q, next_pos = pattern scope right next in
          let same = List.compare_lengths !left !right = 0
                     && List.for_all (fun (name, _) -> List.mem_assoc name !right) !left in
          let p = pcheck next (unify p.Pat.ty q.Pat.ty) {Pat.pat = Or (p, q); ty = p.ty} in
          pnode "or" start @@
          if not same then begin
            (* All of them, so the body doesn't find them unbound *)
            left := !left @ List.filter (fun (name, _) -> not (List.mem_assoc name !left)) !right;
            pmark pos "both sides of `or` must bind the same variables" p, next_pos
          end
          else
            let unify_var (name, ty) = unify ty (List.assoc name !right) in
            pcheck next (List.find_map unify_var !left) p, next_pos
        | _ -> p, pos
      in
      List.fold_left (fun p (name, ty) ->
          if List.mem_assoc name !binds then
            pmark pos (name ^ " is bound twice") p
          else begin
            binds := (name, ty) :: !binds;
            p
          end)
        p !left,
      pos

    and atomic_pattern scope binds pos =
      let types = List.map (fun (name, p) -> name, p.Pat.ty) in
      let start = skip input pos in
      match tokenize pos with
      | Ident name, next ->
        let p = {Pat.pat = Var name; ty = Type.fresh ()} in
        pnode "var" start @@
        if List.mem_assoc name !binds then
          pmark pos (name ^ " is bound twice") p, next
        else begin
          binds := (name, p.ty) :: !binds;
          p, next
        end

      | Underscore, next ->
        pnode "wildcard" start ({Pat.pat = Wildcard; ty = Type.fresh ()}, next)

      | LeftParen, next ->
        let p, pos = pattern scope binds next in
        pnode "parens" start (p, expect RightParen pos)

      | LeftCurly, next ->
        let fields, rest, _, pos =
          sequence ~rest:(fun pos -> (), pos) ~row:"entry" ~sep:Equal (pattern scope binds)
            RightCurly next
        in
        let ty = Type.Record {fields = types fields; rest = Option.map Type.fresh rest} in
        pnode "record" start ({Pat.pat = Record fields; ty}, pos)

      | Tag tag, next ->
        let fields, pos = payload (pattern scope binds) next in
        let ty = variant_type tag (types fields) in
        pnode "variant" start ({Pat.pat = Variant (tag, fields); ty}, pos)

      | Ampersand, next ->
        let p, pos = atomic_pattern scope binds next in
        let ty = Type.Recurs {body = p.ty; index = Type.fresh ()} in
        pnode "roll" start ({Pat.pat = Roll p; ty}, pos)

      | The, next ->
        let ty, pos = annotation scope next in
        let p, next_pos = pattern scope binds pos in
        pnode "the" start ({(pcheck pos (unify (repr ty) p.ty) p) with ty}, next_pos)

      | _ -> unexpected pos
    in

    let rec expr scope pos =
      let start = skip input pos in
      let e, pos = atomic_expr scope pos in
      compound_expr scope start e pos

    (* The operand of `&` and `the T` takes field accesses and applications,
       but not a match, so `&e [clauses]` matches on `&e` *)
    and operand scope pos =
      let start = skip input pos in
      let e, pos = atomic_expr scope pos in
      compound_expr ~matches:false scope start e pos

    (* Field accesses, applications and matches on [left], which begins at
       [start] *)
    and compound_expr ?(matches = true) scope start left pos =
      let continue ?(matches = matches) form e next =
        node form (Expr e) start next;
        compound_expr ~matches scope start e next
      in
      match tokenize pos with
      | Field name, next ->
        let ty = Type.fresh () in
        let record = Type.Record {fields = [name, ty]; rest = Some (Type.fresh ())} in
        let problem = unify left.Expr.ty record in
        continue "field" (check pos problem {expr = Field (left, name); ty}) next

      | LeftParen, next ->
        let args, _, deps, next =
          sequence ~using:(expr scope) ~sep:Equal (expr scope) RightParen next
        in
        let ty = Type.fresh () in
        let found = Type.Function {
            inputs = Record {fields = List.map (fun (name, e) -> name, e.Expr.ty) args; rest = None};
            deps = (match deps with Some e -> e.Expr.ty | None -> Type.empty);
            exists = [];
            output = ty
          }
        in
        let problem = unify (Type.open_exists left.ty) found in
        continue "apply" (check pos problem {expr = Apply {f = left; args; deps}; ty}) next

      | LeftSquare, next when matches ->
        let ty = Type.fresh () in
        let clause pos =
          let binds = ref [] and start = skip input pos in
          let pat, pos = pattern scope binds pos in
          (* Before the body, so its variables' types are known there *)
          let pat = pcheck pos (unify left.ty pat.ty) pat in
          let pos = expect Arrow pos in
          let body, next = expr {scope with vars = !binds @ scope.vars} pos in
          let body = check pos (unify ty body.ty) body in
          node "clause" Other start next;
          (pat, body), next
        in
        let clauses, _, _, next = sequence ~sep:Equal clause RightSquare next in
        let clauses = List.map snd clauses in
        let problem = exhaustive (List.map fst clauses) in
        continue ~matches:true "match" (check pos problem {expr = Match (left, clauses); ty}) next

      | _ -> left, pos

    and atomic_expr scope pos =
      let start = skip input pos in
      match tokenize pos with
      | Ident name, next ->
        enode "var" start @@
        begin match List.assoc_opt name scope.vars with
          | Some ty -> {Expr.expr = Var name; ty = Type.instantiate ty}, next
          | None ->
            mark pos ("unbound variable " ^ name) {expr = Var name; ty = Type.fresh ()}, next
        end

      | Underscore, next -> enode "hole" start ({expr = Hole; ty = Type.fresh ()}, next)

      | Dep name, next ->
        let ty = Type.fresh () in
        let record = Type.Record {fields = [name, ty]; rest = Some (Type.fresh ())} in
        let problem = unify scope.deps record in
        enode "dep" start (check pos problem {expr = Dep name; ty}, next)

      | LeftParen, next ->
        let e, pos = expr scope next in
        enode "parens" start (e, expect RightParen pos)

      | Let, next ->
        incr Type.level;
        let binds = ref [] and binding = skip input next in
        let pat, pos = pattern scope binds next in
        let defn, next =
          match pat.pat, tokenize pos with
          | Var _, (LeftParen, _) -> lambda scope Equal pos (* `let f(x) = e` *)
          | _ -> expr scope (expect Equal pos)
        in
        let defn = check pos (unify pat.ty defn.ty) defn in
        let pat = pcheck pos (exhaustive [pat]) pat in
        node "binding" Other binding next;
        decr Type.level;
        List.iter (fun (_, ty) -> Type.generalize ty) !binds;
        let body, next = expr {scope with vars = !binds @ scope.vars} (expect In next) in
        enode "let" start ({expr = Let {pat; defn; body}; ty = body.ty}, next)

      | Fun, next -> enode "fun" start (lambda scope Arrow next)

      | LeftCurly, next ->
        let fields, rest, _, next =
          sequence ~func:(lambda scope Equal) ~rest:(expr scope) ~row:"entry" ~sep:Equal
            (expr scope) RightCurly next
        in
        let tail = Option.map (fun _ -> Type.fresh ()) rest in
        let rest = Option.map (fun r ->
            check pos (unify r.Expr.ty (Record {fields = []; rest = tail})) r)
            rest
        in
        let fields_ty = List.map (fun (name, e) -> name, e.Expr.ty) fields in
        let ty = Type.Record {fields = fields_ty; rest = tail} in
        enode "record" start ({expr = Record {fields; rest}; ty}, next)

      | Tag tag, next ->
        let fields, next = payload (expr scope) next in
        let ty = variant_type tag (List.map (fun (name, e) -> name, e.Expr.ty) fields) in
        enode "variant" start ({expr = Variant (tag, fields); ty}, next)

      | Ampersand, next ->
        let e, next = operand scope next in
        enode "roll" start ({expr = Roll e; ty = Recurs {body = e.ty; index = Type.empty}}, next)

      | Recur, next -> enode "recur" start (recur scope (expect LeftParen next))

      | Abstract, next ->
        begin match tokenize next with
          | Ident name, next ->
            let ty = Type.rigid name (Type.fresh ()) in
            enode "abstract" start
              (expr {scope with types = (name, ty) :: scope.types} (expect In next))
          | _ -> unexpected next
        end

      | The, next ->
        let ty, pos = annotation scope next in
        let e, next = operand scope pos in
        enode "the" start ({(check pos (unify (repr ty) e.ty) e) with ty}, next)

      | _ -> unexpected pos

    (* `(params) <arrow> body`: [arrow] is `->` after `fun`, and `=` in the
       sugar `let f(x) = e` and `{.f(x) = e}` *)
    and lambda scope arrow pos =
      incr Type.fun_level;
      let binds = ref [] in
      let params, _, deps, pos =
        sequence ~using:(pattern scope binds) ~sep:Equal (pattern scope binds) RightParen
          (expect LeftParen pos)
      in
      let inputs =
        Type.Record {fields = List.map (fun (name, p) -> name, p.Pat.ty) params; rest = None}
      in
      let problem = exhaustive [{pat = Record params; ty = inputs}] in
      let deps_ty = Type.fresh () in
      let deps = Option.map (fun p ->
          let p = pcheck pos (unify deps_ty p.Pat.ty) p in
          pcheck pos (exhaustive [p]) p)
          deps
      in
      let body, next =
        expr {scope with vars = !binds @ scope.vars; deps = deps_ty} (expect arrow pos)
      in
      decr Type.fun_level;
      let exists = Type.existentials body.ty in
      let escapes =
        if Type.mentions exists inputs || Type.mentions exists deps_ty then
          Some "abstract type escapes through a parameter"
        else None
      in
      let ty = Type.Function {inputs; deps = deps_ty; exists; output = body.ty} in
      let e = {Expr.expr = Function {params; deps; body}; ty} in
      check pos (if problem = None then escapes else problem) e, next

    (* `recur (p <- e, acc = init, ...) do body`. Within body, `continue`
       continues with a subterm of e and new accumulators. p matches e's top
       layer, whose subterms get a fresh index, so only they can be continued
       with. The index can't escape into the accumulators or anything outside,
       which is checked like an existential's level. On the way out it becomes
       e's own index, since the subterms are still e's subterms, and `forget`
       does the same for a layer within body. *)
    and recur scope pos =
      let level = !Type.fun_level + 1 in
      let binds = ref [] in
      Type.fun_level := level;
      let root, pos = pattern scope binds pos in
      let root = pcheck pos (exhaustive [root]) root in
      decr Type.fun_level;
      let input, pos = expr scope (expect LeftArrow pos) in
      let rec accs pos =
        match tokenize pos with
        | Comma, next ->
          let p, pos = pattern scope binds next in
          let init, pos = expr scope (expect Equal pos) in
          let init = check pos (unify p.Pat.ty init.Expr.ty) init in
          let p = pcheck pos (exhaustive [p]) p in
          let rest, pos = accs pos in
          (p, init) :: rest, pos
        | RightParen, next -> [], next
        | _ -> unexpected pos
      in
      let accs, pos = accs pos in
      Type.fun_level := level;
      let k = Type.abstract "recur" Type.empty in
      let r = {Type.body = root.ty; index = Rigid {abs = k; view = Type.empty}} in
      let labelled xs = List.mapi (fun i x -> label i, x) xs in
      let params = labelled ({Pat.pat = Roll root; ty = Recurs r} :: List.map fst accs) in
      let output = Type.fresh () in
      let ty = Type.Function {
          inputs = Record {fields = List.map (fun (l, p) -> l, p.Pat.ty) params; rest = None};
          deps = Type.empty;
          exists = [];
          output
        }
      in
      (* Any index, so both subterms and the re-rolled layer can be forgotten *)
      let forget = Type.Function {
          inputs = Record {
              fields = [label 0, Recurs {body = root.ty; index = Type.fresh ~level:Type.generic ()}];
              rest = None
            };
          deps = Type.empty;
          exists = [];
          output = input.ty
        }
      in
      let start = !Type.counter in
      let continue_name = "continue" and forget_name = "forget" in
      let vars = !binds @ [continue_name, ty; forget_name, forget] @ scope.vars in
      let body, next = expr {scope with vars} (expect Do pos) in
      let body = check pos (unify output body.ty) body in
      decr Type.fun_level;
      (* Each iteration introduces its own abstract types, so they can't be
         passed between iterations, through the result or the accumulators *)
      let carried = output :: List.map (fun (p, _) -> p.Pat.ty) accs in
      let problem =
        if k.fun_level < level then Some "recursion index escapes"
        else
          List.find_opt (fun abs -> abs.Type.id > start) (List.concat_map Type.abstracts carried)
          |> Option.map (fun abs -> "abstract type " ^ abs.Type.name ^ " escapes the recursion")
      in
      let outer = Type.fresh () in
      let copy = Type.copy (function Rigid r when r.abs == k -> Some outer | _ -> None) in
      let input_ty = copy (Recurs r) and ty = copy output in
      let problem = if problem = None then unify input.ty input_ty else problem in
      let args = labelled (input :: List.map snd accs) in
      let recur = Expr.Recur {continue = continue_name; forget = forget_name; params; args; body} in
      check pos problem {expr = recur; ty}, next
    in

    Type.level := 0;
    Type.fun_level := 0;
    let expr, pos = expr {vars = []; types = []; deps = Type.empty} 0 in
    match tokenize pos with
    | EOF, _ ->
      (* The implicit top-level `let` *)
      decr Type.level;
      Type.generalize expr.ty;
      let errors = List.sort (fun (a, _) (b, _) -> Int.compare a b) (List.rev !errors) in
      let stop = String.length input in
      {expr; errors; syntax = {form = "program"; info = Other; start = 0; stop; children = !nodes}}
    | _ -> unexpected pos
end

module Runtime : sig
  type value
  val show : value -> string
  val eval : (string * value) list -> Expr.typed -> value
  (* The environment within `let p = e in ...`, unless binding it depends on
     a hole *)
  val define : (string * value) list -> Pat.typed -> Expr.typed -> (string * value) list option
end = struct
  type value =
      Record of (string * value) list
    | Variant of string * (string * value) list
    | Closure of {
        params : (string * Pat.typed) list;
        deps : Pat.typed option;
        body : Expr.typed;
        env : (string * value) list
      }
    | Native of ((string * value) list -> value)
    | Roll of value
    | Hole

  (* Raised when evaluation needs to know more about a hole than that it is
     one, making the expression being evaluated a hole too *)
  exception Indeterminate

  (* The current function's dependencies are bound under a name that no
     variable can have *)
  let deps_name = "@"

  let show value =
    let buf = Buffer.create 32 in
    let rec aux = function
      | Record fields ->
        Buffer.add_char buf '{';
        show_fields buf ~sep:"=" aux fields;
        Buffer.add_char buf '}'
      | Variant (tag, []) -> Printf.bprintf buf "#%s" tag
      | Variant (tag, fields) ->
        Printf.bprintf buf "#%s(" tag;
        show_fields buf ~sep:"=" aux fields;
        Buffer.add_char buf ')'
      | Closure _ | Native _ -> Buffer.add_string buf "<function>"
      | Roll value -> Buffer.add_char buf '&'; aux value
      | Hole -> Buffer.add_char buf '_'
    in
    aux value;
    Buffer.contents buf

  (* Programs are well typed and patterns exhaustive, except where marked as
     erroneous, which evaluates to a hole. So evaluation can't go wrong: the
     failures below are assertions. *)
  let fields_of = function
    | Record fields -> fields
    | Hole -> raise Indeterminate
    | _ -> assert false

  let rec bind env (p : Pat.typed) value =
    match p.pat, value with
    | Pat.Var name, _ -> Some ((name, value) :: env)
    | Pat.Wildcard, _ -> Some env
    | Pat.Record ps, Record values -> bind_fields env ps values
    | Pat.Variant (tag, ps), Variant (tag', values) when String.equal tag tag' ->
      bind_fields env ps values
    | Pat.Roll p, Roll value -> bind env p value
    | Pat.Or (p, q), _ ->
      begin match bind env p value with
        | None -> bind env q value
        | found -> found
      end
    | Pat.Record ps, Hole -> bind_fields env ps (List.map (fun (name, _) -> name, Hole) ps)
    | Pat.Roll p, Hole -> bind env p Hole
    | Pat.Variant _, Hole | Pat.Error _, _ -> raise Indeterminate
    | _ -> None

  and bind_fields env ps values =
    List.fold_left (fun env (name, p) ->
        Option.bind env (fun env -> bind env p (List.assoc name values)))
      (Some env) ps

  let rec eval env node =
    try step env node with Indeterminate -> Hole

  and step env (node : Expr.typed) =
    match node.expr with
    | Expr.Record {fields; rest} ->
      let fields = List.map (fun (name, e) -> name, eval env e) fields in
      let rest =
        match rest with
        | Some e ->
          List.filter (fun (name, _) -> not (List.mem_assoc name fields)) (fields_of (eval env e))
        | None -> []
      in
      Record (fields @ rest)

    | Expr.Field (e, name) -> List.assoc name (fields_of (eval env e))

    | Expr.Variant (tag, fields) ->
      Variant (tag, List.map (fun (name, e) -> name, eval env e) fields)

    | Expr.Match (e, clauses) ->
      let value = eval env e in
      let env, body =
        Option.get (List.find_map (fun (p, body) ->
            Option.map (fun env -> env, body) (bind env p value))
            clauses)
      in
      eval env body

    | Expr.Function {params; deps; body} -> Closure {params; deps; body; env}

    | Expr.Apply {f; args; deps} ->
      let f = eval env f in
      let args = List.map (fun (name, e) -> name, eval env e) args in
      begin match f with
        | Native f -> f args
        | Hole -> raise Indeterminate
        | Closure c ->
          let deps = match deps with Some e -> eval env e | None -> Record [] in
          let inner = Option.get (bind_fields ((deps_name, deps) :: c.env) c.params args) in
          let inner = match c.deps with Some p -> Option.get (bind inner p deps) | None -> inner in
          eval inner c.body
        | _ -> assert false
      end

    | Expr.Dep name -> List.assoc name (fields_of (List.assoc deps_name env))

    | Expr.Var name -> List.assoc name env

    | Expr.Let {pat; defn; body} -> eval (Option.get (bind env pat (eval env defn))) body

    | Expr.Roll e -> Roll (eval env e)

    (* Unlike a closure, keeps the enclosing function's dependencies *)
    | Expr.Recur {continue; forget; params; args; body} ->
      let identity = Native (fun args -> List.assoc (label 0) args) in
      let rec loop args =
        let env = (continue, Native loop) :: (forget, identity) :: env in
        eval (Option.get (bind_fields env params args)) body
      in
      loop (List.map (fun (name, e) -> name, eval env e) args)

    | Expr.Hole | Expr.Error _ -> Hole

  let define env pat defn =
    try bind env pat (eval env defn) with Indeterminate -> None
end

let run code =
  match Parsing.parse code with
  | exception Compile_error msg -> Error msg
  | {expr = e; errors = []; _} ->
    Ok (Printf.sprintf "the %s %s" (Type.show e.ty) (Runtime.show (Runtime.eval [] e)))
  | {errors; _} ->
    Error (String.concat "\n" (List.map (fun (pos, msg) -> Parsing.describe code pos msg) errors))
