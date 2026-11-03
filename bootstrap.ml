module Symbol : sig
  (* Strings backed by a WeakSet *)
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val of_string : string -> t
  val to_string : t -> string
end = struct
  type t = string

  let equal a b = a == b
  let compare = String.compare
  let hash = String.hash

  let of_string =
    let module Table = Weak.Make(String) in
    let table = Table.create 64 in

    fun str ->
      match Table.find_opt table str with
      | Some s -> s
      | None ->
        Table.add table str;
        str

  let to_string s = s
end

exception Compile_error of string

(* Fields, environments and rows are association lists keyed by symbols, so
   List.assq and friends apply. Positional fields are labelled 1, 2, ... *)
let label i = Symbol.of_string (string_of_int (i + 1))

(* Bound within the body of a `recur` *)
let continue_name = Symbol.of_string "continue"
let forget_name = Symbol.of_string "forget"

let show_fields buf ~sep show fields =
  List.iteri (fun i (name, x) ->
      if i <> 0 then
        Buffer.add_string buf ", ";
      if not (Symbol.equal name (label i)) then
        Printf.bprintf buf ".%s %s " (Symbol.to_string name) sep;
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

  and row = {fields : (Symbol.t * t) list; rest : t option}

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
    name : Symbol.t;
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
        List.iter (fun (name, a) -> Option.iter (go a) (List.assq_opt name r2.fields)) r1.fields
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
        Buffer.add_string buf (Symbol.to_string abs.name);
        begin match args abs view with
          | [] -> ()
          | args ->
            Buffer.add_char buf '(';
            List.iteri (fun i ty -> if i <> 0 then Buffer.add_string buf ", "; go ty) args;
            Buffer.add_char buf ')'
        end

      | Record r ->
        Buffer.add_char buf '{';
        row (show_fields buf ~sep:":" go) r;
        Buffer.add_char buf '}'

      | Variant r ->
        Buffer.add_char buf '[';
        row (List.iteri (fun i (tag, payload) ->
            if i <> 0 then
              Buffer.add_string buf ", ";
            Printf.bprintf buf "#%s" (Symbol.to_string tag);
            match prune payload with
            | Record {fields = []; rest = None} -> ()
            | Record r ->
              Buffer.add_char buf '(';
              row (show_fields buf ~sep:":" go) r;
              Buffer.add_char buf ')'
            | ty -> go ty))
          r;
        Buffer.add_char buf ']'

      | Function fn ->
        Buffer.add_string buf "fun(";
        let start = Buffer.length buf in
        begin match prune fn.inputs with
          | Record r -> row (show_fields buf ~sep:":" go) r
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
            (String.concat ", " (List.map (fun abs -> Symbol.to_string abs.name) fn.exists));
        go fn.output

      | Recurs r ->
        match List.assq_opt r !recs with
        | Some name -> Buffer.add_string buf name
        | None ->
          let cyclic =
            try iter (function Recurs r' when r' == r -> raise Exit | _ -> ()) r.body; false
            with Exit -> true
          in
          let name = if cyclic then next () else "_" in
          recs := (r, name) :: !recs;
          Buffer.add_string buf "rec ";
          begin match prune r.index with
            | Rigid {abs; _} -> Printf.bprintf buf "[%s] " (Symbol.to_string abs.name)
            | _ -> ()
          end;
          Printf.bprintf buf "%s. " name;
          go r.body

    and row show_items {fields; rest} =
      let rec flatten acc rest =
        match Option.map prune rest with
        | Some (Record r | Variant r) -> flatten (acc @ r.fields) r.rest
        | rest -> acc, rest
      in
      let fields, rest = flatten fields rest in
      let fields =
        List.fold_left (fun acc (name, ty) ->
            if List.mem_assq name acc then acc else acc @ [name, ty])
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
     variables and abstract types *)
  let copy leaf ty =
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
    go ty

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
    let find_generic = function
      | Var {contents = Unbound u} when u.level = generic -> raise Exit
      | _ -> ()
    in
    match iter find_generic ty with
    | () -> ty
    | exception Exit ->
      copy (function
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

  let mentions abss ty =
    try iter (function Rigid {abs; _} when List.memq abs abss -> raise Exit | _ -> ()) ty; false
    with Exit -> true

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
            u.level <- min u.level lv;
            u.fun_level <- min u.fun_level fl
          | Rigid {abs; _} -> abs.fun_level <- min abs.fun_level fl
          | _ -> ())
        ty
    | Link _ -> ()

  let unify a b =
    let seen = ref [] and renamed = ref [] and binders = ref [] in
    let rec go a b =
      match prune a, prune b with
      | Var v1, Var v2 when v1 == v2 -> ()
      | Var v, ty | ty, Var v -> occurs v ty; v := Link ty
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
          when Symbol.equal r1.abs.name r2.abs.name && not (rename r1.abs r2.abs) ->
          ", a different abstract type"
        | _ -> ""
      in
      raise (Compile_error (Printf.sprintf "cannot unify %s with %s%s" (show a) (show b) why))

    (* Collects a row's fields through bound row variables; duplicate fields
       (from record extension) must agree *)
    and flatten variant {fields; rest} =
      let add acc (name, ty) =
        match List.assq_opt name acc with
        | Some ty' -> go ty ty'; acc
        | None -> acc @ [name, ty]
      in
      let rec aux acc rest =
        match Option.map prune rest with
        | Some (Record r) when not variant -> aux (List.fold_left add acc r.fields) r.rest
        | Some (Variant r) when variant -> aux (List.fold_left add acc r.fields) r.rest
        | Some (Var _) | None as rest -> acc, rest
        | Some ty -> raise (Compile_error ("expected a row, found " ^ show ty))
      in
      aux (List.fold_left add [] fields) rest

    and rows variant r1 r2 =
      let wrap row = if variant then Variant row else Record row in
      let f1, rest1 = flatten variant r1 in
      let f2, rest2 = flatten variant r2 in
      List.iter (fun (name, ty) -> Option.iter (go ty) (List.assq_opt name f2)) f1;
      let extra fs others = List.filter (fun (name, _) -> not (List.mem_assq name others)) fs in
      let extra1 = extra f1 f2 and extra2 = extra f2 f1 in
      let missing = function
        | [] -> ()
        | (name, _) :: _ ->
          raise (Compile_error (Printf.sprintf "no %s%s" (if variant then "tag #" else "field .")
                                  (Symbol.to_string name)))
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
    go a b

  (* A variant row's tags with their payloads, and its tail variable if it's
     open, which identifies the row *)
  let rec tags ty =
    match prune ty with
    | Variant {fields; rest = Some rest} ->
      let more, tail = tags rest in
      fields @ more, tail
    | Variant {fields; rest = None} -> fields, None
    | Var v -> [], Some v
    | _ -> [], None

  (* Closes a variant row by its tail, so it can't take more tags *)
  let close tail = unify (Var tail) (Variant {fields = []; rest = None})
end

module Pat = struct
  type t =
      Var of Symbol.t
    | Wildcard
    | Record of (Symbol.t * typed) list
    | Variant of Symbol.t * (Symbol.t * typed) list
    | Roll of typed
    | Or of typed * typed

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
          acc @ List.filter (fun name -> not (List.memq name acc)) (List.map fst fields))
        [] fieldss
    in
    let show_fields names ws =
      String.concat ", " (List.mapi (fun i (name, w) ->
          if Symbol.equal name (label i) then w else "." ^ Symbol.to_string name ^ " = " ^ w)
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
        let is_wild p = match p.pat with Var _ | Wildcard -> true | _ -> false in
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
          List.map (fun name -> Option.value (List.assq_opt name fields) ~default:wild) names
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
                | {pat = Variant (tag', fields); _} when tag' == tag -> Some fields
                | _ -> None)
                heads
            in
            let names = names fieldss in
            specialize (List.length names)
              (function
                | {pat = Variant (tag', fields); _} when tag' == tag -> Some (fields_of names fields)
                | _ -> None)
              (fun ws ->
                 let tag = "#" ^ Symbol.to_string tag in
                 match ws, Type.prune payload with
                 | [], Record {fields = []; rest = None} -> tag
                 | [], _ -> tag ^ "(..)"
                 | ws, _ -> tag ^ "(" ^ show_fields names ws ^ ")")
          in
          let complete = not open_ && List.for_all (fun (tag, _) -> List.memq tag seen) tags in
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
      Record of {fields : (Symbol.t * typed) list; rest : typed option}
    | Field of typed * Symbol.t

    | Variant of Symbol.t * (Symbol.t * typed) list
    | Match of typed * (Pat.typed * typed) list

    | Function of {
        params : (Symbol.t * Pat.typed) list;
        deps : Pat.typed option;
        body : typed
      }
    | Apply of {
        f : typed;
        args : (Symbol.t * typed) list;
        deps : typed option
      }
    | Dep of Symbol.t

    | Var of Symbol.t
    | Let of {
        pat : Pat.typed;
        defn : typed;
        body : typed
      }

    | Roll of typed
    (* `recur (p <- e, ...) do body`: [params] start with `&p` *)
    | Recur of {
        params : (Symbol.t * Pat.typed) list;
        args : (Symbol.t * typed) list;
        body : typed
      }

  and typed = {
    expr : t;
    ty : Type.t
  }
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
    | Ident of Symbol.t
    | Field of Symbol.t
    | Tag of Symbol.t
    | TypeVar of Symbol.t
    | Dep of Symbol.t
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
    | Ident sym -> Symbol.to_string sym
    | Field sym -> "." ^ Symbol.to_string sym
    | Tag sym -> "#" ^ Symbol.to_string sym
    | TypeVar sym -> "'" ^ Symbol.to_string sym
    | Dep sym -> "@" ^ Symbol.to_string sym
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

  let fail input pos msg =
    let line, col = line_and_col_of_pos input pos in
    raise (Compile_error (Printf.sprintf "line %i, column %i: %s" line col msg))

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
      Symbol.of_string (String.sub input start (!stop - start)), !stop
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
        match Symbol.to_string sym with
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
    vars : (Symbol.t * Type.t) list;
    types : (Symbol.t * Type.t) list; (* names bound by `abstract` *)
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

  (* Parses and typechecks in a single pass *)
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

    let unify pos a b =
      try Type.unify a b with Compile_error msg -> fail pos msg
    in

    let exhaustive pos pats =
      match Pat.check pats with
      | Exhaustive -> ()
      | Missing w -> fail pos ("patterns are not exhaustive, missing " ^ w)
      | Ambiguous ->
        fail pos "patterns are only exhaustive if more variant types are closed, \
                  and which ones is ambiguous: add a catch-all clause or a type annotation"
    in

    (* Comma separated, up to [closer]: positional items, `.name <sep> item`,
       `.name(params) <sep> body` given [func], `..rest`, and `using item` *)
    let sequence ?func ?rest ?using ~sep item closer pos =
      let rec aux i fields tail deps pos =
        let i, fields, tail, deps, pos =
          match tokenize pos, rest, using with
          | (Field name, next), _, _ ->
            if List.mem_assq name fields then
              fail pos "duplicate field";
            let x, pos =
              match tokenize next, func with
              | (LeftParen, _), Some func -> func next
              | _ -> item (expect sep next)
            in
            i, (name, x) :: fields, tail, deps, pos
          | (DotDot, next), Some rest, _ ->
            let x, pos = rest next in
            i, fields, Some x, deps, pos
          | (Using, next), _, Some using ->
            let x, pos = using next in
            i, fields, tail, Some x, pos
          | _ ->
            let x, pos = item pos in
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
        begin match List.assq_opt name binders with
          | Some (Some ty) -> ty, next
          | Some None -> fail pos "recursive type is not strictly positive"
          | None ->
            match List.assq_opt name !vars with
            | Some ty -> ty, next
            | None ->
              let ty = Type.fresh () in
              vars := (name, ty) :: !vars;
              ty, next
        end

      | Ident name, next ->
        begin match List.assq_opt name scope.types with
          | Some ty -> ty, next
          | None -> fail pos ("unknown type " ^ Symbol.to_string name)
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

    let annotation scope pos = type_expr scope (ref []) [] pos in

    let rec pattern scope binds pos =
      let left = ref [] in
      let p, pos = atomic_pattern scope left pos in
      let p, pos =
        match tokenize pos with
        | Or, next ->
          let right = ref [] in
          let q, next_pos = pattern scope right next in
          unify next p.Pat.ty q.Pat.ty;
          if List.compare_lengths !left !right <> 0 then
            fail pos "both sides of `or` must bind the same variables";
          List.iter (fun (name, ty) ->
              match List.assq_opt name !right with
              | Some ty' -> unify next ty ty'
              | None -> fail pos "both sides of `or` must bind the same variables")
            !left;
          {Pat.pat = Or (p, q); ty = p.ty}, next_pos
        | _ -> p, pos
      in
      List.iter (fun (name, ty) ->
          if List.mem_assq name !binds then
            fail pos (Symbol.to_string name ^ " is bound twice");
          binds := (name, ty) :: !binds)
        !left;
      p, pos

    and atomic_pattern scope binds pos =
      let types = List.map (fun (name, p) -> name, p.Pat.ty) in
      match tokenize pos with
      | Ident name, next ->
        if List.mem_assq name !binds then
          fail pos (Symbol.to_string name ^ " is bound twice");
        let ty = Type.fresh () in
        binds := (name, ty) :: !binds;
        {Pat.pat = Var name; ty}, next

      | Underscore, next ->
        {Pat.pat = Wildcard; ty = Type.fresh ()}, next

      | LeftParen, next ->
        let p, pos = pattern scope binds next in
        p, expect RightParen pos

      | LeftCurly, next ->
        let fields, rest, _, pos =
          sequence ~rest:(fun pos -> (), pos) ~sep:Equal (pattern scope binds) RightCurly next
        in
        let ty = Type.Record {fields = types fields; rest = Option.map Type.fresh rest} in
        {Pat.pat = Record fields; ty}, pos

      | Tag tag, next ->
        let fields, pos = payload (pattern scope binds) next in
        {Pat.pat = Variant (tag, fields); ty = variant_type tag (types fields)}, pos

      | Ampersand, next ->
        let p, pos = atomic_pattern scope binds next in
        {Pat.pat = Roll p; ty = Recurs {body = p.ty; index = Type.fresh ()}}, pos

      | The, next ->
        let ty, pos = annotation scope next in
        let p, next_pos = pattern scope binds pos in
        unify pos (repr ty) p.ty;
        {p with ty}, next_pos

      | _ -> unexpected pos
    in

    let rec expr scope pos =
      let e, pos = atomic_expr scope pos in
      compound_expr scope e pos

    (* The operand of `&` and `the T` takes field accesses and applications,
       but not a match, so `&e [clauses]` matches on `&e` *)
    and operand scope pos =
      let e, pos = atomic_expr scope pos in
      compound_expr ~matches:false scope e pos

    and compound_expr ?(matches = true) scope left pos =
      match tokenize pos with
      | Field name, next ->
        let ty = Type.fresh () in
        unify pos left.Expr.ty (Record {fields = [name, ty]; rest = Some (Type.fresh ())});
        compound_expr ~matches scope {expr = Field (left, name); ty} next

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
        unify pos (Type.open_exists left.ty) found;
        compound_expr ~matches scope {expr = Apply {f = left; args; deps}; ty} next

      | LeftSquare, next when matches ->
        let ty = Type.fresh () in
        let clause pos =
          let binds = ref [] in
          let pat, pos = pattern scope binds pos in
          (* Before the body, so its variables' types are known there *)
          unify pos left.ty pat.ty;
          let pos = expect Arrow pos in
          let body, next = expr {scope with vars = !binds @ scope.vars} pos in
          unify pos ty body.ty;
          (pat, body), next
        in
        let clauses, _, _, next = sequence ~sep:Equal clause RightSquare next in
        let clauses = List.map snd clauses in
        exhaustive pos (List.map fst clauses);
        compound_expr scope {expr = Match (left, clauses); ty} next

      | _ -> left, pos

    and atomic_expr scope pos =
      match tokenize pos with
      | Ident name, next ->
        begin match List.assq_opt name scope.vars with
          | Some ty -> {Expr.expr = Var name; ty = Type.instantiate ty}, next
          | None -> fail pos ("unbound variable " ^ Symbol.to_string name)
        end

      | Dep name, next ->
        let ty = Type.fresh () in
        unify pos scope.deps (Record {fields = [name, ty]; rest = Some (Type.fresh ())});
        {expr = Dep name; ty}, next

      | LeftParen, next ->
        let e, pos = expr scope next in
        e, expect RightParen pos

      | Let, next ->
        incr Type.level;
        let binds = ref [] in
        let pat, pos = pattern scope binds next in
        let defn, next =
          match pat.pat, tokenize pos with
          | Var _, (LeftParen, _) -> lambda scope Equal pos (* `let f(x) = e` *)
          | _ -> expr scope (expect Equal pos)
        in
        unify pos pat.ty defn.ty;
        exhaustive pos [pat];
        decr Type.level;
        List.iter (fun (_, ty) -> Type.generalize ty) !binds;
        let body, next = expr {scope with vars = !binds @ scope.vars} (expect In next) in
        {expr = Let {pat; defn; body}; ty = body.ty}, next

      | Fun, next -> lambda scope Arrow next

      | LeftCurly, next ->
        let fields, rest, _, next =
          sequence ~func:(lambda scope Equal) ~rest:(expr scope) ~sep:Equal (expr scope)
            RightCurly next
        in
        let tail = Option.map (fun r ->
            let tail = Type.fresh () in
            unify pos r.Expr.ty (Record {fields = []; rest = Some tail});
            tail)
            rest
        in
        let fields_ty = List.map (fun (name, e) -> name, e.Expr.ty) fields in
        {expr = Record {fields; rest}; ty = Record {fields = fields_ty; rest = tail}}, next

      | Tag tag, next ->
        let fields, next = payload (expr scope) next in
        let ty = variant_type tag (List.map (fun (name, e) -> name, e.Expr.ty) fields) in
        {expr = Variant (tag, fields); ty}, next

      | Ampersand, next ->
        let e, next = operand scope next in
        {expr = Roll e; ty = Recurs {body = e.ty; index = Type.empty}}, next

      | Recur, next -> recur scope (expect LeftParen next)

      | Abstract, next ->
        begin match tokenize next with
          | Ident name, next ->
            let ty = Type.rigid name (Type.fresh ()) in
            expr {scope with types = (name, ty) :: scope.types} (expect In next)
          | _ -> unexpected next
        end

      | The, next ->
        let ty, pos = annotation scope next in
        let e, next = operand scope pos in
        unify pos (repr ty) e.ty;
        {e with ty}, next

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
      exhaustive pos [{pat = Record params; ty = inputs}];
      let deps_ty = Type.fresh () in
      Option.iter (fun p -> unify pos deps_ty p.Pat.ty; exhaustive pos [p]) deps;
      let body, next =
        expr {scope with vars = !binds @ scope.vars; deps = deps_ty} (expect arrow pos)
      in
      decr Type.fun_level;
      let exists = Type.existentials body.ty in
      if Type.mentions exists inputs || Type.mentions exists deps_ty then
        fail pos "abstract type escapes through a parameter";
      let ty = Type.Function {inputs; deps = deps_ty; exists; output = body.ty} in
      {Expr.expr = Function {params; deps; body}; ty}, next

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
      exhaustive pos [root];
      decr Type.fun_level;
      let input, pos = expr scope (expect LeftArrow pos) in
      let rec accs pos =
        match tokenize pos with
        | Comma, next ->
          let p, pos = pattern scope binds next in
          let init, pos = expr scope (expect Equal pos) in
          unify pos p.Pat.ty init.Expr.ty;
          exhaustive pos [p];
          let rest, pos = accs pos in
          (p, init) :: rest, pos
        | RightParen, next -> [], next
        | _ -> unexpected pos
      in
      let accs, pos = accs pos in
      Type.fun_level := level;
      let k = Type.abstract (Symbol.of_string "recur") Type.empty in
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
      let vars = !binds @ [continue_name, ty; forget_name, forget] @ scope.vars in
      let body, next = expr {scope with vars} (expect Do pos) in
      unify pos output body.ty;
      decr Type.fun_level;
      if k.fun_level < level then
        fail pos "recursion index escapes";
      (* Each iteration introduces its own abstract types, so they can't be
         passed between iterations, through the result or the accumulators *)
      let carried = output :: List.map (fun (p, _) -> p.Pat.ty) accs in
      begin match List.find_opt (fun abs -> abs.Type.id > start)
                    (List.concat_map Type.abstracts carried) with
      | Some abs ->
        fail pos ("abstract type " ^ Symbol.to_string abs.name ^ " escapes the recursion")
      | None -> ()
      end;
      let outer = Type.fresh () in
      let input_ty, ty =
        match Type.copy (function Rigid r when r.abs == k -> Some outer | _ -> None)
            (Record {fields = [label 0, Recurs r; label 1, output]; rest = None}) with
        | Record {fields = [_, input_ty; _, ty]; _} -> input_ty, ty
        | _ -> assert false
      in
      unify pos input.ty input_ty;
      let args = labelled (input :: List.map snd accs) in
      {expr = Recur {params; args; body}; ty}, next
    in

    Type.level := 0;
    Type.fun_level := 0;
    let e, pos = expr {vars = []; types = []; deps = Type.empty} 0 in
    match tokenize pos with
    | EOF, _ ->
      (* The implicit top-level `let` *)
      decr Type.level;
      Type.generalize e.ty;
      e
    | _ -> unexpected pos
end

module Runtime : sig
  type value
  val show : value -> string
  val eval : (Symbol.t * value) list -> Expr.typed -> value
end = struct
  type value =
      Record of (Symbol.t * value) list
    | Variant of Symbol.t * (Symbol.t * value) list
    | Closure of {
        params : (Symbol.t * Pat.typed) list;
        deps : Pat.typed option;
        body : Expr.typed;
        env : (Symbol.t * value) list
      }
    | Native of ((Symbol.t * value) list -> value)
    | Roll of value

  (* The current function's dependencies are bound under a name that no
     variable can have *)
  let deps_name = Symbol.of_string "@"

  let show value =
    let buf = Buffer.create 32 in
    let rec aux = function
      | Record fields ->
        Buffer.add_char buf '{';
        show_fields buf ~sep:"=" aux fields;
        Buffer.add_char buf '}'
      | Variant (tag, []) -> Printf.bprintf buf "#%s" (Symbol.to_string tag)
      | Variant (tag, fields) ->
        Printf.bprintf buf "#%s(" (Symbol.to_string tag);
        show_fields buf ~sep:"=" aux fields;
        Buffer.add_char buf ')'
      | Closure _ | Native _ -> Buffer.add_string buf "<function>"
      | Roll value -> Buffer.add_char buf '&'; aux value
    in
    aux value;
    Buffer.contents buf

  let fields_of = function
    | Record fields -> fields
    | _ -> failwith "expected a record"

  let rec bind env (p : Pat.typed) value =
    match p.pat, value with
    | Pat.Var name, _ -> Some ((name, value) :: env)
    | Pat.Wildcard, _ -> Some env
    | Pat.Record ps, Record values -> bind_fields env ps values
    | Pat.Variant (tag, ps), Variant (tag', values) when Symbol.equal tag tag' ->
      bind_fields env ps values
    | Pat.Roll p, Roll value -> bind env p value
    | Pat.Or (p, q), _ ->
      begin match bind env p value with
        | None -> bind env q value
        | found -> found
      end
    | _ -> None

  and bind_fields env ps values =
    List.fold_left (fun env (name, p) ->
        Option.bind env (fun env -> bind env p (List.assq name values)))
      (Some env) ps

  let must = function
    | Some env -> env
    | None -> failwith "pattern did not match"

  let rec eval env (node : Expr.typed) =
    match node.expr with
    | Expr.Record {fields; rest} ->
      let fields = List.map (fun (name, e) -> name, eval env e) fields in
      let rest =
        match rest with
        | Some e ->
          List.filter (fun (name, _) -> not (List.mem_assq name fields)) (fields_of (eval env e))
        | None -> []
      in
      Record (fields @ rest)

    | Expr.Field (e, name) -> List.assq name (fields_of (eval env e))

    | Expr.Variant (tag, fields) ->
      Variant (tag, List.map (fun (name, e) -> name, eval env e) fields)

    | Expr.Match (e, clauses) ->
      let value = eval env e in
      begin match List.find_map (fun (p, body) ->
          Option.map (fun env -> env, body) (bind env p value))
          clauses
        with
        | Some (env, body) -> eval env body
        | None -> failwith "no clause matched"
      end

    | Expr.Function {params; deps; body} -> Closure {params; deps; body; env}

    | Expr.Apply {f; args; deps} ->
      let f = eval env f in
      let args = List.map (fun (name, e) -> name, eval env e) args in
      begin match f with
        | Native f -> f args
        | Closure c ->
          let deps = match deps with Some e -> eval env e | None -> Record [] in
          let inner = must (bind_fields ((deps_name, deps) :: c.env) c.params args) in
          let inner = match c.deps with Some p -> must (bind inner p deps) | None -> inner in
          eval inner c.body
        | _ -> failwith "expected a function"
      end

    | Expr.Dep name -> List.assq name (fields_of (List.assq deps_name env))

    | Expr.Var name -> List.assq name env

    | Expr.Let {pat; defn; body} -> eval (must (bind env pat (eval env defn))) body

    | Expr.Roll e -> Roll (eval env e)

    (* Unlike a closure, keeps the enclosing function's dependencies *)
    | Expr.Recur {params; args; body} ->
      let forget = Native (fun args -> List.assq (label 0) args) in
      let rec continue args =
        let env = (continue_name, Native continue) :: (forget_name, forget) :: env in
        eval (must (bind_fields env params args)) body
      in
      continue (List.map (fun (name, e) -> name, eval env e) args)
end

let run code =
  match Parsing.parse code with
  | exception Compile_error msg -> Error msg
  | e ->
    match Runtime.eval [] e with
    | exception Failure msg -> Error ("runtime error: " ^ msg)
    | value -> Ok (Printf.sprintf "the %s %s" (Type.show e.ty) (Runtime.show value))

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
    match run code with
    | Ok out -> print_endline out; 0
    | Error msg -> print_endline msg; 1

let () =
  if not !Sys.interactive then
    exit (main ())
