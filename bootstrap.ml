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

(* Type annotations, as written *)
module Annot = struct
  type t =
      Var of string (* 'a *)
    | Name of string (* bound by `abstract` *)
    | Record of row
    | Variant of row (* each tag's payload is a Record *)
    | Function of {inputs : row; deps : t option; output : t}
    | Rec of string * t

  and row = {fields : (string * t) list; rest : t option}
end

(* The shapes of patterns, whose subpatterns are ['p] *)
module Pat = struct
  type 'p t =
      Var of string
    | Wildcard
    | Record of {fields : (string * 'p) list; rest : bool (* `..` *)}
    | Variant of string * (string * 'p) list
    | Roll of 'p
    | Or of 'p * 'p
    | The of Annot.t * 'p
end

(* The shapes of expressions, whose subexpressions are ['e] and patterns
   ['p] *)
module Expr = struct
  type ('e, 'p) t =
      Record of {fields : (string * 'e) list; rest : 'e option}
    | Field of 'e * string

    | Variant of string * (string * 'e) list
    | Match of 'e * ('p * 'e) list

    | Function of {
        params : (string * 'p) list;
        deps : 'p option;
        body : 'e
      }
    | Apply of {
        f : 'e;
        args : (string * 'e) list;
        deps : 'e option
      }
    | Dep of string

    | Var of string
    | Let of {
        pat : 'p;
        defn : 'e;
        body : 'e
      }

    | Roll of 'e
    (* `recur (p <- e, ...) do body`: [params] start with `&p`, and body sees
       [continue] and [forget] *)
    | Recur of {
        continue : string;
        forget : string;
        params : (string * 'p) list;
        args : (string * 'e) list;
        body : 'e
      }

    | The of Annot.t * 'e
    | Abstract of string * 'e (* `abstract t in e` *)

    | Hole (* `_` *)
end

(* Types, and checking programs: the tree of a program, which checking sets
   the types of *)
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
    (* The type of a node with a type error, which unifies with anything, so
       one error doesn't lead to others *)
    | Error of error

  and row = {fields : (string * t) list; rest : t option}

  and error =
    (* [found] where [expected] was needed, and [why], where within them they
       differ *)
    | Mismatch of {expected : t; found : t; why : string}
    | Unbound_variable of string
    | Bound_twice of string
    | Or_binds (* the sides of an `or` bind different variables *)
    | Missing of string (* a value no pattern matches, written as a pattern *)
    | Ambiguous (* patterns only exhaustive if unknown variant types are closed *)
    | Escapes_parameter (* an existential type, through a function's parameter *)
    | Escapes_recursion of string (* an abstract type, from one iteration to the next *)
    | Index_escapes (* a `recur`'s index, out of it *)
    | Unknown_type of string
    | Not_positive of string (* a recursive type's variable, where it can't be *)

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
   * Inference walks a program once it's read:
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
      | Error _ -> Buffer.add_string buf "<error>"

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

  (* Whether a node's type is an error, so the node has one *)
  let is_error = function Error _ -> true | _ -> false

  let describe = function
    | Mismatch {why; _} -> why
    | Unbound_variable name -> "unbound variable " ^ name
    | Bound_twice name -> name ^ " is bound twice"
    | Or_binds -> "both sides of `or` must bind the same variables"
    | Missing w -> "patterns are not exhaustive, missing " ^ w
    | Ambiguous ->
      "patterns are only exhaustive if more variant types are closed, \
       and which ones is ambiguous: add a catch-all clause or a type annotation"
    | Escapes_parameter -> "abstract type escapes through a parameter"
    | Escapes_recursion name -> "abstract type " ^ name ^ " escapes the recursion"
    | Index_escapes -> "recursion index escapes"
    | Unknown_type name -> "unknown type " ^ name
    | Not_positive _ -> "recursive type is not strictly positive"

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
      | Error _, _ | _, Error _ -> ()
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

  (* Programs, and once they're checked, their types. [ty] is set by
     checking, and is an error if the node has one, which makes it evaluate
     to a hole. [loc] is where the node is, in whatever the program was read
     from. *)
  type 'loc expr = {
    expr : ('loc expr, 'loc pat) Expr.t;
    mutable ty : t;
    loc : 'loc
  }

  and 'loc pat = {
    pat : 'loc pat Pat.t;
    mutable ty : t;
    loc : 'loc
  }

  (* The problem, if patterns aren't exhaustive, following Maranget's
     usefulness algorithm. Closes the open variant rows they must close to
     be: those a match can't be exhaustive without, even with every other row
     closed. Closing a row only removes values, so if closing just those isn't
     enough, there's no single least choice of rows to close, and it's
     ambiguous. *)
  let exhaustive (pats : _ pat list) =
    (* A wildcard in place of a pattern *)
    let wild (p : _ pat) = {p with pat = Wildcard; ty = empty} in
    let rec row_type ty =
      match prune ty with
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
        | {pat = The (_, p); ty; _} :: rest when not (is_error ty) -> expand (p :: rest)
        | row -> [row]
      in
      match List.concat_map expand rows with
      | [] -> Some (List.init n (fun _ -> "_"))
      | _ when n = 0 -> None
      | rows ->
        (* An erroneous pattern doesn't count as missing anything *)
        let is_wild (p : _ pat) =
          match p.ty, p.pat with Error _, _ | _, (Var _ | Wildcard) -> true | _ -> false
        in
        let heads = List.map List.hd rows in
        (* Rows whose head is the constructor [sub] picks out, with its k
           subpatterns in place of the head *)
        let specialize k sub rebuild =
          let rows = List.filter_map (function
              | p :: rest when is_wild p -> Some (List.init k (fun _ -> wild p) @ rest)
              | p :: rest -> Option.map (fun ps -> ps @ rest) (sub p)
              | [] -> None)
              rows
          in
          Option.map (fun w -> rebuild (List.take k w) :: List.drop k w)
            (go closed (k + n - 1) rows)
        in
        let fields_of p names fields =
          List.map (fun name -> Option.value (List.assoc_opt name fields) ~default:(wild p)) names
        in
        match List.find_opt (fun p -> not (is_wild p)) heads with
        | None -> Option.map (fun w -> "_" :: w) (go closed (n - 1) (List.map List.tl rows))

        | Some {pat = Roll _; _} ->
          specialize 1 (function {pat = Roll p; _} -> Some [p] | _ -> None)
            (fun ws -> "&" ^ List.hd ws)

        | Some {pat = Record _; _} ->
          let names = names (List.filter_map (function
              | {pat = Record {fields; _}; _} -> Some fields
              | _ -> None)
              heads)
          in
          specialize (List.length names)
            (function {pat = Record {fields; _}; _} as p -> Some (fields_of p names fields) | _ -> None)
            (fun ws -> "{" ^ show_fields names ws ^ "}")

        | Some p ->
          let tags, tail = tags (row_type p.ty) in
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
                | {pat = Variant (tag', fields); _} as p when tag' = tag -> Some (fields_of p names fields)
                | _ -> None)
              (fun ws ->
                 let tag = "#" ^ tag in
                 match ws, prune payload with
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
    | Some w -> Some (Missing w)
    | None ->
      let forced = List.filter (fun v -> missing (fun v' -> v' != v) <> None) !found in
      match missing (fun v -> List.memq v forced) with
      | None -> List.iter close forced; None
      | Some _ -> Some Ambiguous

  (* Checking a program sets each node's type. A node with a type error has
     the error as its type, and the error is reported to the front end the
     program was read from, at the node's location. *)

  type 'loc scope = {
    vars : (string * t) list;
    types : (string * t) list; (* names bound by `abstract` *)
    deps : t; (* dependencies of the innermost function *)
    report : 'loc -> error -> unit
  }

  let mark scope (e : _ expr) problem =
    scope.report e.loc problem;
    e.ty <- Error problem

  let pmark scope (p : _ pat) problem =
    scope.report p.loc problem;
    p.ty <- Error problem

  let mark_if scope e problem = Option.iter (mark scope e) problem
  let pmark_if scope p problem = Option.iter (pmark scope p) problem

  (* Checks return the problem they find, if any. Here, that [found] doesn't
     unify with [expected]. *)
  let expect expected found =
    match unify expected found with
    | () -> None
    | exception Compile_error why -> Some (Mismatch {expected; found; why})

  (* For `the T e`, e has type T with each abstract type written in T replaced
     by its underlying type, so T can be a whole signature *)
  let repr ty =
    copy (function
        | Rigid r -> Some r.view
        | _ -> None)
      ty

  let tagged tag payload =
    Variant {
      fields = [tag, Record {fields = payload; rest = None}];
      rest = Some (fresh ())
    }

  let types fields = List.map (fun (name, (x : _ expr)) -> name, x.ty) fields
  let ptypes fields = List.map (fun (name, (p : _ pat)) -> name, p.ty) fields

  (* A type annotation's type, with the problems in it reported at [loc].
     Each type variable stands for one type throughout. Within `rec 'a.
     body`, 'a is the recursive type, except in a function type's
     parameters, where it wouldn't be strictly positive. The parts with
     problems are errors, which unify with anything. *)
  let annotation scope loc ann =
    let vars = ref [] and problems = ref [] in
    let problem p =
      problems := p :: !problems;
      Error p
    in
    let rec go binders : Annot.t -> t = function
      | Var name ->
        begin match List.assoc_opt name binders with
          | Some (Some ty) -> ty
          | Some None -> problem (Not_positive name)
          | None ->
            match List.assoc_opt name !vars with
            | Some ty -> ty
            | None ->
              let ty = fresh () in
              vars := (name, ty) :: !vars;
              ty
        end
      | Name name ->
        begin match List.assoc_opt name scope.types with
          | Some ty -> ty
          | None -> problem (Unknown_type name)
        end
      | Record r -> Record (row binders r)
      | Variant r -> Variant (row binders r)
      | Function {inputs; deps; output} ->
        let params = List.map (fun (name, _) -> name, None) binders in
        let inputs = row params inputs in
        let deps = Option.fold deps ~none:empty ~some:(go params) in
        Function {inputs = Record inputs; deps; exists = []; output = go binders output}
      | Rec (name, body) ->
        let r = {body = empty; index = fresh ()} in
        r.body <- go ((name, Some (Recurs r)) :: binders) body;
        Recurs r
    and row binders ({fields; rest} : Annot.row) =
      let fields = List.map (fun (name, ty) -> name, go binders ty) fields in
      {fields; rest = Option.map (go binders) rest}
    in
    let ty = go [] ann in
    List.iter (scope.report loc) (List.rev !problems);
    ty

  (* The names patterns bind, with their types *)
  type binds = (string * t) list ref

  let bind scope (binds : binds) p name ty =
    if List.mem_assoc name !binds then pmark scope p (Bound_twice name)
    else binds := (name, ty) :: !binds

  (* Checks a pattern, adding the names it binds to [binds] *)
  let rec pattern scope binds (p : _ pat) =
    match p.pat with
    | Var name ->
      p.ty <- fresh ();
      bind scope binds p name p.ty

    | Wildcard -> p.ty <- fresh ()

    (* With `..`, it matches records with more fields *)
    | Record {fields; rest} ->
      List.iter (fun (_, q) -> pattern scope binds q) fields;
      let rest = if rest then Some (fresh ()) else None in
      p.ty <- Record {fields = ptypes fields; rest}

    | Variant (tag, fields) ->
      List.iter (fun (_, q) -> pattern scope binds q) fields;
      p.ty <- tagged tag (ptypes fields)

    | Roll q ->
      pattern scope binds q;
      p.ty <- Recurs {body = q.ty; index = fresh ()}

    (* An erroneous pattern keeps its error *)
    | The (ann, q) ->
      let ty = annotation scope p.loc ann in
      pattern scope binds q;
      p.ty <- ty;
      if not (is_error q.ty) then pmark_if scope p (expect (repr ty) q.ty)

    (* Both sides must bind the same names. All of them are bound either way,
       so none are found unbound. *)
    | Or (q, r) ->
      let left = ref [] and right = ref [] in
      pattern scope left q;
      pattern scope right r;
      p.ty <- q.ty;
      pmark_if scope p (expect q.ty r.ty);
      let same = List.compare_lengths !left !right = 0
                 && List.for_all (fun (name, _) -> List.mem_assoc name !right) !left in
      if not same then pmark scope p Or_binds
      else pmark_if scope p (List.find_map (fun (name, ty) -> expect ty (List.assoc name !right)) !left);
      let extra = List.filter (fun (name, _) -> not (List.mem_assoc name !left)) !right in
      List.iter (fun (name, ty) -> bind scope binds p name ty) (!left @ extra)

  let rec infer scope (e : _ expr) =
    match e.expr with
    | Var name ->
      begin match List.assoc_opt name scope.vars with
        | Some ty -> e.ty <- instantiate ty
        | None -> mark scope e (Unbound_variable name)
      end

    | Hole -> e.ty <- fresh ()

    | Dep name ->
      e.ty <- fresh ();
      let record = Record {fields = [name, e.ty]; rest = Some (fresh ())} in
      mark_if scope e (expect record scope.deps)

    | Field (left, name) ->
      infer scope left;
      e.ty <- fresh ();
      let record = Record {fields = [name, e.ty]; rest = Some (fresh ())} in
      mark_if scope e (expect record left.ty)

    | Apply {f; args; deps} ->
      infer scope f;
      List.iter (fun (_, x) -> infer scope x) args;
      Option.iter (infer scope) deps;
      e.ty <- fresh ();
      let expected = Function {
          inputs = Record {fields = types args; rest = None};
          deps = (match deps with Some (x : _ expr) -> x.ty | None -> empty);
          exists = [];
          output = e.ty
        }
      in
      mark_if scope e (expect expected (open_exists f.ty))

    (* Each clause's pattern is checked before its body, so its variables'
       types are known there *)
    | Match (left, clauses) ->
      infer scope left;
      e.ty <- fresh ();
      List.iter (fun ((pat : _ pat), body) ->
          let binds = ref [] in
          pattern scope binds pat;
          pmark_if scope pat (expect left.ty pat.ty);
          infer {scope with vars = !binds @ scope.vars} body;
          mark_if scope body (expect e.ty body.ty))
        clauses;
      mark_if scope e (exhaustive (List.map fst clauses))

    | Record {fields; rest} ->
      List.iter (fun (_, x) -> infer scope x) fields;
      Option.iter (infer scope) rest;
      let tail = Option.map (fun _ -> fresh ()) rest in
      Option.iter (fun (r : _ expr) ->
          mark_if scope r (expect (Record {fields = []; rest = tail}) r.ty))
        rest;
      e.ty <- Record {fields = types fields; rest = tail}

    | Variant (tag, fields) ->
      List.iter (fun (_, x) -> infer scope x) fields;
      e.ty <- tagged tag (types fields)

    | Roll x ->
      infer scope x;
      e.ty <- Recurs {body = x.ty; index = empty}

    (* p and e are checked a level deeper, so that p's variables are
       generalized for body *)
    | Let {pat; defn; body} ->
      incr level;
      let binds = ref [] in
      pattern scope binds pat;
      infer scope defn;
      mark_if scope defn (expect pat.ty defn.ty);
      pmark_if scope pat (exhaustive [pat]);
      decr level;
      List.iter (fun (_, ty) -> generalize ty) !binds;
      infer {scope with vars = !binds @ scope.vars} body;
      (* An error in the body is the body's, not the let's *)
      e.ty <- if is_error body.ty then fresh () else body.ty

    (* body sees t as a new abstract type *)
    | Abstract (name, body) ->
      infer {scope with types = (name, rigid name (fresh ())) :: scope.types} body;
      e.ty <- if is_error body.ty then fresh () else body.ty

    (* An erroneous expression keeps its error, since it can't be evaluated *)
    | The (ann, x) ->
      let ty = annotation scope e.loc ann in
      infer scope x;
      e.ty <- ty;
      if not (is_error x.ty) then mark_if scope e (expect (repr ty) x.ty)

    | Function {params; deps; body} ->
      incr fun_level;
      let binds = ref [] in
      List.iter (fun (_, p) -> pattern scope binds p) params;
      Option.iter (pattern scope binds) deps;
      let inputs = Record {fields = ptypes params; rest = None} in
      let problem = exhaustive [{pat = Record {fields = params; rest = false}; ty = inputs; loc = e.loc}] in
      let deps_ty = fresh () in
      Option.iter (fun (p : _ pat) ->
          pmark_if scope p (expect deps_ty p.ty);
          pmark_if scope p (exhaustive [p]))
        deps;
      infer {scope with vars = !binds @ scope.vars; deps = deps_ty} body;
      decr fun_level;
      let exists = existentials body.ty in
      let escapes =
        if mentions exists inputs || mentions exists deps_ty then Some Escapes_parameter
        else None
      in
      e.ty <- Function {inputs; deps = deps_ty; exists; output = body.ty};
      mark_if scope e (if problem = None then escapes else problem)

    (* `recur (p <- e, acc = init, ...) do body`, where [params] are `&p` and
       the accumulators, and [args] e and their initial values. Within body,
       [continue] continues with a subterm of e and new accumulators. p
       matches e's top layer, whose subterms get a fresh index, so only they
       can be continued with. The index can't escape into the accumulators or
       anything outside, which is checked like an existential's level. On the
       way out it becomes e's own index, since the subterms are still e's
       subterms, and [forget] does the same for a layer within body.

       p is checked a function level deeper, so its variables can't be
       unified with anything outside. *)
    | Recur {continue; forget; params; args; body} ->
      let level = !fun_level + 1 in
      fun_level := level;
      let binds = ref [] in
      let rolled, root, accs, input, inits =
        match params, args with
        | (_, ({pat = Roll root; _} as rolled)) :: accs, (_, input) :: inits ->
          rolled, root, List.map snd accs, input, List.map snd inits
        | _ -> invalid_arg "recur"
      in
      pattern scope binds root;
      pmark_if scope root (exhaustive [root]);
      decr fun_level;
      infer scope input;
      List.iter2 (fun (p : _ pat) (init : _ expr) ->
          pattern scope binds p;
          infer scope init;
          mark_if scope init (expect p.ty init.ty);
          pmark_if scope p (exhaustive [p]))
        accs inits;
      fun_level := level;
      let index = abstract "recur" empty in
      let layer = {body = root.ty; index = Rigid {abs = index; view = empty}} in
      rolled.ty <- Recurs layer;
      let output = fresh () in
      let continue_ty = Function {
          inputs = Record {fields = ptypes params; rest = None};
          deps = empty;
          exists = [];
          output
        }
      in
      (* Any index, so both subterms and the re-rolled layer can be forgotten *)
      let forget_ty = Function {
          inputs = Record {
              fields = [label 0, Recurs {body = root.ty; index = fresh ~level:generic ()}];
              rest = None
            };
          deps = empty;
          exists = [];
          output = input.ty
        }
      in
      let counter = !counter in (* abstract types made after this are made within *)
      let vars = !binds @ [continue, continue_ty; forget, forget_ty] @ scope.vars in
      infer {scope with vars} body;
      mark_if scope body (expect output body.ty);
      decr fun_level;
      (* Each iteration introduces its own abstract types, so they can't be
         passed between iterations, through the result or the accumulators *)
      let carried = output :: List.map (fun (p : _ pat) -> p.ty) accs in
      let problem =
        if index.fun_level < level then Some Index_escapes
        else
          List.find_opt (fun abs -> abs.id > counter) (List.concat_map abstracts carried)
          |> Option.map (fun abs -> Escapes_recursion abs.name)
      in
      let outer = fresh () in
      let copy = copy (function Rigid x when x.abs == index -> Some outer | _ -> None) in
      let input_ty = copy (Recurs layer) and ty = copy output in
      let problem = if problem = None then expect input_ty input.ty else problem in
      e.ty <- ty;
      mark_if scope e problem

  (* A program, with [vars] in scope, is checked like a let's definition *)
  let program ?(vars = []) report (e : _ expr) =
    level := 0;
    fun_level := 0;
    infer {vars; types = []; deps = empty; report} e;
    decr level;
    generalize e.ty
end

(* The concrete syntax tree, for the editor: each construct's [form], like
   "let" or "match", with the node it was read as, its span in the
   source, and the constructs within it. Keywords and punctuation are in the
   text between the children's spans. The sugar `let f(x) = e` and
   `.f(x) = e` has no node for the function, so its parameters and body are
   the binding's or the field's.

   Some nodes are rows, which the editor can rearrange: a record's entries,
   a match's clauses, and a let's binding, `p = e` without the body. *)
module Syntax = struct
  (* Where a node was in the source, from its start to its stop *)
  type span = int * int

  type t = {
    form : string;
    info : info;
    start : int;
    stop : int;
    children : t list
  }

  and info = Expr of span Type.expr | Pat of span Type.pat | Other
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

  (* A syntax error at [pos], where [expected] would have fit there: a token,
     or `_` for a missing expression or pattern *)
  exception Syntax_error of {pos : int; msg : string; expected : string option}

  let fail ?expected pos msg = raise (Syntax_error {pos; msg; expected})

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
      | _, next when Int.equal next (pos+1) -> fail pos "expected a name"
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
    | c -> fail pos (Printf.sprintf "unexpected character '%c'" c)

  type result = {
    expr : Syntax.span Type.expr;
    errors : (Syntax.span * Type.error) list; (* in order *)
    syntax : Syntax.t
  }

  (* Parses a program, then checks it with [vars] in scope. A syntax error
     stops parsing with Syntax_error, but type errors are marked in the tree,
     which goes on being checked. *)
  let parse ?vars input =
    let tokenize = tokenize input in
    let fail ?expected pos = fail ?expected (skip input pos) in

    let unexpected ?expected pos =
      let token, _ = tokenize pos in
      fail ?expected pos (Printf.sprintf "unexpected %s" (string_of_token token))
    in

    let expect token pos =
      match tokenize pos with
      | found, next when found = token -> next
      | _ -> unexpected ~expected:(string_of_token token) pos
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
    (* Nodes of the program, whose types are set when it's checked *)
    let make expr start stop = {Type.expr; ty = Type.empty; loc = (start, stop)} in
    (* Records a node, and goes on after it *)
    let enode form expr start stop =
      let e = make expr start stop in
      node form (Expr e) start stop;
      e, stop
    in
    let pnode form pat start stop =
      let p = {Type.pat; ty = Type.empty; loc = (start, stop)} in
      node form (Pat p) start stop;
      p, stop
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
        | _ -> unexpected ~expected:(string_of_token closer) pos
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

    let rec type_expr pos =
      match tokenize pos with
      | TypeVar name, next -> Annot.Var name, next
      | Ident name, next -> Annot.Name name, next

      | LeftParen, next ->
        let inner, pos = type_expr next in
        inner, expect RightParen pos

      | LeftCurly, next ->
        let fields, rest, _, pos = sequence ~rest:type_expr ~sep:Colon type_expr RightCurly next in
        Annot.Record {fields; rest}, pos

      | LeftSquare, next ->
        let tag pos =
          match tokenize pos with
          | Tag name, next ->
            let fields, rest, _, pos =
              match tokenize next with
              | LeftParen, next -> sequence ~rest:type_expr ~sep:Colon type_expr RightParen next
              | _ -> [], None, None, next
            in
            (name, Annot.Record {fields; rest}), pos
          | _ -> unexpected pos
        in
        let tags, rest, _, pos = sequence ~rest:type_expr ~sep:Colon tag RightSquare next in
        Annot.Variant {fields = List.map snd tags; rest}, pos

      | Fun, next ->
        let fields, rest, deps, pos =
          sequence ~rest:type_expr ~using:type_expr ~sep:Colon type_expr RightParen
            (expect LeftParen next)
        in
        let output, pos = type_expr (expect Arrow pos) in
        Annot.Function {inputs = {fields; rest}; deps; output}, pos

      | Rec, next ->
        begin match tokenize next with
          | TypeVar name, next ->
            let body, pos = type_expr (expect Dot next) in
            Annot.Rec (name, body), pos
          | _ -> unexpected next
        end

      | _ -> unexpected pos
    in

    let annotation pos =
      let start = skip input pos in
      let ty, pos = type_expr pos in
      node "type" Other start pos;
      ty, pos
    in

    let rec pattern pos =
      let start = skip input pos in
      let p, pos = atomic_pattern pos in
      match tokenize pos with
      | Or, next ->
        let q, next = pattern next in
        pnode "or" (Pat.Or (p, q)) start next
      | _ -> p, pos

    and atomic_pattern pos =
      let start = skip input pos in
      match tokenize pos with
      | Ident name, next -> pnode "var" (Pat.Var name) start next
      | Underscore, next -> pnode "wildcard" Pat.Wildcard start next

      | LeftParen, next ->
        let p, pos = pattern next in
        let next = expect RightParen pos in
        node "parens" (Pat p) start next;
        p, next

      | LeftCurly, next ->
        let fields, rest, _, pos =
          sequence ~rest:(fun pos -> (), pos) ~row:"entry" ~sep:Equal pattern RightCurly next
        in
        pnode "record" (Pat.Record {fields; rest = rest <> None}) start pos

      | Tag tag, next ->
        let fields, pos = payload pattern next in
        pnode "variant" (Pat.Variant (tag, fields)) start pos

      | Ampersand, next ->
        let p, pos = atomic_pattern next in
        pnode "roll" (Pat.Roll p) start pos

      | The, next ->
        let ty, pos = annotation next in
        let p, next = pattern pos in
        pnode "the" (Pat.The (ty, p)) start next

      | _ -> unexpected ~expected:"_" pos
    in

    let rec expr pos =
      let start = skip input pos in
      let e, pos = atomic_expr pos in
      compound_expr start e pos

    (* The operand of `&` and `the T` takes field accesses and applications,
       but not a match, so `&e [clauses]` matches on `&e` *)
    and operand pos =
      let start = skip input pos in
      let e, pos = atomic_expr pos in
      compound_expr ~matches:false start e pos

    (* Field accesses, applications and matches on [left], which begins at
       [start] *)
    and compound_expr ?(matches = true) start left pos =
      let continue ?(matches = matches) (e, next) = compound_expr ~matches start e next in
      match tokenize pos with
      | Field name, next -> continue (enode "field" (Expr.Field (left, name)) start next)

      | LeftParen, next ->
        let args, _, deps, next = sequence ~using:expr ~sep:Equal expr RightParen next in
        continue (enode "apply" (Expr.Apply {f = left; args; deps}) start next)

      | LeftSquare, next when matches ->
        let clause pos =
          let clause_start = skip input pos in
          let pat, pos = pattern pos in
          let body, next = expr (expect Arrow pos) in
          node "clause" Other clause_start next;
          (pat, body), next
        in
        let clauses, _, _, next = sequence ~sep:Equal clause RightSquare next in
        continue ~matches:true (enode "match" (Expr.Match (left, List.map snd clauses)) start next)

      | _ -> left, pos

    and atomic_expr pos =
      let start = skip input pos in
      match tokenize pos with
      | Ident name, next -> enode "var" (Expr.Var name) start next
      | Underscore, next -> enode "hole" Expr.Hole start next
      | Dep name, next -> enode "dep" (Expr.Dep name) start next

      | LeftParen, next ->
        let e, pos = expr next in
        let next = expect RightParen pos in
        node "parens" (Expr e) start next;
        e, next

      | Let, next ->
        let binding = skip input next in
        let pat, pos = pattern next in
        let defn, next =
          match pat.pat, tokenize pos with
          | Pat.Var _, (LeftParen, _) -> lambda Equal pos (* `let f(x) = e` *)
          | _ -> expr (expect Equal pos)
        in
        node "binding" Other binding next;
        let body, next = expr (expect In next) in
        enode "let" (Expr.Let {pat; defn; body}) start next

      | Fun, next ->
        let e, next = lambda ~start Arrow next in
        node "fun" (Expr e) start next;
        e, next

      | LeftCurly, next ->
        let fields, rest, _, next =
          sequence ~func:(lambda Equal) ~rest:expr ~row:"entry" ~sep:Equal expr RightCurly next
        in
        enode "record" (Expr.Record {fields; rest}) start next

      | Tag tag, next ->
        let fields, next = payload expr next in
        enode "variant" (Expr.Variant (tag, fields)) start next

      | Ampersand, next ->
        let e, next = operand next in
        enode "roll" (Expr.Roll e) start next

      | Recur, next -> recur start (expect LeftParen next)

      | Abstract, next ->
        begin match tokenize next with
          | Ident name, next ->
            let body, next = expr (expect In next) in
            enode "abstract" (Expr.Abstract (name, body)) start next
          | _ -> unexpected next
        end

      | The, next ->
        let ty, pos = annotation next in
        let e, next = operand pos in
        enode "the" (Expr.The (ty, e)) start next

      | _ -> unexpected ~expected:"_" pos

    (* `(params) <arrow> body`: [arrow] is `->` after `fun`, and `=` in the
       sugar `let f(x) = e` and `{.f(x) = e}`, where the function has no node
       of its own, but is located from its parameters *)
    and lambda ?start arrow pos =
      let params_start = skip input pos in
      let params, _, deps, pos =
        sequence ~using:pattern ~sep:Equal pattern RightParen (expect LeftParen pos)
      in
      let body, next = expr (expect arrow pos) in
      let start = Option.value start ~default:params_start in
      make (Expr.Function {params; deps; body}) start next, next

    (* `recur (p <- e, acc = init, ...) do body`, whose parameters are `&p`
       and the accumulators *)
    and recur start pos =
      let root, pos = pattern pos in
      let input, pos = expr (expect LeftArrow pos) in
      let rec accs pos =
        match tokenize pos with
        | Comma, next ->
          let p, pos = pattern next in
          let init, pos = expr (expect Equal pos) in
          let rest, pos = accs pos in
          (p, init) :: rest, pos
        | RightParen, next -> [], next
        | _ -> unexpected ~expected:")" pos
      in
      let accs, pos = accs pos in
      let body, next = expr (expect Do pos) in
      let labelled xs = List.mapi (fun i x -> label i, x) xs in
      let params = labelled ({root with pat = Pat.Roll root} :: List.map fst accs) in
      let args = labelled (input :: List.map snd accs) in
      let recur = Expr.Recur {continue = "continue"; forget = "forget"; params; args; body} in
      enode "recur" recur start next
    in

    let expr, pos = expr 0 in
    match tokenize pos with
    | EOF, _ ->
      let errors = ref [] in
      Type.program ?vars (fun loc problem -> errors := (loc, problem) :: !errors) expr;
      let errors = List.stable_sort (fun ((a, _), _) ((b, _), _) -> Int.compare a b) (List.rev !errors) in
      let stop = String.length input in
      {expr; errors; syntax = {form = "program"; info = Other; start = 0; stop; children = !nodes}}
    | _ -> unexpected pos
end

module Runtime : sig
  type value
  val show : value -> string
  val eval : (string * value) list -> 'loc Type.expr -> value
  (* The environment within `let p = e in ...`, unless binding it depends on
     a hole *)
  val define : (string * value) list -> 'loc Type.pat -> 'loc Type.expr -> (string * value) list option
  (* A record's field, which is a hole if the record is *)
  val field : value -> string -> value
end = struct
  type value =
      Record of (string * value) list
    | Variant of string * (string * value) list
    (* A function, given its caller's dependencies and its arguments *)
    | Closure of (value -> (string * value) list -> value)
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

  let rec bind env (p : _ Type.pat) value =
    match p.pat, value with
    | _ when Type.is_error p.ty -> raise Indeterminate
    | Pat.Var name, _ -> Some ((name, value) :: env)
    | Pat.Wildcard, _ -> Some env
    | Pat.Record {fields = ps; _}, Record values -> bind_fields env ps values
    | Pat.Variant (tag, ps), Variant (tag', values) when String.equal tag tag' ->
      bind_fields env ps values
    | Pat.Roll p, Roll value -> bind env p value
    | Pat.The (_, p), _ -> bind env p value
    | Pat.Or (p, q), _ ->
      begin match bind env p value with
        | None -> bind env q value
        | found -> found
      end
    | Pat.Record {fields = ps; _}, Hole -> bind_fields env ps (List.map (fun (name, _) -> name, Hole) ps)
    | Pat.Roll p, Hole -> bind env p Hole
    | Pat.Variant _, Hole -> raise Indeterminate
    | _ -> None

  and bind_fields env ps values =
    List.fold_left (fun env (name, p) ->
        Option.bind env (fun env -> bind env p (List.assoc name values)))
      (Some env) ps

  let rec eval env node =
    try step env node with Indeterminate -> Hole

  and step env (node : _ Type.expr) =
    match node.expr with
    | _ when Type.is_error node.ty -> Hole
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

    | Expr.Function {params; deps = pattern; body} ->
      Closure (fun deps args ->
          let inner = Option.get (bind_fields ((deps_name, deps) :: env) params args) in
          let inner = match pattern with Some p -> Option.get (bind inner p deps) | None -> inner in
          eval inner body)

    | Expr.Apply {f; args; deps} ->
      let f = eval env f in
      let args = List.map (fun (name, e) -> name, eval env e) args in
      begin match f with
        | Native f -> f args
        | Hole -> raise Indeterminate
        | Closure f -> f (match deps with Some e -> eval env e | None -> Record []) args
        | _ -> assert false
      end

    | Expr.Dep name -> List.assoc name (fields_of (List.assoc deps_name env))

    | Expr.Var name -> List.assoc name env

    | Expr.Let {pat; defn; body} -> eval (Option.get (bind env pat (eval env defn))) body

    | Expr.Roll e -> Roll (eval env e)

    | Expr.The (_, e) | Expr.Abstract (_, e) -> eval env e

    (* Unlike a closure, keeps the enclosing function's dependencies *)
    | Expr.Recur {continue; forget; params; args; body} ->
      let identity = Native (fun args -> List.assoc (label 0) args) in
      let rec loop args =
        let env = (continue, Native loop) :: (forget, identity) :: env in
        eval (Option.get (bind_fields env params args)) body
      in
      loop (List.map (fun (name, e) -> name, eval env e) args)

    | Expr.Hole -> Hole

  let define env pat defn =
    try bind env pat (eval env defn) with Indeterminate -> None

  let field value name =
    try List.assoc name (fields_of value) with Indeterminate -> Hole
end

(* The names in scope in every program, with their types and values: the
   fields of the prelude, which must be a record *)
type prelude = {vars : (string * Type.t) list; env : (string * Runtime.value) list}

let describe_errors code errors =
  String.concat "\n" (List.map (fun ((pos, _), problem) ->
      Parsing.describe code pos (Type.describe problem))
      errors)

let load_prelude source =
  match Parsing.parse source with
  | exception Parsing.Syntax_error {pos; msg; _} ->
    Error ("in the prelude, " ^ Parsing.describe source pos msg)
  | {errors = _ :: _ as errors; _} -> Error ("in the prelude, " ^ describe_errors source errors)
  | {expr; _} ->
    match Type.prune expr.ty with
    | Record {fields; _} ->
      let value = Runtime.eval [] expr in
      Ok {vars = fields; env = List.map (fun (name, _) -> name, Runtime.field value name) fields}
    | ty -> Error ("the prelude must be a record, but it's a " ^ Type.show ty)

let run prelude code =
  match Parsing.parse ~vars:prelude.vars code with
  | exception Parsing.Syntax_error {pos; msg; _} -> Error (Parsing.describe code pos msg)
  | {expr = e; errors = []; _} ->
    Ok (Printf.sprintf "the %s %s" (Type.show e.ty) (Runtime.show (Runtime.eval prelude.env e)))
  | {errors; _} -> Error (describe_errors code errors)
