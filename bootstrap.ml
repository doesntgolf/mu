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

module Assoc(M : sig
    type t
    val equal : t -> t -> bool
  end) = struct

  type 'a t =
    | Binding of {name : M.t; value : 'a; env : 'a t}
    | Empty

  let empty = Empty
  let is_empty = function
    | Binding _ -> false
    | Empty -> true

  let singleton name value = Binding {name; value; env = Empty}
  let add name value env = Binding {name; value; env}

  let remove key env =
    let rec aux = function
      | Binding {name; env; _} when M.equal name key -> env
      | Binding {name; value; env} -> Binding {name; value; env = aux env}
      | Empty -> Empty
    in
    aux env

  let find_opt key env =
    let rec aux = function
      | Binding {name; value; _} when M.equal name key -> Some value
      | Binding {env; _} -> aux env
      | Empty -> None
    in
    aux env

  let find key env = Option.get (find_opt key env)

  let rev env =
    let rec aux acc = function
      | Binding {name; value; env} -> aux (Binding {name; value; env=acc}) env
      | Empty -> acc
    in
    aux Empty env

  let map f env =
    let rec aux acc = function
      | Binding {name; value; env} ->
        let acc = Binding {name; value = f value; env = acc} in
        aux acc env
      | Empty ->
        rev acc
    in
    aux Empty env

  let fold f env init =
    let rec aux acc = function
      | Empty -> acc
      | Binding {name; value; env} ->
        let acc = f name value acc in
        aux acc env
    in
    aux init env

  let merge f xs ys =
    let rec aux acc = function
      | Binding {name; value; env} ->
        let y = find_opt name ys in
        let acc =
          match f name (Some value) y with
          | Some value -> Binding {name; value; env=acc}
          | None       -> acc
        in
        aux acc env
      | Empty -> acc
    in
    let acc = aux Empty xs in

    let rec aux acc = function
      | Binding {name; value; env} ->
        let acc =
          match find_opt name xs with
          | Some _ -> acc
          | None -> match f name None (Some value) with
            | Some z -> add name z acc
            | None -> acc
        in
        aux acc env
      | Empty -> acc
    in
    aux acc ys

  let iteri f env =
    let rec aux i = function
      | Binding {name; value; env} -> f name value i; aux (i+1) env
      | Empty -> ()
    in
    aux 0 env
end

module Env = Assoc(Symbol)

module Abelian = struct
  type mult_expr =
      Factor of Symbol.t
    | One
    | Mul of mult_expr * mult_expr
    | Inv of mult_expr

  let combine_exponents =
    Env.merge (fun _ c1 c2 ->
        let v1 = Option.value c1 ~default:0 in
        let v2 = Option.value c2 ~default:0 in
        match v1 + v2 with
        | 0 -> None
        | sum -> Some sum)

  let invert_exponents =
    Env.map (fun c -> -c)

  let rec normalize = function
    | One -> Env.empty
    | Factor x -> Env.singleton x 1
    | Mul (t1, t2) -> combine_exponents (normalize t1) (normalize t2)
    | Inv t1 -> invert_exponents (normalize t1)

  let apply_subst_to_term x t_sub t =
    match Env.find_opt x t with
    | None -> t
    | Some cx ->
      let without_x = Env.remove x t in
      let scaled_sub = Env.map (fun c -> c * cx) t_sub in
      combine_exponents without_x scaled_sub

  let apply_subst_to_env x t_sub =
    List.map (fun (y, ty) -> (y, apply_subst_to_term x t_sub ty))

  let fresh_var =
    let counter = ref 0 in
    fun () ->
      incr counter;
      Symbol.of_string (Printf.sprintf "z_%i" !counter)

  let rec solve_diophantine ratio =
    if Env.is_empty ratio then []
    else
      let min_var, min_c =
        Env.fold (fun v c (mv, mc) ->
            let abs_c = abs c in
            if abs_c > 0  && abs_c < mc then Some v, abs_c
            else mv, mc)
          ratio (None, max_int)
      in
      match min_var with
      | None -> []
      | Some xm ->
        let cm = Env.find xm ratio in

        if Int.equal (abs cm) 1 then
          let sign = -cm in
          let rhs = Env.fold
              (fun v c acc ->
                 if Symbol.equal v xm then acc
                 else Env.add v (sign * c) acc)
              ratio
              Env.empty
          in
          [(xm, rhs)]
        else
          let fresh_z = fresh_var () in

          let qs, rs = Env.fold
              (fun v c (q_map, r_map) ->
                 if Symbol.equal v xm then (q_map, r_map)
                 else
                   let q = c / cm in
                   let r = c mod cm in
                   let q, r =
                     if r < 0 && cm > 0 then (q - 1, r + cm)
                     else if r > 0 && cm < 0 then (q - 1, r - cm)
                     else (q, r)
                   in
                   (Env.add v q q_map, Env.add v r r_map))
              ratio
              (Env.empty, Env.empty)
          in

          let xm_subst = Env.add fresh_z 1 (invert_exponents qs) in
          let new_eq = Env.add fresh_z cm rs in
          let deeper_substs = solve_diophantine new_eq in
          let final_xm_subst =
            List.fold_left
              (fun acc (sv, srhs) -> apply_subst_to_term sv srhs acc)
              xm_subst
              deeper_substs
          in

          (xm, final_xm_subst) :: deeper_substs

  let unify t1 t2 =
    let ratio = normalize (Mul (t1, Inv t2)) in
    solve_diophantine ratio

  let factorize n =
    if n <= 1 then []
    else
      let rec aux d n count acc =
        if Int.equal n 1 then
          if count > 0 then (d, count) :: acc
          else acc
        else if Int.equal (n mod d) 0 then
          aux d (n / d) (count + 1) acc
        else
          let next_d = if Int.equal d 0 then 3 else d + 2 in
          let new_acc =
            if count > 0 then (d, count) :: acc
            else acc
          in
          if d * d > n then (n, 1) :: new_acc
          else aux next_d n 0 new_acc
      in
      aux 2 n 0 []

  let rational_to_scale numer denom =
    let add_factors factors sign map =
      List.fold_left
        (fun acc (p, exp) ->
           let p_sym = string_of_int p |> Symbol.of_string in
           let current = match Env.find_opt p_sym acc with
             | Some c -> c
             | None -> 0
           in
           let updated = current + (sign * exp) in
           if Int.equal updated 0 then
             Env.remove p_sym acc
           else
             Env.add p_sym updated acc)
        map
        factors
    in
    let map_num = add_factors (factorize (abs numer)) 1 Env.empty in
    add_factors (factorize (abs denom)) (-1) map_num
end

module Type = struct
  type annotation =
      Forall of Symbol.t * annotation
    | Exists of Symbol.t * annotation
    | Recurs of Symbol.t * annotation
    | Var of Symbol.t
    | Function of {
        inputs : annotation Env.t;
        output : annotation
      }
    | Record of {fields : annotation Env.t; row : annotation option}
    | Variant of {variants : annotation Env.t Env.t; row : annotation option}

  type t =
    | Record of {fields : t Env.t; row : t option}
    | Variant of {variants : (t Env.t) Env.t; row : t option}
    | Function of {
        inputs : t Env.t;
        exists : int list;
        output : t
      }
    | Recurs of {
        binder : Symbol.t;
        body : t
      }
    | Repr of t
    | PolyVar of polyvar ref
    | RigidVar of {
        id : int;
        mutable fun_level : int
      }
    | Error of string

  and polyvar =
      Unbound of {
        id : int;
        mutable let_level : int
      }
    | Forwarded of t

  type scheme = Forall of int list * t

  let type_of_annotation anno =
    ()

  let show ty = 
    let buf = Buffer.create 16 in
    let rec aux = function
      | Record {fields; _} ->
        Buffer.add_char buf '{';
        Env.iteri
          (fun name ty i ->
             if i <> 0 then
               Buffer.add_string buf ", ";
             Printf.bprintf buf ".%s = " (Symbol.to_string name);
             aux ty)
          fields;
        Buffer.add_char buf '}';

      | PolyVar {contents = Unbound {id; _}} -> Printf.bprintf buf "`%i" id
      | PolyVar {contents = Forwarded ty} -> aux ty

      | RigidVar {id; _} -> Printf.bprintf buf "~%i" id

      | Function {inputs; exists; output} ->
        Buffer.add_string buf "fun(";
        Env.iteri (fun name ty i ->
            if i <> 0 then
              Buffer.add_string buf ", ";
            Printf.bprintf buf ".%s = " (Symbol.to_string name);
            aux ty)
          inputs;
        Buffer.add_string buf ") -> ";
        aux output

      | Variant {variants; _} ->
        Buffer.add_char buf '[';
        Env.iteri (fun name fields i ->
            if i <> 0 then
              Buffer.add_string buf ", ";
            match fields with
            | Env.Empty -> Printf.bprintf buf "'%s" (Symbol.to_string name)
            | fields ->
              Printf.bprintf buf "'%s(" (Symbol.to_string name);
              Env.iteri (fun name ty i ->
                  if i <> 0 then
                    Buffer.add_string buf ", ";
                  aux ty)
                fields;
              Buffer.add_char buf ')')
          variants;
        Buffer.add_char buf ']'

      | Recurs {binder; body} -> Printf.bprintf buf "μ %s. " (Symbol.to_string binder); aux body

      | Error s -> Printf.bprintf buf "error: %s" s

      | _ -> failwith "TODO: show type"
    in
    aux ty;
    Buffer.contents buf

  let rec occurs polyvar ty =
    match ty with
    | PolyVar var when polyvar == var -> Result.Error "occurs check"
    | PolyVar ({contents = Unbound ({id; let_level} as unbound)}) ->
      let min_level =
        match !polyvar with
        | Unbound {let_level = let_level'} -> Int.min let_level let_level'
        | _ -> let_level
      in
      unbound.let_level <- min_level;
      Ok ()
    | PolyVar {contents = Forwarded ty} -> occurs polyvar ty

    (* TODO: traverse other kinds *)
    | _ -> Error "unimplemented"

  let rec unify a b =
    if a == b then Ok ()
    else match a, b with
      | PolyVar {contents = Forwarded t1}, t2
      | t1, PolyVar {contents = Forwarded t2} ->
        unify t1 t2

      | PolyVar ({contents = Unbound _} as polyvar), t 
      | t, PolyVar ({contents = Unbound _} as polyvar) ->
        Result.bind (occurs polyvar t) (fun () ->
            polyvar := Forwarded t;
            Ok ())

      | Record {fields = a_fields; _}, Record {fields = b_fields; _} ->
        (* NOTE: incomplete *)
        let rec aux a_fields =
          match a_fields with
          | Env.Binding {name; value = a_field; env = a_fields} ->
            begin match Env.find_opt name b_fields with
              | None -> Result.Error "TODO"
              | Some b_field ->
                let _ = unify a_field b_field in
                aux a_fields
            end
          | Env.Empty -> Ok ()
        in
        aux a_fields

      | Function {inputs=a_inputs; output=a_output; _}, Function {inputs=b_inputs; output=b_output; _} ->
        let rec aux a_inputs =
          match a_inputs with
          | Env.Empty -> ()
          | Env.Binding {name; value=a_input; env=a_rest} ->
            let () =
              match Env.find_opt name b_inputs with
              | Some b_input ->
                let _ = unify a_input b_input in ()
              | None ->
                ()
            in
            aux a_rest
        in
        let _ = aux a_inputs in
        unify a_output b_output

      (* TODO traverse other kinds *)
      | _, _ ->
        Printf.printf "Error unifying %s and %s\n" (show a) (show b);
        Error "TODO"
end

module Pat = struct
  type ('pat, 'sym) t =
      Var of 'sym
    | Wildcard
    | Record of 'pat Env.t
    | Variant of 'sym * 'pat Env.t
    | Roll of 'pat
    | Or of 'pat * 'pat
    | The of Type.annotation * 'pat

  type 'loc typed = {
    pat : ('loc typed, Symbol.t) t;
    location : 'loc;
    ty : Type.t
  }

  let var env =
    env

  let wildcard env =
    ({pat = Wildcard; location = (); ty = Type.Error "unimplemented"}, env)

  let record env fields =
    ({pat = Record fields; location = (); ty = Type.Record {fields = Env.empty; row = None}}, env)
end

module Expr = struct
  (* The general structure of this type (and Pat.t) is described at
     https://blog.ezyang.com/2013/05/the-ast-typing-problem/ as "two level types". *)
  type ('expr, 'pat, 'sym) t =
      Record of {fields : 'expr Env.t; row : 'expr option}
    | Field of 'expr * 'sym

    | Variant of 'sym * 'expr Env.t
    | Match of {
        scrutinee : 'expr;
        clauses : ('pat * 'expr) list
      }

    | Function of {
        param : 'pat Env.t;
        body : 'expr
      }
    | Apply of {
        f : 'expr;
        args : 'expr Env.t
      }

    | Var of 'sym
    | Let of {
        pat : 'pat;
        defn : 'expr;
        body : 'expr
      }

    | Abstract of 'sym * 'expr
    | The of Type.annotation * 'expr

    | Roll of 'expr
    | Loop of {
        pat : 'pat;
        from : 'expr;
        body : 'expr
      }

  type 'loc typed = {
    expr : ('loc typed, 'loc Pat.typed, Symbol.t) t;
    location : 'loc;
    ty : Type.t
  }

  (***
   * The inference algorithm:
   *  - Algorithm J-style, using refs for type vars rather than a Map
   *  - Algorithm M-style, passing down an expected type, rather than bottom-up W-style
   *  - Attaches levels to type vars for generalization rather than scanning the environment
   **)
  let infer env expr =
    let let_level = ref 0 in
    let fun_level = ref 0 in (* fun_level(language_design) > 9000 *)

    let current_roll = ref None in
    let constructor_env = ref Env.Empty in

    let new_universal =
      let n = ref 0 in
      fun () ->
        let id = !n in
        incr n;
        PolyVar (ref (Unbound {id; let_level = !let_level}))
    in
    let new_existential =
      let n = ref 0 in
      fun () ->
        let id = !n in
        incr n;
        RigidVar {id; fun_level = !fun_level}
    in
    let new_binder =
      let n = ref 0 in
      fun () ->
        let id = !n in
        incr n;
        id
    in

    let generalize ty =
      let rec aux acc ty =
        match ty with
        | Type.PolyVar {contents = Unbound {id; let_level=lev}}
          when lev > !let_level && not (List.exists (Int.equal id) acc) ->
          id :: acc

        | PolyVar {contents = Forwarded ty} -> aux acc ty

        | Function {exists; inputs; output} ->
          let rec fun_aux acc inputs =
            match inputs with
            | Env.Binding {name; value; env=inputs} ->
              let acc = aux acc value in
              fun_aux acc inputs
            | Env.Empty ->
              aux acc output
          in
          fun_aux acc inputs

        (* TODO: traverse record, variant *)
        | _ -> acc
      in
      let vars = aux [] ty in
      Type.Forall (vars, ty)
    in

    let no_generalize ty = Type.Forall ([], ty) in

    let instantiate = function
      | Type.Forall ([], ty) -> ty
      | Type.Forall (vars, ty) ->
        let mapping = List.map
            (fun var -> (var, new_universal ()))
            vars
        in
        let rec aux ty =
          match ty with
          | Type.PolyVar {contents = Unbound {id; _}} ->
            begin match List.assoc_opt id mapping with
              | Some replacement -> replacement
              | None -> ty
            end
          | PolyVar {contents = Forwarded ty} -> aux ty

          | Record {fields; _} ->
            Type.Record {fields = Env.map aux fields; row = None}

          | Variant {variants; _} ->
            Variant {variants =
                       (Env.map
                          (fun variant -> Env.map aux variant)
                          variants);
                     row = None}

          | Function {exists; inputs; output} ->
            Function {
              exists;
              inputs = Env.map aux inputs;
              output = aux output
            }

          | Recurs {binder; body} ->
            Recurs {binder; body = aux body}

          | _ -> ty
        in
        aux ty
    in

    let rec aux env ~expected expr =
      match expr with
      | Record {fields; _} ->
        let fields = Env.map
            (fun field -> aux env ~expected:(new_universal ()) field)
            fields
        in
        let ty = Type.Record {fields = Env.map (fun field -> field.ty) fields; row = None} in
        let _ = Type.unify expected ty in
        {expr = Record {fields; row = None}; location = (); ty}

      | Field (expr, name) ->
        let rec_expected = Type.Record {fields = Env.Binding {name; value = expected; env = Env.Empty}; row = None} in
        let rec_expr = aux env ~expected:rec_expected expr in
        {expr = Field (rec_expr, name); location = (); ty = expected}

      | Let {pat; defn; body} ->
        incr let_level;
        let defn_node = aux env ~expected:(new_universal ()) defn in
        decr let_level;
        let (pat_node, body_env) = Pat.infer env ~expected:defn_node.ty ~generalize pat in
        let body_node = aux body_env ~expected body in
        {
          expr = Let {pat = pat_node; defn = defn_node; body = body_node};
          location = ();
          ty = body_node.ty
        }

      | Var sym ->
        let ty =
          match Env.find_opt sym env with
          | Some scheme -> instantiate scheme
          | None -> Error "var not found"
        in
        let _ = Type.unify expected ty in
        {expr = Var sym; location = (); ty}

      | Function {param; body} ->
        (* TODO: this is all hardcoded for a single parameter *)
        let first_param = Symbol.of_string "1" in
        let input = new_universal () in
        let output = new_universal () in
        let found = Type.Function {
            exists = [];
            inputs = Env.Binding {
                name = first_param;
                value = input;
                env = Env.Empty
              };
            output
          }
        in
        let _ = Type.unify expected found in
        let [@warning "-8"] Env.Binding {value = param; _} = param in
        let (pat_node, inner_env) = Pat.infer env ~expected:input ~generalize:no_generalize param in
        let body_node = aux inner_env ~expected:output body in
        let expr = Function {
            param = Env.Binding {name = first_param; value = pat_node; env = Env.Empty};
            body = body_node
          }
        in
        {expr; location = (); ty = found}

      | Apply {f; args} ->
        (* TODO: this is all hardcoded for a single parameter *)
        let first_param = Symbol.of_string "1" in
        let arg_expected = new_universal () in
        let inputs = Env.Binding {
            name = first_param;
            value = arg_expected;
            env = Env.Empty
          }
        in
        let f_ty = Type.Function {
            exists = [];
            inputs;
            output = expected
          }
        in
        let f_node = aux env ~expected:f_ty f in
        let [@warning "-8"] Env.Binding {value = arg; _} = args in
        let arg_node = aux env ~expected:arg_expected arg in
        {
          expr = Apply {
              f = f_node;
              args = Binding {
                  name = first_param;
                  value = arg_node;
                  env = Env.Empty
                }
            };
          location = ();
          ty = expected
        }

      | Variant (tag, fields) ->
        let fields = Env.map (aux env ~expected:(new_universal ())) fields in
        let field_types = Env.map (fun node -> node.ty) fields in
        let found =
          Type.Variant {variants = (Binding {
              name = tag;
              value = field_types;
              env = Empty
            });
             row = None}
        in
        let _ = Type.unify expected found in
        {
          expr = Variant (tag, fields);
          location = ();
          ty = found
        }

      | Roll expr ->
        let inner_ty = new_universal () in
        let id = new_binder () in

        let prev_roll = !current_roll in
        current_roll := Some id;
        let inner_node = aux env ~expected:inner_ty expr in
        current_roll := prev_roll;

        let found_ty = Type.Recurs {exists = []; id; body = inner_node.ty} in
        let _ = Type.unify expected found_ty in
        {expr = Roll inner_node; location = (); ty = found_ty}

      | Abstract (sym, body) ->
        let prev_cons_env = !constructor_env in
        constructor_env := Env.Binding {name=sym; value = new_existential (); env = prev_cons_env};
        let body_node = aux env ~expected body in
        constructor_env := prev_cons_env;
        {expr = Abstract (sym, body_node); location = (); ty = body_node.ty}

      | The (anno, expr) ->
        failwith "TODO infer the"

      | _ ->
        failwith "TODO Expr.infer"
    in
    aux env ~expected:(new_universal ()) expr

  type state = {
    mutable let_level : int;
    mutable fun_level : int
  }

  let record fields row =
    let expr = Record {fields; row} in
    {expr; location = (); ty = Type.Error ""}

  let field expr name =
    let expr = Field (expr, name) in
    {expr; location = (); ty = Type.Error ""}
end

module Parsing = struct
  type token =
      Let
    | LeftParen
    | RightParen
    | LeftCurly
    | RightCurly
    | LeftSquare
    | RightSquare
    | Greater
    | Less
    | Ident of Symbol.t
    | Field of Symbol.t
    | Tag of Symbol.t
    | Comma
    | Arrow
    | Equal
    | Abstract
    | The
    | In
    | Or
    | Ampersand
    | Pipe
    | ForwardSlash
    | Int of int
    | Underscore
    | EOF
    | TokenError of string
    | UnexpectedChar of char

  let string_of_token = function
    | Let -> "let"
    | LeftParen -> "("
    | RightParen -> ")"
    | LeftCurly -> "{"
    | RightCurly -> "}"
    | LeftSquare -> "["
    | RightSquare -> "]"
    | Greater -> ">"
    | Less -> "<"
    | Ident sym -> Printf.sprintf "ident %s" (Symbol.to_string sym)
    | Field sym -> Printf.sprintf "field %s" (Symbol.to_string sym)
    | Tag sym -> Printf.sprintf "tag %s" (Symbol.to_string sym)
    | Comma -> ","
    | Arrow -> "->"
    | Equal -> "="
    | Abstract -> "abstract"
    | The -> "the"
    | In -> "in"
    | Or -> "or"
    | Ampersand -> ";"
    | Pipe -> "|"
    | ForwardSlash -> "\\"
    | Int i -> string_of_int i
    | Underscore -> "_"
    | EOF -> "EOF"
    | _ -> "unimplemented string_of_token"

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

  let tokenize input =
    let rec skip_comment pos =
      match input.[pos] with
      | exception (Invalid_argument _) -> pos
      | '\n'                           -> pos+1
      | _                              -> skip_comment (pos+1)
    in

    (* TODO parse decimal, unit, scientific notation *)
    let rec number pos =
      let rec aux acc pos =
        match input.[pos] with
        | '0'..'9' as c ->
          let acc = acc * 10 in
          let i = int_of_char c - 48 in
          aux (acc + i) (pos + 1)

        | exception (Invalid_argument _)
        | _ -> Int acc, pos
      in
      aux 0 pos
    in

    let symbol =
      let buf = Buffer.create 16 in
      let rec aux pos =
        match input.[pos] with
        | 'a'..'z'
        | 'A'..'Z'
        | '0'..'9'
        | '-' | '_' as c ->
          Buffer.add_char buf c;
          aux (pos+1)

        | exception (Invalid_argument _)
        | _ ->
          let str = Buffer.contents buf in
          Buffer.reset buf;
          str, pos
      in
      aux
    in

    let keyword = function
      | "let" -> Let
      | "abstract" -> Abstract
      | "the" -> The
      | "in" -> In
      | "or" -> Or
      | "_" -> Underscore
      | s -> Ident (Symbol.of_string s)
    in

    let rec aux pos =
      match input.[pos] with
      | ' ' | '\b' | '\012'
      | '\t' | '\011'
      | '\n' | '\r' -> aux (pos+1)

      | ',' -> Comma, (pos+1)
      | ';' ->
        let pos = skip_comment (pos+1) in
        aux pos

      | '0'..'9' -> number pos

      | 'a'..'z'
      | 'A'..'Z'
      | '_' ->
        let str, pos = symbol pos in
        keyword str, pos

      | '.' ->
        let str, pos = symbol (pos+1) in
        begin match keyword str with
          | Ident sym -> Field sym, pos
          | _ -> TokenError "unexpected keyword", pos
        end

      | '\'' ->
        let str, pos = symbol (pos+1) in
        begin match keyword str with
          | Ident sym -> Tag sym, pos
          | _ -> TokenError "unexpected keyword", pos
        end

      | '-' -> begin match input.[pos+1] with
          | '>' -> Arrow, pos+2
          | '0'..'9' -> number pos
          | _ -> UnexpectedChar '-', pos+1
        end

      | '=' -> Equal, pos+1
      | '<' -> Less, pos+1
      | '>' -> Greater, pos+1

      | '(' -> LeftParen, pos+1
      | ')' -> RightParen, pos+1
      | '{' -> LeftCurly, pos+1
      | '}' -> RightCurly, pos+1
      | '[' -> LeftSquare, pos+1
      | ']' -> RightSquare, pos+1

      | '\\' -> ForwardSlash, pos+1
      | '|' -> Pipe, pos+1
      | '&' -> Ampersand, pos+1

      | c -> UnexpectedChar c, pos+1
      | exception (Invalid_argument _) -> EOF, pos
    in
    aux

  let parse input =
    let tokenize = tokenize input in

    let unexpected_token token pos =
      let line, col = line_and_col_of_pos input pos in
      failwith (Printf.sprintf "found unexpected token '%s' at line %i col %i"
                  (string_of_token token) line col)
    in

    let assume token pos =
      let found, pos = tokenize pos in
      if token = found then
        pos
      else
        unexpected_token found pos
    in

    let comma_sep what closer pos =
      let token, next_pos = tokenize pos in
      if token = closer then
        [], next_pos
      else
        let rec aux acc pos =
          let item = what pos in
          let token, next_pos = tokenize pos in
          if token = Comma then
            aux (item :: acc) next_pos
          else if token = closer then
            List.rev acc, next_pos
          else
            unexpected_token token pos
        in
        aux [] pos
    in

    let rec whole_pat pos =
      let token, pos = tokenize pos in
      match token with
      | LeftParen ->
        let pat, pos = whole_pat pos in
        let pos = assume RightParen pos in
        pat, pos

      | Ident sym -> Pat.(Bare (Var sym)), pos
      | Underscore -> Pat.(Bare Wildcard), pos

      | Ampersand ->
        let pat, pos = whole_pat pos in
        Pat.(Bare (Roll pat)), pos

      | token ->
        unexpected_token token pos
    in

    let rec type_expr pos =
      let token, pos = tokenize pos in
      match token with
      | Ident sym -> Type.Expr.Var sym, pos
      | LeftParen ->
        let inner, pos = type_expr (pos+1) in
        let pos = assume RightParen pos in
        inner, pos

      | LeftCurly ->
        let rec aux acc pos =
          failwith "TODO"
        in
        aux Env.Empty (pos+1)

      | _ ->
        failwith "TODO"
    in

    let rec atomic_expr pos =
      let token, pos = tokenize pos in
      match token with
      | LeftParen ->
        let expr, pos = whole_expr pos in
        let pos = assume RightParen pos in
        expr, pos

      | Ident sym -> Expr.(Bare (Var sym)), pos

      | Let ->
        let pat, pos = whole_pat pos in
        let pos = assume Equal pos in
        let defn, pos = whole_expr pos in
        let pos = assume In pos in
        let body, pos = whole_expr pos in
        let expr = Expr.(Bare (Let {pat; defn; body})) in
        expr, pos

      | ForwardSlash ->
        let pat, pos = whole_pat pos in
        let pos = assume Arrow pos in
        let body, pos = whole_expr pos in
        let param = Env.Binding {
            name = Symbol.of_string "1";
            value = pat;
            env = Env.Empty
          } in
        let expr = Expr.(Bare (Function {param; body})) in
        expr, pos

      | LeftCurly ->
        let rec aux acc pos =
          let token, pos = tokenize pos in
          match token with
          | Field name ->
            let pos = assume Equal pos in
            let expr, pos = whole_expr pos in
            let acc = Env.Binding {name; value = expr; env = acc} in
            aux acc pos
          | Comma -> aux acc pos
          | RightCurly -> Expr.Bare (Record {fields = acc; row = None}), pos
          | token ->
            unexpected_token token pos
        in
        aux Env.Empty pos

      | Tag tag ->
        let token, next_pos = tokenize pos in
        begin match token with
          | LeftParen ->
            let rec aux acc pos =
              (* TODO: this just parses one payload field *)
              let expr, pos = whole_expr pos in
              let pos = assume RightParen pos in
              let expr = Expr.(Bare (Variant (tag, Env.Binding {
                  name = Symbol.of_string "1";
                  value = expr;
                  env = Env.Empty
                })))
              in
              expr, pos
            in
            aux Env.Empty next_pos

          | _ ->
            Expr.(Bare (Variant (tag, Env.Empty))), pos
        end

      | Ampersand ->
        let expr, pos = whole_expr pos in
        Expr.(Bare (Roll expr)), pos

      | Abstract ->
        let sym, pos =
          match tokenize pos with
          | Ident sym, pos -> sym, pos
          | token, _ ->
            unexpected_token token pos
        in
        let pos = assume In pos in
        let body, pos = whole_expr pos in
        let expr = Expr.(Bare (Abstract (sym, body))) in
        expr, pos

      | The ->
        let ty_expr, pos = type_expr pos in
        let body, pos = whole_expr pos in
        let expr : Expr.typed = {
          expr = The (ty_expr, body);
          ty = Type.Error "TODO"
        } in
        expr, pos

      | token ->
        unexpected_token token pos

    and compound_expr left pos =
      let token, next_pos = tokenize pos in
      match token with
      | Field name ->
        let expr = Expr.Bare (Field (left, name)) in
        compound_expr expr next_pos

      | LeftParen ->
        let arg, pos = whole_expr next_pos in
        let pos = assume RightParen pos in
        let args = Env.Binding {
            name = Symbol.of_string "1";
            value = arg;
            env = Env.Empty
          }
        in
        let expr = Expr.(Bare (Apply {
            f = left;
            args;
            dependency = None
          }))
        in
        compound_expr expr pos

      | _ -> left, pos

    and whole_expr pos =
      let inner, outer_pos = atomic_expr pos in
      compound_expr inner outer_pos
    in

    let expr, _ = whole_expr 0 in
    Ok expr

  let read_file fname =
    let ch = open_in fname in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s
end

module Runtime : sig
  type value
  val show : Type.t -> value -> string
  val eval : value Env.t -> 'a Expr.typed -> value
end = struct
  type value =
      Number of {
        value : int;
        exp : int;
        unit : (Symbol.t * int) list
      }
    | Record of value Env.t
    | Variant of {
        tag : Symbol.t;
        payload : value Env.t
      }
    | Function of {
        param : Type.typed_pat Env.t;
        body_env : value Env.t;
        body : Type.typed_expr
      }
    | Roll of {
        env : value Env.t;
        body : Type.typed_expr
      }

  module Frame = Hashtbl.Make(Symbol)

  let show ty value =
    let buf = Buffer.create 32 in
    let rec aux ty value =
      match ty with
      | Type.Variant vars ->
        let Variant {tag; payload} = value in
        if Env.is_empty payload then
          Printf.bprintf buf "'%s" (Symbol.to_string tag)
        else begin
          let Some payload_ty = Env.find_opt tag vars in
          Printf.bprintf buf "'%s(" (Symbol.to_string tag);
          Env.iteri (fun name ty i ->
              if i <> 0 then
                Buffer.add_string buf ", ";
              Printf.bprintf buf ".%s = " (Symbol.to_string name);
              let Some field_val = Env.find_opt name payload in
              aux ty field_val)
            payload_ty;
          Buffer.add_char buf ')'
        end

      | Type.Record fields ->
        let Record field_vals = value in
        Buffer.add_char buf '{';
        Env.iteri
          (fun name ty i ->
             if i <> 0 then
               Buffer.add_string buf ", ";
             Printf.bprintf buf ".%s = " (Symbol.to_string name);
             let Some field_val = Env.find_opt name field_vals in
             aux ty field_val)
          fields;
        Buffer.add_char buf '}'

      | Type.Function _ -> Buffer.add_string buf "<function>"
      | Type.Recurs _ -> Buffer.add_string buf "<roll>"

      | Type.PolyVar {contents = Forwarded ty} -> aux ty value
    in
    aux ty value;
    Buffer.contents buf

  let rec match_ env (typed_pat : Type.typed_pat) value =
    match typed_pat.pat with
    | Pat.Var name -> Env.Binding {name; value; env}
    | Pat.Wildcard -> env

    | Pat.Roll pat ->
      begin match value with
        | Roll {env = roll_env; body; _} ->
          begin match eval roll_env body with
            | Ok forced_val -> match_ env pat forced_val
            | Error _ -> failwith "force roll failure"
          end
        | _ -> failwith "Expected Roll value in Pat.Roll match"
      end

  and eval env node =
    let frame = Frame.create 16 in

    let rec aux env (node : Type.typed_expr) ~frame k =
      match node.ty with
      | Error str -> Error (Printf.sprintf "Type error: %s" str)
      | _ ->
        match node.expr with
        | Expr.Record {fields; _} ->
          let rec field_aux acc = function
            | Env.Empty -> k (Record acc)
            | Env.Binding {name; value; env = rec_env} ->
              aux env value ~frame (fun field_val ->
                  let acc = Env.Binding {name; value=field_val; env=acc} in
                  field_aux acc rec_env)
          in
          field_aux Env.Empty fields

        | Expr.Field (record, name) ->
          aux env record ~frame (fun (Record fields) ->
              match Env.find_opt name fields with
              | Some value -> k value
              | None -> Error (Printf.sprintf "Field error: %s" (Symbol.to_string name)))

        | Expr.Let {pat; defn; body} ->
          aux env defn ~frame (fun defn_val ->
              let env = match_ env pat defn_val in
              aux env body ~frame k)

        | Expr.Var sym ->
          begin match Env.find_opt sym env with
            | Some value -> k value
            | None -> Error (Printf.sprintf "Variable not in env: %s" (Symbol.to_string sym))
          end

        | Expr.Function {param; body} ->
          k (Function {param; body_env = env; body})

        | Expr.Apply {f; args; dependency} ->
          let outer_env = env in
          aux outer_env f ~frame (fun (Function {param; body_env; body}) ->
              let rec apply_aux env_acc args =
                match args with
                | Env.Binding {name; value=arg; env=args} ->
                  aux outer_env arg ~frame (fun arg_value ->
                      let env_acc =
                        match Env.find_opt name param with
                        | Some param -> match_ env_acc param arg_value
                        | None ->
                          Printf.printf "Missing parameter: %s\n" (Symbol.to_string name);
                          env_acc
                      in
                      apply_aux env_acc args)
                | Env.Empty ->
                  let inner_frame = Frame.create 16 in
                  aux env_acc body ~frame:inner_frame k
              in
              apply_aux body_env args)

        | Expr.Variant (tag, fields) ->
          let rec field_aux acc = function
            | Env.Binding {name; value; env=rest} ->
              aux env value ~frame (fun value ->
                  let acc = Env.Binding {name; value; env = acc} in
                  field_aux acc rest)
            | Env.Empty ->
              k (Variant {tag; payload = acc})
          in
          field_aux Env.Empty fields

        | Expr.Roll body ->
          let id =
            match node.ty with
            | Type.Recurs {id; _} -> id
            | _ -> failwith "Expected Recurs type for Roll"
          in
          k (Roll {id; env; body})

        | Expr.Abstract (_, body) ->
          aux env body ~frame k

        | _ -> Error ("unimplemented eval for expression")
    in
    aux env node ~frame (fun res -> Ok res)
end

let main () =
  let cmd =
    match Sys.argv.(1) with
    | "-h"
    | "--help" -> `Usage
    | "-v"
    | "--version" -> `Version
    | "-t"
    | "--test" -> `RunTests
    | "-"
    | "--" ->`Prog In_channel.(input_all stdin)
    | "-e"
    | "--eval" -> `Prog Sys.argv.(2)
    | fname -> `Prog (Parsing.read_file fname)
    | exception (Invalid_argument _) -> `Usage
  in
  match cmd with
  | `Usage ->
    let bin_name = Sys.argv.(0) in
    Printf.printf {|usage: %s [command]
Available commands are:
  -h or --help		Print this help text.
  -t or --test		Perform bootstrap tests.
  -e or --eval 'code'	Parse, typecheck, and evaluate 'code'.
  -v or --version	Show version information.
  - or --		Parse, typecheck, and evaluate code from stdin.
  'filename'		Parse, typecheck, and evaluate code from file 'filename'
|} bin_name;
    0

  | `Version ->
    print_endline "Mu 0.0.0 alpha";
    0

  | `RunTests ->
    print_endline "No tests currently implemented";
    38

  | `Prog code ->
    match Parsing.parse code with
    | Error (`UnexpectedToken (token, pos)) ->
      let (line, col) = Parsing.line_and_col_of_pos code pos in
      Printf.printf
        "Unexpected token at line %i, column %i\n"
        line col;
      1
    | Ok ast ->
      match Runtime.eval Env.Empty ast with
      | exception _ -> 1
      | Error s -> print_endline s; 1
      | Ok value ->
        Printf.printf "the %s %s\n" (Type.show ast.ty) (Runtime.show ast.ty value);
        0

let () =
  if not !Sys.interactive then
    exit (main ())
