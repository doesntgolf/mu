module Symbol : sig
  (* Strings backed by a WeakSet, so we can use physical equality *)
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

  module Table = Weak.Make(String)
  let table = Table.create 64

  let of_string str =
    match Table.find_opt table str with
    | Some s -> s
    | None ->
      Table.add table str;
      str

  let to_string s = s
end

module Env = struct
  type 'a t =
    | Binding of {name : Symbol.t; value : 'a; env : 'a t}
    | Empty

  let lookup key env =
    let rec aux = function
      | Binding {name; value; _} when Symbol.equal name key -> Some value
      | Binding {env; _} -> aux env
      | Empty -> None
    in
    aux env

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

  let iteri f env =
    let rec aux i = function
      | Binding {name; value; env} -> f name value i; aux (i+1) env
      | Empty -> ()
    in
    aux 0 env
end

module Pat = struct
  type ('pat, 'sym) t =
      Var of 'sym
    | Wildcard
    | Number of {
        value : int;
        exp : int;
        units : ('sym * int) list
      }
    | Record of 'pat Env.t
    | Variant of 'sym * 'pat Env.t
    | Constructor of 'sym * 'pat
    | Roll of 'pat
    | Pin of 'pat
    | Or of 'pat * 'pat

  type untyped = Bare of (untyped, Symbol.t) t
end

module Expr = struct
  type builtin =
      NumAdd
    | NumSub
    | NumMul
    | NumDiv
    | NumExp
    | NumEq
    | NumCmp

  (* The general pattern of this type (and Pat.t) is described at 
     https://blog.ezyang.com/2013/05/the-ast-typing-problem/ as "two level types". *)
  type ('expr, 'pat, 'sym) t =
      Number of {
        value : int;
        exp : int; (* value * 10^-exp *)
        unit : ('sym * int) list
      }

    | Record of 'expr Env.t
    | Field of 'expr * 'sym

    | Variant of 'sym * 'expr Env.t
    | Match of ('expr, 'pat, 'sym) match_expr

    | Function of {
        param : 'pat Env.t;
        body : 'expr
      }
    | Apply of {
        f : 'expr;
        args : 'expr Env.t;
        dependency : 'expr option
      }
    | Builtin of {
        f : builtin;
        args : 'expr Env.t
      }

    | Var of 'sym
    | Let of {
        pat : 'pat;
        defn : 'expr;
        body : 'expr
      }

    | Dependency of 'sym

    | Array of 'expr list

    | Exists of 'sym * 'expr
    | Constructor of 'sym * 'expr

    | Roll of 'expr
    | Pin of 'expr

  and ('expr, 'pat, 'sym) match_expr = {
    scrutinee : 'expr;
    clauses : ('pat * ('expr, 'pat, 'sym) match_branch) list
  }

  and ('expr, 'pat, 'sym) match_branch =
      Branch of 'expr
    | SubClause of ('expr, 'pat, 'sym) match_expr

  type untyped = Bare of (untyped, Pat.untyped, Symbol.t) t
end

module Type = struct
  type numer = Int of int | Var of int | Unknown
  type denom =
      Known of {coeff : int; vars : Symbol.t list}
    | Unknown

  type t =
      Number of {
        numer : numer;
        denom : denom;
        units : (Symbol.t * int) list
      }
    | Record of t Env.t
    | Variant of (t Env.t) Env.t
    | Function of {
        exists : int list;
        inputs : (t Env.t);
        dependencies : t Env.t;
        output : t
      }
    | Recurs of {
        id : int;
        exists : int list;
        body : t
      }
    | Array of {
        size : numer; (* int | var | ? *)
        ty : t
      }

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

  type typed_pat = {
    pat : (typed_pat, Symbol.t) Pat.t;
    ty : t
  }
  type typed_expr = {
    expr : (typed_expr, typed_pat, Symbol.t) Expr.t;
    ty : t
  }

  let rec show = function
    (* TODO: refactor this to thread through a buffer *)
    | Number {
        numer = Int i;
        denom = Known {coeff; vars};
        units
      } -> Printf.sprintf "Num %i/%i" i coeff
    | Record fields ->
      let buf = Buffer.create 16 in
      Buffer.add_char buf '{';
      Env.iteri
        (fun name ty i ->
           if i <> 0 then
             Buffer.add_string buf ", ";
           Printf.bprintf buf ".%s = %s" (Symbol.to_string name) (show ty))
        fields;
      Buffer.add_char buf '}';
      Buffer.contents buf

    | PolyVar {contents = Unbound {id; _}} -> Printf.sprintf "`%i" id
    | PolyVar {contents = Forwarded ty} -> show ty

    | Function {exists; inputs; dependencies; output} ->
      let buf = Buffer.create 16 in
      Buffer.add_string buf "fun(";
      Env.iteri (fun name ty i ->
          if i <> 0 then
            Buffer.add_string buf ", ";
          Printf.bprintf buf ".%s = %s" (Symbol.to_string name) (show ty))
        inputs;
      Buffer.add_string buf ") -> ";
      Buffer.add_string buf (show output);
      Buffer.contents buf

    | Variant variants ->
      let buf = Buffer.create 32 in
      Buffer.add_char buf '[';
      Env.iteri (fun name fields i ->
          if i <> 0 then
            Buffer.add_string buf ", ";
          Printf.bprintf buf "'%s(" (Symbol.to_string name);
          Env.iteri (fun name ty i ->
              if i <> 0 then
                Buffer.add_string buf ", ";
              Buffer.add_string buf (show ty))
            fields;
          Buffer.add_char buf ')')
        variants;
      Buffer.add_char buf ']';
      Buffer.contents buf

    | Recurs {id; exists; body} -> Printf.sprintf "μ `%i. %s" id (show body)

    | Error s -> Printf.sprintf "error: %s" s

  let rec occurs polyvar ty =
    match ty with
    | PolyVar var when polyvar == var -> failwith "occurs check"
    | PolyVar ({contents = Unbound ({id; let_level} as unbound)}) ->
      let min_level =
        match !polyvar with
        | Unbound {let_level = let_level'} -> Int.min let_level let_level'
        | _ -> let_level
      in
      unbound.let_level <- min_level
    | PolyVar {contents = Forwarded ty} -> occurs polyvar ty

    (* TODO: traverse other kinds *)

    | _ -> ()

  let rec unify a b =
    if a == b then Ok ()
    else match a, b with
      | PolyVar {contents = Forwarded t1}, t2
      | t1, PolyVar {contents = Forwarded t2} ->
        unify t1 t2

      | PolyVar ({contents = Unbound _} as polyvar), t 
      | t, PolyVar ({contents = Unbound _} as polyvar) ->
        occurs polyvar t;
        polyvar := Forwarded t;
        Ok ()

      | Record a_fields, Record b_fields ->
        (* NOTE: incomplete *)
        let rec aux a_fields =
          match a_fields with
          | Env.Binding {name; value = a_field; env = a_fields} ->
            begin match Env.lookup name b_fields with
              | None -> Result.Error ()
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
              match Env.lookup name b_inputs with
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
        Error ()

  (***
   * The inference algorithm:
   *  - Algorithm J-style, using refs for type vars rather than a Map
   *  - Algorithm M-style, passing down an expected type, rather than bottom-up W-style
   *  - Attaches levels to type vars for generalization rather than scanning the environment
   **)
  let infer env expr =
    let let_level = ref 0 in
    let fun_level = ref 0 in (* fun_level of bootstrapping a language: over 9000 *)

    let current_roll = ref None in

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
        | PolyVar {contents = Unbound {id; let_level=lev}}
          when lev > !let_level && not (List.exists (Int.equal id) acc) ->
          id :: acc

        | PolyVar {contents = Forwarded ty} -> aux acc ty

        | Function {exists; inputs; dependencies; output} ->
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
      Forall (vars, ty)
    in

    let no_generalize ty = Forall ([], ty) in

    let instantiate (Forall (vars, ty)) =
      let mapping = List.map
          (fun var -> (var, new_universal ()))
          vars
      in
      let rec aux ty =
        match ty with
        | PolyVar {contents = Unbound {id; _}} ->
          begin match List.assoc_opt id mapping with
            | Some replacement -> replacement
            | None -> ty
          end
        | PolyVar {contents = Forwarded ty} -> aux ty

        | Record fields ->
          Record (Env.map aux fields)

        | Variant variants ->
          Variant (Env.map
                     (fun variant -> Env.map aux variant)
                     variants)

        | Function {exists; inputs; dependencies; output} ->
          Function {
            exists;
            inputs = Env.map aux inputs;
            dependencies = Env.map aux dependencies;
            output = aux output
          }

        | Recurs {exists; id; body} ->
          Recurs {exists; id; body = aux body}

        | Array {size; ty} ->
          Array {size; ty = aux ty}

        | _ -> ty
      in
      aux ty
    in

    let infer_pat env ~expected ~generalize pat =
      let rec aux env ~expected (Pat.Bare pat) =
        match pat with
        | Pat.Var name ->
          let value = generalize expected in
          let env = Env.Binding {name; value; env} in
          ({pat = Pat.Var name; ty = expected}, env)

        | Pat.Roll inner ->
          let inner_ty = new_universal () in
          let found = Recurs {id = new_binder (); exists = []; body = inner_ty} in
          let (inner_node, env) = aux env ~expected:inner_ty inner in
          ({pat = Pat.Roll inner_node; ty = found}, env)
      in
      aux env ~expected pat
    in

    let rec aux env ~expected (Expr.Bare expr) =
      match expr with
      | Expr.Number {value; exp; unit} -> 
        let ty = Number {
            numer = Int value;
            denom = Known {coeff = 1; vars = []};
            units = []
          }
        in
        let _ = unify expected ty in
        {expr = Expr.Number {value; exp; unit}; ty}

      | Expr.Record fields ->
        let fields = Env.map
            (fun field -> aux env ~expected:(new_universal ()) field)
            fields
        in
        let ty = Record (Env.map (fun field -> field.ty) fields) in
        let _ = unify expected ty in
        {expr = Expr.Record fields; ty}

      | Expr.Field (expr, name) ->
        let rec_expected = Record (Env.Binding {name; value = expected; env = Env.Empty}) in
        let rec_expr = aux env ~expected:rec_expected expr in
        {expr = Expr.Field (rec_expr, name); ty = expected}

      | Expr.Let {pat; defn; body} ->
        incr let_level;
        let defn_node = aux env ~expected:(new_universal ()) defn in
        decr let_level;
        let (pat_node, body_env) = infer_pat env ~expected:defn_node.ty ~generalize pat in
        let body_node = aux body_env ~expected body in
        {
          expr = Expr.Let {pat = pat_node; defn = defn_node; body = body_node};
          ty = body_node.ty
        }

      | Expr.Var sym ->
        let ty =
          match Env.lookup sym env with
          | Some scheme -> instantiate scheme
          | None -> Error "var not found"
        in
        let _ = unify expected ty in
        {expr = Expr.Var sym; ty}

      | Expr.Function {param; body} ->
        (* TODO: this is all hardcoded for a single parameter *)
        let first_param = Symbol.of_string "1" in
        let input = new_universal () in
        let output = new_universal () in
        let found = Function {
            exists = [];
            inputs = Env.Binding {
                name = first_param;
                value = input;
                env = Env.Empty
              };
            dependencies = Env.Empty;
            output
          }
        in
        let _ = unify expected found in
        let Env.Binding {value = param; _} = param in
        let (pat_node, inner_env) = infer_pat env ~expected:input ~generalize:no_generalize param in
        let body_node = aux inner_env ~expected:output body in
        let expr = Expr.Function {
            param = Env.Binding {name = first_param; value = pat_node; env = Env.Empty};
            body = body_node
          }
        in
        {expr; ty = found}

      | Expr.Apply {f; args; dependency} ->
        (* TODO: this is all hardcoded for a single parameter *)
        let first_param = Symbol.of_string "1" in
        let arg_expected = new_universal () in
        let inputs = Env.Binding {
            name = first_param;
            value = arg_expected;
            env = Env.Empty
          }
        in
        let f_ty = Function {
            exists = [];
            inputs;
            dependencies = Env.Empty;
            output = expected
          }
        in
        let f_node = aux env ~expected:f_ty f in
        let Env.Binding {value = arg; _} = args in
        let arg_node = aux env ~expected:arg_expected arg in
        {
          expr = Expr.Apply {
              f = f_node;
              args = Binding {
                  name = first_param;
                  value = arg_node;
                  env = Env.Empty
                };
              dependency = None
            };
          ty = expected
        }

      | Expr.Variant (tag, fields) ->
        let fields = Env.map (aux env ~expected:(new_universal ())) fields in
        let field_types = Env.map (fun node -> node.ty) fields in
        let found =
          Variant (Binding {
              name = tag;
              value = field_types;
              env = Empty
            })
        in
        let _ = unify expected found in
        {
          expr = Variant (tag, fields);
          ty = found
        }

      | Expr.Roll expr ->
        let inner_ty = new_universal () in
        let id = new_binder () in

        let prev_roll = !current_roll in
        current_roll := Some id;
        let inner_node = aux env ~expected:inner_ty expr in
        current_roll := prev_roll;

        let found_ty = Recurs {exists = []; id; body = inner_node.ty} in
        let _ = unify expected found_ty in
        {expr = Roll inner_node; ty = found_ty}

      | Expr.Pin expr ->
        (* TODO: this isn't right. i need to use a PolyVar or something as Recurs {binder} *)
        let inner_ty = new_universal () in
        let inner_node = aux env ~expected:inner_ty expr in
        let _ = unify expected inner_node.ty in
        {expr = Pin inner_node; ty = inner_node.ty}
    in
    aux env ~expected:(new_universal ()) expr
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
    | Undefined
    | Exists
    | In
    | And
    | Or
    | Ampersand
    | Caret
    | Pipe
    | ForwardSlash
    | Int of int
    | Underscore
    | EOF
    | TokenError of string
    | UnexpectedChar of char

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
    let rec number pos yield =
      let rec aux acc pos =
        match input.[pos] with
        | '0'..'9' as c ->
          let acc = acc * 10 in
          let i = int_of_char c - 48 in
          aux (acc + i) (pos + 1)

        | exception (Invalid_argument _)
        | _ -> yield (Int acc) pos
      in
      aux 0 pos
    in

    let symbol =
      let buf = Buffer.create 16 in
      let rec aux pos yield =
        match input.[pos] with
        | 'a'..'z'
        | 'A'..'Z'
        | '0'..'9'
        | '-' | '_' as c ->
          Buffer.add_char buf c;
          aux (pos+1) yield

        | exception (Invalid_argument _)
        | _ ->
          let str = Buffer.contents buf in
          Buffer.reset buf;
          yield pos str
      in
      aux
    in

    let keyword = function
      | "let" -> Let
      | "exists" -> Exists
      | "in" -> In
      | "undefined" -> Undefined
      | "and" -> And
      | "or" -> Or
      | "_" -> Underscore
      | s -> Ident (Symbol.of_string s)
    in

    let rec aux pos yield =
      match input.[pos] with
      | ' ' | '\b' | '\012'
      | '\t' | '\011'
      | '\n' | '\r' -> aux (pos+1) yield

      | ',' -> yield Comma (pos+1)
      | ';' ->
        let pos = skip_comment (pos+1) in
        aux pos yield

      | '0'..'9' -> number pos yield

      | 'a'..'z'
      | 'A'..'Z'
      | '_' ->
        symbol pos (fun pos str ->
            let token = keyword str in
            yield token pos)

      | '.' ->
        symbol (pos+1) (fun pos str ->
            match keyword str with
            | Ident sym -> yield (Field sym) pos
            | _ -> yield (TokenError "unexpected keyword") pos)

      | '\'' ->
        symbol (pos+1) (fun pos str ->
            match keyword str with
            | Ident sym -> yield (Tag sym) pos
            | _ -> yield (TokenError "unexpected keyword") pos)

      | '-' -> begin match input.[pos+1] with
          | '>' -> yield Arrow (pos+2)
          | '0'..'9' -> number pos yield
          | _ -> yield (UnexpectedChar '-') (pos+1)
        end

      | '=' -> yield Equal (pos+1)
      | '<' -> yield Less (pos+1)
      | '>' -> yield Greater (pos+1)

      | '(' -> yield LeftParen (pos+1)
      | ')' -> yield RightParen (pos+1)
      | '{' -> yield LeftCurly (pos+1)
      | '}' -> yield RightCurly (pos+1)
      | '[' -> yield LeftSquare (pos+1)
      | ']' -> yield RightSquare (pos+1)

      | '\\' -> yield ForwardSlash (pos+1)
      | '|' -> yield Pipe (pos+1)
      | '&' -> yield Ampersand (pos+1)
      | '^' -> yield Caret (pos+1)

      | c -> yield (UnexpectedChar c) (pos+1)
      | exception (Invalid_argument _) -> yield EOF pos
    in
    aux

  let parse input =
    let tokenize = tokenize input in

    let expect expected pos k =
      tokenize pos (fun token pos ->
          if token = expected then
            k pos
          else
            Error (`UnexpectedToken (token, pos)))
    in

    let rec whole_pat pos k =
      tokenize pos (fun token pos ->
          match token with
          | Ident sym -> k (Pat.(Bare (Var sym))) pos
          | Underscore -> k (Pat.(Bare Wildcard)) pos

          | Ampersand ->
            whole_pat pos (fun pat pos ->
                k (Pat.(Bare (Roll pat))) pos)
          | Caret ->
            whole_pat pos (fun pat pos ->
                k (Pat.(Bare (Pin pat))) pos)

          | token -> Error (`UnexpectedToken (token, pos)))
    in

    let rec atomic_expr pos k =
      tokenize pos (fun token pos ->
          match token with
          | Int value -> k (Expr.(Bare (Number {
              value;
              exp = 0;
              unit = []
            }))) pos

          | Ident sym -> k (Expr.(Bare (Var sym))) pos

          | Let ->
            whole_pat pos (fun pat pos ->
                expect Equal pos (fun pos ->
                    whole_expr pos (fun defn pos ->
                        expect In pos (fun pos ->
                            whole_expr pos (fun body pos ->
                                let expr = Expr.(Bare (Let {pat; defn; body})) in
                                k expr pos)))))

          | ForwardSlash ->
            whole_pat pos (fun pat pos ->
                expect Arrow pos (fun pos ->
                    whole_expr pos (fun body pos ->
                        let param = Env.Binding {
                            name = Symbol.of_string "1";
                            value = pat;
                            env = Env.Empty
                          } in
                        let expr = Expr.(Bare (Function {param; body})) in
                        k expr pos)))

          | LeftCurly ->
            let rec aux acc pos =
              tokenize pos (fun token pos ->
                  match token with
                  | Field name ->
                    tokenize pos (fun token pos ->
                        match token with
                        | Equal ->
                          whole_expr pos (fun expr pos ->
                              let acc = Env.Binding {name; value = expr; env = acc} in
                              aux acc pos))
                  | Comma -> aux acc pos
                  | RightCurly -> k (Expr.Bare (Record acc)) pos
                  | _ -> Error (`UnexpectedToken (token, pos)))
            in
            aux Env.Empty pos

          | Tag tag ->
            tokenize pos (fun token next_pos ->
                match token with
                | LeftParen ->
                  let rec aux acc pos =
                    (* TODO: this just parses one payload field *)
                    whole_expr pos (fun expr pos ->
                        expect RightParen pos (fun pos ->
                            let expr = Expr.(Bare (Variant (tag, Env.Binding {
                                name = Symbol.of_string "1";
                                value = expr;
                                env = Env.Empty
                              })))
                            in
                            k expr pos))
                  in
                  aux Env.Empty next_pos

                | _ ->
                  k (Expr.(Bare (Variant (tag, Env.Empty)))) pos)

          | Ampersand ->
            whole_expr pos (fun expr pos ->
                k (Expr.(Bare (Roll expr))) pos)
          | Caret ->
            whole_expr pos (fun expr pos ->
                k (Expr.(Bare (Pin expr))) pos)

          | token -> Error (`UnexpectedToken (token, pos)))

    and compound_expr left pos k =
      tokenize pos (fun token next_pos ->
          match token with
          | Field name ->
            let expr = Expr.Bare (Field (left, name)) in
            compound_expr expr next_pos k

          | LeftParen ->
            whole_expr next_pos (fun arg pos ->
                expect RightParen pos (fun pos ->
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
                    compound_expr expr pos k))

          | _ -> k left pos)

    and whole_expr pos k =
      atomic_expr pos (fun inner outer_pos ->
          compound_expr inner outer_pos k)
    in

    whole_expr 0 (fun expr pos ->
        Ok expr)

  let read_file fname =
    let ch = open_in fname in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s
end

module Runtime : sig
  type value
  val show : value -> string
  val eval : value Env.t -> Type.typed_expr -> (value, string) result
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
    | Roll of {env : value Env.t; body : Type.typed_expr}

  module Frame = Hashtbl.Make(Symbol)

  let rec show = function
    | Number {value; exp; unit} -> string_of_int value
    | Record fields ->
      let buf = Buffer.create 16 in
      Buffer.add_char buf '{';
      Env.iteri
        (fun name value i ->
           if i <> 0 then
             Buffer.add_string buf ", ";
           Printf.bprintf buf "%s = %s" (Symbol.to_string name) (show value))
        fields;
      Buffer.add_char buf '}';
      Buffer.contents buf;
    | Variant {tag; payload} ->
      let buf = Buffer.create 16 in
      Printf.bprintf buf "'%s(" (Symbol.to_string tag);
      Env.iteri (fun name ty i ->
          if i <> 0 then
            Buffer.add_string buf ", ";
          Printf.bprintf buf ".%s = %s" (Symbol.to_string name) (show ty))
        payload;
      Buffer.add_char buf ')';
      Buffer.contents buf
    | Function _ -> "<function>"
    | Roll _ -> "<roll>"

  let rec match_ env (typed_pat : Type.typed_pat) value =
    match typed_pat.pat with
    | Pat.Var name -> Env.Binding {name; value; env}
    | Pat.Wildcard -> env

    | Pat.Roll pat ->
      let Roll {env = roll_env; body} = value in
      begin match eval roll_env body with
        | Ok value -> match_ env pat value
        | Error _ -> failwith "force roll failure"
      end
    | Pat.Pin pat -> match_ env pat value

  and eval env node =
    let frame = Frame.create 16 in

    let rec aux env (node : Type.typed_expr) ~frame k =
      match node.ty with
      | Error str -> Error (Printf.sprintf "Type error: %s" str)
      | _ ->
        match node.expr with
        | Expr.Number {value; exp; unit} ->
          k (Number {value; exp; unit})

        | Expr.Record fields ->
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
              match Env.lookup name fields with
              | Some value -> k value
              | None -> Error (Printf.sprintf "Field error: %s" (Symbol.to_string name)))

        | Expr.Let {pat; defn; body} ->
          aux env defn ~frame (fun defn_val ->
              let env = match_ env pat defn_val in
              aux env body ~frame k)

        | Expr.Var sym ->
          begin match Env.lookup sym env with
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
                        match Env.lookup name param with
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
          k (Roll {env; body})
        | Expr.Pin expr ->
          aux env expr ~frame k

        | _ -> Error ("unimplemented eval for expression")
    in
    aux env node ~frame (fun res -> Ok res)
end

module Test = struct
  let test ~code ~ty ~value =
    let expr = Parsing.parse code in
    (* expect expr.ty = ty *)
    (* let result = eval expr in
       expect result = value *)
    ()

  let run_tests () =
    print_endline "TODO: run tests"
end

let main () =
  let cmd =
    if Array.length Sys.argv < 2 then
      `PrintHelp
    else
      match Sys.argv.(1) with
      | "-h"
      | "--help" -> `PrintHelp
      | "-t"
      | "--test" -> `RunTests
      | "-"
      | "--" ->`Prog In_channel.(input_all stdin)
      | "-e"
      | "--eval" -> `Prog Sys.argv.(2)
      | fname -> `Prog (Parsing.read_file fname)
  in
  match cmd with
  | `RunTests -> Test.run_tests (); 38

  | `Prog code -> begin
      match Parsing.parse code with
      | Error (`UnexpectedToken (token, pos)) ->
        let (line, col) = Parsing.line_and_col_of_pos code pos in
        Printf.printf
          "Unexpected token at line %i, column %i\n"
          line col;
        1
      | Ok ast ->
        let typed = Type.infer Env.Empty ast in
        Printf.printf "type: %s\n" (Type.show typed.ty);
        match Runtime.eval Env.Empty typed with
        | Error s -> print_endline s; 1
        | Ok value ->
          Printf.printf "result: %s\n" (Runtime.show value);
          0
    end

  | `PrintHelp ->
    Printf.printf {|usage: %s [option]
  -h or --help		Print this help text.
  -t or --test		Perform bootstrap tests.
  -e or --eval 'code'	Parse, typecheck, and evaluate 'code'.
  - or --		Parse, typecheck, and evaluate code from stdin.
  'filename'		Parse, typecheck, and evaluate code from file 'filename'
|} Sys.argv.(0);
    0

let () =
  if not !Sys.interactive then
    exit (main ())
