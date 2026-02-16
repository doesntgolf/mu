module Symbol : sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val of_string : string -> t
  val to_string : t -> string
end = struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  let hash = Int.hash

  module Table = Hashtbl.Make(String)
  let table = Table.create 64
  let n = ref 0

  let of_string str =
    match Table.find_opt table str with
    | Some v -> v
    | None ->
      let curr = !n in
      incr n;
      Table.add table str curr;
      curr
  let to_string n =
    let exception Found of string in
    try
      Table.iter
        (fun str i ->
           if Int.equal n i then
             raise_notrace (Found str))
        table;
      raise Not_found
    with
    | Found key -> key
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
end

module Num : sig
  type atom = Int of int | Var of int | Unknown
  type monomial =
      Known of {coeff : int; vars : Symbol.t list}
    | Uknown
  type units = (Symbol.t * int) list
  type t = {
    numer : atom;
    denom : monomial;
    units : units
  }

  val unify : t -> t -> unit
end = struct
  type atom = Int of int | Var of int | Unknown
  type monomial =
      Known of {coeff : int; vars : Symbol.t list}
    | Uknown
  type units = (Symbol.t * int) list

  type t = {
    numer : atom;
    denom : monomial;
    units : units;
  }

  let unify _ _ = ()
end

module Pat = struct
  type ('pat, 'sym) t =
      Var of 'sym
    | Wildcard
    | Number of {
        value : int;
        exp : int;
        units : Num.units
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
        unit : ('sym * int) option
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
        args : 'expr Env.t
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
  type t =
      Number of Num.t
    | Record of t Env.t
    | Variant of (t Env.t) Env.t
    | Function of {
        exists : Symbol.t list;
        input : (t Env.t);
        output : t
      }
    | Recurs of {
        exists : Symbol.t list;
        binder : Symbol.t;
        body : t
      }
    (* | Array of t * int option * int option list *)
    | Error of string

  type scheme = Forall of string * t

  type typed_pat = {
    pat : (typed_pat, Symbol.t) Pat.t;
    ty : t
  }
  type typed_expr = {
    expr : (typed_expr, typed_pat, Symbol.t) Expr.t;
    ty : t
  }

  let show = function
    | Number {
        numer = Int i;
        denom = Known {coeff; vars};
        units
      } -> Printf.sprintf "Num %i/%i" i coeff

  let occurs a b = ()

  let unify a b = ()

  let generalize ty = Forall ("", ty)

  let instantiate (Forall (v, ty)) = ty

  let infer_pat env (Pat.Bare pat) =
    let rec aux env = function
      | Pat.Number _ -> env
    in
    aux env pat

  let infer env expr =
    let let_level = ref 0 in
    let fun_level = ref 0 in (* fun_level of bootstrapping a language: over 9000 *)
    let roll_level = ref 0 in

    let rec aux env ~expected (Expr.Bare expr) =
      match expr with
      | Expr.Number {value; exp; unit} -> {
          expr = Expr.Number {value; exp; unit};
          ty = Number {
              numer = Int value;
              denom = Known {coeff = 1; vars = []};
              units = []
            }
        }
      (* 
      | Expr.Record fields ->
        let fields = Env.map (aux env ~expected) fields in
        Record fields

      | Expr.Field (expr, name) ->
        let expr_type = aux env ~expected expr in
        let fields = Env.(Binding {name; value = expr_type; env = Empty}) in
        Record fields

      | Expr.Variant (tag, payload) ->
        Variant (Binding {
            name = tag;
            value = Env.map (aux env ~expected) payload;
            env = Empty (* TODO fresh type var *)
          })

      | Expr.Let {pat; defn; body} ->
        incr let_level;
        let defn_ty = aux env ~expected defn in
        decr let_level;
        let env = infer_pat env pat in
        aux env ~expected body

      | Expr.Var var ->
        match Env.lookup var env with
        | Some scheme -> instantiate scheme
        | None -> Error "var not found"
        *)
    in
    aux env ~expected:(Record Empty) expr
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
    | Error of string
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
            | _ -> yield (Error "unexpected keyword") pos)

      | '\'' ->
        symbol (pos+1) (fun pos str ->
            match keyword str with
            | Ident sym -> yield (Tag sym) pos
            | _ -> yield (Error "unexpected keyword") pos)

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

    let pat pos k =
      ()
    in

    let expr_atom pos k =
      tokenize pos (fun token pos ->
          match token with
          | Int i -> k token pos)
    in

    let expr_compound pos k =
      expr_atom pos (fun token pos ->
          match token with
          | Int value -> k (Expr.(Bare (Number {
              value;
              exp = 0;
              unit = None
            }))) pos)
    in
    expr_compound 0 (fun token pos -> token)

  let read_file fname =
    let ch = open_in fname in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s
end

module Runtime : sig
  type value
  val show : value -> string
  val eval : value Env.t -> Type.typed_expr -> (value, unit) result
end = struct
  type value =
      Number of {
        value : int;
        exp : int;
        unit : (Symbol.t * int) option
      }
    | Record of value Env.t
    | Variant of {
        tag : Symbol.t;
        payload : value Env.t
      }

  module Frame = Hashtbl.Make(Symbol)
  type position = Return | Block

  let show = function
    | Number {value; exp; unit} -> string_of_int value

  let eval env node =
    let frame = Frame.create 16 in
    let position = Return in

    let rec aux env node ~frame ~position k =
      match (node : Type.typed_expr).expr with
      | Expr.Number {value; exp; unit} -> k (Number {value; exp; unit})
      | _ -> Error ()
    in
    aux env node ~frame ~position (fun res -> Ok res)
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
      let ast = Parsing.parse code in
      let typed = Type.infer Env.Empty ast in
      Printf.printf "type: %s\n" (Type.show typed.ty);
      match Runtime.eval Empty typed with
      | Error () -> print_endline "runtime error"; 1
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
