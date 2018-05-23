(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let b2i x = if x then 1 else 0
let i2b x = if x = 0 then false else true
let rec zip lst1 lst2 = match lst1,lst2 with
  | [],_ -> []
  | _, []-> []
  | (x::xs),(y::ys) -> (x,y) :: (zip xs ys)

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    let empty_part x = failwith (Printf.sprintf "Undefined variable %s" x)

    let update_part x v s = fun y -> if x = y then v else s y

    (* Empty state *)
    let empty = (empty_part, empty_part, [])

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v (g, l, sc) = if List.mem x sc then (g, update_part x v l, sc) else (update_part x v g, l, sc)

    (* Evals a variable in a state w.r.t. a scope *)
    let eval (g, l, sc) x = if List.mem x sc then l x else g x

    (* Creates a new scope, based on a given state *)
    let enter (g, _, _) xs = (g, empty_part, xs)

    (* Drops a scope. semantic: leave FROM scope TO scope *)
    let leave (g, _, _) (_, l', sc') = (g, l', sc')

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)

    let parseBinOp op z1 z2 = match op with
    | "+" -> z1 + z2
    | "-" -> z1 - z2
    | "*" -> z1 * z2
    | "/" -> z1 / z2
    | "%" -> z1 mod z2
    | ">" -> b2i (z1 > z2)
    | "<" -> b2i (z1 < z2)
    | ">=" -> b2i (z1 >= z2)
    | "<=" -> b2i (z1 <= z2)
    | "==" -> b2i (z1 = z2)
    | "!=" -> b2i (z1 <> z2)
    | "!!" -> b2i ((i2b z1) || (i2b z2))
    | "&&" -> b2i ((i2b z1) && (i2b z2))
    | _ -> failwith ("unknown__operand:" ^ op)

    let not e = Binop("==", e, Const 0)

    let rec eval env ((s, i, o, r) as conf) expr = match expr with
    | Const (z)           -> (s, i, o, Some z)
    | Var (x)             -> (s, i, o, Some (State.eval s x))
    | Binop (str, e1, e2) ->
     let ((_, _, _, Some r2) as conf2) = eval env conf  e1 in
     let (s3, i3, o3, Some r3) = eval env conf2 e2 in
     (s3, i3, o3, Some (parseBinOp str r2 r3))
    | Call (fname, args) -> 
     let upd = fun (argVals, conf) e -> let (_, _, _, Some v) as conf = eval env conf e in (v::argVals, conf) in
     let (argVals, conf2) = List.fold_left upd ([], conf) args in
     env#definition env fname (List.rev argVals) conf2

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    let bop op x y = Binop (op, x, y)
    ostap (
      const: x:DECIMAL {Const(x)};
      var: x:IDENT {Var(x)};
      call: fname:IDENT -"(" args:!(Util.list0)[parse] -")" {Call(fname, args)};
      expr:
  	!(Util.expr
           (fun x -> x)
           [|
             `Lefta , [ostap ("!!"), bop "!!"];
             `Lefta , [ostap ("&&"), bop "&&"];
             `Nona , [ostap ("<="), bop "<="; ostap (">="), bop ">="; ostap ("=="), bop "=="; ostap ("!="), bop "!="; ostap ("<"), bop "<"; ostap (">"), bop ">"];
             `Lefta , [ostap ("+"), bop "+"; ostap ("-"), bop "-"];
             `Lefta, [ostap ("*"), bop "*"; ostap ("/"), bop "/"; ostap ("%"), bop "%"];
           |]
           primary
         );
      primary: call | const | var | -"(" expr -")";
      parse: expr | call | const | var
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)

    let metaSeq x y = match y with
    | Skip -> x
    | _    -> Seq (x, y)

    let rec eval env ((s, i, o, r) as conf) k stmt = match stmt with
    | Read(x)            -> eval env (match i with | hd::tl -> (State.update x hd s, tl, o, None) | _ -> failwith "trying to read from empty stream") Skip k
    | Write(e)           ->
     let (s, i, o, Some r) = Expr.eval env conf e in
     eval env (s, i, o @ [r], None) Skip k
    | Assign(x, e)       ->
     let (s, i, o, Some r) = Expr.eval env conf e in
     eval env (State.update x r s, i, o, None) Skip k
    | Seq (st1, st2)     -> eval env conf (metaSeq st2 k) st1
    | Skip -> (match k with | Skip -> conf | _ -> eval env conf Skip k)
    | If (e, br1, br2)   ->
     let (s, i, o, Some r) = Expr.eval env conf e in
     let br = if i2b r then br1 else br2 in
     eval env (s, i, o, None) k br
    | While (e, xs)      ->
     let (s, i, o, Some r) = Expr.eval env conf e in
     let br = if i2b r then Seq(xs, stmt) else Skip in
     eval env (s, i, o, None) k br
    | Repeat (xs, e)     -> eval env conf k (Seq(xs, While(Expr.not e, xs)))
    | Call (fname, args) -> eval env (Expr.eval env conf (Expr.Call(fname, args))) Skip k
    | Return (eOpt)      -> (match eOpt with 
      | None   -> (s, i, o, None)
      | Some e -> Expr.eval env conf e
     )

    (* Statement parser *)
    ostap (
      read: -"read" -"(" x:IDENT -")" {Read (x)};
      write: -"write" -"(" e:!(Expr.parse) -")" {Write (e)};
      assign: x:IDENT -":=" e:!(Expr.parse) {Assign (x, e)};
      skip: -"skip" {Skip};
      ite: -"if" e:!(Expr.parse) -"then" branch1:seq branch2:els -"fi" {If (e, branch1, branch2)};
      els: -"else" branch:seq {branch} | -"elif" e:!(Expr.parse) -"then" branch1:seq branch2:els {If(e, branch1, branch2)} | -"" {Skip};
      whl: -"while" e:!(Expr.parse) -"do" xs:seq -"od" {While (e, xs)};
      sugarfor: -"for" st:simpleStmt -"," e:!(Expr.parse) -"," st2:simpleStmt -"do" body:seq -"od" {Seq(st, While(e, Seq(body, st2)))};
      repeat: -"repeat" xs:seq -"until" e:!(Expr.parse) {Repeat(xs, e)};
      call: fname:IDENT -"(" args:!(Util.list0)[Expr.parse] -")" {Call(fname, args)};
      return: -"return" e:!(Expr.parse) {Return (Some e)} | -"return" {Return (None)};
      simpleStmt: read | write | assign | skip | ite | whl | sugarfor | repeat | call | return;
      seq: x:simpleStmt -";" xs:seq {Seq(x, xs)} | simpleStmt;
      parse: seq
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      names: !(Util.list0)[ostap(IDENT)];
      loc: -"local" names | -"" {[]};
      parse: -"fun" fname:IDENT -"(" args:names -")" locals:loc -"{" body:!(Stmt.parse) -"}" {(fname, (args, locals, body))}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o
(* Top-level parser *)
ostap (
  parse: defs:!(Definition.parse)* body:!(Stmt.parse) {(defs, body)}
)
