(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap

let b2i x = if x then 1 else 0
let i2b x = if x = 0 then false else true

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

    (* вот тут появляются переменные в скоупе. если написать внутри функции присваивание не local переменной, то она станет глобальной*)
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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)


    let parseBinOp op z1 z2 = match op with
        "+" -> z1 + z2
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

    let rec eval s e = match e with
        Const(z) -> z
       | Var(x) -> s x
       | Binop(str, e1, e2) -> parseBinOp str (eval s e1) (eval s e2)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    let bop op x y = Binop (op, x, y)
    ostap (
      const: x:DECIMAL {Const(x)};
      var: x:IDENT {Var(x)};
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
      primary: const | var | -"(" expr -")";
      parse: expr | const | var
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((s, i, o) as conf) stmt = match stmt with
    | Read(x)       -> (match i with
                       | hd::tl -> (Expr.update x hd s, tl, o)
                       | _      -> failwith "trying to read from empty stream")
    | Write(e)       -> (s, i, o @ [Expr.eval s e])
    | Assign(x, e)   -> (Expr.update x (Expr.eval s e) s, i, o)
    | Seq(st1, st2)  -> eval env (eval env conf st1) st2
    | Skip           -> conf
    | If(e, br1, br2)-> if i2b @@ Expr.eval s e then eval env conf br1 else eval env conf br2
    | While(e, xs)   -> if i2b @@ Expr.eval s e then eval env conf @@ Seq(xs, stmt) else conf
    | Repeat(xs, e)  ->
      let ((s', _, _) as c') = eval env conf xs in
      if i2b @@ Expr.eval s' e then c' else eval env c' @@ Repeat(xs, e)

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
      simpleStmt: read | write | assign | skip | ite | whl | sugarfor | repeat;
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
      parse: empty {failwith "Not implemented"}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = failwith "Not implemented"
(*
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
*)

(* Top-level parser *)
let parse = failwith "Not implemented"
