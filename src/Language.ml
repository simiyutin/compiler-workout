(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let b2i x = if x then 1 else 0
    let i2b x = if x = 0 then false else true

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
    ostap (
      parse: empty {failwith "Not implemented yet"}
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) stmt = match stmt with
    | Read(x)       -> (match i with
                       | hd::tl -> (Expr.update x hd s, tl, o)
                       | _      -> failwith "trying to read from empty stream")
    | Write(e)      -> (s, i, o @ [Expr.eval s e])
    | Assign(x, e)  -> (Expr.update x (Expr.eval s e) s, i, o)
    | Seq(st1, st2) -> eval (eval (s, i, o) st1) st2

    (* Statement parser *)
    ostap (
      parse: empty {failwith "Not implemented yet"}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
