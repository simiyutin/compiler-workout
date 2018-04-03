(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
       
let b2i x = if x then 1 else 0
let i2b x = if x = 0 then false else true

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
    (* loop with a post-condition       *) (* add yourself *)  with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((s, i, o) as conf) stmt = match stmt with
    | Read(x)       -> (match i with
                       | hd::tl -> (Expr.update x hd s, tl, o)
                       | _      -> failwith "trying to read from empty stream")
    | Write(e)       -> (s, i, o @ [Expr.eval s e])
    | Assign(x, e)   -> (Expr.update x (Expr.eval s e) s, i, o)
    | Seq(st1, st2)  -> eval (eval conf st1) st2
    | Skip           -> conf
    | If(e, br1, br2)-> if i2b @@ Expr.eval s e then eval conf br1 else eval conf br2
    | While(e, xs)   -> if i2b @@ Expr.eval s e then eval conf @@ Seq(xs, stmt) else conf

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
      simpleStmt: read | write | assign | skip | ite | whl | sugarfor;
      seq: x:simpleStmt -";" xs:seq {Seq(x, xs)} | simpleStmt;
      parse: seq
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
