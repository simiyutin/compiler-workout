open GT       
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)       


let handleBinOp op (stack, conf) = match stack with 
  | h::hs::hss -> ((Syntax.Expr.parseBinOp op h hs)::hss, conf)
  | _          -> failwith "stack is too small"

let handleConst i (stack, conf) = (i::stack, conf)

let handleRead (stack, conf) = match conf with
  | (s, h::hs, o) -> (h::stack, (s, hs, o))
  | _             -> failwith "cannot read from empty input stream"

let handleWrite (stack, (s, i, o)) = match stack with
  | h::hs -> (hs, (s, i, o@[h]))
  | _     -> failwith "stack is too small"

let handleLoad x (stack, (s, i, o)) = (s x::stack, (s, i, o))

let handleStore x (stack, (s, i, o)) = match stack with 
  | h::hs -> (hs, (Syntax.Expr.update x h s, i, o))
  | _     -> failwith "stack is too small"
                  
let rec eval conf prg = match prg with 
  | [] -> conf
  | hd::tl -> ( match hd with
        | BINOP(op) -> eval (handleBinOp op conf) tl
        | CONST(i)  -> eval (handleConst i conf) tl
        | READ      -> eval (handleRead conf) tl
        | WRITE     -> eval (handleWrite conf) tl
        | LD(x)     -> eval (handleLoad x conf) tl
        | ST(x)     -> eval (handleStore x conf) tl
  )

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileExpr pg e = match e with
         Syntax.Expr.Const(z)           -> pg@[CONST z]
       | Syntax.Expr.Var(x)             -> pg@[LD x]
       | Syntax.Expr.Binop(str, e1, e2) -> pg@(compileExpr [] e2)@(compileExpr [] e1)@[BINOP str]

let rec compileStmt pg stmt = match stmt with
   (* read to stack and store it to variable *)
    | Syntax.Stmt.Read(x)       -> pg@[READ]@[ST x]
   (* evaluate expression and write from stack *)
    | Syntax.Stmt.Write(e)      -> pg@compileExpr [] e@[WRITE]
   (* evaluate expression and store it to variable *)
    | Syntax.Stmt.Assign(x, e)  -> pg@compileExpr [] e@[ST x]
   (* concatenate programs recursively *)
    | Syntax.Stmt.Seq(st1, st2) -> pg@compileStmt [] st1@compileStmt [] st2

let compile stmt = compileStmt [] stmt
