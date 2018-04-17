open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)
let handleBinOp op (stack, conf) = match stack with
  | h::hs::hss -> ((Language.Expr.parseBinOp op h hs)::hss, conf)
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
  | h::hs -> (hs, (Language.Expr.update x h s, i, o))
  | _     -> failwith "stack is too small"

let pop2 (stack, conf) = match stack with
  | _::_::tl -> (tl, conf)
  | _        -> failwith("pop2: stack is too small")

let condition suff (stack, conf) = match stack with
  | h::hs::hss -> (match suff with

    | "e" -> h = hs
    | _   -> failwith "unimplemented operation"
  )
  | _          -> failwith "condition: stack is too small"

(* let eval env ((cstack, stack, ((st, i, o) as c)) as conf) = failwith "Not implemented" *)
let rec eval env conf prg = match prg with
  | [] -> conf
  | hd::tl -> ( match hd with
        | BINOP(op) -> eval env (handleBinOp op conf) tl
        | CONST(i)  -> eval env (handleConst i conf) tl
        | READ      -> eval env (handleRead conf) tl
        | WRITE     -> eval env (handleWrite conf) tl
        | LD(x)     -> eval env (handleLoad x conf) tl
        | ST(x)     -> eval env (handleStore x conf) tl
        | LABEL(x)  -> eval env conf tl
        | JMP(x)    -> eval env conf @@ env#labeled x
        | CJMP(s, x)-> if condition s conf then eval env (pop2 conf) @@ env#labeled x else eval env (pop2 conf) tl
  )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compileExpr pg e = match e with
         Language.Expr.Const(z)           -> pg@[CONST z]
       | Language.Expr.Var(x)             -> pg@[LD x]
       | Language.Expr.Binop(str, e1, e2) -> pg@(compileExpr [] e2)@(compileExpr [] e1)@[BINOP str]

let freshName : string -> string =
  let module M = Map.Make (String) in
  let counters = ref M.empty in
  fun prefix ->
    if not (M.mem prefix !counters) then
      counters := M.add prefix 0 !counters;
    let n = M.find prefix !counters in
    counters := M.add prefix (n + 1) !counters;
    Printf.sprintf "%s_%d" prefix n

let rec compileStmt pg stmt = match stmt with
   (* read to stack and store it to variable *)
    | Language.Stmt.Read(x)       -> pg@[READ]@[ST x]
   (* evaluate expression and write from stack *)
    | Language.Stmt.Write(e)      -> pg@compileExpr [] e@[WRITE]
   (* evaluate expression and store it to variable *)
    | Language.Stmt.Assign(x, e)  -> pg@compileExpr [] e@[ST x]
   (* concatenate programs recursively *)
    | Language.Stmt.Seq(st1, st2) -> pg@compileStmt [] st1@compileStmt [] st2
    | Language.Stmt.Skip          -> pg
    | Language.Stmt.If(e, b1, b2) ->
      let endlabel = freshName "end" in
      let elselabel = freshName "b2"  in
      pg@compileExpr [] e@[CONST(0); CJMP("e", elselabel)]@compileStmt [] b1@[JMP(endlabel); LABEL(elselabel)]@compileStmt [] b2@[LABEL(endlabel)]
    | Language.Stmt.While(e, st)  ->
      let beginlabel = freshName "begin" in
      let endlabel   = freshName "end" in
      pg@[LABEL(beginlabel)]@compileExpr [] e@[CONST(0); CJMP("e", endlabel)]@compileStmt [] st@[JMP(beginlabel); LABEL(endlabel)]
    | Language.Stmt.Repeat(st, e) ->
      let beginLabel = freshName "begin" in
      pg@[LABEL(beginLabel)]@compileStmt [] st@compileExpr [] e@[CONST(0); CJMP("e", beginLabel)]

(* todo: stmt -> top level program*)
let compile (defs, p) = compileStmt [] p


