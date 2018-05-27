open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list


(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let handleBinOp op (cstack, stack, conf) = match stack with
  | h::hs::hss -> (cstack, (Value.of_int @@ Expr.parseBinOp op (Value.to_int h) (Value.to_int hs))::hss, conf)
  | _          -> failwith "binop: stack is too small"

let handleConst i (cstack, stack, conf) = (cstack, i::stack, conf)

let handleLoad x (cstack, stack, (s, i, o)) = (cstack, (State.eval s x)::stack, (s, i, o))

let handleStore x (cstack, stack, (s, i, o)) = match stack with
  | h::hs -> (cstack, hs, (State.update x h s, i, o))
  | _     -> failwith "store: stack is too small"

let pop2 (cstack, stack, conf) = match stack with
  | _::_::tl -> (cstack, tl, conf)
  | _        -> failwith("pop2: stack is too small")

let condition suff (cstack, stack, conf) = match stack with
  | h::hs::hss -> (match suff with

    | "e" -> h = hs
    | _   -> failwith "unimplemented operation"
  )
  | _          -> failwith "condition: stack is too small"

let handleBegin argnames locnames (cstack, stack, (st, i, o)) =
  let upd st (x, z) = State.update x z st in
  let entst = State.enter st (argnames @ locnames) in
  let entst = List.fold_left upd entst (zip argnames stack) in
  let rec chopn n lst = if n == 0 then lst else chopn (n - 1) @@ List.tl lst in
  (cstack, chopn (List.length argnames) stack, (entst, i, o))


let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = match prg with
  | [] -> conf
  | hd::tl -> ( match hd with

        | BINOP(op)     -> eval env (handleBinOp op conf) tl
        | CONST(i)      -> eval env (handleConst (Language.Value.of_int i) conf) tl
        | STRING(x)     -> eval env (handleConst (Language.Value.of_string x) conf) tl
        | LD(x)         -> eval env (handleLoad x conf) tl
        | ST(x)         -> eval env (handleStore x conf) tl
        | LABEL(x)      -> eval env conf tl
        | JMP(x)        -> eval env conf @@ env#labeled x
        | CJMP(s, x)    -> if condition s conf then eval env (pop2 conf) @@ env#labeled x else eval env (pop2 conf) tl
        | STA(x, n)     -> let v::idxs, stackxs = split (n + 1) stack in eval env (cstack, stackxs, (Language.Stmt.update st x v (List.rev idxs), i, o)) tl
        | CALL(fname, nargs, isFunction) -> (
            let flabel = "L" ^ fname in
            if env#is_label flabel
            then eval env ((tl, st)::cstack, stack, c) @@ env#labeled flabel
            else eval env (env#builtin conf fname nargs (not isFunction)) tl
        )

        | END | RET _   -> (match cstack with
                            | (p, st')::tl -> eval env (tl, stack, (State.leave st st', i, o)) p
                            | []           -> conf
                           )
        | BEGIN(_, argnames, locnames) -> eval env (handleBegin argnames locnames conf) tl

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let compileCall fname args isFunction compiler = (List.concat @@ List.map (compiler []) args) @ [CALL(fname, List.length args, isFunction)]

let rec compileExpr pg e = match e with
         Language.Expr.Const(z)           -> pg@[CONST z]
       | Language.Expr.Var(x)             -> pg@[LD x]
       | Language.Expr.String(x)          -> pg@[STRING x]
       | Language.Expr.Array(xs)          -> pg@compileCall "$array" xs true compileExpr
       | Language.Expr.Elem(a, i)         -> pg@compileCall "$elem" [a; i] true compileExpr
       | Language.Expr.Length(e)          -> pg@compileCall "$length" [e] true compileExpr
       | Language.Expr.Binop(str, e1, e2) -> pg@(compileExpr [] e2)@(compileExpr [] e1)@[BINOP str]
       | Language.Expr.Call(fname, args)  -> pg@compileCall fname (List.rev args) true compileExpr

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
   (* evaluate expression and store it to variable *)
    | Language.Stmt.Assign(x, idxs, e)  -> (match idxs with
      | [] -> pg@compileExpr [] e@[ST x]
      | idxs -> pg@(List.concat @@ List.map (compileExpr []) idxs)@compileExpr [] e@[STA(x, List.length idxs)]
    )
   (* concatenate programs recursively *)
    | Language.Stmt.Seq(st1, st2) -> pg@compileStmt [] st1@compileStmt [] st2
    | Language.Stmt.Skip          -> pg
    | Language.Stmt.If(e, b1, b2) ->
      let endlabel = freshName "endif" in
      let elselabel = freshName "else"  in
      pg@compileExpr [] e@[CONST(0); CJMP("e", elselabel)]@compileStmt [] b1@[JMP(endlabel); LABEL(elselabel)]@compileStmt [] b2@[LABEL(endlabel)]
    | Language.Stmt.While(e, st)  ->
      let beginlabel = freshName "whilebegin" in
      let endlabel   = freshName "whileend" in
      pg@[LABEL(beginlabel)]@compileExpr [] e@[CONST(0); CJMP("e", endlabel)]@compileStmt [] st@[JMP(beginlabel); LABEL(endlabel)]
    | Language.Stmt.Repeat(st, e) ->
      let beginLabel = freshName "begin" in
      pg@[LABEL(beginLabel)]@compileStmt [] st@compileExpr [] e@[CONST(0); CJMP("e", beginLabel)]
    | Language.Stmt.Call(fname, args) -> pg@compileCall fname (List.rev args) false compileExpr
    | Language.Stmt.Return(eOpt) -> (match eOpt with | None -> [RET false] | Some e -> compileExpr [] e @ [RET true])

let compileDef (name, (argnames, locnames, body)) = [LABEL("L" ^ name); BEGIN(name, argnames, locnames)] @ (compileStmt [] body) @ [END]

let compile (defs, p) = (compileStmt [] p) @ [END] @ (List.concat @@ List.map compileDef defs)

