open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
  | h::hs::hss -> (cstack, (Value.of_int @@ Expr.parseBinOp op (Value.to_int hs) (Value.to_int h))::hss, conf)
  | _          -> failwith "binop: stack is too small"

let handleConst i (cstack, stack, conf) = (cstack, i::stack, conf)

let handleLoad x (cstack, stack, (s, i, o)) = (cstack, (State.eval s x)::stack, (s, i, o))

let handleStore x (cstack, stack, (s, i, o)) = match stack with
  | h::hs -> (cstack, hs, (State.update x h s, i, o))
  | _     -> failwith "store: stack is too small"

let pop2 (cstack, stack, conf) = match stack with
  | _::_::tl -> (cstack, tl, conf)
  | _        -> failwith("pop2: stack is too small")

let pop1 (cstack, stack, conf) = match stack with
  | _::tl -> (cstack, tl, conf)
  | _        -> failwith("pop1: stack is too small")

let condition suff (cstack, stack, conf) = match stack with
  | h::hs -> (match suff with

    | "e" -> (Value.to_int h) = 0
    | _   -> failwith "condition: unimplemented operation"
  )
  | _          -> failwith "condition: stack is too small"

let handleBegin argnames locnames (cstack, stack, (st, i, o)) =
  let upd st (x, z) = State.update x z st in
  let entst = State.enter st (argnames @ locnames) in
  let entst = List.fold_left upd entst (zip (List.rev argnames) stack) in
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
        | CJMP(s, x)    -> if condition s conf then eval env (pop1 conf) @@ env#labeled x else eval env (pop1 conf) tl
        | STA(x, n)     -> let v::idxs, stackxs = split (n + 1) stack in eval env (cstack, stackxs, (Language.Stmt.update st x v (List.rev idxs), i, o)) tl
        | CALL(f, nargs, isProcedure) -> (
            if env#is_label f
            then eval env ((tl, st)::cstack, stack, c) @@ env#labeled f
            else eval env (env#builtin conf f nargs isProcedure) tl
        )

        | END | RET _   -> (match cstack with
                            | (p, st')::tl -> eval env (tl, stack, (State.leave st st', i, o)) p
                            | []           -> conf
                           )
        | BEGIN(_, argnames, locnames) -> eval env (handleBegin argnames locnames conf) tl
        | _ -> failwith "SM: eval: unknown token"

  )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
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


let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse _ = failwith "Not implemented"
  and bindings p = failwith "Not implemented"
  and expr e = match e with
         Language.Expr.Const(z)           -> [CONST z]
       | Language.Expr.Var(x)             -> [LD x]
       | Language.Expr.String(x)          -> [STRING x]
       | Language.Expr.Array(xs)          -> call ".array" xs false
       | Language.Expr.Elem(a, i)         -> call ".elem" [a; i] false
       | Language.Expr.Length(e)          -> call ".length" [e] false
       | Language.Expr.Binop(str, e1, e2) -> (expr e1)@(expr e2)@[BINOP str]
       | Language.Expr.Call(fname, args)  -> call fname (args) false
       | _ -> failwith "SM: expr: unknown expr"

 in
  (* returns (env, flag (???), code) *)
  let rec compile_stmt l env stmt = match stmt with
    | Language.Stmt.Assign(x, idxs, e)  -> (match idxs with
      | [] -> (env, false, expr e @ [ST x])
      | idxs -> (env, false, (List.concat @@ List.map expr idxs)@expr e@[STA(x, List.length idxs)])
    )

    | Language.Stmt.Seq(st1, st2) -> 
      let env, _, code1 = compile_stmt l env st1 in 
      let env, _, code2 = compile_stmt l env st2 in
      (env, false, code1 @ code2)

    | Language.Stmt.Skip          -> (env, false, [])

    | Language.Stmt.If(e, b1, b2) ->
      let endlabel, env = env#get_label "endif" in
      let elselabel, env = env#get_label "else"  in
      let env, _, thenCode = compile_stmt l env b1 in
      let env, _, elseCode = compile_stmt l env b2 in
      let code = expr e@[CJMP("e", elselabel)]@thenCode@[JMP(endlabel); LABEL(elselabel)]@elseCode@[LABEL(endlabel)] in
      (env, false, code)

    | Language.Stmt.While(e, st)  ->
      let beginlabel, env = env#get_label "whilebegin" in
      let endlabel, env   = env#get_label "whileend" in
      let env, _, whileBodyCode = compile_stmt l env st in
      let code = [LABEL(beginlabel)]@expr e@[CJMP("e", endlabel)]@ whileBodyCode @[JMP(beginlabel); LABEL(endlabel)] in
      (env, false, code)

    | Language.Stmt.Repeat(st, e) ->
      let beginLabel, env = env#get_label "begin" in
      let env, _, repeatBodyCode = compile_stmt l env st in
      let code = [LABEL(beginLabel)]@ repeatBodyCode @expr e@[CJMP("e", beginLabel)] in
      (env, false, code)

    | Language.Stmt.Call(fname, args) -> (env, false, call fname (args) true)

    | Language.Stmt.Return(eOpt) -> (env, false, (match eOpt with | None -> [RET false] | Some e -> expr e @ [RET true]))

    | _ -> failwith "SM: compile_stmt: unknown statement"


 in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label ("_end_" ^ name) in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label str = (label @@ str ^ (string_of_int ls)), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label "end" in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

