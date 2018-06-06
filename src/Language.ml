(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let init_list n ~f =
  let rec init_list' acc i n f =
    if i >= n then acc
    else init_list' ((f i) :: acc) (i+1) n f
  in List.rev (init_list' [] 0 n f)

let b2i x = if x then 1 else 0
let i2b x = if x = 0 then false else true
let rec zip lst1 lst2 = match lst1,lst2 with
  | [],_ -> []
  | _, []-> []
  | (x::xs),(y::ys) -> (x,y) :: (zip xs ys)

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = init_list   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
   let parseBinOp op z1 z2 = 
    match op with
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
    | Const (z)           -> (s, i, o, Some (Value.of_int z))
    | String (x)          -> (s, i, o, Some (Value.of_string x))

    | Array (es)          -> 
     let (s, i, o, xs) = eval_list env conf es in
     env#definition env ".array" xs (s, i, o, None)

    | Sexp(t, es) -> 
     let (s, i, o, xs) = eval_list env conf es in
     (s, i, o, Some(Value.sexp t xs))

    | Elem (a, i)         -> 
     let (s, i, o, ai) = eval_list env conf [a; i] in
     env#definition env ".elem" ai (s, i, o, None)

    | Length (e)          ->
     let (s, i, o, Some a) = eval env conf e in
     env#definition env ".length" [a] (s, i, o, None)

    | Var (x)             -> (s, i, o, Some (State.eval s x))
    | Binop (str, e1, e2) ->
     let ((_, _, _, Some r2) as conf2) = eval env conf  e1 in
     let (s3, i3, o3, Some r3) = eval env conf2 e2 in
     (s3, i3, o3, Some (Value.of_int @@ parseBinOp str (Value.to_int r2) (Value.to_int r3)))
    | Call (fname, args) ->
     let (s, i, o, args) = eval_list env conf args in
     env#definition env fname args (s, i, o, None)
    | _ -> failwith "expression evaluator: unimplemented operand"
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
let bop op x y = Binop (op, x, y)

    ostap (
      const: x:DECIMAL {Const(x)};
      chr: x:CHAR {Const(Char.code x)};
      str: x:STRING {String(String.sub x 1 @@ (String.length x) - 2)};
      var: x:IDENT {Var(x)};
      call: fname:IDENT -"(" args:!(Util.list0)[parse] -")" {Call(fname, args)};
      arr: -"[" elements:!(Util.list0)[parse] -"]" {Array(elements)};
      sexp: -"`" x:IDENT -"(" args:!(Util.list0)[parse] -")" {Sexp(x, args)} | -"`" x:IDENT {Sexp(x, [])};

      primary: arr | call | str | sexp | chr | const | var | -"(" parse -")";

      idx: -"[" i:parse -"]" {`e i};
      len: -".length" {`l};
      unary: expr:primary ex:(idx | len)* {List.fold_left (fun expr -> function `e i -> Elem(expr, i) | `l -> Length expr) expr ex};

      parse:
  	!(Util.expr
           (fun x -> x)
           [|
             `Lefta , [ostap ("!!"), bop "!!"];
             `Lefta , [ostap ("&&"), bop "&&"];
             `Nona , [ostap ("<="), bop "<="; ostap (">="), bop ">="; ostap ("=="), bop "=="; ostap ("!="), bop "!="; ostap ("<"), bop "<"; ostap (">"), bop ">"];
             `Lefta , [ostap ("+"), bop "+"; ostap ("-"), bop "-"];
             `Lefta, [ostap ("*"), bop "*"; ostap ("/"), bop "/"; ostap ("%"), bop "%"];
           |]
           unary
         )
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          recurr: -"`" x:IDENT -"(" args:!(Util.list0)[parse] -")" {Sexp(x, args)} | -"`" x:IDENT {Sexp(x, [])};
          parse: recurr | -"_" {Wildcard} | x:IDENT {Ident(x)}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

let metaSeq x y = match y with
    | Skip -> x
    | _    -> Seq (x, y)


let rec eval env ((s, i, o, r) as conf) k stmt = match stmt with
    | Assign(x, idxs, e)       ->
     let (s, i, o, idxs) = Expr.eval_list env conf idxs in
     let (s, i, o, Some r) = Expr.eval env conf e in
     eval env (update s x r idxs, i, o, None) Skip k
    | Seq (st1, st2)     -> eval env conf (metaSeq st2 k) st1
    | Skip -> (match k with | Skip -> conf | _ -> eval env conf Skip k)
    | If (e, br1, br2)   ->
     let (s, i, o, Some r) = Expr.eval env conf e in
     let br = if i2b (Value.to_int r) then br1 else br2 in
     eval env (s, i, o, None) k br
    | While (e, xs)      ->
     let (s, i, o, Some r) = Expr.eval env conf e in
     let br = if i2b (Value.to_int r) then Seq(xs, stmt) else Skip in
     eval env (s, i, o, None) k br
    | Repeat (xs, e)     -> eval env conf k (Seq(xs, While(Expr.not e, xs)))
    | Call (fname, args) -> eval env (Expr.eval env conf (Expr.Call(fname, args))) Skip k
    | Return (eOpt)      -> (match eOpt with
      | None   -> (s, i, o, None)
      | Some e -> Expr.eval env conf e
     )
    | Case (e, patterns) -> 
     let (s, i, o, Some r) as conf1 = Expr.eval env conf e in
     let rec matchPattern p r s =
       let safeUpdate x r sOpt = (match sOpt with None -> None | Some s -> Some(State.bind x r s)) in 
         (match p, r with
           | Pattern.Ident x, r -> safeUpdate x r s
           | Pattern.Wildcard, r -> s
           | Pattern.Sexp(t1, patterns), Value.Sexp(t2, values) when t1 = t2 -> matchSexps patterns values s
           | _ -> None
         )
       and matchSexps patterns values s = (match patterns, values with
           | [], [] -> s
           | p::ps, v::vs -> matchSexps ps vs (matchPattern p v s)
           | _ -> None
         )
     in
     let rec handleCase ((s, i, o, _) as conf) patterns = (match patterns with
      | [] -> failwith "pattern matching failed: no branch found"
      | (p, b)::tl ->
       let sOpt = matchPattern p r (Some State.undefined) in (match sOpt with 
        | None -> handleCase conf tl
        | Some s1 -> eval env (State.push s s1 (Pattern.vars p), i, o, None) k (Seq(b, Leave))
       )
     ) in
     handleCase conf1 patterns
    | Leave -> eval env (State.drop s, i, o, r) Skip k
    | _ -> failwith "statement evaluator: unimplemented operand"

    (* Statement parser *)
    ostap (
      idx: -"[" e:!(Expr.parse) -"]" exs:idx {e::exs} | -"" {[]};
      assign: x:IDENT idxs:idx -":=" e:!(Expr.parse) {Assign (x, idxs, e)};
      skip: -"skip" {Skip};
      ite: -"if" e:!(Expr.parse) -"then" branch1:seq branch2:els -"fi" {If (e, branch1, branch2)};
      els: -"else" branch:seq {branch} | -"elif" e:!(Expr.parse) -"then" branch1:seq branch2:els {If(e, branch1, branch2)} | -"" {Skip};
      whl: -"while" e:!(Expr.parse) -"do" xs:seq -"od" {While (e, xs)};
      sugarfor: -"for" st:simpleStmt -"," e:!(Expr.parse) -"," st2:simpleStmt -"do" body:seq -"od" {Seq(st, While(e, Seq(body, st2)))};
      repeat: -"repeat" xs:seq -"until" e:!(Expr.parse) {Repeat(xs, e)};
      case: -"case" e:!(Expr.parse) -"of" pts:!(Util.listBy)[ostap("|")][ostap(p:!(Pattern.parse) -"->" s:parse {(p, s)})] -"esac" {Case(e, pts)};
      call: fname:IDENT -"(" args:!(Util.list0)[Expr.parse] -")" {Call(fname, args)};
      return: -"return" e:!(Expr.parse) {Return (Some e)} | -"return" {Return (None)};
      simpleStmt: assign | skip | ite | whl | sugarfor | repeat | call | case| return;
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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
