(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
(* Opening a library for lists *)
open List

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let bot_func = fun x -> failwith ("Undefined variable: " ^ x)
      in {g = bot_func; l = bot_func; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update_func x v s = fun x' -> if x = x' then v else s x'

    let update x v s = if mem x s.scope
      then {s with l = update_func x v s.l}
      else {s with g = update_func x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

let int_of_bool b = if b then 1 else 0
let bool_of_int i = if i == 0 then false else true

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

    (* Perform an operation encoded as string

          val eval_op : string -> int -> int -> int
    *)
    let eval_op op x y =
      match op with
      | "+" -> x + y
      | "-" -> x - y
      | "*" -> x * y
      | "/" -> x / y
      | "%" -> x mod y
      | "==" -> int_of_bool (x == y)
      | "!=" -> int_of_bool (x != y)
      | "<=" -> int_of_bool (x <= y)
      | "<" -> int_of_bool (x < y)
      | ">=" -> int_of_bool (x >= y)
      | ">" -> int_of_bool (x > y)
      | "!!" -> int_of_bool ((bool_of_int x) || (bool_of_int y))
      | "&&" -> int_of_bool ((bool_of_int x) && (bool_of_int y))
      | other -> failwith ("Unexpected operator: " ^ other)

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval sf e =
      match e with
      | Const n -> n
      | Var x -> State.eval sf x
      | Binop (op, a, b) -> eval_op op (eval sf a) (eval sf b)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    let ostapOps ops = map (fun op -> (ostap ($(op)), fun x y -> Binop(op, x, y))) ops

    ostap (
      parse: expr;

      expr:
        !(Util.expr
            (fun x -> x)
            [|
              `Lefta, ostapOps ["!!"];
              `Lefta, ostapOps ["&&"];
              `Nona,  ostapOps ["<="; ">="; ">"; "<"; "=="; "!="];
              `Lefta, ostapOps ["+"; "-"];
              `Lefta, ostapOps ["*"; "/"; "%"]
            |]
            term
         );

      term:
          name:IDENT { Var name }
        | n:DECIMAL  { Const n }
        | -"(" expr -")"
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
    let rec eval env ((sf, input, output) as config) e =
      match e with
      | Read x ->
        (State.update x (hd input) sf, tl input, output)
      | Write e ->
        (sf, input, output @ [(Expr.eval sf e)])
      | Assign (x, e) ->
        (State.update x (Expr.eval sf e) sf, input, output)
      | Seq (s, s') ->
        eval env (eval env config s) s'
      | Skip -> config
      | If (cond, the, els) ->
        eval env config (if Expr.eval sf cond == 1 then the else els)
      | While (cond, action) ->
        let rec while_cycle (sf', _, _) as config' =
          if (Expr.eval sf' cond == 1)
          then while_cycle (eval env config' action)
          else config'
        in while_cycle config
      | Repeat (action, cond) ->
        let rec repeat_cycle (sf', _, _) as config' =
          let (sf'', _, _) as config'' = eval env config' action in
          if (Expr.eval sf'' cond == 1)
          then config''
          else repeat_cycle config''
        in repeat_cycle config
      | Call (func, args) ->
        let (params, locals, body) = env#definition func in
        let param_vals = combine params (map (Expr.eval sf) args) in
        let sf' = State.enter sf (params @ locals) in
        let sf' = fold_left (fun s (p, v) -> State.update p v s) sf' param_vals in
        let (sf'', input', output') = eval env (sf', input, output) body in
        (State.leave sf'' sf, input', output')

    (* Statement parser *)
    let elif_branch elif els =
      let last_action = match els with
        | None -> Skip
        | Some act -> act
      in fold_right (fun (cond, action) branch -> If (cond, action, branch)) elif last_action

    ostap (
      parse:
          sequence
        | statement
        ;

      statement:
          %"read" "(" name:IDENT ")"                             { Read name }
        | %"write" "(" expr: !(Expr.parse) ")"                   { Write expr }
        | name:IDENT
              s: ( ":=" expr: !(Expr.parse)                      { Assign (name, expr) }
                 | "(" args: !(Util.list0 Expr.parse) ")"        { Call (name, args) }
                 )                                               { s }
        | %"skip"                                                { Skip }
        | %"if" cond: !(Expr.parse) %"then" action:parse
              elif:(%"elif" !(Expr.parse) %"then" parse)*
              els:(%"else" parse)?
              %"fi"                                              { If (cond, action, elif_branch elif els)}
        | %"while" cond: !(Expr.parse) %"do" action:parse %"od"  { While (cond, action) }
        | %"repeat" action:parse %"until" cond: !(Expr.parse)    { Repeat (action, cond) }
        | %"for" init:parse "," cond: !(Expr.parse)
              "," inc:parse %"do" action:parse %"od"             { Seq (init, While (cond, Seq (action, inc))) }
        ;

      sequence:
          head:statement -";" tail:parse          { Seq (head, tail) }
    )
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    let maybe_to_list = function
      | None   -> []
      | Some l -> l

    ostap (
      arg: IDENT;
      parse:
        %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
          locals:(%"local" !(Util.list arg))?
          "{" stmt: !(Stmt.parse) "}"             { (name, (args, maybe_to_list locals, stmt)) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
module M = Map.Make (String)

class def_env =
  object (self)
    val mp = M.empty
    method definition func = M.find func mp
    method define func (def: (string list * string list * Stmt.t)) = {< mp = M.add func def mp >}
  end

let eval (defs, body) i =
  let env = fold_left (fun e (f, d) -> e#define f d) (new def_env) defs in
  let (_, _, o) = Stmt.eval env (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
