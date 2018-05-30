(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Opening a library for lists *)
open List

(* List.init implementations (too lazy to update OCaml to 4.04+) *)

let list_init n f =
  let rec go acc k =
    if k < n then go (f k :: acc) (k + 1) else acc
  in rev (go [] 0)

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
    let update_array  a i x = list_init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

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

let int_of_bool b = if b then 1 else 0
let bool_of_int i = if i == 0 then false else true

let maybe_to_list = function
  | None -> []
  | Some ls -> ls

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

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config
    *)
    let rec eval env ((sf, i, o, r) as config) e =
      match e with
      | Const n -> (sf, i, o, Some (Value.of_int n))
      | Array ls ->
        let config', arg_vals = prep_args env config ls in
        env#definition ".array" arg_vals config'
      | String s -> (sf, i, o, Some (Value.of_string s))
      | Sexp (tag, ls) ->
        let (sf', i', o', _), vals = prep_args env config ls in
        (sf', i', o', Some (Value.sexp tag vals))
      | Var x -> (sf, i, o, Some (State.eval sf x))
      | Binop (op, a, b) ->
        let ((_, _, _, Some a') as config') = eval env config a in
        let ((sf', i', o', Some b') as config') = eval env config' b in
        let res = eval_op op (Value.to_int a') (Value.to_int b') in
        (sf', i', o', Some (Value.of_int res))
      | Elem (arr, idx) ->
        let config', arg_vals = prep_args env config [arr; idx] in
        env#definition ".elem" arg_vals config'
      | Length arr ->
        let (_, _, _, Some v) as cfg = eval env config arr in
        env#definition ".length" [v] cfg
      | Call (func, args) ->
        let config', arg_vals = prep_args env config args in
        env#definition func arg_vals config'

    (* Prepare arguments for function/procedure call

          val prep_args : env -> config -> t list -> config * int list
    *)
    and prep_args env ((sf, input, output, res) as config) args =
      let arg_eval (cfg, pvs) a =
        let ((_, _, _, Some v) as cfg') = eval env cfg a in
        (cfg', pvs @ [v])
      in
      fold_left arg_eval (config, []) args

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
            len_term
         );

      len_term:
        t:idx_term l:("." %"length" {0})? { match l with Some _ -> Length t | None -> t };

      idx_term:
        t:term ixs:(-"[" ix:expr -"]" {ix})* { fold_left (fun expr ix -> Elem (expr, ix)) t ixs };

      term:
          n:DECIMAL                              { Const n }
        | s:STRING                               { String (String.sub s 1 (String.length s - 2)) }
        | c:CHAR                                 { Const (Char.code c) }
        | "[" elems:!(Util.list0 expr) "]"       { Array elems }
        | "`" tag:IDENT
            vals:(-"(" !(Util.list expr) -")")?  { Sexp (tag, maybe_to_list vals) }
        | name:IDENT
            s:( "(" args:!(Util.list0 expr) ")"  { Call (name, args) }
              | empty                            { Var name }
              )                                  { s }
        | -"(" expr -")"
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
          parse:
              %"_"                                                { Wildcard }
            | "`" tag:IDENT args:(-"(" !(Util.list parse) -")")?  { Sexp (tag, maybe_to_list args) }
            | name:IDENT                                          { Ident name }
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

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a statement and a current continuation,
       and returns another configuration. The environment is the same as for expressions.
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let concat_prog p q =
      match (p, q) with
      | (Skip, Skip) -> Skip
      | (Skip, q')   -> q'
      | (p', Skip)   -> p'
      | (p', q')     -> Seq (p', q')

    let rec eval env ((sf, input, output, res) as config) e cont =
      match e with
      | Assign (x, ixs, e) ->
        let config', ix_vals = Expr.prep_args env config ixs in
        let (sf', i', o', Some v) = Expr.eval env config' e in
        eval env (update sf' x v ix_vals, i', o', None) cont Skip
      | Seq (s, s') ->
        eval env config s (concat_prog s' cont)
      | Skip ->
        (match cont with
         | Skip -> config
         | p    -> eval env config p Skip)
      | If (cond, the, els) ->
        let (sf', i', o', Some cond_v) = Expr.eval env config cond in
        eval env (sf', i', o', Some cond_v) (if Value.to_int cond_v == 1 then the else els) cont
      | While (cond, action) ->
        let (_, _, _, Some cond_v) as config' = Expr.eval env config cond in
        if Value.to_int cond_v = 1
        then eval env config' action (concat_prog e cont)
        else eval env config' cont Skip
      | Repeat (action, cond) ->
        let config' = eval env config action Skip in
        let (_, _, _, Some cond_v) as config' = Expr.eval env config' cond in
        if Value.to_int cond_v = 1
        then eval env config' cont Skip
        else eval env config' e cont
      | Return opt_expr ->
        (match opt_expr with
         | None   -> (sf, input, output, None)
         | Some e ->
           let (sf', i', o', sv) = Expr.eval env config e in
           (sf', i', o', sv))
      | Call (func, args) ->
        let config' = Expr.eval env config (Expr.Call (func, args)) in
        eval env config' cont Skip
      | Case (expr, branches) ->
        let (_, _, _, Some value) as config' = Expr.eval env config expr in
        let rec match_pattern sf v = function
          | Pattern.Wildcard       -> Some sf
          | Pattern.Ident name     -> Some (State.bind name v sf)
          | Pattern.Sexp (tag, ps) ->
            (match v with
             | Value.Sexp (vtag, vs) ->
               if (vtag <> tag) || (length ps <> length vs)
               then None
               else
                 let pvs = combine ps vs in
                 let matchp mb_sf (p, v) =
                   (match mb_sf with
                    | None -> None
                    | Some sf -> match_pattern sf v p)
                 in
                 fold_left matchp (Some sf) pvs
             | _ -> None)
        in
        let rec next_branch ((sf, i, o, r) as cfg) = function
          | [] -> failwith "error: mismatched pattern"
          | (pattern, br) :: bs ->
            (match match_pattern State.undefined value pattern with
             | None     -> next_branch cfg bs
             | Some sf' -> eval env (State.push sf sf' (Pattern.vars pattern), i, o, r) (Seq (br, Leave)) cont)
        in
        next_branch config' branches
      | Leave -> eval env (State.drop sf, input, output, res) cont Skip

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
          %"skip"                                                { Skip }
        | %"if" cond: !(Expr.parse) %"then" action:parse
              elif:(%"elif" !(Expr.parse) %"then" parse)*
              els:(%"else" parse)?
              %"fi"                                              { If (cond, action, elif_branch elif els) }
        | %"while" cond: !(Expr.parse) %"do" action:parse %"od"  { While (cond, action) }
        | %"repeat" action:parse %"until" cond: !(Expr.parse)    { Repeat (action, cond) }
        | %"return" opt_e: !(Expr.parse)?                        { Return opt_e }
        | %"for" init:parse "," cond: !(Expr.parse)
              "," inc:parse %"do" action:parse %"od"             { Seq (init, While (cond, Seq (action, inc))) }
        | name:IDENT
              s: ( ixs:(-"[" !(Expr.parse) -"]")* ":="
                   expr: !(Expr.parse)                           { Assign (name, ixs, expr) }
                 | "(" args: !(Util.list0 Expr.parse) ")"        { Call (name, args) }
                 )                                               { s }
        | %"case" expr:!(Expr.parse) %"of"
              branches:!(Util.listBy case_delim case_branch)
              %"esac"                                            { Case (expr, branches) }
        ;

      case_delim: -"|";

      case_branch:
          pat:!(Pattern.parse) -"->" br:parse                    { (pat, br) };

      sequence:
          head:statement -";" tail:parse          { Seq (head, tail) }
    )
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

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
    method define func (def: (string list * string list * Stmt.t)) = {< mp = M.add func def mp >}
    method definition func args ((sf, input, output, res) as config) =
      try
        let (params, locals, body) = M.find func mp in
        let param_vals = combine params args in
        let sf' = State.enter sf (params @ locals) in
        let sf' = fold_left (fun s (p, v) -> State.update p v s) sf' param_vals in
        let (sf', input', output', res') = Stmt.eval self (sf', input, output, res) body Skip in
        (State.leave sf' sf, input', output', res')
      with Not_found -> Builtin.eval config args func
  end

let eval (defs, body) i =
  let env = fold_left (fun e (f, d) -> e#define f d) (new def_env) defs in
  let (_, _, o, _) = Stmt.eval env (State.empty, i, [], None) body Skip in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
