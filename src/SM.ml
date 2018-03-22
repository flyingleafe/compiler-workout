open GT
open Language
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* put a constant to stack         *) | CONST of int
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)
let check_cond x = function
  | "true"  -> x <> 0
  | "false" -> x = 0
  | _       -> failwith "Invalid condition type"

let rec eval env ((stack, ((sf, input, output) as in_env)) as config) = function
  | [] -> config
  | op :: ops ->
    (match op with
     | READ      -> eval env (hd input :: stack, (sf, tl input, output)) ops
     | WRITE     -> eval env (tl stack, (sf, input, output @ [hd stack])) ops
     | CONST n   -> eval env (n :: stack, in_env) ops
     | LD x      -> eval env (sf x :: stack, in_env) ops
     | ST x      -> eval env (tl stack, (Expr.update x (hd stack) sf, input, output)) ops
     | LABEL _   -> eval env config ops
     | JMP label -> eval env config (env#labeled label)
     | CJMP (cond, label) ->
       eval env config
         (if check_cond (hd stack) cond then (env#labeled label) else ops)
     | BINOP op  ->
       let y :: x :: rest = stack
       in (Expr.eval_op op x y :: rest, (sf, input, output))
    )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
class labels =
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
  end

let rec compile_expr e =
  match e with
  | Expr.Const n -> [CONST n]
  | Expr.Var x -> [LD x]
  | Expr.Binop (op, a, b) -> compile_expr a @ compile_expr b @ [BINOP op]

let rec compile' lbls st =
  match st with
  | Stmt.Read x        -> lbls, [READ; ST x]
  | Stmt.Write e       -> lbls, compile_expr e @ [WRITE]
  | Stmt.Assign (x, e) -> lbls, compile_expr e @ [ST x]
  | Stmt.Skip          -> lbls, []
  | Stmt.If (cond, the, els) ->
    let lbl_els, lbls' = lbls#new_label in
    let lbl_end, lbls1 = lbls'#new_label in
    let cond_code = compile_expr cond in
    let lbls2, the_code = compile' lbls1 the in
    let lbls3, els_code = compile' lbls2 els in
    let end_jump, end_label =
      (match els_code with [] -> [], [] | _ -> [JMP lbl_end], [LABEL lbl_end]) in
    lbls3,
    cond_code @ [CJMP ("false", lbl_els)] @ the_code @ end_jump @
    [LABEL lbl_els] @ els_code @ end_label
  | Stmt.While (cond, action) ->
    let lbl_begin, lbls' = lbls#new_label in
    let lbl_end, lbls1 = lbls'#new_label in
    let cond_code = compile_expr cond in
    let lbls2, act_code = compile' lbls1 action in
    lbls2,
    [LABEL lbl_begin] @ cond_code @ [CJMP ("false", lbl_end)] @
    act_code @ [JMP lbl_begin] @ [LABEL lbl_end]
  | Stmt.Repeat (action, cond) ->
    let lbl_begin, lbls' = lbls#new_label in
    let lbls1, act_code = compile' lbls' action in
    let cond_code = compile_expr cond in
    lbls1,
    [LABEL lbl_begin] @ act_code @ cond_code @ [CJMP ("true", lbl_begin)]
  | Stmt.Seq (s, s') ->
    let lbls1, fst = compile' lbls s in
    let lbls2, snd = compile' lbls1 s' in
    lbls2, fst @ snd

let compile st = let _, prog = compile' (new labels) st in prog
