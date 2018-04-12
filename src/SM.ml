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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let check_cond x = function
  | "nz" -> x <> 0
  | "z"  -> x = 0
  | _    -> failwith "Invalid condition type"

let rec split_list n l =
  if n = 0 then [], l else
    (match l with
     | []    -> failwith ("List length mismatch: list length is less than " ^ string_of_int n)
     | x::xs -> let ys, zs = split_list (n - 1) xs in x::ys, zs)

let rec eval env ((cstack, stack, ((sf, input, output) as in_env)) as config) = function
  | [] -> config
  | op :: ops ->
    (match op with
     | READ      -> eval env (cstack, hd input :: stack, (sf, tl input, output)) ops
     | WRITE     -> eval env (cstack, tl stack, (sf, input, output @ [hd stack])) ops
     | CONST n   -> eval env (cstack, n :: stack, in_env) ops
     | LD x      -> eval env (cstack, State.eval sf x :: stack, in_env) ops
     | ST x      -> eval env (cstack, tl stack, (State.update x (hd stack) sf, input, output)) ops
     | LABEL _   -> eval env config ops
     | JMP label -> eval env config (env#labeled label)
     | CJMP (cond, label) ->
       eval env (cstack, tl stack, in_env)
         (if check_cond (hd stack) cond then (env#labeled label) else ops)
     | BEGIN (args, locals) ->
       let arg_vals, stack' = split_list (length args) stack in
       let sf' = State.enter sf (args @ locals) in
       let sf' = fold_left (fun s (p, v) -> State.update p v s) sf' (combine args arg_vals) in
       eval env (cstack, stack', (sf', input, output)) ops
     | END -> (match cstack with
         | (prg, sf') :: cstack' -> eval env (cstack', stack, (State.leave sf sf', input, output)) prg
         | []                    -> config)
     | CALL func ->
       eval env ((ops, sf) :: cstack, stack, in_env) (env#labeled func)
     | BINOP op  ->
       let y :: x :: rest = stack
       in eval env (cstack, Expr.eval_op op x y :: rest, (sf, input, output)) ops
    )

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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

let rec compile_stmt lbls st =
  match st with
  | Stmt.Read x        -> lbls, [READ; ST x]
  | Stmt.Write e       -> lbls, compile_expr e @ [WRITE]
  | Stmt.Assign (x, e) -> lbls, compile_expr e @ [ST x]
  | Stmt.Skip          -> lbls, []
  | Stmt.If (cond, the, els) ->
    let lbl_els, lbls' = lbls#new_label in
    let lbl_end, lbls1 = lbls'#new_label in
    let cond_code = compile_expr cond in
    let lbls2, the_code = compile_stmt lbls1 the in
    let lbls3, els_code = compile_stmt lbls2 els in
    let end_jump, end_label =
      (match els_code with [] -> [], [] | _ -> [JMP lbl_end], [LABEL lbl_end]) in
    lbls3,
    cond_code @ [CJMP ("z", lbl_els)] @ the_code @ end_jump @
    [LABEL lbl_els] @ els_code @ end_label
  | Stmt.While (cond, action) ->
    let lbl_begin, lbls' = lbls#new_label in
    let lbl_end, lbls1 = lbls'#new_label in
    let cond_code = compile_expr cond in
    let lbls2, act_code = compile_stmt lbls1 action in
    lbls2,
    [LABEL lbl_begin] @ cond_code @ [CJMP ("z", lbl_end)] @
    act_code @ [JMP lbl_begin] @ [LABEL lbl_end]
  | Stmt.Repeat (action, cond) ->
    let lbl_begin, lbls' = lbls#new_label in
    let lbls1, act_code = compile_stmt lbls' action in
    let cond_code = compile_expr cond in
    lbls1,
    [LABEL lbl_begin] @ act_code @ cond_code @ [CJMP ("z", lbl_begin)]
  | Stmt.Call (func, args) ->
    let args_prepare = concat (rev_map compile_expr args) in
    lbls, args_prepare @ [CALL func]
  | Stmt.Seq (s, s') ->
    let lbls1, fst = compile_stmt lbls s in
    let lbls2, snd = compile_stmt lbls1 s' in
    lbls2, fst @ snd

let compile_def lbls (func, (params, locals, body)) =
  let lbls', cbody = compile_stmt lbls body in
  lbls', [LABEL func; BEGIN (params, locals)] @ cbody @ [END]

let compile (defs, st) =
  let lbls = new labels in
  let lbls, main = compile_stmt lbls st in
  let compile_and_combine (lbls', prev) def =
    let lbls', prg = compile_def lbls' def in
    lbls', prev @ prg
  in
  let _, funcs = fold_left compile_and_combine (lbls, []) defs in
  [LABEL "main"] @ main @ [END] @ funcs
