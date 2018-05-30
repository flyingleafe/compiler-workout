open GT
open Language
open List

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
     | CONST n   -> eval env (cstack, (Value.of_int n) :: stack, in_env) ops
     | STRING s  -> eval env (cstack, (Value.of_string s) :: stack, in_env) ops
     | LD x      -> eval env (cstack, State.eval sf x :: stack, in_env) ops
     | ST x      -> eval env (cstack, tl stack, (State.update x (hd stack) sf, input, output)) ops
     | LABEL _   -> eval env config ops
     | JMP label -> eval env config (env#labeled label)
     | STA (xs, n) ->
       let v :: ixs, stack' = split_list (n + 1) stack in
       eval env (cstack, stack', (Stmt.update sf xs v ixs, input, output)) ops
     | CJMP (cond, label) ->
       eval env (cstack, tl stack, in_env)
         (if check_cond (Value.to_int @@ hd stack) cond then (env#labeled label) else ops)
     | BEGIN (_, args, locals) ->
       let arg_vals, stack' = split_list (length args) stack in
       let sf' = State.enter sf (args @ locals) in
       let sf' = fold_left (fun s (p, v) -> State.update p v s) sf' (combine args arg_vals) in
       eval env (cstack, stack', (sf', input, output)) ops
     | END | RET _ -> (match cstack with
         | (prg, sf') :: cstack' -> eval env (cstack', stack, (State.leave sf sf', input, output)) prg
         | []                    -> config)
     | CALL (func, n_args, is_ret) ->
       if env#is_label func
       then eval env ((ops, sf) :: cstack, stack, in_env) (env#labeled func)
       else eval env (env#builtin config func n_args is_ret) ops
     | BINOP op  ->
       let y :: x :: rest = stack in
       let res = Expr.eval_op op (Value.to_int x) (Value.to_int y) in
       eval env (cstack, (Value.of_int res) :: rest, (sf, input, output)) ops
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split_list n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) args f in
           let stack'' = if not p then stack' else let Some r = r in r::stack' in
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
class labels =
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
  end

let rec compile_expr e =
  match e with
  | Expr.Const n -> [CONST n]
  | Expr.String s -> [STRING s]
  | Expr.Array xs -> prep_args xs @ [CALL ("$array", length xs, true)]
  | Expr.Var x -> [LD x]
  | Expr.Binop (op, a, b) -> compile_expr a @ compile_expr b @ [BINOP op]
  | Expr.Elem (arr, ix) -> compile_expr ix @ compile_expr arr @ [CALL ("$elem", 2, true)]
  | Expr.Length ls -> compile_expr ls @ [CALL ("$length", 1, true)]
  | Expr.Call (func, args) -> prep_args args @ [CALL (func, length args, true)]
and prep_args args =
  concat (rev_map compile_expr args)

let rec compile_stmt lbls st =
  match st with
  | Stmt.Assign (x, [], e)   -> lbls, compile_expr e @ [ST x]
  | Stmt.Assign (x, ixs, e)  -> lbls, prep_args ixs @ compile_expr e @ [STA (x, length ixs)]
  | Stmt.Skip                -> lbls, []
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
  | Stmt.Return opt_v ->
    let value_code =
      (match opt_v with
        | None   -> []
        | Some v -> compile_expr v) in
    lbls, value_code @ [RET (opt_v <> None)]
  | Stmt.Call (func, args) ->
    lbls, prep_args args @ [CALL (func, length args, false)]
  | Stmt.Seq (s, s') ->
    let lbls1, fst = compile_stmt lbls s in
    let lbls2, snd = compile_stmt lbls1 s' in
    lbls2, fst @ snd

let check_end prg =
  match hd (rev prg) with
  | END -> []
  | _ -> [END]

let compile_def lbls (func, (params, locals, body)) =
  let lbls', cbody = compile_stmt lbls body in
  lbls', [LABEL func; BEGIN (func, params, locals)] @ cbody @ check_end cbody

let compile (defs, st) =
  let lbls = new labels in
  let lbls, main = compile_stmt lbls st in
  let compile_and_combine (lbls', prev) def =
    let lbls', prg = compile_def lbls' def in
    lbls', prev @ prg
  in
  let _, funcs = fold_left compile_and_combine (lbls, []) defs in
  main @ check_end main @ funcs
