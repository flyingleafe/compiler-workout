open GT
open Language
open List

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
(* leaves a scope                  *) | LEAVE   with show

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
     | DROP      -> eval env (cstack, tl stack, in_env) ops
     | DUP       -> eval env (cstack, (hd stack) :: stack, in_env) ops
     | SWAP      -> let x::y::rest = stack in eval env (cstack, y::x::rest, in_env) ops
     | LEAVE     -> eval env (cstack, stack, (State.drop sf, input, output)) ops
     | ENTER xs ->
       let vs, stack' = split_list (length xs) stack in
       let bind s (x, v) = State.bind x v s in
       let sf' = fold_left bind State.undefined (combine xs vs) in
       eval env (cstack, stack', (State.push sf sf' xs, input, output)) ops
     | SEXP (tag, n) ->
       let vs, stack' = split_list n stack in
       eval env (cstack, (Value.sexp tag vs) :: stack', in_env) ops
     | TAG t ->
       let res = (match hd stack with
           | Value.Sexp (t', _) when t = t' -> 1
           | _ -> 0) in
       eval env (cstack, (Value.of_int res) :: tl stack, in_env) ops
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

(*
let compile (defs, p) =
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse _ = failwith "Not implemented"
  and bindings p = failwith "Not implemented"
  and expr e = failwith "Not implemented" in
  let rec compile_stmt l env stmt =  failwith "Not implemented" in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
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
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)
*)

class labels =
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
  end

let rec compile_expr = function
  | Expr.Const n -> [CONST n]
  | Expr.String s -> [STRING s]
  | Expr.Array xs -> prep_args xs @ [CALL (".array", length xs, true)]
  | Expr.Sexp (tag, xs) -> prep_args xs @ [SEXP (tag, length xs)]
  | Expr.Var x -> [LD x]
  | Expr.Binop (op, a, b) -> compile_expr a @ compile_expr b @ [BINOP op]
  | Expr.Elem (arr, ix) -> compile_expr ix @ compile_expr arr @ [CALL (".elem", 2, true)]
  | Expr.Length ls -> compile_expr ls @ [CALL (".length", 1, true)]
  | Expr.Call (func, args) -> prep_args args @ [CALL (func, length args, true)]
and prep_args args =
  concat (rev_map compile_expr args)

let rec compile_pattern lbl_end = function
  | Stmt.Pattern.Wildcard       -> [DROP]
  | Stmt.Pattern.Ident _        -> [DROP]
  | Stmt.Pattern.Sexp (tag, ps) ->
    let unpack i p = [DUP; CONST i; SWAP; CALL (".elem", 2, true)] @
                     compile_pattern lbl_end p
    in
    let unpacked = concat @@ mapi unpack ps in
    [DUP; TAG tag; CJMP ("z", lbl_end)] @ unpacked

let rec compile_bind = function
  | Stmt.Pattern.Wildcard       -> [DROP]
  | Stmt.Pattern.Ident _        -> [SWAP]
  | Stmt.Pattern.Sexp (tag, ps) ->
    let unpack i p = [DUP; CONST i; SWAP; CALL (".elem", 2, true)] @
                     compile_bind p
    in
    concat (mapi unpack ps) @ [DROP]

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
  | Stmt.Case (expr, branches) ->
    let expr_code = compile_expr expr in
    let lbl_end, lbls' = lbls#new_label in
    let lbls'', code = fold_left (compile_case_branch lbl_end) (lbls', expr_code) branches in
    lbls'', code @ [LABEL lbl_end]

and compile_case_branch lbl_end (lbls, prev) (pat, st) =
  let next_br_lbl, lbls' = lbls#new_label in
  let pat_code = compile_pattern next_br_lbl pat in
  let bind_code = compile_bind pat @ [ENTER (Stmt.Pattern.vars pat)] in
  let lbls'', br_code = compile_stmt lbls' st in
  lbls'', prev @ pat_code @ bind_code @ br_code @ [LEAVE; JMP lbl_end; LABEL next_br_lbl]

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
