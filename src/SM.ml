open GT
open Syntax
open List

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* put a constant to stack         *) | CONST of int
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let eval_one (stack, sf, input, output) op =
  match op with
  | READ -> (hd input :: stack, sf, tl input, output)
  | WRITE -> (tl stack, sf, input, hd stack :: output)
  | CONST n -> (n :: stack, sf, input, output)
  | LD x -> (sf x :: stack, sf, input, output)
  | ST x -> (tl stack, Expr.update x (hd stack) sf, input, output)
  | BINOP op ->
    let x :: y :: rest = stack
    in (Expr.eval_op op x y :: rest, sf, input, output)

let eval cfg = fold_left eval_one cfg

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile_expr e =
  match e with
  | Expr.Const n -> [CONST n]
  | Expr.Var x -> [LD x]
  | Expr.Binop (op, a, b) -> compile_expr a @ compile_expr b @ [BINOP op]

let rec compile st =
  match st with
  | Stmt.Read x -> [READ; ST x]
  | Stmt.Write e -> compile_expr e @ [WRITE]
  | Stmt.Assign (x, e) -> compile_expr e @ [ST x]
  | Stmt.Seq (s, s') -> compile s @ compile s'
