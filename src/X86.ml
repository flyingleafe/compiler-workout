(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd =
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl"
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM
open List

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let div_res_reg = function
  | "/" -> eax
  | "%" -> edx
  | _   -> failwith "Wrong division operation"

let comp_flag = function
  | "==" -> "e"
  | "!=" -> "ne"
  | "<=" -> "le"
  | "<"  -> "l"
  | ">=" -> "ge"
  | ">"  -> "g"
  | _    -> failwith "Wrong comparison operator"

let if_register pos the els =
  match pos with
  | R _ -> the
  | _   -> els

let compile_binop env op =
  let opB, opA, env = env#pop2 in
  let res, env = env#allocate in
  match op with
  | "+" | "-" | "*" ->
    env, [Mov (opA, eax); Binop (op, opB, eax); Mov (eax, res)]
  | "/" | "%" ->
    env, [Mov (opA, eax); Cltd; IDiv opB; Mov (div_res_reg op, res)]
  | "==" | "!=" | "<=" | "<" | ">=" | ">" ->
    env, [Binop ("^", eax, eax); Mov (opA, edx); Binop ("cmp", opB, edx);
          Set (comp_flag op, "%al"); Mov (eax, res)]
  | "!!" ->
    env, [Binop ("^", eax, eax); Mov (opA, edx); Binop ("!!", opB, edx);
          Set ("nz", "%al"); Mov (eax, res)]
  | "&&" ->
    env, [Binop ("^", eax, eax); Binop ("cmp", opA, eax); Set ("ne", "%al");
          Binop ("^", edx, edx); Binop ("cmp", opB, edx); Set ("ne", "%dl");
          Binop ("&&", edx, eax); Mov (eax, res)]
  | _ -> failwith "Not supported operation"

let compile_instr env = function
  | CONST n ->
    let pos, env = env#allocate in
    env, [Mov (L n, pos)]
  (* | READ ->
   *   let pos, env = env#allocate in
   *   env, [Call "Lread"; Mov (eax, pos)]
   * | WRITE ->
   *   let pos, env = env#pop in
   *   env, [Push pos; Call "Lwrite"; Pop eax] *)
  | LD name ->
    let pos, env = (env#try_global name)#allocate in
    let mem_pos = env#loc name in
    env, if_register pos
      [Mov (mem_pos, pos)]
      [Mov (mem_pos, eax); Mov (eax, pos)]
  | ST name ->
    let pos, env = (env#try_global name)#pop in
    let mem_pos = env#loc name in
    env, if_register pos
      [Mov (pos, mem_pos)]
      [Mov (pos, eax); Mov (eax, mem_pos)]
  | LABEL label ->
    env, [Label label]
  | JMP label ->
    env, [Jmp label]
  | CJMP (cond, label) ->
    let pos, env = env#pop in
    env, [Binop ("cmp", L 0, pos); CJmp (cond, label)]
  | BEGIN (name, args, locals) ->
    let env' = env#enter name args locals in
    env', [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env'#lsize), esp)]
  | END ->
    env, [Label env#epilogue; Mov (ebp, esp); Pop ebp; Ret;
          Meta (Printf.sprintf "\t.set\t%s,\t%d" env#lsize (env#allocated * word_size))]
  | CALL (name, n_args, is_ret) ->
    let regs = env#live_registers in
    let save_regs = map (fun x -> Push x) regs in
    let restore_regs = rev_map (fun x -> Pop x) regs in
    let env', push_args =
      let rec go env acc = function
        | 0 -> env, acc
        | n -> let pos, env = env#pop in
          go env ((Push pos) :: acc) (n - 1)
      in go env [] n_args
    in
    let pop_args =
      if n_args > 0
      then [Binop ("+", L (n_args * word_size), esp)]
      else []
    in
    let env'', ending =
      if is_ret
      then let res, env'' = env'#allocate in env'', [Mov (eax, res)]
      else env', []
    in
    env'', save_regs @ push_args @ [Call name] @ pop_args @ restore_regs @ ending
  | RET is_ret ->
    let env', val_ret =
      if is_ret
      then let pos, env' = env#pop in env', [Mov (pos, eax)]
      else env, []
    in env', val_ret @ [Jmp env'#epilogue]
  | BINOP op -> compile_binop env op

(* Compiles a unit: generates x86 machine code for the stack program and surrounds it
   with function prologue/epilogue
*)
(*
let compile_unit env scode =
  let env, code = compile env scode in
  env,
  ([Push ebp; Mov (esp, ebp); Binop ("-", L (word_size*env#allocated), esp)] @
   code @
   [Mov (ebp, esp); Pop ebp; Binop ("^", eax, eax); Ret]
  )
*)

let rec compile env = function
  | [] -> env, []
  | instr :: code ->
    let env, asm = compile_instr env instr in
    let env, asm' = compile env code in
    env, asm @ asm'

(* A set of strings *)
module S = Set.Make (String)

(* List.init implementations (too lazy to update OCaml to 4.04+) *)

let list_init n f =
  let rec go acc k =
    if k < n then go (f k :: acc) (k + 1) else acc
  in rev (go [] 0)

(* Environment implementation *)
let make_assoc l = combine l (list_init (length l) (fun x -> x))

class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)

    (* gets a name for a global variable *)
    method loc x =
      try S (- (assoc x args)  -  1)
      with Not_found ->
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)

    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+2
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a global variable in the environment, if it's not local *)
    method try_global x = match self#loc x with
      | M _ -> self#global x
      | _   -> self

    (* gets all global variables *)
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots

    (* enters a function *)
    method enter f a l =
      {< stack_slots = length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname

    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      filter (function R _ -> true | _ -> false) stack

  end

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in
  let asm = Buffer.create 1024 in
  iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
