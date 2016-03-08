open Ast;;
open Env;;
open Store;;
open Eval;;

(* main evaluation functions *)
let parse_file f = 
  let chan = open_in f in
  let lexbuf = Lexing.from_channel chan in
  Parser.program Lexer.token lexbuf
;;

let main =
  (* first arg is cflat input file *)
  let (decls, stmts) = parse_file Sys.argv.(1) in
  (* create the symbol table first *)
  let env = initEnv decls in
  let env' = (allocateMem env) in
  let ps = {bp=10000; sp=10000} (*TODO use the right value*) in
  eval_stmt (List stmts) ps env' IntMap.empty;;
