open Ast;;
open Store;;

(* Processor state captures the state of the processors. It can store the
   contents of a processor registers and flags, if you are working with
   a real processor. Here, we are working with an abstract machine, and
   it needs to keep track of only a few things -- base pointer and
   stack pointer in this assignment. *)

type proc_state = {bp: int; sp: int;};;

(* functions to create a symbol table to pass around during evaluation. *)

type varEntry = {
  vtype: ctype;
  kind: varkind;
  loc: location; (* Location contains absolute memory location for static *)
                 (* variables, and offset from base of AR for local vars. *)
};;

type funEntry = {
  ftype: ctype;
  syms: symTable;
  nlocals: int;
  body: stmt list;
  rv: expr
}

and symEntry = Var of varEntry | Fun of funEntry
and symTable = (string * symEntry) list
type environment = symTable list;;
type interpreter_state = {ps: proc_state; env: environment; store: store};;

let procVarDecl (vkind, symTab) (typ, name) = 
  let ventry = Var({vtype=typ; kind=vkind; loc= -1})
  in
  (vkind, symTab @ [(name, ventry)])

let procVarDecls vkind symTab decls = 
  List.fold_left procVarDecl (vkind, symTab) decls

let procDecl symTab decl = match decl with
  | VarDecl (typ, name) -> 
    let (_, symTab') = procVarDecl (Static, symTab) (typ, name) 
    in symTab'
  | FunDecl (typ, name, paramDecls, localDecls, stmts, expr) ->
    let (_, fnSymTab1) = procVarDecls Param [] paramDecls in
    let (_,  fnSymTab) = procVarDecls Local fnSymTab1 localDecls in
    let   fnEntry = Fun({ftype=typ; syms=fnSymTab; 
                         nlocals=List.length localDecls; body=stmts; rv=expr}) in
    symTab @ [(name, fnEntry)]

let procDecls decls = List.fold_left procDecl [] decls
;;

let initEnv decls = [(procDecls decls)];;

let binding_of env name = 
  let lookup name symTab = List.assoc name symTab in
  try 
    lookup name (List.hd env)
  with Not_found ->
    lookup name (List.hd (List.tl env))
;;

let enter_scope env scope = scope::env;;
let exit_scope env = List.tl env;;
let current_scope env = List.hd env;;
