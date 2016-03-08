type ctype = (* Types in C-flat language *)
  Void
| Int
| Array of ctype * int
| Pointer of ctype
;;

type varkind = Static | Param | Local

type vardecl = (* Variable decl in C-flat: includes type and name of variable *)
  ctype * string;;
    
type expr = (* Expressions in C-flat *)

  (* int operations *)
  Add of expr * expr
| Sub of expr * expr
| Mul of expr * expr
| Div of expr * expr
| Neg of expr

  (* constants/variables *)
| Id of string
| IntConst of int

  (* array/pointer operations *)
| At of expr * expr
| Deref of expr
| AddressOf of expr

  (* function *)
| Call of string * expr list

  (* pre- & post-increment *)
| Pre of expr
| Post of expr
;;

type cond = (* Conditions are like expressions over booleans *)
  Equal of expr * expr
| Less of expr * expr
(* missing more, lessorequal, etc. Let's leave them out *)

| And of cond * cond
| Or of cond * cond
| Not of cond

| True
| False
;;

type stmt = (* Statements in C-flat language *)
  Empty 
| VarAss of expr * expr

(* Expressions can be statements in themselves. This is most useful when
   the expression is a function call. Calls to built-in functions are
   just special cases of calls. *)
| Expr of expr 
| PrintStr of string (* string is only static! *)
| PrintInt of expr (* expr should be int *)

(* Control Flow *)
| IfThen of cond * stmt
| IfThenElse of cond * stmt * stmt
| Switch of expr * (int * stmt list) list * stmt list 
  (* Switch (cond, cases, default) *)

| While of cond * stmt
| For of stmt * cond * stmt * stmt

| Break (* used in switch, while and for *)
| Continue (* used in while and for *)

(* nested statements *)
| List of stmt list 
;;

type decl = (* Declarations in C-flat *)
| VarDecl of vardecl
| FunDecl of ctype * string * vardecl list * vardecl list * stmt list * expr
    (* arguments are: function return type, name of the function, 
       formal parameter list, local variable list, function body, and the
       expression whose value is returned at the end of function execution *)
;;

type program = decl list * stmt list;;
