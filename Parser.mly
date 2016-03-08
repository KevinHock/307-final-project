%{
open Ast;;


let parse_error s = (* Called by the parser function on error *)
  print_endline s;
  flush stdout
;;

let farr left_type bs = List.fold_left (fun t b -> Array(t, b) ) left_type bs
;;

%}

%token <int> NUM
%token <string> ID
%token <string> STRING
%token PLUS MINUS STAR DIVIDE UMINUS USTAR PLUSPLUS AMP
%token EQEQ LESS AND OR NOT TRUE FALSE
%token LBRACE RBRACE LBRACK RBRACK LPAR RPAR EQ SEMI COMMA COLON
%token INT VOID
%token IF THEN ELSE FUNCTION FOR WHILE SWITCH CASE BREAK CONTINUE RETURN PRINTSTR PRINTINT DEFAULT
%token EOF

%right PLUSPLUS UMINUS USTAR AMP NOT
%left PLUS MINUS STAR DIVIDE
%left EQEQ LESS AND OR

%left LBRACK LPAR

%start program
%type <Ast.program> program

%%

program:  mdecls mstmts EOF       { ($1, $2) }

ctype:    VOID                    { Void }
        | INT                     { Int }
        | ctype STAR              { Pointer $1 }
;

margs:                           { [] }
        | args                   { $1 }
;

args:   | exp                    { [$1] }
        | exp COMMA args         { $1::$3 }

exp:      exp PLUS exp           { Add ($1, $3) }
        | exp MINUS exp          { Sub ($1, $3) }
        | exp STAR exp           { Mul ($1, $3) }
        | exp DIVIDE exp         { Div ($1, $3) }
        | MINUS exp %prec UMINUS { Neg $2 }
        | ID                     { Id $1 }
        | NUM                    { IntConst $1 }
        | exp LBRACK exp RBRACK  { At ($1, $3) }
        | STAR exp %prec USTAR   { Deref $2 }
        | AMP exp                { AddressOf $2 }
        | ID LPAR margs RPAR     { Call ($1, $3) }
        | exp PLUSPLUS          { Post $1 }
        | PLUSPLUS exp          { Pre $2 }
        | LPAR exp RPAR          { $2 }
;

cond:     exp EQEQ exp           { Equal ($1, $3) }
        | exp LESS exp           { Less ($1, $3) }
        | cond AND cond          { And ($1, $3) }
        | cond OR cond           { Or ($1, $3) }
        | NOT cond               { Not ($2) }
        | TRUE                   { True }
        | FALSE                  { False }
        | LPAR cond RPAR         { $2 }

mdecls:         { [] }
        | decls { $1 }
;
decls:    decl       { [$1] }
        | decl decls { $1::$2 }
;
decl:     ctype ID brackets SEMI { VarDecl(farr $1 $3, $2) }
        | ctype ID LPAR margns RPAR LBRACE mdecls mstmts return RBRACE { 
            FunDecl ($1,$2,$4, (List.map (fun  (VarDecl x) -> x) $7),$8,$9) 
          }
;

mstmts:         { [] }
        | stmts { $1 }
;
stmts:    stmt { [$1] }
        | stmt stmts { $1::$2 }
;

stmt:   | SEMI                             { Empty }
        | exp SEMI                         { Expr $1 }
        | exp EQ exp SEMI                  { VarAss ($1, $3) } 
        | IF LPAR cond RPAR stmt           { IfThen ($3, $5) }
        | IF LPAR cond RPAR stmt ELSE stmt { IfThenElse ($3, $5, $7) }
        | SWITCH LPAR exp RPAR LBRACE cases RBRACE { let (cases, def) = $6 in Switch ($3, cases, def) }
        | WHILE LPAR cond RPAR stmt        { While ($3, $5) }
        | FOR LPAR stmt cond SEMI stmt RPAR stmt { For ($3, $4, $6, $8) }
        | BREAK SEMI                       { Break }
        | CONTINUE SEMI                    { Continue }
        | PRINTSTR LPAR STRING RPAR SEMI   { PrintStr $3 }
        | PRINTINT LPAR exp RPAR SEMI      { PrintInt $3 }
        | LBRACE stmts RBRACE              { List $2 }
;

return:   RETURN exp SEMI { $2 }
        | RETURN SEMI { IntConst 0 }
;

brackets:                               { [] }
          | LBRACK NUM RBRACK brackets  { $2::$4 }
;

cases:    CASE NUM COLON stmts default { ([($2,$4)],$5) }
        | CASE NUM COLON stmts cases   { let (xs,def) = $5 in (($2,$4)::xs,def) }
;

default:  DEFAULT COLON stmts { $3 }
;

margns:                            { [] }
        | argns                    { $1 }
;

argns:    ctype ID                 { [($1,$2)] }
        | ctype ID COMMA argns     { ($1,$2)::$4 }
;

%%
