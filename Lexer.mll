{
open Parser;;
}

rule token = parse
  | '/''/'[^'\n']* { token lexbuf }
  | [' ' '\t' '\n'] { token lexbuf }
  | "++"   { PLUSPLUS }
  | '+'   { PLUS }
  | '-'   { MINUS }
  | '*'   { STAR }
  | '/'   { DIVIDE }
  | '&'   { AMP }
  | "=="  { EQEQ }
  | '='   { EQ }
  | '<'   { LESS }
  | "&&"  { AND }
  | "||"  { OR }
  | "!"   { NOT }
  | "true" { TRUE }
  | "false" { FALSE }
  | '['   { LBRACK }
  | ']'   { RBRACK }
  | '{'   { LBRACE }
  | '}'   { RBRACE }
  | '('   { LPAR }
  | ')'   { RPAR }
  | ';'   { SEMI }
  | ','   { COMMA }
  | ':'   { COLON }
  | "int" { INT }
  | "void" { VOID }
  | "if"  { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "function" { FUNCTION }
  | "for"  { FOR }
  | "while" { WHILE }
  | "switch" { SWITCH }
  | "case" { CASE }
  | "break" { BREAK }
  | "continue" { CONTINUE }
  | "default" { DEFAULT }
  | "return" { RETURN }
  | "print_str" { PRINTSTR }
  | "print_int" { PRINTINT }
  | (['1'-'9']['0'-'9']*|'0') as num { NUM (int_of_string num) }
  | ['_' 'a'-'z' 'A'-'Z']['_' 'a'-'z' 'A'-'Z' '0'-'9']* as s { ID s }
  | '"'([^'"']*)'"' as s { STRING (String.sub s 1 (String.length s - 2)) }
  | eof { EOF }
