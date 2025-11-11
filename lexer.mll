
{
  open Parser;;
  exception Lexical_error;;
}

rule token = parse
    [' ' '\t']  { token lexbuf }
  | "lambda"    { LAMBDA }
  | "L"         { LAMBDA }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "succ"      { SUCC }
  | "pred"      { PRED }
  | "iszero"    { ISZERO }
  | "let"       { LET }
  | "letrec"    { LETREC }
  | "in"        { IN }
  | "Bool"      { BOOL }
  | "Nat"       { NAT }
  | "String"    { STRING }
  | "quit"      { QUIT }
  | "concat"    { CONCAT } 
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '['         { LBRACKET }
  | ']'         { RBRACKET }
  | '{'         { LBRACE }
  | '}'         { RBRACE }
  | ','         { COMMA }
  | '#'        { HASH }
  | '.'         { DOT }
  | '<'         { LT }
  | '>'         { GT }
  | '|'        { PIPE }
  | "as"      { AS }
  | "case"    { CASE }
  | "of"      { OF }
  | "=>"     { DARROW }
  | "List"    { LIST }
  | "nil"     { NIL }
  | "cons"    { CONS }
  | "isnil"   { ISNIL }
  | "head"    { HEAD }
  | "tail"    { TAIL }
  | '='         { EQ }
  | ':'         { COLON }
  | "->"        { ARROW }
  | ['0'-'9']+  { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | ['a'-'z' 'A'-'Z']['a'-'z' '_' '0'-'9']*
                { IDV (Lexing.lexeme lexbuf) }
  | '"' ([^'"']*) '"'
                { let s = Lexing.lexeme lexbuf in
                  STRINGV (String.sub s 1 ((String.length s) - 2)) }
  
  | eof         { EOF }
  | _           { raise Lexical_error }

