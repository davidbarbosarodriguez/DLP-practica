
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token IN
%token CONCAT
%token LBRACE
%token RBRACE
%token COMMA
%token HASH
%token BOOL
%token NAT
%token STRING
%token QUIT
%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token COLON
%token ARROW
%token EOF

%token <int> INTV
%token <string> IDV
%token <string> STRINGV

%start s
%type <Lambda.command> s

%%

s :
    IDV EQ term EOF       
      { Bind ($1, $3) } 
    | IDV EQ ty EOF       
      { BindTy ($1, $3) }    
    | term EOF            
        { Eval $1 }
    | QUIT EOF           
        { Quit }   
    ;       


term :
    appTerm         
      { $1 }
  | IF term THEN term ELSE term 
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term   
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term   
      { TmLetIn ($2, $4, $6) }
  | LETREC IDV COLON ty EQ term IN term 
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }


appTerm :
    atomicTerm      
      { $1 }
  | SUCC atomicTerm 
      { TmSucc $2 }
  | PRED atomicTerm 
      { TmPred $2 }
  | ISZERO atomicTerm 
      { TmIsZero $2 }
  | CONCAT atomicTerm atomicTerm
      { TmConcat ($2, $3) }
  | appTerm atomicTerm  
      { TmApp ($1, $2) }


atomicTerm :
    LPAREN term RPAREN 
      { $2 }
  | TRUE 
      { TmTrue }
  | FALSE 
      { TmFalse }
  | IDV 
      { TmVar $1 }
  | INTV 
      { let rec f = function  
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | STRINGV
      { TmString $1 }
      
  |LBRACE term_reg_list RBRACE
      {TmRcd (List.rev $2) }

  |LBRACE term_list_rev RBRACE
      { TmTuple (List.rev $2) }

  | atomicTerm DOT IDV
      { TmProj ($1, $3) }
  | atomicTerm DOT INTV
      { TmProj ($1, string_of_int $3) }
ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty 
      { TyArr ($1, $3) }

atomicTy :
    LPAREN ty RPAREN 
      { $2 }
  | BOOL 
      { TyBool }
  | NAT 
      { TyNat }
  | STRING
      { TyString }
  | IDV
      { TyVar $1 }
  | LBRACE ty_list_rev RBRACE
      { TyTuple (List.rev $2) }
  | LBRACE ty_reg_list RBRACE
      { TyRcd (List.rev $2) }

 
term_reg_list:
    IDV EQ term                         { [($1, $3)] }
  | term_reg_list COMMA IDV EQ term     { ($3, $5) :: $1 }


ty_reg_list:
    IDV COLON ty                        { [($1, $3)] }
  | ty_reg_list COMMA IDV COLON ty      { ($3, $5) :: $1 }



term_list_rev :
      term
        { [$1] }
    | term_list_rev COMMA term
        { $3 :: $1 }

ty_list_rev :
      ty
        { [$1] }
    | ty_list_rev COMMA ty
        { $3 :: $1 }