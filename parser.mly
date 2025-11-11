
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
%token LT
%token GT
%token PIPE
%token AS
%token CASE
%token OF
%token DARROW
%token LBRACKET
%token RBRACKET
%token LIST
%token NIL
%token CONS
%token ISNIL
%token HEAD
%token TAIL
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
  | CASE term OF case_branches_rev 
      { TmCase ($2, List.rev $4) }


appTerm :
    auxiliaryTerm      
      { $1 }
  | SUCC auxiliaryTerm 
      { TmSucc $2 }
  | PRED auxiliaryTerm 
      { TmPred $2 }
  | ISZERO auxiliaryTerm 
      { TmIsZero $2 }
  | CONCAT auxiliaryTerm auxiliaryTerm
      { TmConcat ($2, $3) }
  | NIL LBRACKET ty RBRACKET
      { TmNil $3 }
  | CONS LBRACKET ty RBRACKET auxiliaryTerm auxiliaryTerm
      { TmCons ($3, $5, $6) }
  | ISNIL LBRACKET ty RBRACKET auxiliaryTerm
      { TmIsNil ($3, $5) }
  | HEAD LBRACKET ty RBRACKET auxiliaryTerm
      { TmHead ($3, $5) }
  | TAIL LBRACKET ty RBRACKET auxiliaryTerm
      { TmTail ($3, $5) }
  | appTerm auxiliaryTerm  
  | appTerm auxiliaryTerm  
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




  | LT IDV EQ term GT AS ty
      { TmVariant ($2, $4, $7) }

auxiliaryTerm:
    atomicTerm { $1 }
    
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
  | LT ty_field_list_rev GT
      { TyVariant (List.rev $2) }
  | LIST atomicTy
      { TyList $2 }
      

 
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

case_branches_rev :
      case_branch
        { [$1] }
    | case_branches_rev PIPE case_branch
        { $3 :: $1 }

case_branch :
    LT IDV EQ IDV GT DARROW term
      { ($2, $4, $7) }

ty_field_list_rev :
    ty_field
      { [$1] }
  | ty_field_list_rev COMMA ty_field
      { $3 :: $1 }

ty_field :
    IDV COLON ty
      { ($1, $3) }