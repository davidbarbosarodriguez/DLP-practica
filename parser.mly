
%{
  open Lambda;;
%}

(* Definition of tokens *)

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
    IDV EQ term EOF  (*x= term*)     
      { Bind ($1, $3) }
    | IDV EQ ty EOF       (*x: type*)
      { BindTy ($1, $3) }    
    | term EOF            (*x*)
        { Eval $1 }
    | QUIT EOF           (*quit*)
        { Quit }   
    ;       


term :
    appTerm        
      { $1 }
  | IF term THEN term ELSE term (*if t1 then t2 else t3*)
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term   (*lambda x:ty.term*)
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term   (*let x = term1 in term2*)
      { TmLetIn ($2, $4, $6) }
  | LETREC IDV COLON ty EQ term IN term (*letrec f:ty = term1 in term2*)
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }
  | CASE term OF case_branches_rev (*case t of ...*)
      { TmCase ($2, List.rev $4) }


appTerm :
    auxiliaryTerm      
      { $1 }
  | SUCC auxiliaryTerm (*succ t*)
      { TmSucc $2 }
  | PRED auxiliaryTerm (*pred t*)
      { TmPred $2 }
  | ISZERO auxiliaryTerm (*iszero t*)
      { TmIsZero $2 }
  | CONCAT auxiliaryTerm auxiliaryTerm (*concat t1 t2*)
      { TmConcat ($2, $3) }
  | NIL LBRACKET ty RBRACKET (*nil [ty]*)
      { TmNil $3 }
  | CONS LBRACKET ty RBRACKET auxiliaryTerm auxiliaryTerm (*cons [ty] t1 t2*)
      { TmCons ($3, $5, $6) }
  | ISNIL LBRACKET ty RBRACKET auxiliaryTerm (*isnil [ty] t*)
      { TmIsNil ($3, $5) }
  | HEAD LBRACKET ty RBRACKET auxiliaryTerm (*head [ty] t*)
      { TmHead ($3, $5) }
  | TAIL LBRACKET ty RBRACKET auxiliaryTerm (*tail [ty] t*)
      { TmTail ($3, $5) }
  | appTerm auxiliaryTerm  
        { TmApp ($1, $2) }


atomicTerm :
    LPAREN term RPAREN (*term*)
      { $2 }
  | TRUE (*true*)
      { TmTrue }
  | FALSE (*false*)
      { TmFalse }
  | IDV (*variable*)
      { TmVar $1 }
  | INTV (*integer value*)
      { let rec f = function  
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | STRINGV (*string value*)
      { TmString $1 }

  | LBRACE RBRACE (*{}*)
      { TmTuple [] }

  |LBRACE term_reg_list RBRACE (*{l1=t1, l2=t2, ...}*)
      {TmRcd (List.rev $2) }

  |LBRACE term_list_rev RBRACE (*{t1, t2, ...}*)
      { TmTuple (List.rev $2) }

  | LT IDV EQ term GT AS ty (*<l = t> as T*)
      { TmVariant ($2, $4, $7) }

auxiliaryTerm:
    atomicTerm { $1 }
    
  | auxiliaryTerm DOT IDV (*t.l*)
      { TmProj ($1, $3) }
  | auxiliaryTerm DOT INTV (*t.n*) 
      { TmProj ($1, string_of_int $3) }

ty :
    atomicTy (*ty*)
      { $1 } 
  | atomicTy ARROW ty (*ty1 -> ty2*)
      { TyArr ($1, $3) }  


atomicTy :
    LPAREN ty RPAREN (*(ty)*)
      { $2 }
  | BOOL (*Bool*)
      { TyBool }
  | NAT (*Nat*)
      { TyNat }
  | STRING (*String*)
      { TyString }
  | LBRACE RBRACE   (*Unit*)
      { TyTuple [] }
  | IDV (*type variable*)
      { TyVar $1 }
  | LBRACE ty_list_rev RBRACE   (*{ty1, ty2, ...}*)
      { TyTuple (List.rev $2) }
  | LBRACE ty_reg_list RBRACE  (*{l1:ty1, l2:ty2, ...}*)
      { TyRcd (List.rev $2) }
  | LT ty_field_list_rev GT  (*<l1:ty1, l2:ty2, ...>*)
      { TyVariant (List.rev $2) }
  | LIST atomicTy (*List ty*)
      { TyList $2 }
      

 
term_reg_list:
    IDV EQ term                         { [($1, $3)] } (* l = t *)
  | term_reg_list COMMA IDV EQ term     { ($3, $5) :: $1 } (* l = t , ... *)


ty_reg_list:
    IDV COLON ty                        { [($1, $3)] } (* l: ty *)
  | ty_reg_list COMMA IDV COLON ty      { ($3, $5) :: $1 } (* l: ty , ... *) 


  

term_list_rev : 
      term 
        { [$1] }
    | term_list_rev COMMA term (*{t1, t2, ...}*)
        { $3 :: $1 }

ty_list_rev :
      ty
        { [$1] }
    | ty_list_rev COMMA ty (*{ty1, ty2, ...}*)
        { $3 :: $1 }

case_branches_rev :
      case_branch
        { [$1] }
    | case_branches_rev PIPE case_branch (*case t of ... | ...*)
        { $3 :: $1 }

case_branch :
    LT IDV EQ IDV GT DARROW term (*<l = x> -> t*)
      { ($2, $4, $7) }

ty_field_list_rev :
    ty_field
      { [$1] }
  | ty_field_list_rev COMMA ty_field (*<l1:ty1, l2:ty2, ...>*)
      { $3 :: $1 }

ty_field :
    IDV COLON ty (*l:ty*)
      { ($1, $3) }