
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
%token BOOL
%token NAT
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

%start s
%type <Lambda.command> s

%%

s :
    IDV EQ term EOF         (* x = t *)
      { Bind ($1, $3) }     
    | term EOF            (* t *)
        { Eval $1 }
    | QUIT EOF           (* quit *)
        { Quit }          

(*Definicion de terminos*)
term :
    appTerm         (* por aqui va cuando es un appTerm *)
      { $1 }
  | IF term THEN term ELSE term (* if t1 then t2 else t3 *)
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term   (* lambda x:T.t *)
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term   (* let x = t1 in t2 *)
      { TmLetIn ($2, $4, $6) }
  | LETREC IDV COLON ty EQ term IN term (* letrec x:T = t1 in t2 *)
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }

(*Operaciones basicas de terminos*)
appTerm :
    atomicTerm      (* por aqui va cuando es un atomicTerm *)
      { $1 }
  | SUCC atomicTerm (* succ t *)
      { TmSucc $2 }
  | PRED atomicTerm (* pred t *)
      { TmPred $2 }
  | ISZERO atomicTerm (* iszero t *)
      { TmIsZero $2 }
  | appTerm atomicTerm  (* t1 t2 *)
      { TmApp ($1, $2) }

(*Definicion de terminos atomicos*)
atomicTerm :
    LPAREN term RPAREN (* ( t ) *)
      { $2 }
  | TRUE (* true *)
      { TmTrue }
  | FALSE (* false *)
      { TmFalse }
  | IDV (* x *)
      { TmVar $1 }
  | INTV (* n *)
      { let rec f = function  (* se va haiendo el numero en base a succesores de 0 *)
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }

(*tipos*)
ty :
    atomicTy (* tipo basico *)
      { $1 }
  | atomicTy ARROW ty (* T1 -> T2 *)
      { TyArr ($1, $3) }

atomicTy :
    LPAREN ty RPAREN (* ( T ) *)
      { $2 }
  | BOOL (* Bool *)
      { TyBool }
  | NAT (* Nat *)
      { TyNat }

