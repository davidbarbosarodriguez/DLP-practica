(*definition of types*)
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString
  | TyVar of string
  | TyTuple of ty list
  | TyRcd of (string * ty) list        
  | TyVariant of (string * ty) list
  | TyList of ty
;;

(*definition of terms*)
type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVar of string
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLetIn of string * term * term
  | TmFix of term
  | TmString of string
  | TmConcat of term * term
  | TmTuple of term list
  | TmProj of term * string
  | TmRcd of (string * term) list
  | TmVariant of string * term * ty
  | TmCase of term * (string * string * term) list
  | TmNil of ty
  | TmCons of ty * term * term 
  | TmIsNil of ty * term
  | TmHead of ty * term
  | TmTail of ty * term
;;

type command =
    Bind of string * term
  | BindTy of string * ty
  | Eval of term
  | Quit
;;

type binding =
    TyBind of ty
  | TyTmBind of (ty * term)
;;

(*lambda context*)
type context =
  (string * binding) list
;;

(* empty context*)
val emptyctx : context;;

(*add a type in the context *)
val addtbinding : context -> string -> ty -> context ;;

(*add a term in the context *)
val addvbinding : context -> string -> ty -> term -> context ;;

(*get a type from the context *)
val gettbinding : context -> string -> ty ;;

(*get a term from the context *)
val getvbinding : context -> string -> term ;;

(*string representation of types*)
val string_of_ty : ty -> string;;
exception Type_error of string;;
exception Type_alias_loop of string;;
val typeof : context -> term -> ty;;

(*string representation of terms*)
val string_of_term : term -> string;;


exception NoRuleApplies;;

(*evaluation of terms*)
val eval : context -> term -> term;;

(*execution of commands*)
val execute : context -> command -> context;;
