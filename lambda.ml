(* TYPE DEFINITIONS *)

type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString 
  | TyVar of string
;;


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
;;

type command =
    Bind of string * term (* x = t *)
  | BindTy of string * ty (* x = T *)
  | Eval of term (* evalua t *)
  | Quit (* quit *)
;;

type binding =
    TyBind of ty (* guarda el tipo *)
  | TyTmBind of (ty * term) (* guarda el tipo y el termino *)
;;

type context =
  (string * binding) list (* x =<binding> *)
;;



let emptyctx =
  []    (* contexto vacio *)
;;

let addtbinding ctx x bind =
  (x, TyBind bind) :: ctx (* añade una variable y tipo al contexto *)
;;

let gettbinding ctx x =
  match List.assoc x ctx with (* busca x en el contexto *)
      TyBind ty -> ty (* devuelve el tipo de la variable en caso de que solo haya tipo *)
    | TyTmBind (ty, _) -> ty (* devuelve el tipo de la variable si tmb hay valor *)
;;

let addvbinding ctx x ty t =
  (x, TyTmBind (ty, t)) :: ctx (* añade una variable, tipo y termino al contexto *)
;;

let getvbinding ctx x = 
  match List.assoc x ctx with (* busca x en el contexto *)
      TyTmBind (_, t) -> t (* devuelve el termino de la variable *)
    | _ -> raise Not_found (* si no tiene termino asociado lanza error *)
;;



(* TYPE MANAGEMENT (TYPING) *)

let rec string_of_ty ty = match ty with (* para pasar de tipo a cadena *)
    TyBool ->
      "Bool"
  | TyNat ->
      "Nat"
  | TyArr (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ ")" ^ " -> " ^ "(" ^ string_of_ty ty2 ^ ")"
  | TyString ->
      "String"
  | TyVar s ->
      s
;;

exception Type_error of string
;;
exception Type_alias_loop of string
;;


(*funcion to resolve alias of types*)
let rec resolve_ty ctx ty seen_aliases = match ty with
  | TyVar s ->
      if List.mem s seen_aliases then
        raise (Type_alias_loop ("Bucle detectado en el alias de tipo: " ^ s));
      let ty' = (try gettbinding ctx s with Not_found -> raise (Type_error ("Alias de tipo no encontrado: " ^ s))) in
      (* Recursive resolution *)
      resolve_ty ctx ty' (s :: seen_aliases)
  | TyArr (t1, t2) ->
      (* Resolve types in functions *)
      TyArr (resolve_ty ctx t1 seen_aliases, resolve_ty ctx t2 seen_aliases)
  | (TyBool | TyNat | TyString) as t -> t
;;


let rec typeof ctx tm = match tm with (* conversiones a tipos todas siguen la rules for typing *)
    (* T-True *)
    TmTrue ->
      TyBool

    (* T-False *)
  | TmFalse ->
      TyBool

    (* T-If *)
  | TmIf (t1, t2, t3) -> (* si es bool comprueba que los dos tengan el mismo tipo y devulve el tipo*)
      if (resolve_ty ctx (typeof ctx t1) []) = TyBool then
        let tyT2 = typeof ctx t2 in
        if (resolve_ty ctx (typeof ctx t3) []) = (resolve_ty ctx tyT2 []) then tyT2
        else raise (Type_error "arms of conditional have different types")
      else
        raise (Type_error "guard of conditional not a boolean")

    (* T-Zero *)
  | TmZero ->
      TyNat

    (* T-Succ *)
  | TmSucc t1 ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")

    (* T-Pred *)
  | TmPred t1 ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")

    (* T-Iszero *)
  | TmIsZero t1 ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")

    (* T-Var *)
  | TmVar x ->
      (try gettbinding ctx x with
       _ -> raise (Type_error ("no binding type for variable " ^ x)))

    (* T-Abs *)
  | TmAbs (x, tyT1, t2) ->
      let tyT1_resolved = resolve_ty ctx tyT1 [] in
      let ctx' = addtbinding ctx x tyT1_resolved in
      let tyT2 = typeof ctx' t2 in
      TyArr (tyT1_resolved, tyT2)

    (* T-App *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match (resolve_ty ctx tyT1 []) with
           TyArr (tyT11, tyT12) ->
             if (resolve_ty ctx tyT2 []) = tyT11 then tyT12
             else raise (Type_error "parameter type mismatch")
         | _ -> raise (Type_error "arrow type expected"))

    (* T-Let *)
  | TmLetIn (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addtbinding ctx x tyT1 in
      typeof ctx' t2
  
    (* T-Fix *)
  | TmFix t1 ->
      let tyT1 = typeof ctx t1 in
      (match (resolve_ty ctx tyT1 []) with
           TyArr (tyT11, tyT12) ->
             if tyT11 = tyT12 then tyT12
             else raise (Type_error "result of body not compatible with domain")
         | _ -> raise (Type_error "arrow type expected"))
  
    (* T-String *)
  | TmString _ ->
      TyString
    (* T-Concat *)
  | TmConcat (t1, t2) ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyString && (resolve_ty ctx (typeof ctx t2) []) = TyString then
        TyString
      else
        raise (Type_error "arguments of concat are not all strings")
        
;;


(* TERMS MANAGEMENT (EVALUATION) *)

let rec string_of_term t = (* para pasar de termino a cadena *)
  match t with
  | TmTrue -> "true"
  | TmFalse -> "false"
  | TmZero -> "0"
  | TmIf (t1,t2,t3) ->
      "if " ^ string_of_term t1 ^
      " then " ^ string_of_term t2 ^
      " else " ^ string_of_term t3
  | TmSucc t ->
      let rec f n t' = match t' with
        | TmZero -> string_of_int n
        | TmSucc s -> f (n+1) s
        | _ -> "succ " ^ string_of_atom t'
      in f 1 t
  | TmPred t -> "pred " ^ string_of_atom t ^ ""
  | TmIsZero t -> "iszero " ^ string_of_atom t ^ ""
  | TmVar s -> s
  | TmAbs (s, tyS, t) ->
      "lambda " ^ s ^ ":" ^ string_of_ty tyS ^ ". " ^ string_of_term t ^ ""
  | TmApp _ as t -> string_of_app t
  | TmLetIn (s, t1, t2) ->
      "let " ^ s ^ " = " ^ string_of_term t1 ^ " in " ^ string_of_term t2
  | TmFix t ->
      "fix " ^ string_of_term t ^ ""
  | TmString s ->
      "\"" ^ s ^ "\""
  | TmConcat (t1, t2) ->
      "concat(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ ")"
  
and string_of_atom t =
  match t with
  | TmVar s -> s
  | TmTrue -> "true"
  | TmFalse -> "false"
  | TmZero -> "0"
  | _ -> "(" ^ string_of_term t ^ ")"

and string_of_app t =
  match t with
  | TmApp (t1, t2) ->
      string_of_app t1 ^ " " ^ string_of_atom t2
  | t -> string_of_atom t
 
;;





let rec ldif l1 l2 = match l1 with (* devuelve lo que está en l1 pero no en l2  *)
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;

let rec lunion l1 l2 = match l1 with (* une dos listas sin repetir elementos *)
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;

let rec free_vars tm = match tm with (* calcula las variables libres de un termino *)
    TmTrue ->
      []
  | TmFalse ->
      []
  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero ->
      []
  | TmSucc t ->
      free_vars t
  | TmPred t ->
      free_vars t
  | TmIsZero t ->
      free_vars t
  | TmVar s ->
      [s]
  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]
  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmLetIn (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmFix t ->
      free_vars t
  | TmString _ ->
      []
  | TmConcat (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
;;

let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm = match tm with (* sustitucion de variable x por termino s en tm abstraccion *)
    TmTrue ->
      TmTrue
  | TmFalse ->
      TmFalse
  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero ->
      TmZero
  | TmSucc t ->
      TmSucc (subst x s t)
  | TmPred t ->
      TmPred (subst x s t)
  | TmIsZero t ->
      TmIsZero (subst x s t)
  | TmVar y ->
      if y = x then s else tm
  | TmAbs (y, tyY, t) ->
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t))
  | TmApp (t1, t2) ->
      TmApp (subst x s t1, subst x s t2)
  | TmLetIn (y, t1, t2) ->
      if y = x then TmLetIn (y, subst x s t1, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLetIn (y, subst x s t1, subst x s t2)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLetIn (z, subst x s t1, subst x s (subst y (TmVar z) t2))
  | TmFix t ->
      TmFix (subst x s t)
  | TmString str ->
      TmString str
  | TmConcat (t1, t2) ->
      TmConcat (subst x s t1, subst x s t2)
;;

let rec isnumericval tm = match tm with
    TmZero -> true
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | t when isnumericval t -> true
  | TmString _ -> true
  | _ -> false
;;

exception NoRuleApplies
;;

let rec eval1 ctx tm = match tm with
    (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 ctx t1 in
      TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 ctx t1 in
      TmSucc t1'

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 ctx t1 in
      TmPred t1'

    (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse

    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 ctx t1 in
      TmIsZero t1'

    (* E-AppAbs *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 ctx t2 in
      TmApp (v1, t2')

    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLetIn (x, v1, t2) when isval v1 ->
      subst x v1 t2

    (* E-Let *)
  | TmLetIn(x, t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmLetIn (x, t1', t2)
    
    (* E-FixBeta *)
  | TmFix (TmAbs (x, _, t2)) ->
      subst x tm t2
  
    (* E-Fix *)
  | TmFix t1 ->
      let t1' = eval1 ctx t1 in
      TmFix t1'
    (* E-ConcatStr *)
  | TmConcat (TmString s1, TmString s2) ->
      TmString (s1 ^ s2)

    (* E-Concat2 *)
  | TmConcat (t1, t2) when isval t1 ->
      let t2' = eval1 ctx t2 in
      TmConcat (t1, t2')

    (* E-Concat1 *)
  | TmConcat (t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmConcat (t1', t2)

  | TmVar s ->
      getvbinding ctx s

  | _ ->
      raise NoRuleApplies
;;

let apply_ctx ctx1 ctx2 = (* se sustituyen las variables libres de ctx1 por sus valores en el contexto ctx2 *)
List.fold_left (fun t x -> subst x (getvbinding ctx2 x) t ) ctx1 (free_vars ctx1)
;;


let rec eval ctx tm = (* Llama a la función de eval1 para realicar el evaluation*)
  try
    let tm' = eval1 ctx tm in
    eval ctx tm'
  with
    NoRuleApplies -> apply_ctx tm ctx

;;


let execute ctx = function
  Eval tm ->
    let tyT = typeof ctx tm in
    let tm' = eval ctx tm in
    print_endline (string_of_term tm' ^ " : " ^ string_of_ty tyT);
      ctx
  | Bind (x, t) ->
      let tyTm = typeof ctx t in
      let tm' = eval ctx t in
      print_endline (x ^ " = " ^ string_of_term tm' ^ " : " ^ string_of_ty tyTm);
      addvbinding ctx x tyTm tm'
  | BindTy (s, ty) ->
      (try
        let ty' = resolve_ty ctx ty [] in
        print_endline (s ^ " = " ^ string_of_ty ty');
        addtbinding ctx s ty'
      with
        Type_error e -> print_endline ("type error: " ^ e); ctx
      | Type_alias_loop e -> print_endline ("type error: " ^ e); ctx)
  | Quit ->
        raise End_of_file
  ;;


