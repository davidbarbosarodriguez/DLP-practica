(* TYPE DEFINITIONS *)

(*types*)
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

(*different kind of terms *)
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
  []    (*empty context *)
;;

 (* add a var and their type to the context *)
let addtbinding ctx x bind =
  (x, TyBind bind) :: ctx
;;
(*get a type of a var in the context*)
let gettbinding ctx x =
  match List.assoc x ctx with 
      TyBind ty -> ty 
    | TyTmBind (ty, _) -> ty 
;;

(*add a value and their type to the context *)
let addvbinding ctx x ty t =
  (x, TyTmBind (ty, t)) :: ctx (* añade una variable, tipo y termino al contexto *)
;;

(*get the value of a varible in the context*)
let getvbinding ctx x = 
  match List.assoc x ctx with 
      TyTmBind (_, t) -> t 
    | _ -> raise Not_found 
;;



(* TYPE MANAGEMENT (TYPING) *)

open Format

(* Helper para imprimir tipos *)
let rec print_ty fmt ty = match ty with
  | TyBool -> fprintf fmt "Bool"
  | TyNat -> fprintf fmt "Nat"
  | TyString -> fprintf fmt "String"
  | TyVar s -> fprintf fmt "%s" s
  | TyList ty -> fprintf fmt "List %a" print_atomic_ty ty
  | TyArr (t1, t2) ->
      fprintf fmt "@[%a ->@ %a@]" print_atomic_ty t1 print_ty t2
  | TyTuple tys ->
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_ty) tys
  | TyRcd fields ->
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field_ty) fields
  | TyVariant fields ->
      fprintf fmt "<@[<hov>%a@]>" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field_ty) fields

and print_atomic_ty fmt ty = match ty with
  | TyArr _ -> fprintf fmt "(%a)" print_ty ty
  | _ -> print_ty fmt ty

and print_field_ty fmt (l, ty) =
  fprintf fmt "%s : %a" l print_ty ty
;;

(* Wrapper para mantener compatibilidad con el resto del código *)
let string_of_ty ty =
  let buf = Buffer.create 100 in
  let fmt = formatter_of_buffer buf in
  print_ty fmt ty;
  pp_print_flush fmt ();
  Buffer.contents buf
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
  | TyTuple tys ->
      TyTuple (List.map (fun t -> resolve_ty ctx t seen_aliases) tys)
  | TyRcd fields ->
      let resolved_fields = List.map (fun (label, ty_field) -> (label, resolve_ty ctx ty_field seen_aliases)) fields in
      TyRcd resolved_fields
  | TyVariant fields ->
      TyVariant (List.map (fun (l, t) -> (l, resolve_ty ctx t seen_aliases)) fields)
  | TyList ty ->
      TyList (resolve_ty ctx ty seen_aliases)
  | (TyBool | TyNat | TyString) as t -> t
;;



(* Comprueba si tyS es subtipo de tyT *)
let rec subtype ctx tyS tyT =
  (* Primero resolvemos los alias para comparar los tipos reales *)
  let tyS = resolve_ty ctx tyS [] in
  let tyT = resolve_ty ctx tyT [] in
  
  if tyS = tyT then true (* S-Refl: Son iguales *)
  else
    match (tyS, tyT) with
    (* S-Rcd: Ancho, Profundidad y Permutación combinados *)
    | (TyRcd fieldsS, TyRcd fieldsT) ->
        (* Para cada campo que espera T (l: tyT_field)... *)
        List.for_all (fun (l, tyT_field) ->
          try
            (* ...buscamos si S tiene ese campo (l: tyS_field) *)
            let tyS_field = List.assoc l fieldsS in
            (* Y comprobamos recursivamente si tyS_field <: tyT_field *)
            subtype ctx tyS_field tyT_field
          with Not_found -> false (* Si S no tiene un campo que T pide, falla (Width) *)
        ) fieldsT

    (* S-Arrow: Funciones *)
    | (TyArr(s1, s2), TyArr(t1, t2)) ->
        (* Contravarianza en el argumento (T1 <: S1) y Covarianza en resultado (S2 <: T2) *)
        (subtype ctx t1 s1) && (subtype ctx s2 t2)
    | _ -> false
;;


(*get the type of a term*)
let rec typeof ctx tm = match tm with 
    (* T-True *)
    TmTrue ->
      TyBool

    (* T-False *)
  | TmFalse ->
      TyBool

    (* T-If *)
  | TmIf (t1, t2, t3) -> (*both parts need to have the same type *)
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
  | TmVar x -> gettbinding ctx x (*try-with???*)

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
             if subtype ctx tyT2 tyT11 then tyT12
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
    (* T-Tuple *)
  | TmTuple ts ->
      TyTuple (List.map (typeof ctx) ts)
    (* T-Rcd *)
  | TmRcd fields ->
      let field_types = List.map (fun (lbl, term_field) -> (lbl, typeof ctx term_field)) fields in
      TyRcd field_types
    (*T-Proj*)
  | TmProj (t, lbl) ->
      (match (resolve_ty ctx (typeof ctx t) []) with
        | TyRcd fields ->
            (try List.assoc lbl fields (*try to find the field in the record*)
             with Not_found -> raise (Type_error ("label "^lbl^" not found in record")))
        | TyTuple tys ->
            (try (*return the n-1 element of the list*)
              let index = int_of_string lbl in
              List.nth tys (index-1)
             with Failure _ | Invalid_argument _ -> raise (Type_error ("invalid tuple index: " ^ lbl)))
        | _ -> raise (Type_error "argument of projection is not a record"))
  
    (* T-Variant *)
  | TmVariant (l, t, ty) ->
      (match (resolve_ty ctx ty []) with
        TyVariant fields ->
          (try (*if the ty expect is the same as the real ty return the ty*)
            let ty_expected = List.assoc l fields in
            let ty_t = typeof ctx t in
            if (resolve_ty ctx ty_t []) = (resolve_ty ctx ty_expected []) then ty
            else raise (Type_error "type of variant does not match declared type")
          with
            Not_found -> raise (Type_error ("label " ^ l ^ " not found in variant type")))
        | _ -> raise (Type_error "expected a variant type"))
    (* T-Case *)
  | TmCase (t, branches) ->
      (match (resolve_ty ctx (typeof ctx t) []) with
        TyVariant fields ->
            if branches = [] then (*no cases*)
              raise (Type_error "case expression has no branches");
            let (first_label, first_var, first_branch) = List.hd branches in (*take the first branch*)
            let ty_field1 = (try List.assoc first_label fields with 
                           Not_found -> raise (Type_error ("label " ^ first_label ^ " not found in variant type"))) in
            let ctx' = addtbinding ctx first_var ty_field1 in
            let ty_result = typeof ctx' first_branch in

            List.iter (fun (l, v, br) ->
              let ty_field = (try List.assoc l fields with
                                Not_found -> raise (Type_error ("label " ^ l ^ " not found in variant type"))) in
              let ctx'' = addtbinding ctx v ty_field in
              let ty_br = typeof ctx'' br in
              
              if ty_br <> ty_result then
                raise (Type_error "all branches of case must have the same type")
            ) (List.tl branches);
            ty_result
        | _ -> raise (Type_error "expected a variant type"))
  (* T-NIL *)
  | TmNil ty ->
      TyList (resolve_ty ctx ty []) (*return the TyList with the simpliest type*)
      
  (* T-CONS *)
  | TmCons (ty, t1, t2) -> (*compare two lists  *)
      let ty' = resolve_ty ctx ty [] in
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      if (resolve_ty ctx tyT1 []) <> ty' then
        raise (Type_error "tipo de la cabeza de la lista incorrecto");
      if (resolve_ty ctx tyT2 []) <> TyList ty' then
        raise (Type_error "tipo de la cola de la lista incorrecto");
      TyList ty'

  (* T-ISNIL *)
  | TmIsNil (ty, t) ->
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then
        raise (Type_error "isnil se aplica sobre un tipo no-lista");
      TyBool

  (* T-HEAD *)
  | TmHead (ty, t) -> (*return the type of the head of the list*)
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then
        raise (Type_error "head se aplica sobre un tipo no-lista");
      ty' (* Devuelve el tipo del elemento *)

  (* T-TAIL *)
  | TmTail (ty, t) -> (*return the type of the tail list*)
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then
        raise (Type_error "tail se aplica sobre un tipo no-lista");
      TyList ty' (* Devuelve el tipo de la lista *)
;;


(* TERMS MANAGEMENT (EVALUATION) *)

let rec print_term fmt t = match t with
  | TmIf (t1, t2, t3) ->
      fprintf fmt "@[<v 2>if %a then@ %a@ else@ %a@]"
        print_term t1 print_term t2 print_term t3
  | TmAbs (s, tyS, t) ->
      fprintf fmt "@[<2>lambda %s:%a.@ %a@]" s print_ty tyS print_term t
  | TmLetIn (s, t1, t2) ->
      fprintf fmt "@[<v>let %s = %a in@ %a@]" s print_term t1 print_term t2
  | TmFix t ->
      fprintf fmt "@[<2>fix %a@]" print_term t
  | TmCase (t, branches) ->
      fprintf fmt "@[<v 2>case %a of@ %a@]"
        print_term t
        (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ | ") print_branch) branches
  | _ ->
      print_app_term fmt t

and print_app_term fmt t = match t with
  | TmApp (t1, t2) ->
      fprintf fmt "@[<2>%a@ %a@]" print_app_term t1 print_atomic_term t2
  | TmSucc t1 ->
      let rec f n t' = match t' with
        | TmZero -> fprintf fmt "%d" n
        | TmSucc s -> f (n+1) s
        | _ -> fprintf fmt "(succ %a)" print_atomic_term t1
      in f 1 t1
  | TmPred t1 -> fprintf fmt "pred %a" print_atomic_term t1
  | TmIsZero t1 -> fprintf fmt "iszero %a" print_atomic_term t1
  | TmConcat (t1, t2) -> fprintf fmt "concat %a %a" print_atomic_term t1 print_atomic_term t2
  | TmCons (ty, t1, t2) ->
      fprintf fmt "@[<2>cons [%a]@ %a@ %a@]" print_ty ty print_atomic_term t1 print_atomic_term t2
  | TmHead (ty, t) -> fprintf fmt "head [%a] %a" print_ty ty print_atomic_term t
  | TmTail (ty, t) -> fprintf fmt "tail [%a] %a" print_ty ty print_atomic_term t
  | TmIsNil (ty, t) -> fprintf fmt "isnil [%a] %a" print_ty ty print_atomic_term t
  | _ ->
      print_atomic_term fmt t

and print_atomic_term fmt t = match t with
  | TmTrue -> fprintf fmt "true"
  | TmFalse -> fprintf fmt "false"
  | TmZero -> fprintf fmt "0"
  | TmVar s -> fprintf fmt "%s" s
  | TmString s -> fprintf fmt "\"%s\"" s
  | TmNil ty -> fprintf fmt "nil [%a]" print_ty ty
  | TmTuple ts ->
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_term) ts
  | TmRcd fields ->
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field) fields
  | TmVariant (l, t, _) ->
      fprintf fmt "<%s=%a>" l print_term t
  | TmProj (t, l) ->
      fprintf fmt "%a.%s" print_atomic_term t l
  | _ ->
      fprintf fmt "(%a)" print_term t

and print_field fmt (l, t) =
  fprintf fmt "%s = %a" l print_term t

and print_branch fmt (l, x, t) =
  fprintf fmt "<%s=%s> => %a" l x print_term t
;;

(* Wrapper: Convierte la salida formateada a string plano para usar en el resto del programa *)
let string_of_term t =
  let buf = Buffer.create 100 in
  let fmt = formatter_of_buffer buf in
  print_term fmt t;
  pp_print_flush fmt ();
  Buffer.contents buf
;;



let rec ldif l1 l2 = match l1 with (* return the elements in l1 but not in l2  *)
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;

let rec lunion l1 l2 = match l1 with (* return the union of both lists  *)
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;

let rec free_vars tm = match tm with (* return the free vars  of a term *)
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
  | TmTuple ts ->
      List.fold_left lunion [] (List.map free_vars ts)
  | TmRcd fields ->
      List.fold_left lunion [] (List.map (fun (_, t) -> free_vars t) fields)
  | TmProj (t, _) ->
      free_vars t
  | TmVariant (_, t, _) ->
      free_vars t
  | TmCase (t, branches) ->
      let fv_t = free_vars t in
      let fv_branches = List.map (fun (l, x, b) -> ldif (free_vars b) [x]) branches in
      List.fold_left lunion fv_t fv_branches
  | TmNil _ ->
      []
  | TmCons (_, t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmIsNil (_, t) ->
      free_vars t
  | TmHead (_, t) ->
      free_vars t
  | TmTail (_, t) ->
      free_vars t


let rec fresh_name x l = (*return a new name *)
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm = match tm with (* substitution of a var to their fresh-name *)
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
  | TmTuple ts ->
      TmTuple (List.map (subst x s) ts)
  | TmRcd fields ->
      TmRcd (List.map (fun (lbl, t) -> (lbl, subst x s t)) fields)
  | TmProj (t, n) ->
      TmProj (subst x s t, n)
  | TmVariant (l, t, ty) ->
      TmVariant (l, subst x s t, ty)
  | TmCase (t, branches) -> 
      let new_branches = List.map (fun (l, v, b) ->
          if v = x then 
            (l, v, b)
          else 
            let z = fresh_name v (free_vars s) in
            let b' = subst v (TmVar z) b in
            (l, z, subst x s b')
      ) branches in
      TmCase (subst x s t, new_branches)
  | TmNil ty ->
      TmNil ty
  | TmCons (ty, t1, t2) ->
      TmCons (ty, subst x s t1, subst x s t2)
  | TmIsNil (ty, t) ->
      TmIsNil (ty, subst x s t)
  | TmHead (ty, t) ->
      TmHead (ty, subst x s t)
  | TmTail (ty, t) ->
      TmTail (ty, subst x s t)

;;

let rec isnumericval tm = match tm with (*check if the var is numeric *)
    TmZero -> true
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with (*check if is a var*)
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | t when isnumericval t -> true
  | TmString _ -> true
  | TmTuple ts -> List.for_all isval ts
  | TmRcd fields -> List.for_all (fun (_, t) -> isval t) fields
  | TmVariant (l, t, _) -> isval t
  | TmNil _ ->
      true
  | TmCons (_, v1, v2) ->
      isval v1 && isval v2
  | _ -> false

;;

exception NoRuleApplies
;;

(*eval a term*)
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

  | TmProj (TmTuple ts, n) ->
      (try List.nth ts ((int_of_string n)-1)
       with Failure _ | Invalid_argument _ -> raise NoRuleApplies)
  
    (* E-PROJ *)
  | TmProj (TmRcd fields, lbl) ->
    (try List.assoc lbl fields
     with Not_found -> raise NoRuleApplies)
  
    (* E-TUPLE*)
  | TmTuple ts ->
      let rec eval_step l_evaluados = function
        | [] -> raise NoRuleApplies (* is just a value *)
        | h::t ->
            if isval h then
              eval_step (h::l_evaluados) t 
            else
              (*  *)
              let h' = eval1 ctx h in
              TmTuple(List.rev l_evaluados @ (h'::t))
      in
      eval_step [] ts
  | TmRcd fields ->
      let rec eval_field l_evaluados = function
        | [] -> raise NoRuleApplies 
        | (lbl, h)::t ->
            if isval h then
              eval_field ((lbl, h)::l_evaluados) t
            else
              let h' = eval1 ctx h in
              TmRcd (List.rev l_evaluados @ ((lbl, h')::t))
      in
      eval_field [] fields

      (* E-VARIANT*)
  | TmVariant (l, t, ty) when not (isval t) ->
      TmVariant (l, eval1 ctx t, ty)
      
    (* E-CASEVARIANT*)
  | TmCase (TmVariant (l_val, v, _), branches) when isval v ->
      (try
         let (x, b) = List.assoc l_val (List.map (fun (l,x,b) -> (l,(x,b))) branches) in
         subst x v b
       with Not_found -> raise NoRuleApplies) 

    (* E-CASE*)
  | TmCase (t, branches) ->
      let t' = eval1 ctx t in
      TmCase (t', branches)

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

  (* E-CONS1 (Evalúa cabeza) *)
  | TmCons (ty, t1, t2) when not (isval t1) ->
      TmCons (ty, eval1 ctx t1, t2)
  (* E-CONS2 (Evalúa cola) *)
  | TmCons (ty, v1, t2) when isval v1 && not (isval t2) ->
      TmCons (ty, v1, eval1 ctx t2)

  (* E-ISNILNIL *)
  | TmIsNil (ty, TmNil _) ->
      TmTrue
  (* E-ISNILCONS *)
  | TmIsNil (ty, TmCons(_, _, _)) ->
      TmFalse
  (* E-ISNIL (Congruencia) *)
  | TmIsNil (ty, t) ->
      TmIsNil (ty, eval1 ctx t)
  (* E-HEADCONS *)
  | TmHead (ty, TmCons(_, v1, _)) ->
      v1
    (* E-HEADNIL *)
  | TmHead (ty, TmNil _) ->
      raise NoRuleApplies 
    (* E-HEAD (Congruencia) *)
  | TmHead (ty, t) ->
      TmHead (ty, eval1 ctx t)

    (* E-TAILCONS *)
  | TmTail (ty, TmCons(_, _, v2)) ->
      v2
    (* E-TAILNIL *)
  | TmTail (ty, TmNil _) ->
      raise NoRuleApplies 
    (* E-TAIL (Congruencia) *)
  | TmTail (ty, t) ->
      TmTail (ty, eval1 ctx t)
  | TmVar s ->
      getvbinding ctx s

  | _ ->
      raise NoRuleApplies
;;

let apply_ctx ctx1 ctx2 = 
List.fold_left (fun t x -> subst x (getvbinding ctx2 x) t ) ctx1 (free_vars ctx1)
;;


let rec eval ctx tm = (* LCalls eval1 function*)
  try
    let tm' = eval1 ctx tm in
    eval ctx tm'
  with
    NoRuleApplies -> apply_ctx tm ctx

;;


let execute ctx = function
  Eval tm ->
    (* if tm is a variable and is in the context, return the type *)
    (match tm with
     | TmVar x -> 
         let ty = gettbinding ctx x in
         (try
            let val_tm = eval ctx tm in
            print_endline (x ^ " : " ^ string_of_ty ty ^ " = " ^ string_of_term val_tm)
          with Not_found ->
            print_endline (x ^ " : " ^ string_of_ty ty))
         ;
         ctx
     | _ ->
         (* eval and show results*)
         let tyT = typeof ctx tm in
         let tm' = eval ctx tm in
         print_endline (string_of_term tm' ^ " : " ^ string_of_ty tyT);
         ctx
    )
| Bind (x, t) ->
    let tyTm, tm' = match t with
      (* when is a variable, return the value if is in the context *)
      | TmVar y ->
          let ty = gettbinding ctx y in       
          let v = try getvbinding ctx y      
                  with Not_found -> TmVar y
          in
          (ty, v)
      (*when is a function, eval *)
      | _ ->
          let ty = typeof ctx t in
          let v = eval ctx t in
          (ty, v)
    in
    let tyTm_resolved = resolve_ty ctx tyTm [] in (*take the simpliest type of a function/var*)
    print_endline (x ^ " : " ^ string_of_ty tyTm_resolved ^ " = " ^ string_of_term tm');
    addvbinding ctx x tyTm tm'(*add it to the context*)

  | BindTy (s, ty) ->
      (try
        let ty' = resolve_ty ctx ty [] in (*take the simpliest type of a function/var*)
        print_endline (s ^ " = " ^ string_of_ty ty');
        addtbinding ctx s ty'
      with
        Type_error e -> print_endline ("type error: " ^ e); ctx
      | Type_alias_loop e -> print_endline ("type error: " ^ e); ctx)
  | Quit ->
        raise End_of_file
  ;;


