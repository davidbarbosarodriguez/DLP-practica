(* TYPE DEFINITIONS *)
exception Type_error of string
exception Type_alias_loop of string

(*types*)
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  (* [EXT] String support *)
  | TyString 
  (* [EXT] Type Aliasing support (holds the alias name) *)
  | TyVar of string
  (* [EXT] Data structures: Tuples, Records, Variants, Lists *)
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
  (* [EXT] String literals and concatenation *)
  | TmString of string
  | TmConcat of term * term
  (* [EXT] Tuples and Projections *)
  | TmTuple of term list
  | TmProj of term * string
  (* [EXT] Records *)
  | TmRcd of (string * term) list
  (* [EXT] Variants and Pattern Matching *)
  | TmVariant of string * term * ty
  | TmCase of term * (string * string * term) list
  (* [EXT] List operations *)
  | TmNil of ty
  | TmCons of ty * term * term
  | TmIsNil of ty * term
  | TmHead of ty * term
  | TmTail of ty * term
;;

type command =
    Bind of string * term (* x = t *) 
  (* [EXT] Command to register a global Type Alias (type T = Nat) *)
  | BindTy of string * ty (* x = T *)
  | Eval of term (* evalua t *)
  | Quit (* quit *)
;;

type binding =
  (* [EXT] Binding to store type definitions in Context *)
    TyBind of ty (* guarda el tipo *)
  | TyTmBind of (ty * term) (* guarda el tipo y el termino *)
;;

type context =
  (string * binding) list (* x =<binding> *)
;;

(* ... (Context helper functions omitted for brevity, standard implementation) ... *)
let emptyctx = [] ;;
let addtbinding ctx x bind = (x, TyBind bind) :: ctx ;;
let gettbinding ctx x = match List.assoc x ctx with TyBind ty -> ty | TyTmBind (ty, _) -> ty ;;
let addvbinding ctx x ty t = (x, TyTmBind (ty, t)) :: ctx ;;
let getvbinding ctx x = 
  try
    match List.assoc x ctx with 
    | TyTmBind (_, t) -> t 
    | TyBind _ -> raise (Type_error ("Identifier " ^ x ^ " is a Type, not a Value"))
  with Not_found -> 
    raise (Type_error ("Variable " ^ x ^ " is not defined"))
;;

(* TYPE MANAGEMENT (TYPING) *)

open Format

(* [MOD] Updated to print new types (Lists, Variants, Strings) *)
(* Asegúrate de tener esto al principio del archivo o módulo *)
open Format

let rec print_ty fmt ty = match ty with
  | TyBool -> fprintf fmt "Bool"
  | TyNat -> fprintf fmt "Nat"
  | TyString -> fprintf fmt "String"
  | TyVar s -> fprintf fmt "%s" s
  | TyList ty -> fprintf fmt "List %a" print_atomic_ty ty
  | TyArr (t1, t2) ->
      fprintf fmt "@[%a ->@ %a@]" print_atomic_ty t1 print_ty t2
  | TyTuple tys ->
      (* Imprime tuplas como {Nat, Bool} *)
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_ty) tys
  | TyRcd fields ->
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field_ty) fields
  | TyVariant fields ->
      fprintf fmt "<@[<hov>%a@]>" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field_ty) fields

(* Fíjate en el 'and' aquí abajo, es crucial *)
and print_atomic_ty fmt ty = match ty with
  | TyArr _ -> fprintf fmt "(%a)" print_ty ty
  | TyList _ -> fprintf fmt "(%a)" print_ty ty (* Paréntesis necesarios si hay listas anidadas complejas *)
  | _ -> print_ty fmt ty

(* Y otro 'and' aquí *)
and print_field_ty fmt (l, ty) =
  fprintf fmt "%s : %a" l print_ty ty
;;

let string_of_ty ty =
  let buf = Buffer.create 100 in
  let fmt = formatter_of_buffer buf in
  print_ty fmt ty;
  pp_print_flush fmt ();
  Buffer.contents buf
;;


(* [NEW] Function to handle Type Aliases (e.g., resolving 'T' to 'Nat') with cycle detection *)
let rec resolve_ty ctx ty seen_aliases = match ty with
  | TyVar s ->
      if List.mem s seen_aliases then
        raise (Type_alias_loop ("Bucle detectado en el alias de tipo: " ^ s));
      let ty' = (try gettbinding ctx s with Not_found -> raise (Type_error ("Alias de tipo no encontrado: " ^ s))) in
      resolve_ty ctx ty' (s :: seen_aliases)
  | TyArr (t1, t2) ->
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

(* [NEW] Function implementing Subtyping rules (Width, Depth, Permutation for Records; Contravariance for Arrows) *)
let rec subtype ctx tyS tyT =
  (* Resolve aliases first to compare actual types *)
  let tyS = resolve_ty ctx tyS [] in
  let tyT = resolve_ty ctx tyT [] in
  
  if tyS = tyT then true (* S-Refl *)
  else
    match (tyS, tyT) with
    (* S-Rcd: Handles Width, Depth, and Permutation *)
    | (TyRcd fieldsS, TyRcd fieldsT) ->
        List.for_all (fun (l, tyT_field) ->
          try
            let tyS_field = List.assoc l fieldsS in
            subtype ctx tyS_field tyT_field
          with Not_found -> false
        ) fieldsT

    (* S-Arrow: Contravariant arg, Covariant result *)
    | (TyArr(s1, s2), TyArr(t1, t2)) ->
        (subtype ctx t1 s1) && (subtype ctx s2 t2)
    | _ -> false
;;


(*get the type of a term*)
let rec typeof ctx tm = match tm with 
  (* ... (Standard Bool/Nat/If/Succ cases) ... *)
    TmTrue -> TyBool
  | TmFalse -> TyBool
  | TmIf (t1, t2, t3) ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyBool then
        let tyT2 = typeof ctx t2 in
        if (resolve_ty ctx (typeof ctx t3) []) = (resolve_ty ctx tyT2 []) then tyT2
        else raise (Type_error "arms of conditional have different types")
      else raise (Type_error "guard of conditional not a boolean")
  | TmZero -> TyNat
  | TmSucc t1 ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")
  | TmPred t1 ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")
  | TmIsZero t1 ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")
  | TmVar x -> gettbinding ctx x 

  | TmAbs (x, tyT1, t2) ->
      let tyT1_resolved = resolve_ty ctx tyT1 [] in
      let ctx' = addtbinding ctx x tyT1_resolved in
      let tyT2 = typeof ctx' t2 in
      TyArr (tyT1_resolved, tyT2)

  (* [MOD] Application now uses Subtyping check instead of strict equality *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match (resolve_ty ctx tyT1 []) with
           TyArr (tyT11, tyT12) ->
             if subtype ctx tyT2 tyT11 then tyT12 (* Subtype Check *)
             else raise (Type_error "parameter type mismatch")
         | _ -> raise (Type_error "arrow type expected"))

  | TmLetIn (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addtbinding ctx x tyT1 in
      typeof ctx' t2
  
  | TmFix t1 ->
      let tyT1 = typeof ctx t1 in
      (match (resolve_ty ctx tyT1 []) with
           TyArr (tyT11, tyT12) ->
             if tyT11 = tyT12 then tyT12
             else raise (Type_error "result of body not compatible with domain")
         | _ -> raise (Type_error "arrow type expected"))
  
  (* [EXT] String type checking *)
  | TmString _ -> TyString
  | TmConcat (t1, t2) ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyString && (resolve_ty ctx (typeof ctx t2) []) = TyString then
        TyString
      else raise (Type_error "arguments of concat are not all strings")

  (* [EXT] Tuple typing *)
  | TmTuple ts -> TyTuple (List.map (typeof ctx) ts)
  
  (* [EXT] Record typing *)
  | TmRcd fields ->
      let field_types = List.map (fun (lbl, term_field) -> (lbl, typeof ctx term_field)) fields in
      TyRcd field_types
  
  (* [EXT] Projection (handles both Records and Tuples via index string) *)
  | TmProj (t, lbl) ->
      (match (resolve_ty ctx (typeof ctx t) []) with
        | TyRcd fields ->
            (try List.assoc lbl fields
             with Not_found -> raise (Type_error ("label "^lbl^" not found in record")))
        | TyTuple tys ->
            (try 
              let index = int_of_string lbl in
              List.nth tys (index-1)
             with Failure _ | Invalid_argument _ -> raise (Type_error ("invalid tuple index: " ^ lbl)))
        | _ -> raise (Type_error "argument of projection is not a record"))
  
  (* [EXT] Variant injection typing *)
  | TmVariant (l, t, ty) ->
      (match (resolve_ty ctx ty []) with
        TyVariant fields ->
          (try 
            let ty_expected = List.assoc l fields in
            let ty_t = typeof ctx t in
            if (resolve_ty ctx ty_t []) = (resolve_ty ctx ty_expected []) then ty
            else raise (Type_error "type of variant does not match declared type")
          with
            Not_found -> raise (Type_error ("label " ^ l ^ " not found in variant type")))
        | _ -> raise (Type_error "expected a variant type"))

    (* [EXT] Case / Pattern Matching typing *)
  | TmCase (t, branches) ->
      (match (resolve_ty ctx (typeof ctx t) []) with
        TyVariant fields ->
            if branches = [] then raise (Type_error "case expression has no branches");
            let (first_label, first_var, first_branch) = List.hd branches in 
            let ty_field1 = (try List.assoc first_label fields with 
                           Not_found -> raise (Type_error ("label " ^ first_label ^ " not found in variant type"))) in
            let ctx' = addtbinding ctx first_var ty_field1 in
            let ty_result = typeof ctx' first_branch in

            (* Check all branches return the same type *)
            List.iter (fun (l, v, br) ->
              let ty_field = (try List.assoc l fields with
                                Not_found -> raise (Type_error ("label " ^ l ^ " not found in variant type"))) in
              let ctx'' = addtbinding ctx v ty_field in
              let ty_br = typeof ctx'' br in
              if ty_br <> ty_result then raise (Type_error "all branches of case must have the same type")
            ) (List.tl branches);
            ty_result
        | _ -> raise (Type_error "expected a variant type"))

  (* [EXT] List Typing rules *)
  | TmNil ty -> TyList (resolve_ty ctx ty [])
  | TmCons (ty, t1, t2) -> 
      let ty' = resolve_ty ctx ty [] in
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      if (resolve_ty ctx tyT1 []) <> ty' then raise (Type_error "tipo de la cabeza de la lista incorrecto");
      if (resolve_ty ctx tyT2 []) <> TyList ty' then raise (Type_error "tipo de la cola de la lista incorrecto");
      TyList ty'
  | TmIsNil (ty, t) ->
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then raise (Type_error "isnil se aplica sobre un tipo no-lista");
      TyBool
  | TmHead (ty, t) -> 
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then raise (Type_error "head se aplica sobre un tipo no-lista");
      ty' 
  | TmTail (ty, t) -> 
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then raise (Type_error "tail se aplica sobre un tipo no-lista");
      TyList ty' 
;;


(* TERMS MANAGEMENT (EVALUATION) *)

(* [MOD] Pretty printing extended for Case, Tuples, Variants, Lists *)
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
  (* ... helpers omitted ... *)
and print_field fmt (l, t) = fprintf fmt "%s = %a" l print_term t
and print_branch fmt (l, x, t) = fprintf fmt "<%s=%s> => %a" l x print_term t
;;

let string_of_term t =
  let buf = Buffer.create 100 in
  let fmt = formatter_of_buffer buf in
  print_term fmt t;
  pp_print_flush fmt ();
  Buffer.contents buf
;;

(* ... (free_vars, ldif, lunion omitted for brevity) ... *)
let rec ldif l1 l2 = match l1 with [] -> [] | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2) ;;
let rec lunion l1 l2 = match l1 with [] -> l2 | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2) ;;

let rec free_vars tm = match tm with 
  (* ... (Standard cases omitted) ... *)
    TmTrue -> []
  | TmFalse -> []
  | TmIf (t1, t2, t3) -> lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero -> []
  | TmSucc t -> free_vars t
  | TmPred t -> free_vars t
  | TmIsZero t -> free_vars t
  | TmVar s -> [s]
  | TmAbs (s, _, t) -> ldif (free_vars t) [s]
  | TmApp (t1, t2) -> lunion (free_vars t1) (free_vars t2)
  | TmLetIn (s, t1, t2) -> lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmFix t -> free_vars t
  (* [EXT] Free vars for new terms *)
  | TmString _ -> []
  | TmConcat (t1, t2) -> lunion (free_vars t1) (free_vars t2)
  | TmTuple ts -> List.fold_left lunion [] (List.map free_vars ts)
  | TmRcd fields -> List.fold_left lunion [] (List.map (fun (_, t) -> free_vars t) fields)
  | TmProj (t, _) -> free_vars t
  | TmVariant (_, t, _) -> free_vars t
  | TmCase (t, branches) ->
      let fv_t = free_vars t in
      let fv_branches = List.map (fun (l, x, b) -> ldif (free_vars b) [x]) branches in
      List.fold_left lunion fv_t fv_branches
  | TmNil _ -> []
  | TmCons (_, t1, t2) -> lunion (free_vars t1) (free_vars t2)
  | TmIsNil (_, t) -> free_vars t
  | TmHead (_, t) -> free_vars t
  | TmTail (_, t) -> free_vars t


let rec fresh_name x l = if not (List.mem x l) then x else fresh_name (x ^ "'") l ;;

let rec subst x s tm = match tm with 
  (* ... (Standard cases omitted) ... *)
    TmTrue -> TmTrue
  | TmFalse -> TmFalse
  | TmIf (t1, t2, t3) -> TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero -> TmZero
  | TmSucc t -> TmSucc (subst x s t)
  | TmPred t -> TmPred (subst x s t)
  | TmIsZero t -> TmIsZero (subst x s t)
  | TmVar y -> if y = x then s else tm
  | TmAbs (y, tyY, t) ->
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t))
  | TmApp (t1, t2) -> TmApp (subst x s t1, subst x s t2)
  | TmLetIn (y, t1, t2) ->
      if y = x then TmLetIn (y, subst x s t1, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLetIn (y, subst x s t1, subst x s t2)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLetIn (z, subst x s t1, subst x s (subst y (TmVar z) t2))
  | TmFix t -> TmFix (subst x s t)
  (* [EXT] Substitution for Strings, Tuples, Records *)
  | TmString str -> TmString str
  | TmConcat (t1, t2) -> TmConcat (subst x s t1, subst x s t2)
  | TmTuple ts -> TmTuple (List.map (subst x s) ts)
  | TmRcd fields -> TmRcd (List.map (fun (lbl, t) -> (lbl, subst x s t)) fields)
  | TmProj (t, n) -> TmProj (subst x s t, n)
  | TmVariant (l, t, ty) -> TmVariant (l, subst x s t, ty)
  (* [EXT] Substitution for Case (handles variable binding in branches) *)
  | TmCase (t, branches) -> 
      let new_branches = List.map (fun (l, v, b) ->
          if v = x then (l, v, b)
          else 
            let z = fresh_name v (free_vars s) in
            let b' = subst v (TmVar z) b in
            (l, z, subst x s b')
      ) branches in
      TmCase (subst x s t, new_branches)
  (* [EXT] Substitution for Lists *)
  | TmNil ty -> TmNil ty
  | TmCons (ty, t1, t2) -> TmCons (ty, subst x s t1, subst x s t2)
  | TmIsNil (ty, t) -> TmIsNil (ty, subst x s t)
  | TmHead (ty, t) -> TmHead (ty, subst x s t)
  | TmTail (ty, t) -> TmTail (ty, subst x s t)
;;

let rec isnumericval tm = match tm with TmZero -> true | TmSucc t -> isnumericval t | _ -> false ;;

let rec isval tm = match tm with 
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | t when isnumericval t -> true
  (* [EXT] Value checks for extensions *)
  | TmString _ -> true
  | TmTuple ts -> List.for_all isval ts
  | TmRcd fields -> List.for_all (fun (_, t) -> isval t) fields
  | TmVariant (l, t, _) -> isval t
  | TmNil _ -> true
  | TmCons (_, v1, v2) -> isval v1 && isval v2
  | _ -> false
;;

exception NoRuleApplies ;;

(*eval a term*)
let rec eval1 ctx tm = match tm with 
  (* ... (Standard If/Succ/Pred/IsZero cases) ... *)
    TmIf (TmTrue, t2, _) -> t2
  | TmIf (TmFalse, _, t3) -> t3
  | TmIf (t1, t2, t3) -> let t1' = eval1 ctx t1 in TmIf (t1', t2, t3)
  | TmSucc t1 -> let t1' = eval1 ctx t1 in TmSucc t1'
  | TmPred TmZero -> TmZero
  | TmPred (TmSucc nv1) when isnumericval nv1 -> nv1
  | TmPred t1 -> let t1' = eval1 ctx t1 in TmPred t1'
  | TmIsZero TmZero -> TmTrue
  | TmIsZero (TmSucc nv1) when isnumericval nv1 -> TmFalse
  | TmIsZero t1 -> let t1' = eval1 ctx t1 in TmIsZero t1'
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 -> subst x v2 t12
  | TmApp (v1, t2) when isval v1 -> let t2' = eval1 ctx t2 in TmApp (v1, t2')
  | TmApp (t1, t2) -> let t1' = eval1 ctx t1 in TmApp (t1', t2)
  | TmLetIn (x, v1, t2) when isval v1 -> subst x v1 t2
  | TmLetIn(x, t1, t2) -> let t1' = eval1 ctx t1 in TmLetIn (x, t1', t2)
  | TmFix (TmAbs (x, _, t2)) -> subst x tm t2
  | TmFix t1 -> let t1' = eval1 ctx t1 in TmFix t1'

  (* [EXT] Projection for Tuples/Records *)
  (* En lambda.ml, dentro de 'rec eval1 ctx tm = match tm with' ... *)

  (* 1. Intenta proyectar si es una TUPLA literal *)
  | TmProj (TmTuple ts, n) ->
      (try List.nth ts ((int_of_string n)-1)
       with Failure _ | Invalid_argument _ -> raise NoRuleApplies)

  (* 2. Intenta proyectar si es un RECORD literal *)
  | TmProj (TmRcd fields, lbl) ->
      (try List.assoc lbl fields
       with Not_found -> raise NoRuleApplies)
  
  (* 3. [NUEVO] REGLA DE CONGRUENCIA: Si no es valor, evalúa el interior *)
  | TmProj (t1, l) -> 
      let t1' = eval1 ctx t1 in TmProj (t1', l)


  (* [EXT] Evaluation of Tuples (left-to-right) *)
  | TmTuple ts ->
      let rec eval_step l_evaluados = function
        | [] -> raise NoRuleApplies 
        | h::t ->
            if isval h then eval_step (h::l_evaluados) t 
            else let h' = eval1 ctx h in TmTuple(List.rev l_evaluados @ (h'::t))
      in eval_step [] ts
  (* [EXT] Evaluation of Records *)
  | TmRcd fields ->
      let rec eval_field l_evaluados = function
        | [] -> raise NoRuleApplies 
        | (lbl, h)::t ->
            if isval h then eval_field ((lbl, h)::l_evaluados) t
            else let h' = eval1 ctx h in TmRcd (List.rev l_evaluados @ ((lbl, h')::t))
      in eval_field [] fields

  (* [EXT] Variant evaluation *)
  | TmVariant (l, t, ty) when not (isval t) -> TmVariant (l, eval1 ctx t, ty)
      
  (* [EXT] Case execution (pattern matching) *)
  | TmCase (TmVariant (l_val, v, _), branches) when isval v ->
      (try
         let (x, b) = List.assoc l_val (List.map (fun (l,x,b) -> (l,(x,b))) branches) in
         subst x v b
       with Not_found -> raise NoRuleApplies) 
  | TmCase (t, branches) -> let t' = eval1 ctx t in TmCase (t', branches)

  (* [EXT] String Concatenation *)
  | TmConcat (TmString s1, TmString s2) -> TmString (s1 ^ s2)
  | TmConcat (t1, t2) when isval t1 -> let t2' = eval1 ctx t2 in TmConcat (t1, t2')
  | TmConcat (t1, t2) -> let t1' = eval1 ctx t1 in TmConcat (t1', t2)

  (* [EXT] List Evaluation (Cons, IsNil, Head, Tail) *)
  | TmCons (ty, t1, t2) when not (isval t1) -> TmCons (ty, eval1 ctx t1, t2)
  | TmCons (ty, v1, t2) when isval v1 && not (isval t2) -> TmCons (ty, v1, eval1 ctx t2)
  | TmIsNil (ty, TmNil _) -> TmTrue
  | TmIsNil (ty, TmCons(_, _, _)) -> TmFalse
  | TmIsNil (ty, t) -> TmIsNil (ty, eval1 ctx t)
  | TmHead (ty, TmCons(_, v1, _)) -> v1
  | TmHead (ty, TmNil _) -> raise NoRuleApplies 
  | TmHead (ty, t) -> TmHead (ty, eval1 ctx t)
  | TmTail (ty, TmCons(_, _, v2)) -> v2
  | TmTail (ty, TmNil _) -> raise NoRuleApplies 
  | TmTail (ty, t) -> TmTail (ty, eval1 ctx t)
  
  | TmVar s -> getvbinding ctx s
  | _ -> raise NoRuleApplies
;;

let apply_ctx ctx1 ctx2 = 
List.fold_left (fun t x -> subst x (getvbinding ctx2 x) t ) ctx1 (free_vars ctx1)
;;


let rec eval ctx tm = 
  try let tm' = eval1 ctx tm in eval ctx tm'
  with NoRuleApplies -> apply_ctx tm ctx
;;


let execute ctx = function
  Eval tm ->
    (match tm with
     | TmVar x -> 
         let ty = gettbinding ctx x in
         (try
            let val_tm = eval ctx tm in
            print_endline (x ^ " : " ^ string_of_ty ty ^ " = " ^ string_of_term val_tm)
          with Not_found -> print_endline (x ^ " : " ^ string_of_ty ty)) ; ctx
     | _ ->
         let tyT = typeof ctx tm in
         let tm' = eval ctx tm in
         print_endline (string_of_term tm' ^ " : " ^ string_of_ty tyT); ctx
    )
  | Bind (x, t) ->
    let tyTm, tm' = match t with
      | TmVar y ->
          let ty = gettbinding ctx y in       
          let v = try getvbinding ctx y with Not_found -> TmVar y in (ty, v)
      | _ ->
          let ty = typeof ctx t in
          let v = eval ctx t in (ty, v)
    in
    let tyTm_resolved = resolve_ty ctx tyTm [] in
    print_endline (x ^ " : " ^ string_of_ty tyTm_resolved ^ " = " ^ string_of_term tm');
    addvbinding ctx x tyTm tm'

  (* [EXT] Handling of Type Alias Definitions (type T = ...) *)
  | BindTy (s, ty) ->
      (try
        let ty' = resolve_ty ctx ty [] in
        print_endline (s ^ " = " ^ string_of_ty ty');
        addtbinding ctx s ty'
      with
        Type_error e -> print_endline ("type error: " ^ e); ctx
      | Type_alias_loop e -> print_endline ("type error: " ^ e); ctx)
  | Quit -> raise End_of_file
  ;;


