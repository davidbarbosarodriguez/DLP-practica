(* ========== TYPE DEFINITIONS ========== *)

(* Custom exceptions for type checking errors *)
exception Type_error of string
exception Type_alias_loop of string

(* Type definitions for our lambda calculus *)
type ty =
    TyBool                          (* Boolean type *)
  | TyNat                           (* Natural numbers *)
  | TyArr of ty * ty                (* Function types: T1 -> T2 *)
  | TyString                        (* String literals *)
  | TyVar of string                 (* Type aliases (named types) *)
  | TyTuple of ty list              (* Tuple types: {T1, T2, ...} *)
  | TyRcd of (string * ty) list     (* Record types: {l1:T1, l2:T2} *)
  | TyVariant of (string * ty) list (* Variant/sum types: <l1:T1 | l2:T2> *)
  | TyList of ty                    (* List types: List T *)
;;

(* Term definitions - the actual expressions in our language *)
type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term      (* if-then-else conditionals *)
  | TmZero                           (* The number 0 *)
  | TmSucc of term                   (* Successor function *)
  | TmPred of term                   (* Predecessor function *)
  | TmIsZero of term                 (* Check if a number is zero *)
  | TmVar of string                  (* Variables *)
  | TmAbs of string * ty * term      (* Lambda abstraction: λx:T.t *)
  | TmApp of term * term             (* Function application *)
  | TmLetIn of string * term * term  (* Let bindings: let x = t1 in t2 *)
  | TmFix of term                    (* Fixed-point combinator (for recursion) *)
  | TmString of string               (* String literals *)
  | TmConcat of term * term          (* String concatenation *)
  | TmTuple of term list             (* Tuple construction *)
  | TmProj of term * string          (* Projection (access tuple/record fields) *)
  | TmRcd of (string * term) list    (* Record construction *)
  | TmVariant of string * term * ty  (* Variant injection *)
  | TmCase of term * (string * string * term) list  (* Pattern matching *)
  | TmNil of ty                      (* Empty list *)
  | TmCons of ty * term * term       (* List construction (cons) *)
  | TmIsNil of ty * term             (* Check if list is empty *)
  | TmHead of ty * term              (* Get first element of list *)
  | TmTail of ty * term              (* Get rest of list *)
;;

(* Commands that can be executed in the REPL *)
type command =
    Bind of string * term    (* Bind a variable: x = t *)
  | BindTy of string * ty    (* Register a type alias: type T = Nat *)
  | Eval of term             (* Evaluate a term *)
  | Quit                     (* Exit the interpreter *)
;;

(* Bindings stored in the context *)
type binding =
    TyBind of ty              (* Type-only binding (for type aliases) *)
  | TyTmBind of (ty * term)   (* Type and term binding (for variables) *)
;;

(* Context maps variable names to their bindings *)
type context = (string * binding) list ;;

(* Context manipulation functions *)
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


open Format

(* Pretty-print types with proper formatting *)
let rec print_ty fmt ty = match ty with
  | TyBool -> fprintf fmt "Bool"
  | TyNat -> fprintf fmt "Nat"
  | TyString -> fprintf fmt "String"
  | TyVar s -> fprintf fmt "%s" s
  | TyList ty -> fprintf fmt "List %a" print_atomic_ty ty
  | TyArr (t1, t2) ->
      fprintf fmt "@[%a ->@ %a@]" print_atomic_ty t1 print_ty t2
  | TyTuple [] -> fprintf fmt "Unit"

  | TyTuple tys ->
      (* Print tuples like {Nat, Bool} *)
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_ty) tys
  | TyRcd fields ->
      fprintf fmt "{@[<hov>%a@]}" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field_ty) fields
  | TyVariant fields ->
      fprintf fmt "<@[<hov>%a@]>" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") print_field_ty) fields

(* Print atomic types (add parentheses when needed) *)
and print_atomic_ty fmt ty = match ty with
  | TyArr _ -> fprintf fmt "(%a)" print_ty ty
  | TyList _ -> fprintf fmt "(%a)" print_ty ty
  | _ -> print_ty fmt ty

(* Print record/variant field types *)
and print_field_ty fmt (l, ty) =
  fprintf fmt "%s : %a" l print_ty ty
;;

(* Convert type to string *)
let string_of_ty ty =
  let buf = Buffer.create 100 in
  let fmt = formatter_of_buffer buf in
  print_ty fmt ty;
  pp_print_flush fmt ();
  Buffer.contents buf
;;


(* Resolve type aliases to their actual types, detecting cycles *)
let rec resolve_ty ctx ty seen_aliases = match ty with
  | TyVar s ->
      (* Check for circular type alias definitions *)
      if List.mem s seen_aliases then
        raise (Type_alias_loop ("Loop detected in type alias: " ^ s));
      let ty' = (try gettbinding ctx s with Not_found -> raise (Type_error ("Type alias not found: " ^ s))) in
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

(* 
 * Implement subtyping rules:
 * - S-Refl: Every type is a subtype of itself
 * - S-Rcd: Record subtyping (width, depth, permutation)
 * - S-Arrow: Function subtyping (contravariant in argument, covariant in result)
 *)
let rec subtype ctx tyS tyT =
  (* Resolve aliases first to compare actual types *)
  let tyS = resolve_ty ctx tyS [] in
  let tyT = resolve_ty ctx tyT [] in
  
  if tyS = tyT then true (* Reflexivity: S <: S *)
  else
    match (tyS, tyT) with
    (* Record subtyping: S is a subtype of T if S has all fields of T with compatible types *)
      | (TyRcd _, TyTuple []) -> true
    
      | (TyRcd fieldsS, TyRcd fieldsT) ->
        List.for_all (fun (l, tyT_field) ->
          try
            let tyS_field = List.assoc l fieldsS in
            subtype ctx tyS_field tyT_field
          with Not_found -> false
        ) fieldsT

    (* Arrow subtyping: contravariant in argument, covariant in result *)
    | (TyArr(s1, s2), TyArr(t1, t2)) ->
        (subtype ctx t1 s1) && (subtype ctx s2 t2)
    | _ -> false
;;


(* The main type-checking function *)
let rec typeof ctx tm = match tm with 
  (* Boolean constants have type Bool *)
  | TmTrue -> TyBool
  | TmFalse -> TyBool
  
  (* If-then-else: guard must be Bool, branches must have same type *)
  | TmIf (t1, t2, t3) ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyBool then
        let tyT2 = typeof ctx t2 in
        if (resolve_ty ctx (typeof ctx t3) []) = (resolve_ty ctx tyT2 []) then tyT2
        else raise (Type_error "arms of conditional have different types")
      else raise (Type_error "guard of conditional not a boolean")
  
  (* Natural number operations *)
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
  
  (* Variables: look up their type in the context *)
  | TmVar x -> gettbinding ctx x 

  (* Lambda abstraction: add parameter to context and type-check body *)
  | TmAbs (x, tyT1, t2) ->
      let tyT1_resolved = resolve_ty ctx tyT1 [] in
      let ctx' = addtbinding ctx x tyT1_resolved in
      let tyT2 = typeof ctx' t2 in
      TyArr (tyT1_resolved, tyT2)

  (* Function application: check that argument type is compatible with parameter *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match (resolve_ty ctx tyT1 []) with
           TyArr (tyT11, tyT12) ->
             if subtype ctx tyT2 tyT11 then tyT12 (* Use subtyping instead of exact equality *)
             else raise (Type_error "parameter type mismatch")
         | _ -> raise (Type_error "arrow type expected"))

  (* Let binding: type-check bound expression and add to context *)
  | TmLetIn (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addtbinding ctx x tyT1 in
      typeof ctx' t2
  
  (* Fixed-point: type must be T -> T *)
  | TmFix t1 ->
      let tyT1 = typeof ctx t1 in
      (match (resolve_ty ctx tyT1 []) with
           TyArr (tyT11, tyT12) ->
             if tyT11 = tyT12 then tyT12
             else raise (Type_error "result of body not compatible with domain")
         | _ -> raise (Type_error "arrow type expected"))
  
  (* String operations *)
  | TmString _ -> TyString
  | TmConcat (t1, t2) ->
      if (resolve_ty ctx (typeof ctx t1) []) = TyString && (resolve_ty ctx (typeof ctx t2) []) = TyString then
        TyString
      else raise (Type_error "arguments of concat are not all strings")

  (* Tuple: type is tuple of element types *)
  | TmTuple ts -> TyTuple (List.map (typeof ctx) ts)
  
  (* Record: type is record of field types *)
  | TmRcd fields ->
      let field_types = List.map (fun (lbl, term_field) -> (lbl, typeof ctx term_field)) fields in
      TyRcd field_types
  
  (* Projection: extract type of field from record or tuple *)
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
  
  (* Variant injection: check that label exists and value has correct type *)
  | TmVariant (l, t, ty) ->
      (match (resolve_ty ctx ty []) with
        TyVariant fields ->
          (try 
            let ty_expected = List.assoc l fields in
            let ty_t = typeof ctx t in
            if subtype ctx ty_t ty_expected then ty
            else raise (Type_error "type of variant does not match declared type")
          with
            Not_found -> raise (Type_error ("label " ^ l ^ " not found in variant type")))
        | _ -> raise (Type_error "expected a variant type"))

  (* Pattern matching: all branches must return the same type *)
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

  (* List operations *)
  | TmNil ty -> TyList (resolve_ty ctx ty [])
  | TmCons (ty, t1, t2) -> 
      let ty' = resolve_ty ctx ty [] in
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      if (resolve_ty ctx tyT1 []) <> ty' then raise (Type_error "head of list has incorrect type");
      if (resolve_ty ctx tyT2 []) <> TyList ty' then raise (Type_error "tail of list has incorrect type");
      TyList ty'
  | TmIsNil (ty, t) ->
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then raise (Type_error "isnil applied to non-list type");
      TyBool
  | TmHead (ty, t) -> 
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then raise (Type_error "head applied to non-list type");
      ty' 
  | TmTail (ty, t) -> 
      let ty' = resolve_ty ctx ty [] in
      let tyT = typeof ctx t in
      if (resolve_ty ctx tyT []) <> TyList ty' then raise (Type_error "tail applied to non-list type");
      TyList ty' 
;;


(* Pretty-print terms with proper precedence *)
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
      (* Pretty-print natural numbers as decimal *)
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
  | TmTuple [] -> fprintf fmt "unit"
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

(* Set operations for variable lists *)
let rec ldif l1 l2 = match l1 with [] -> [] | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2) ;;
let rec lunion l1 l2 = match l1 with [] -> l2 | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2) ;;

(* Compute the set of free variables in a term *)
let rec free_vars tm = match tm with 
  | TmTrue -> []
  | TmFalse -> []
  | TmIf (t1, t2, t3) -> lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero -> []
  | TmSucc t -> free_vars t
  | TmPred t -> free_vars t
  | TmIsZero t -> free_vars t
  | TmVar s -> [s]
  | TmAbs (s, _, t) -> ldif (free_vars t) [s]  (* Remove bound variable *)
  | TmApp (t1, t2) -> lunion (free_vars t1) (free_vars t2)
  | TmLetIn (s, t1, t2) -> lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmFix t -> free_vars t
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

(* Generate a fresh variable name not in the given list *)
let rec fresh_name x l = if not (List.mem x l) then x else fresh_name (x ^ "'") l ;;


(* Capture-avoiding substitution: replace x with s in tm *)
let rec subst x s tm = match tm with 
  | TmTrue -> TmTrue
  | TmFalse -> TmFalse
  | TmIf (t1, t2, t3) -> TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero -> TmZero
  | TmSucc t -> TmSucc (subst x s t)
  | TmPred t -> TmPred (subst x s t)
  | TmIsZero t -> TmIsZero (subst x s t)
  | TmVar y -> if y = x then s else tm
  | TmAbs (y, tyY, t) ->
      if y = x then tm  (* Variable is shadowed *)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else (* Rename to avoid capture *)
                let z = fresh_name y (free_vars t @ fvs) in
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
  | TmString str -> TmString str
  | TmConcat (t1, t2) -> TmConcat (subst x s t1, subst x s t2)
  | TmTuple ts -> TmTuple (List.map (subst x s) ts)
  | TmRcd fields -> TmRcd (List.map (fun (lbl, t) -> (lbl, subst x s t)) fields)
  | TmProj (t, n) -> TmProj (subst x s t, n)
  | TmVariant (l, t, ty) -> TmVariant (l, subst x s t, ty)
  | TmCase (t, branches) -> 
      let new_branches = List.map (fun (l, v, b) ->
          if v = x then (l, v, b)  (* Variable is shadowed in this branch *)
          else 
            let z = fresh_name v (free_vars s) in
            let b' = subst v (TmVar z) b in
            (l, z, subst x s b')
      ) branches in
      TmCase (subst x s t, new_branches)
  | TmNil ty -> TmNil ty
  | TmCons (ty, t1, t2) -> TmCons (ty, subst x s t1, subst x s t2)
  | TmIsNil (ty, t) -> TmIsNil (ty, subst x s t)
  | TmHead (ty, t) -> TmHead (ty, subst x s t)
  | TmTail (ty, t) -> TmTail (ty, subst x s t)
;;


(* Check if a term is a numeric value (0, succ 0, succ succ 0, ...) *)
let rec isnumericval tm = match tm with TmZero -> true | TmSucc t -> isnumericval t | _ -> false ;;

(* Check if a term is a value (fully evaluated) *)
let rec isval tm = match tm with 
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | t when isnumericval t -> true
  | TmString _ -> true
  | TmTuple ts -> List.for_all isval ts
  | TmRcd fields -> List.for_all (fun (_, t) -> isval t) fields
  | TmVariant (l, t, _) -> isval t
  | TmNil _ -> true
  | TmCons (_, v1, v2) -> isval v1 && isval v2
  | _ -> false
;;

exception NoRuleApplies ;;

(* Single-step evaluation (small-step semantics) *)
let rec eval1 ctx tm = match tm with 
  (* Conditional evaluation *)
  | TmIf (TmTrue, t2, _) -> t2
  | TmIf (TmFalse, _, t3) -> t3
  | TmIf (t1, t2, t3) -> let t1' = eval1 ctx t1 in TmIf (t1', t2, t3)
  
  (* Successor *)
  | TmSucc t1 -> let t1' = eval1 ctx t1 in TmSucc t1'
  
  (* Predecessor *)
  | TmPred TmZero -> TmZero
  | TmPred (TmSucc nv1) when isnumericval nv1 -> nv1
  | TmPred t1 -> let t1' = eval1 ctx t1 in TmPred t1'
  
  (* IsZero *)
  | TmIsZero TmZero -> TmTrue
  | TmIsZero (TmSucc nv1) when isnumericval nv1 -> TmFalse
  | TmIsZero t1 -> let t1' = eval1 ctx t1 in TmIsZero t1'
  
  (* Beta-reduction for function application *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 -> subst x v2 t12
  | TmApp (v1, t2) when isval v1 -> let t2' = eval1 ctx t2 in TmApp (v1, t2')
  | TmApp (t1, t2) -> let t1' = eval1 ctx t1 in TmApp (t1', t2)
  
  (* Let binding *)
  | TmLetIn (x, v1, t2) when isval v1 -> subst x v1 t2
  | TmLetIn(x, t1, t2) -> let t1' = eval1 ctx t1 in TmLetIn (x, t1', t2)
  | TmFix (TmAbs (x, _, t2)) -> subst x tm t2
  | TmFix t1 -> let t1' = eval1 ctx t1 in TmFix t1'

  (* Projection for Tuples/Records *)

  (* 1. Try to project a tuple *)
  | TmProj (TmTuple ts, n) ->
      (try List.nth ts ((int_of_string n)-1)
       with Failure _ | Invalid_argument _ -> raise NoRuleApplies)

  (* 2. Try to project if it is a RECORD literal *)
  | TmProj (TmRcd fields, lbl) ->
      (try List.assoc lbl fields
       with Not_found -> raise NoRuleApplies)
  
  (* 3.Congruence rule: If it is not a value, evaluate the interior *)
  | TmProj (t1, l) -> 
      let t1' = eval1 ctx t1 in TmProj (t1', l)


  (* Evaluation of Tuples (left-to-right) *)
  | TmTuple ts ->
      let rec eval_step l_evaluados = function
        | [] -> raise NoRuleApplies 
        | h::t ->
            if isval h then eval_step (h::l_evaluados) t 
            else let h' = eval1 ctx h in TmTuple(List.rev l_evaluados @ (h'::t))
      in eval_step [] ts
  (* Evaluation of Records *)
  | TmRcd fields ->
      let rec eval_field l_evaluados = function
        | [] -> raise NoRuleApplies 
        | (lbl, h)::t ->
            if isval h then eval_field ((lbl, h)::l_evaluados) t
            else let h' = eval1 ctx h in TmRcd (List.rev l_evaluados @ ((lbl, h')::t))
      in eval_field [] fields

  (* Variant evaluation *)
  | TmVariant (l, t, ty) when not (isval t) -> TmVariant (l, eval1 ctx t, ty)
      
  (* Case execution (pattern matching) *)
  | TmCase (TmVariant (l_val, v, _), branches) when isval v ->
      (try
         let (x, b) = List.assoc l_val (List.map (fun (l,x,b) -> (l,(x,b))) branches) in
         subst x v b
       with Not_found -> raise NoRuleApplies) 
  | TmCase (t, branches) -> let t' = eval1 ctx t in TmCase (t', branches)

  (* String Concatenation *)
  | TmConcat (TmString s1, TmString s2) -> TmString (s1 ^ s2)
  | TmConcat (t1, t2) when isval t1 -> let t2' = eval1 ctx t2 in TmConcat (t1, t2')
  | TmConcat (t1, t2) -> let t1' = eval1 ctx t1 in TmConcat (t1', t2)

  (* List Evaluation (Cons, IsNil, Head, Tail) *)
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
  (* Var evaluation *)
  | TmVar s -> getvbinding ctx s
  | _ -> raise NoRuleApplies
;;

(* Apply substitutions for all free variables in ctx2 to ctx1 *)
let apply_ctx ctx1 ctx2 = 
List.fold_left (fun t x -> subst x (getvbinding ctx2 x) t ) ctx1 (free_vars ctx1)
;;

(* Full evaluation to normal form *)
let rec eval ctx tm = 
  try let tm' = eval1 ctx tm in eval ctx tm'
  with NoRuleApplies -> apply_ctx tm ctx
;;

(* Execute a command in the given context, returning the updated context *)
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

  (* Handling of Type Alias Definitions (type T = ...) *)
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


