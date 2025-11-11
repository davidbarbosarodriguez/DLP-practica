(* TYPE DEFINITIONS *)

type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString 
  | TyVar of string
  | TyTuple of ty list
  | TyRcd of (string * ty) list
  | TyVariant of (string * ty) list
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
  | TmTuple of term list
  | TmProj of term * string
  | TmRcd of (string * term) list
  | TmVariant of string * term * ty
  | TmCase of term * (string * string * term) list
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

let rec string_of_ty ty =
  match ty with
  | TyBool -> "Bool"
  | TyNat -> "Nat"
  | TyString -> "String"
  | TyVar s -> s
  | TyArr (ty1, ty2) ->
      let s1 =
        match ty1 with
        | TyArr _ -> "(" ^ string_of_ty ty1 ^ ")"
        | _ -> string_of_ty ty1
      in
      let s2 = string_of_ty ty2 in
      s1 ^ " -> " ^ s2
  | TyTuple tys ->
      "{" ^ (String.concat " , " (List.map string_of_ty tys)) ^ "}"
  | TyRcd fields ->
      let field_strings = List.map (fun (label, ty) -> label ^ ": " ^ string_of_ty ty) fields in
      "{" ^ (String.concat " , " field_strings) ^   "}"
  | TyVariant fields -> 
      let s_fields = List.map (fun (l, ty) -> l ^ ":" ^ string_of_ty ty) fields in
      "<" ^ (String.concat ", " s_fields) ^ ">"
  
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
  | TmVar x -> gettbinding ctx x (*que hace el try with *)


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
    (* T-Tuple *)
  | TmTuple ts ->
      TyTuple (List.map (typeof ctx) ts)
    (* T-Proj *)
  | TmRcd fields ->
      let field_types = List.map (fun (lbl, term_field) -> (lbl, typeof ctx term_field)) fields in
      TyRcd field_types

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
  
    (* T-Variant *)
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
    (* T-Case *)
  | TmCase (t, branches) ->
      (match (resolve_ty ctx (typeof ctx t) []) with
        TyVariant fields ->
            if branches = [] then
              raise (Type_error "case expression has no branches");
            let (first_label, first_var, first_branch) = List.hd branches in
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
  | TmTuple ts ->
      "{" ^ (String.concat ", " (List.map string_of_term ts)) ^ "}"
  | TmRcd fields ->
      let field_strings =
        List.map (fun (lbl, t) -> lbl ^ " = " ^ string_of_term t) fields
      in
      "{" ^ (String.concat ", " field_strings) ^ "}"
  | TmProj (t, lbl) ->
      (match t with
      | TmRcd fields ->
          (try string_of_term (List.assoc lbl fields)
            with Not_found -> raise (Type_error ("label "^lbl^" not found in record")))
        | TmTuple ts ->
            (try string_of_term (List.nth ts (int_of_string lbl - 1))
              with Failure _ | Invalid_argument _ -> raise (Type_error ("invalid tuple index: " ^ lbl)))
      | _ ->
          "(" ^ string_of_term t ^ ")." ^ lbl)
  | TmVariant (l, t, ty) ->
      "<" ^ l ^ "=" ^ string_of_term t ^ ">"

  | TmCase (t, branches) ->
      let string_branches = List.map (fun (l, x, t_branch) ->
        "<" ^ l ^ "=" ^ x ^ "> => " ^ string_of_term t_branch) branches
      in
      "case " ^ string_of_term t ^ " of " ^ String.concat " | " string_branches
  
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
  | TmTuple ts -> List.for_all isval ts
  | TmRcd fields -> List.for_all (fun (_, t) -> isval t) fields
  | TmVariant (l, t, _) -> isval t
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
        | [] -> raise NoRuleApplies (* Ya es un valor *)
        | h::t ->
            if isval h then
              eval_step (h::l_evaluados) t
            else
              (* Encontrado un no-valor, evalúalo *)
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
              (* Encontrado un no-valor, evalúalo *)
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
      let tyTm_resolved = resolve_ty ctx tyTm [] in
      print_endline (x ^ " : " ^ string_of_ty tyTm_resolved ^ " = " ^ string_of_term tm');
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


