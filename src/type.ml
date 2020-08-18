(** A type, with free type variables for polymorphic arguments. *)
open Types
open SmartPrint
open Monad.Notations

type t =
  | Variable of Name.t
  | Kind of Kind.t
  | Arrow of t * t
  | Eq of t * t
  | Sum of (string * t) list
  | Tuple of t list
  | Apply of MixedPath.t * t list
  | Package of bool * PathName.t * arity_or_typ Tree.t
  | ForallModule of Name.t * t * t
  | ForallTyps of Name.t list * t
  | String of string
  | FunTyps of Name.t list * t
  | Error of string
and arity_or_typ =
  | Arity of int
  | Typ of t

let tag_constructor_of
    (* (name : Name.t) *)
    (typ : t) =
  match typ with
  | Variable a -> "var " ^ (Name.to_string a)
  | Arrow _ -> "arrow"
  | Eq _ -> "eq"
  | Sum _ -> "sum"
  | Tuple _ -> "tuple"
  | Apply (mpath, _) -> MixedPath.to_string mpath
  | Package _ -> "package"
  | ForallModule _ -> "forallModule"
  | ForallTyps _ -> "forallTyps"
  | FunTyps _ -> "funTyps"
  | Error s -> "error" ^ s
  | Kind k -> Kind.to_string k
  | String s -> "string"

let rec tag_typ_constr_aux
    (typ : t)
  : t Monad.t =
  let tag_ty = tag_typ_constr_aux in
  match typ with
  | Arrow (t1, t2) ->
    let* t1 = tag_ty t1 in
    let* t2 = tag_ty t2 in
    let tag = "arrow_tag" |> Name.of_string_raw |> MixedPath.of_name  in
    return (Apply (tag, [t1; t2]))
  | Tuple ts ->
    let tag = "tuple_tag" |> Name.of_string_raw |> MixedPath.of_name  in
    if List.length ts = 2
    then
      let* ts = Monad.List.map tag_ty ts in
      return (Apply (tag, ts))
    else
      let* t = tag_ty (List.hd ts) in
      let* ts = tag_ty @@ Tuple (List.tl ts) in
      return (Apply (tag, [t; ts]))
  | Apply (mpath, ts) ->
    let* ts = Monad.List.map tag_ty ts in
    let arg_names = List.map tag_constructor_of ts in
    let tag = "constr_tag" |> Name.of_string_raw |> MixedPath.of_name  in
    let name = (MixedPath.to_string mpath) in
    let str_repr = name ^
                   (List.fold_left (fun acc ty -> acc ^ "_" ^ ty) "" arg_names) in
    return (Apply (tag, [String str_repr; typ]))
  | _ -> return typ

let type_exprs_of_row_field (row_field : Types.row_field)
  : Types.type_expr list =
  match row_field with
  | Rpresent None -> []
  | Rpresent (Some typ) -> [typ]
  | Reither (_, typs, _, _) -> typs
  | Rabsent -> []

let filter_typ_params_in_valid_set
  (typ_params : AdtParameters.AdtVariable.t list) (valid_set : Name.Set.t) : bool list =
  typ_params |> List.map (function
      | AdtParameters.AdtVariable.Parameter name -> Name.Set.mem name valid_set
      | _ -> false )

let is_type_abstract
    (path : Path.t)
  : bool Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_kind = Type_abstract; _ } -> return @@ true
  | _ | exception _ -> return false

let is_new_type
    (path : Path.t)
  : bool Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_is_newtype = true; _ } -> return @@ true
  | _ | exception _ -> return false

let is_type_variant (t : Types.type_expr) : bool Monad.t =
  match t.desc with
  | Tconstr (path, _, _) ->
    let* is_variant = PathName.is_variant_declaration path in
    return @@ Option.is_some is_variant
  | _ -> return false

(** This function is utilized for building dependent pattern matching,
    if typ is a type constructor then it will return a list of equations
    relating each index of the type constructor to its real instantiation *)
let normalize_constructor (typ : t) : t * t list =
  match typ with
  | Apply (t, args) ->
    let (args, eqs) = args |> List.mapi (fun i typ ->
        let x = "t" ^ string_of_int i |> Name.of_string_raw in
        (Variable x, Eq (Variable x, typ))
      ) |> List.split in
    (Apply (t, args), eqs)
  | _ -> (typ, [])


(** Import an OCaml type. Add to the environment all the new free type variables. *)
let rec of_typ_expr_in_constr
  (constr : Path.t option)
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typ : Types.type_expr)
  : (t * Name.t Name.Map.t * VarEnv.t) Monad.t =
  match typ.desc with
  | Tvar x | Tunivar x ->
    (match x with
    | None ->
      if with_free_vars then
        let n = Name.Map.cardinal typ_vars in
        return (Printf.sprintf "A%d" typ.id, String.make 1 (Char.chr (Char.code 'A' + n)))
      else
        raise ("_", "_") NotSupported "The placeholders `_` in types are not handled"
    | Some x -> return (x, x)
    ) >>= fun (source_name, generated_name) ->
    let* source_name = Name.of_string false source_name in
    let* generated_name = Name.of_string false generated_name in
    let* constr_is_gadt = match constr with
      | Some constr -> PathName.is_gadt constr
      | None -> return false in
    let typ = if constr_is_gadt
      then Kind.Tag
      else Kind.Set in
    let new_typ_vars = [(generated_name, typ)] in
    let (typ_vars, name) =
      if Name.Map.mem source_name typ_vars
      then
        let name = Name.Map.find source_name typ_vars in
        (typ_vars, name)
      else
        let typ_vars = Name.Map.add source_name generated_name typ_vars in
        (typ_vars, generated_name) in
    return (Variable name, typ_vars, new_typ_vars)
  | Tarrow (_, typ_x, typ_y, _) ->
    of_typ_expr_in_constr constr with_free_vars typ_vars typ_x >>= fun (typ_x, typ_vars, new_typ_vars_x) ->
    of_typ_expr_in_constr constr with_free_vars typ_vars typ_y >>= fun (typ_y, typ_vars, new_typ_vars_y) ->
    let new_typ_vars = VarEnv.union new_typ_vars_x new_typ_vars_y in
    return (Arrow (typ_x, typ_y), typ_vars, new_typ_vars)
  | Ttuple typs ->
    of_typs_exprs_constr constr with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
    return (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, abbr) ->
    let* mixed_path = MixedPath.of_path false path None in
    let* is_abstract = is_type_abstract path in
    let* is_new_type = is_new_type path in
    (* For unknown reasons a type variable becomes a Tconstr some times (see type of patterns)
       This if is to try to figure out if such constructor was supposed to be a variable *)
    if is_abstract && is_new_type && List.length typs = 0
    then
        let var_name = (Name.of_last_path path) in
        let var = Variable var_name in
        let* new_typ_vars =
          match constr with
          | None -> return []
          | Some constr ->
            let* constr_is_gadt = PathName.is_gadt constr in
            if constr_is_gadt
            then return [(var_name, Kind.Tag)]
            else return []
        in
      return @@ (var , typ_vars, new_typ_vars)
    else
      begin
        (* Make sure it is not a type synonym before taging *)
        let* is_variant = PathName.is_variant_declaration path |> Monad.Option.is_some in
        let constr = if is_variant then Some path else None in
        let* (typs, typ_vars, new_typs_vars) = of_typs_exprs_constr constr with_free_vars typ_vars typs in
        let* typs = if is_variant
          then typs |> Monad.List.map (tag_typ_constr path)
          else return typs in
        return (Apply (mixed_path, typs), typ_vars, new_typs_vars)
      end
  | Tobject (_, object_descr) ->
    begin match !object_descr with
    | Some (path, _ :: typs) ->
      of_typs_exprs_constr constr with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
      MixedPath.of_path false path None >>= fun mixed_path ->
      return (Apply (mixed_path, typs), typ_vars, new_typ_vars)
    | _ ->
      raise
        (Error "unhandled_object_type", typ_vars, [])
        NotSupported
        "We do not handle this form of object types"
    end
  | Tfield (_, _, typ1, typ2) ->
    of_typ_expr_in_constr constr with_free_vars typ_vars typ1 >>= fun (typ1, typ_vars, new_typ_vars1) ->
    of_typ_expr_in_constr constr with_free_vars typ_vars typ2 >>= fun (typ2, typ_vars, new_typ_vars2) ->
    let new_typ_vars = VarEnv.union new_typ_vars1 new_typ_vars2 in
    raise
      (
        Tuple [typ1; typ2],
        typ_vars,
        new_typ_vars
      )
      NotSupported "Field types are not handled"
  | Tnil ->
    raise
      (Error "nil", typ_vars, [])
      NotSupported
      "Nil type is not handled"
  | Tlink typ | Tsubst typ -> of_typ_expr_in_constr constr with_free_vars typ_vars typ
  | Tvariant { row_fields; _ } ->
    PathName.typ_of_variants (List.map fst row_fields) >>= fun path_name ->
    begin match path_name with
    | Some path_name ->
      return (
        Apply (MixedPath.PathName (path_name, false), []),
        typ_vars,
        []
      )
    | None ->
      Monad.List.fold_left
        (fun (fields, typ_vars, new_typ_vars) (name, row_field) ->
          let typs = type_exprs_of_row_field row_field in
          of_typs_exprs_constr constr with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars') ->
          let new_typ_vars = VarEnv.union new_typ_vars new_typ_vars' in
          return (
            (name, Tuple typs) :: fields,
            typ_vars,
            new_typ_vars
          )
        )
        ([], typ_vars, [])
        row_fields >>= fun (fields, typ_vars, new_typ_vars) ->
      return (Sum (List.rev fields), typ_vars, new_typ_vars)
    end
  | Tpoly (typ, typ_args) ->
    let* typ_args =
      AdtParameters.typ_params_ghost_marked typ_args in
    let typ_args = typ_args |> AdtParameters.get_parameters in
    of_typ_expr_in_constr constr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars_typ) ->
    return (ForallTyps (typ_args, typ), typ_vars, new_typ_vars_typ)
  | Tpackage (path, idents, typs) ->
      let* path_name = PathName.of_path_without_convert false path in
      let typ_substitutions = List.map2 (fun ident typ -> (ident, typ)) idents typs in
      Monad.List.fold_left
        (fun (typ_substitutions, typ_vars, new_typ_vars) (ident, typ) ->
          let* path_name = PathName.of_long_ident false ident in
          of_typ_expr_in_constr constr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
          let new_typ_vars = VarEnv.union new_typ_vars new_typ_vars' in
          return (
            (path_name, typ) :: typ_substitutions,
            typ_vars,
            new_typ_vars
          )
        )
        ([], typ_vars, [])
        typ_substitutions >>= fun (typ_substitutions, typ_vars, new_typ_vars) ->
      get_env >>= fun env ->
      let module_typ = Env.find_modtype path env in
      ModuleTypParams.get_module_typ_declaration_typ_params_arity
        module_typ >>= fun signature_typ_params ->
      let typ_params = List.fold_left
        (fun typ_values (path_name, typ) ->
          Tree.map_at typ_values path_name (fun _ -> Typ typ)
        )
        (signature_typ_params |> Tree.map (fun arity -> Arity arity))
        typ_substitutions in
      return (Package (true, path_name, typ_params), typ_vars, new_typ_vars)

 and tag_typ_constr
     (path : Path.t)
     (typ : t)
   : t Monad.t =
   if PathName.is_native_datatype path
   then return typ
   else tag_typ_constr_aux typ

and of_typs_exprs_constr
  (path : Path.t option)
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typs : Types.type_expr list)
  : (t list * Name.t Name.Map.t * VarEnv.t) Monad.t =
  (Monad.List.fold_left
    (fun (typs, typ_vars, new_typ_vars) typ ->
      of_typ_expr_in_constr path with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
      let new_typ_vars = VarEnv.union new_typ_vars new_typ_vars' in
      return (typ :: typs, typ_vars, new_typ_vars)
    )
    ([], typ_vars, [])
    typs
  ) >>= fun (typs, typ_vars, new_typ_vars) ->
  return (List.rev typs, typ_vars, new_typ_vars)

let rec decode_var_tags
    (typ_vars : VarEnv.t)
    (constr: MixedPath.t option)
    (in_native : bool)
    (typ : t)
  : t Monad.t =
  let dec = decode_var_tags typ_vars constr in_native in
  match typ with
  | Variable name ->
    begin
      match constr with
      | None ->
        begin match List.assoc_opt name typ_vars with
          | None -> return typ
          | Some Kind.Set -> return typ
          | Some Kind.Tag ->
            let decname = MixedPath.dec_name in
            return @@ Apply (decname, [typ])
        end
      | Some mpath ->
        if MixedPath.is_gadt mpath || in_native
        then return typ
        else match List.assoc_opt name typ_vars with
          | None -> return typ
          | Some Kind.Set -> return typ
          | Some Kind.Tag ->
            let decname = MixedPath.dec_name in
            return @@ Apply (decname, [typ])
    end
  | Arrow (t1, t2) ->
    let* t1 = decode_var_tags typ_vars constr true t1 in
    let* t2 = decode_var_tags typ_vars constr true t2 in
    return @@ Arrow (t1, t2)
  | Tuple ts ->
    let* ts = Monad.List.map (decode_var_tags typ_vars constr true) ts in
    return @@ Tuple ts
  | Apply (mpath, ts) ->
    let path_str = MixedPath.to_string mpath in
    let in_native = List.mem path_str ["tuple_tag"; "arrow_tag"; "list_tag"; "option_tag"] in
    let dec = decode_var_tags typ_vars (Some mpath) in_native in
    let* ts = Monad.List.map dec ts in
    return @@ Apply (mpath, ts)
  | ForallModule (name, t1, t2) ->
    let* t1 = dec t1 in
    let* t2 = dec t2 in
    return @@ ForallModule (name, t1, t2)
  | ForallTyps (names, t) ->
    let* t = dec t in
    return @@ ForallTyps (names, t)
  | FunTyps (names, t) ->
    let* t = dec t in
    return @@ FunTyps (names, t)
  | _ -> return typ

let of_typ_expr
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typ : Types.type_expr)
  : (t * Name.t Name.Map.t * VarEnv.t) Monad.t =
  of_typ_expr_in_constr None with_free_vars typ_vars typ

let of_typs_exprs
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typs : Types.type_expr list)
  : (t list * Name.t Name.Map.t * VarEnv.t) Monad.t =
  of_typs_exprs_constr None with_free_vars typ_vars typs

let rec of_type_expr_variable (typ : Types.type_expr) : Name.t Monad.t =
  match typ.desc with
  | Tvar (Some x) | Tunivar (Some x) -> Name.of_string false x
  | Tlink typ | Tsubst typ -> of_type_expr_variable typ
  | _ ->
    raise
      (Name.of_string_raw "expected_variable")
      NotSupported
      "Only type variables are supported as parameters."

let of_type_expr_without_free_vars (typ : Types.type_expr) : t Monad.t =
  of_typ_expr false Name.Map.empty typ >>= fun (typ, _, _) ->
  return typ

(** We do not generate error messages for this function. Indeed, if there are
    errors for the following types, they should be noticed elsewhere (by the
    conversion function to Coq for example). *)
let rec existential_typs_of_typ (typ : Types.type_expr) : Name.Set.t Monad.t =
  match typ.desc with
  | Tvar _ | Tunivar _ -> return Name.Set.empty
  | Tarrow (_, typ_x, typ_y, _) -> existential_typs_of_typs [typ_x; typ_y]
  | Ttuple typs -> existential_typs_of_typs typs
  | Tconstr (path, typs, _) ->
    get_env >>= fun env ->
    let* path_existential =
      match path with
      | Path.Pident ident ->
        begin match Env.find_type path env with
        | _ -> return Name.Set.empty
        | exception Not_found ->
          let* ident = Name.of_ident false ident in
          return (Name.Set.singleton ident)
        end
      | _ -> return Name.Set.empty in
    existential_typs_of_typs typs >>= fun existentials ->
    return (Name.Set.union path_existential existentials)
  | Tobject (_, object_descr) ->
    let param_typs =
      match !object_descr with
      | Some (_, _ :: param_typs) -> List.tl param_typs
      | _ -> [] in
    existential_typs_of_typs param_typs
  | Tfield (_, _, typ1, typ2) -> existential_typs_of_typs [typ1; typ2]
  | Tnil -> return Name.Set.empty
  | Tlink typ | Tsubst typ -> existential_typs_of_typ typ
  | Tvariant { row_fields; _ } ->
    existential_typs_of_typs (
      row_fields |>
      List.map (fun (_, row_field) -> type_exprs_of_row_field row_field) |>
      List.concat
    )
  | Tpoly (typ, typs) -> existential_typs_of_typs (typ :: typs)
  | Tpackage (_, _, typs) -> existential_typs_of_typs typs

and existential_typs_of_typs (typs : Types.type_expr list)
  : Name.Set.t Monad.t =
  Monad.List.fold_left
    (fun existentials typ ->
      existential_typs_of_typ typ >>= fun existentials_typ ->
      return (Name.Set.union existentials existentials_typ)
    )
    Name.Set.empty typs

(** The free variables of a type. *)
let rec typ_args_of_typ (typ : t) : Name.Set.t =
  match typ with
  | String x -> Name.Set.empty
  | Variable x -> Name.Set.singleton x
  | Kind _ -> Name.Set.empty
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Eq (typ1, typ2) -> typ_args_of_typs [typ1;typ2]
  | Sum typs -> typ_args_of_typs (List.map snd typs)
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs
  | Package (_, _, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | Arity _ -> None
      | Typ typ -> Some (typ_args_of_typ typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ForallModule (_, param, result) ->
    Name.Set.union (typ_args_of_typ param) (typ_args_of_typ result)
  | ForallTyps (typ_params, typ) | FunTyps (typ_params, typ) ->
    Name.Set.diff (typ_args_of_typ typ) (Name.Set.of_list typ_params)
  | Error _ -> Name.Set.empty

and typ_args_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args_of_typ typ))
    Name.Set.empty typs

(** The local type constructors of a type. Used to detect the existential
    variables which are actually used by a type, once we remove the phantom
    types. *)
let rec local_typ_constructors_of_typ (typ : t) : Name.Set.t =
  match typ with
  | String _ -> Name.Set.empty
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> local_typ_constructors_of_typs [typ1; typ2]
  | Eq (typ1, typ2) -> local_typ_constructors_of_typs [typ1; typ2]
  | Kind _ -> Name.Set.empty
  | Sum typs -> local_typ_constructors_of_typs (List.map snd typs)
  | Tuple typs -> local_typ_constructors_of_typs typs
  | Apply (mixed_path, typs) ->
    let local_typ_constructors = local_typ_constructors_of_typs typs in
    begin match mixed_path with
    | MixedPath.PathName ({ path = []; base }, _) ->
      Name.Set.add base local_typ_constructors
    | _ -> local_typ_constructors
    end
  | Package (_, _, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | Arity _ -> None
      | Typ typ -> Some (local_typ_constructors_of_typ typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ForallModule (_, param, result) ->
    local_typ_constructors_of_typs [param; result]
  | ForallTyps (_, typ) | FunTyps (_, typ) -> local_typ_constructors_of_typ typ
  | Error _ -> Name.Set.empty

and local_typ_constructors_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (local_typ_constructors_of_typ typ))
    Name.Set.empty typs

(** In a function's type extract the body's type (up to [n] arguments). *)
let rec open_type (typ : t) (n : int) : t list * t =
  if n = 0 then
    ([], typ)
  else
    match typ with
    | Arrow (typ1, typ2) ->
      let (typs, typ) = open_type typ2 (n - 1) in
      (typ1 :: typs, typ)
    | _ -> failwith "Expected an arrow type."

(** The context to know if parenthesis are needed. *)
module Context = struct
  type t =
    | Apply
    | Arrow
    | Sum
    | Tuple
    | Forall
    | Eq

  let get_order (context : t) : int =
    match context with
    | Apply -> 0
    | Arrow -> 3
    | Sum -> 2
    | Tuple -> 1
    | Forall -> 4
    | Eq -> 5

  let should_parens (context : t option) (current_context : t) : bool =
    match context with
    | None -> false
    | Some context ->
      let order = get_order context in
      let current_order = get_order current_context in
      order <= current_order

  let parens
    (context : t option)
    (current_context : t)
    (doc : SmartPrint.t)
    : SmartPrint.t =
    Pp.parens (should_parens context current_context) doc
end

let rec accumulate_nested_arrows (typ : t) : t list * t =
  match typ with
  | Arrow (typ_x, typ_y) ->
    let (typ_xs, typ_y) = accumulate_nested_arrows typ_y in
    (typ_x :: typ_xs, typ_y)
  | _ -> ([], typ)

module Subst = struct
  type t = {
    name : Name.t -> Name.t;
    path_name : PathName.t -> PathName.t }
end

let tag_notation (typs : t list): t option =
  if List.length typs <> 2 then None
  else let typ = List.nth typs 1 in
    let name = tag_constructor_of typ in
    let tagged_name = (Name.of_string_raw (name ^ "_tag")) in
    if List.mem name ["int"; "string"; "bool"; "float"]
    then Some (Variable tagged_name)
    else match typ with
      | Apply (mname, ts) ->
        if List.mem name ["list"; "option"]
        then Some (Apply (MixedPath.of_name tagged_name, ts))
        else None
      | _ -> None

(** Pretty-print a type. Use the [context] parameter to know if we should add
    parenthesis. *)
let rec to_coq (subst : Subst.t option) (context : Context.t option) (typ : t)
  : SmartPrint.t =
  match typ with
  | String x -> !^ ("\"" ^ x ^ "\"")
  | Variable x  ->
    let x =
      match subst with
      | None -> x
      | Some subst -> subst.name x in
    Name.to_coq x
  | Kind k -> Kind.to_coq k
  | Eq (lhs, rhs) ->
    Context.parens context Context.Eq @@ group (
        (to_coq subst (Some Context.Eq) lhs ^^ !^ "="
      )) ^^
      to_coq subst (Some Context.Eq) rhs
  | Arrow _ ->
    let (typ_xs, typ_y) = accumulate_nested_arrows typ in
    Context.parens context Context.Arrow @@ group (
      separate space (typ_xs |> List.map (fun typ_x ->
        group (to_coq subst (Some Context.Arrow) typ_x ^^ !^ "->"
      ))) ^^
      to_coq subst (Some Context.Arrow) typ_y
    )
  | Sum typs ->
    let typs = typs |> List.map (fun (name, typ) ->
      let context = if List.length typs = 1 then context else Some Sum in
      group (nest (!^ "(*" ^^ !^ ("`" ^ name) ^^ !^ "*)") ^^ to_coq subst context typ)
    ) in
    begin match typs with
    | [] -> !^ "Empty_set"
    | [typ] -> typ
    | _ ->
      Context.parens context Context.Sum @@ nest @@
      separate (space ^^ !^ "+" ^^ space) typs
    end
  | Tuple typs ->
    begin match typs with
    | [] -> !^ "unit"
    | [typ] -> to_coq subst context typ
    | _ ->
      Context.parens context Context.Tuple @@ nest @@
      separate (space ^^ !^ "*" ^^ space)
        (List.map (to_coq subst (Some Context.Tuple)) typs)
    end
  | Apply (path, typs) ->
    (* Prints tags as notations *)
    let tag = tag_notation typs in
    if MixedPath.is_tag path && Option.is_some tag
    then let tag = Option.get tag in
      to_coq subst (Some Context.Apply) tag
    else let path =
           match subst with
           | None -> path
           | Some subst ->
             begin match path with
               | MixedPath.PathName (path_name, is_gadt) ->
                 MixedPath.PathName (subst.path_name path_name, is_gadt)
               | _ -> path
             end in
      Pp.parens (Context.should_parens context Context.Apply && typs <> []) @@
      nest @@ separate space
        (MixedPath.to_coq path :: List.map (to_coq subst (Some Context.Apply)) typs)
  | Package (is_in_exp, path_name, typ_params) ->
    let existential_typs =
      Tree.flatten typ_params |>
      Util.List.filter_map (function
        | (path_name, Arity arity) -> Some (path_name, arity)
        | _ -> None
      ) in
    let existential_typs_pattern =
      existential_typs |>
      List.map (fun (path_name, _) ->
        ModuleTypParams.to_coq_typ_param_name path_name
      ) |>
      Pp.primitive_tuple_pattern in
    let existential_typs_typ =
      existential_typs |>
      List.map (fun (_, arity) -> Pp.typ_arity arity) |>
      Pp.primitive_tuple_type in
    nest (braces (
      existential_typs_pattern ^^ !^ ":" ^^ existential_typs_typ ^^
      (if is_in_exp then !^ "@" else !^ "&") ^^
      nest (
        separate space (
          nest (PathName.to_coq path_name ^-^ !^ "." ^-^ !^ "signature") ::
          (Tree.flatten typ_params |> List.map (fun (path_name, typ) ->
            let name = ModuleTypParams.to_coq_typ_param_name path_name in
            nest (parens (
              name ^^ !^ ":=" ^^
              match typ with
              | Arity _ -> name
              | Typ typ -> to_coq subst (Some Context.Apply) typ
            ))
          ))
        )
      )
    ))
  | ForallModule (name, param, result) ->
    Context.parens context Context.Forall @@ nest (
      !^ "forall" ^^ parens (
        Name.to_coq name ^^ !^ ":" ^^ to_coq subst None param
      ) ^-^ !^ "," ^^
      to_coq subst (Some Context.Forall) result
    )
  | ForallTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ nest (
        !^ "forall" ^^ braces (
          nest (
            separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
          )
        ) ^-^ !^ "," ^^
        to_coq subst (Some Context.Forall) typ
      )
    end
  | FunTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ nest (
        !^ "fun" ^^ parens (
          nest (
            separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
          )
        ) ^^ !^ "=>" ^^
        to_coq subst (Some Context.Forall) typ
      )
    end
  | Error message -> !^ message


let typ_vars_to_coq
    (delim : SmartPrint.t -> SmartPrint.t)
    (sep_before : SmartPrint.t)
    (sep_after : SmartPrint.t)
    (typ_vars : VarEnv.t) : SmartPrint.t =
  let typ_vars = VarEnv.group_by_kind typ_vars in
  if List.length typ_vars = 0
  then empty
  else sep_before ^^
       (separate space
          (typ_vars |> List.map (fun (typ, vars) ->
               delim ((separate space (vars |> List.rev |> List.map Name.to_coq))
                      ^^ !^ ":" ^^ (Kind.to_coq typ)))
       )) ^-^ sep_after
