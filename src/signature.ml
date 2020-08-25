(** An OCaml signature which will by transformed into a dependent record. *)
open SmartPrint
open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Module of Name.t * ModuleTyp.t
  | TypExistential of Name.t * Name.t list
  | TypSynonym of Name.t * VarEnv.t * Type.t
  | Value of Name.t * VarEnv.t * Type.t

type t = {
  items: item list;
  typ_params: Kind.t ModuleTypParams.t
}

let items_of_types_signature
    (typ_params : VarEnv.t)
    (signature : Types.signature)
  : (item list * VarEnv.t) Monad.t =
  let of_types_signature_item
      (typ_params : VarEnv.t)
      (signature_item : Types.signature_item)
    : (item * VarEnv.t) Monad.t =
    match signature_item with
    | Sig_value (ident, { val_type; _ }, _) ->
      let* name = Name.of_ident true ident in
      Type.of_typ_expr true Name.Map.empty val_type >>= fun (typ, _, new_typ_vars) ->
      let* typ = Type.decode_var_tags new_typ_vars None false false typ in
      let keys = List.map fst typ_params in
      let typ_args = VarEnv.remove_many keys new_typ_vars in
      return (Value (name, typ_args, typ), new_typ_vars)
    | Sig_type (ident, { type_manifest = None; type_params; _ }, _, _) ->
      let* name = Name.of_ident false ident in
      Monad.List.map Type.of_type_expr_variable type_params >>= fun typ_args ->
      return (TypExistential (name, typ_args), [])
    | Sig_type (ident, { type_manifest = Some typ; type_params; _ }, _, _) ->
      let* name = Name.of_ident false ident in
      Type.of_typ_expr true Name.Map.empty typ >>= fun (typ, _, new_typ_vars) ->
      let* typ = Type.decode_var_tags new_typ_vars None false false typ in
      let keys = List.map fst typ_params in
      let typ_args = VarEnv.remove_many keys new_typ_vars in
      return (TypSynonym (name, typ_args, typ), new_typ_vars)
    | Sig_typext (_, { ext_type_path; _ }, _, _) ->
      let name = Path.name ext_type_path in
      raise
        (Error ("extensible_type_definition `" ^ name ^ "`"), [])
        NotSupported
        ("Extensible type '" ^ name ^ "' not handled")
    | Sig_module (ident, _, { md_type; _ }, _, _) ->
      let* name = Name.of_ident false ident in
      IsFirstClassModule.is_module_typ_first_class
        md_type >>= fun is_first_class ->
      begin match is_first_class with
      | Found signature_path ->
        PathName.of_path_with_convert false signature_path
          >>= fun signature_path_name ->
        let mapper ident { Types.type_manifest; type_params; _ } =
          let* name = Name.of_ident false ident in
          begin match type_manifest with
          | None -> return (Type.Arity (List.length type_params))
          | Some type_manifest ->
            (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
            Type.of_type_expr_without_free_vars type_manifest >>= fun typ ->
            let typ = Type.FunTyps (typ_args, typ) in
            return (Type.Typ typ)
          end >>= fun arity_or_typ ->
          return (Some (Tree.Item (name, arity_or_typ))) in
        ModuleTypParams.get_module_typ_typ_params
          mapper md_type >>= fun typ_params ->
        raise
          (Module (name, ModuleTyp.With (signature_path_name, typ_params)), [])
          Module
          (
            "Sub-module '" ^ Ident.name ident ^ "' in included " ^
            "signature.\n\n" ^
            "Sub-modules in included signatures are not handled well yet. " ^
            "It does not work if there are destructive type " ^
            "substitutions (:=) in the sub-module or type definitions in the " ^
            "sub-module's source signature. We do not develop this feature " ^
            "further as it is working in our cases.\n\n" ^
            "A safer way is to make a sub-module instead of an `include`."
          )
      | Not_found reason ->
        raise
          (Error ("module " ^ Ident.name ident), [])
          Module
          (
            "Signature name for the module '" ^ Ident.name ident ^
            "' in included signature not found.\n\n" ^
            reason
          )
      end
    | Sig_modtype (ident, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("module_type" ^ name), [])
        NotSupported
        ("Signatures '" ^ name ^ "' inside signature is not handled")
    | Sig_class (ident, _, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("class" ^ name), [])
        NotSupported
        ("Class '" ^ name ^ "' not handled.")
    | Sig_class_type (ident, _, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("class_type" ^ name), [])
        NotSupported
        ("Class type '" ^ name ^ "' not handled.") in
  let* (items, varenv) = signature |> Monad.List.fold_left (fun (acc_item, acc_varenv) item ->
      let* (item, varenv) = of_types_signature_item typ_params item in
      return @@ (item :: acc_item, VarEnv.union acc_varenv varenv)
    ) ([], []) in
  return (List.rev items, varenv)

let items_of_signature
    (typ_params : VarEnv.t)
    (signature : signature)
  : (item list * VarEnv.t) Monad.t =
  let of_signature_item
      (typ_params : VarEnv.t)
      (signature_item : signature_item)
    : (item list * VarEnv.t) Monad.t =
    set_env signature_item.sig_env (
    set_loc (Loc.of_location signature_item.sig_loc) (
    match signature_item.sig_desc with
    | Tsig_attribute _ -> return ([], [])
    | Tsig_class _ ->
      raise ([Error "class"], []) NotSupported "Signature item `class` not handled."
    | Tsig_class_type _ ->
      raise
        ([Error "class_type"], [])
        NotSupported
        "Signature item `class_type` not handled."
    | Tsig_exception _ ->
      raise
        ([Error "exception"], [])
        SideEffect
        "Signature item `exception` not handled."
    | Tsig_include { incl_type; _ } -> items_of_types_signature typ_params incl_type
    | Tsig_modsubst _ ->
      raise
        ([Error "module_substitution"], [])
        NotSupported
        "We do not handle module substitutions"
    | Tsig_modtype _ ->
      raise
        ([Error "module_type"], [])
        NotSupported
        "Signatures inside signatures are not handled."
    | Tsig_module { md_id; md_type; _ } ->
      push_env (
      let* name = Name.of_ident false md_id in
      ModuleTyp.of_ocaml md_type >>= fun module_typ ->
      return ([Module (name, module_typ)], [])
    )
    | Tsig_open _ ->
      raise ([Error "open"], []) NotSupported "Signature item `open` not handled."
    | Tsig_recmodule _ ->
      raise ([Error "recursive_module"], []) NotSupported "Recursive module signatures are not handled."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = None; type_kind; type_params; _ }; _ } ]) ->
      begin match type_kind with
      | Type_abstract -> return ()
      | _ ->
        raise
          ()
          Module
          "We do not handle the definition of new types in signatures"
      end >>= fun () ->
      let* name = Name.of_ident false typ_id in
      (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      return ([TypExistential (name, typ_args)], [])
    | Tsig_type (_, typs) | Tsig_typesubst typs ->
      begin match typs with
      | [ {
          typ_id;
          typ_type = { type_manifest = Some typ; type_params; _ };
          _
        } ] ->
        let* name = Name.of_ident false typ_id in
        Type.of_typ_expr true Name.Map.empty typ >>= fun (typ, _, new_typ_vars) ->
        let* typ = Type.decode_var_tags new_typ_vars None false false typ in
        let keys = List.map fst typ_params in
        let typ_args = VarEnv.remove_many keys new_typ_vars in
        return ([TypSynonym (name, typ_args, typ)], new_typ_vars)
      | _ ->
        raise
          ([Error "mutual_type"], [])
          NotSupported
          "Mutual type definitions in signatures not handled."
      end
    | Tsig_typext { tyext_path; _ } ->
      raise
        ([Error ("extensible_type " ^ Path.last tyext_path)], [])
        ExtensibleType
        "We do not handle extensible types"
    | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
      let* name = Name.of_ident true val_id in
      Type.of_typ_expr true Name.Map.empty ctyp_type >>= fun (typ, _, new_typ_vars) ->
      let* typ = Type.decode_var_tags new_typ_vars None false false typ in
      let keys = List.map fst typ_params in
      let typ_args = VarEnv.remove_many keys new_typ_vars in
      return ([Value (name, typ_args, typ)], new_typ_vars))) in
  let* (items, varenv) = signature.sig_items |> Monad.List.fold_left (fun (acc_items, acc_varenv) item ->
      let* (items, varenv) = of_signature_item typ_params item in
      return (items @ acc_items, VarEnv.union acc_varenv varenv)
    ) ([], []) in
  return (List.rev items, varenv)


      (* let* module_typ = match module_typ with
       *   | With (name, typs) ->
       *     let* typs = Tree.monad_map (fun typ_or_arity ->
       *         match typ_or_arity with
       *         | Type.Arity _ -> return typ_or_arity
       *         | Type.Typ typ ->
       *           let* typ = Type.decode_var_tags typ_params None false false typ in
       *           return @@ Type.Typ typ
       *       ) typs in
       *     return (ModuleTyp.With (name, typs))
       *   | _ -> return module_typ
       * in *)

let decode_items
    (varenv : VarEnv.t)
    (items : item list)
  : item list Monad.t =
  items |> Monad.List.map (fun i ->
      match i with
      | TypSynonym (name, typ_params, typ) ->
        let* typ = Type.decode_var_tags varenv None false false typ in
        return @@ TypSynonym (name, typ_params, typ)
      | Value (name, typ_params, typ) ->
        let* typ = Type.decode_var_tags varenv None false false typ in
        return @@ Value (name, typ_params, typ)
      | Module (name, module_typ) ->
        let* module_typ = module_typ |> ModuleTyp.monad_map (fun ar_or_typ ->
            match ar_or_typ with
            | Type.Typ typ ->
              let* typ = Type.decode_var_tags varenv None false false typ in
              return @@ Type.Typ typ
            | _ -> return ar_or_typ
          ) in
        return @@ Module (name, module_typ)
      | _ -> return i
    )


let of_signature (signature : signature) : t Monad.t =
  push_env (
  let* typ_params = ModuleTypParams.get_signature_typ_params_kind signature.sig_type in
  let varenv = ModuleTypParams.build_varenv typ_params in
  let* (items, varenv) = items_of_signature varenv signature in
  let* items = decode_items varenv items in
  let typ_params = Tree.update_items varenv typ_params in

  return { items; typ_params })

let to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^ ("(* " ^ message ^ " *)")
  | Module (name, module_typ) ->
    nest (Name.to_coq name ^^ !^ ":" ^^ ModuleTyp.to_coq name module_typ ^-^ !^ ";")
  | TypExistential (name, _) ->
    nest (Name.to_coq name ^^ !^ ":=" ^^ Name.to_coq name ^-^ !^ ";")
  | TypSynonym (name, typ_args, typ) ->
    nest (
      Name.to_coq name ^^
      Type.typ_vars_to_coq parens empty empty typ_args
      ) ^^ !^ ":=" ^^ Type.to_coq None None typ ^-^ !^ ";"
  | Value (name, typ_args, typ) ->
    nest (
      Name.to_coq name ^^ !^ ":" ^^
      Type.typ_vars_to_coq braces (!^ "forall") (!^ ",") typ_args)
    ^^ Type.to_coq None None typ ^-^ !^ ";"

let rec to_coq_type_kind (arity : int) : SmartPrint.t =
  if arity = 0 then
    Pp.set
  else
    Pp.set ^^ !^ "->" ^^ to_coq_type_kind (arity - 1)

let to_coq_definition (name : Name.t) (signature : t) : SmartPrint.t =
  let typ_params : (SmartPrint.t * Kind.t) list =
    Tree.flatten signature.typ_params |> List.map (fun (path_name, kind) ->
      (ModuleTypParams.to_coq_typ_param_name path_name, kind)
    ) in
  let reversed_grouped_typ_params : (SmartPrint.t list * Kind.t) list =
    List.fold_left
      (fun grouped (typ_param, kind) ->
        match grouped with
        | [] -> [([typ_param], kind)]
        | (typ_params, kind') :: grouped' ->
          if kind = kind' then
            (typ_param :: typ_params, kind') :: grouped'
          else
            ([typ_param], kind) :: grouped
      )
      []
      typ_params in
  let grouped_typ_params =
    reversed_grouped_typ_params |>
    List.map (fun (typ_params, kind) -> (List.rev typ_params, kind)) |>
    List.rev in
  !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
  indent (
    nest (
      !^ "Record" ^^ !^ "signature" ^^
      separate space (grouped_typ_params |> List.map (fun (typ_params, kind) ->
        braces (
          separate space typ_params ^^ !^ ":" ^^ Kind.to_coq kind
        )
      )) ^^
      nest (!^ ":" ^^ Pp.set) ^^
      !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate newline (List.map to_coq_item signature.items)) ^^ newline ^^
      !^ "}" ^-^ !^ "."
    )
  ) ^^ newline ^^
  !^ "End" ^^ Name.to_coq name ^-^ !^ "."
