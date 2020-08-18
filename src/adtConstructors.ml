(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
open SmartPrint
open Monad.Notations

module RecordSkeleton = struct
  type t = {
    fields : Name.t list;
    module_name : Name.t;
    typ_name : Name.t;
  }

  let to_coq_record
      (module_name : Name.t)
      (typ_name : Name.t)
      (typ_args : Name.t list)
      (fields : (Name.t * Type.t) list)
      (with_with : bool)
    : SmartPrint.t =
    nest (
      !^ "Module" ^^ Name.to_coq module_name ^-^ !^ "." ^^ newline ^^
      indent (
        !^ "Record" ^^ !^ "record" ^^
        begin match typ_args with
          | [] -> empty
          | _ :: _ ->
            braces (nest (
                separate space (List.map Name.to_coq typ_args) ^^
                !^ ":" ^^ Pp.set
              ))
        end ^^
        nest (!^ ":" ^^ Pp.set) ^^
        !^ ":=" ^^ !^ "Build" ^^
        !^ "{" ^^ newline ^^
        indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
            nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None typ)))) ^^
        !^ "}." ^^
        begin match typ_args with
          | [] -> empty
          | _ :: _ ->
            newline ^^ !^ "Arguments" ^^ !^ "record" ^^ !^ ":" ^^
            !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
        end ^^
        newline ^^
        begin if with_with then
            separate newline (fields |> List.map (fun (name, _) ->
                let prefixed_typ_args =
                  typ_args |> List.map (fun typ_arg ->
                      Name.to_coq (Name.prefix_by_t typ_arg)
                    ) in
                let record_typ =
                  nest (separate space (!^ "record" :: prefixed_typ_args)) in
                nest (
                  !^ "Definition" ^^ Name.to_coq (Name.prefix_by_with name) ^^
                  begin match typ_args with
                    | [] -> empty
                    | _ :: _ -> braces (nest (separate space prefixed_typ_args))
                  end ^^
                  Name.to_coq name ^^
                  nest (parens (!^ "r" ^^ !^ ":" ^^ record_typ)) ^-^
                  !^ " :=" ^^ newline ^^
                  indent @@ nest (
                    !^ "Build" ^^
                    separate space prefixed_typ_args ^^
                    separate space (fields |> List.map (fun (name', _) ->
                        nest (
                          if Name.equal name name' then
                            Name.to_coq name
                          else
                            !^ "r" ^-^ !^ ".(" ^-^ Name.to_coq name' ^-^ !^ ")"
                        )
                      )) ^-^ !^ "."
                  )
                )
              )) ^^ newline
          else
            empty
        end
      ) ^^
      !^ "End" ^^ Name.to_coq module_name ^-^ !^ "." ^^ newline ^^
      nest (
        !^ "Definition" ^^ Name.to_coq typ_name ^^ !^ ":=" ^^
        Name.to_coq module_name ^-^ !^ ".record" ^-^ !^ "."
      )
    )

  let to_coq (record_skeleton : t) : SmartPrint.t =
    let { fields; module_name; typ_name } = record_skeleton in
    to_coq_record module_name typ_name fields (fields |>
                                               List.map (fun field -> (field, Type.Variable field))
                                              ) true
end

(** [constructor_name]: forall [typ_vars], [param_typs] -> t [res_typ_params] *)
type item = {
  constructor_name : Name.t;
  param_typs : Type.t list; (** The parameters of the constructor. *)
  res_typ_params : Type.t list;
  (** The type parameters of the result type of the constructor. *)
  typ_vars : VarEnv.t; (** The polymorphic type variables. *)
}

(* We can probably get rid of this now *)
type t = item list

module Single = struct
  type t = {
    constructor_name : Name.t;
    param_typs : Type.t list; (** The parameters of the constructor. *)
    return_typ_params : Type.t list;
    (** The return type, in case of GADT constructor, with some inference to
        rule-out GADTs with only existential variables. *)
    typ_vars : VarEnv.t;
  }

  let of_ocaml_case
      (typ_name : Name.t)
      (defined_typ_params : Name.t list)
      (case : Types.constructor_declaration)
    : (t * (RecordSkeleton.t * Name.t list * Type.t) option) Monad.t =
    let { Types.cd_args; cd_id; cd_loc; cd_res; _ } = case in
    set_loc (Loc.of_location cd_loc) (
      let* constructor_name =
        PathName.map_constructor_name
          (Ident.name cd_id) (Name.to_string typ_name) in
      let* constructor_name = Name.of_string false constructor_name in
      let typ_vars = Name.Map.empty in
      begin match cd_args with
        | Cstr_tuple param_typs ->
          Type.of_typs_exprs true typ_vars param_typs >>= fun (param_typs, _, new_typs_vars) ->
          return (param_typs, new_typs_vars, None)
        | Cstr_record labeled_typs ->
          set_loc (Loc.of_location cd_loc) (
            (
              labeled_typs |>
              List.map (fun { Types.ld_type; _ } -> ld_type) |>
              Type.of_typs_exprs true typ_vars
            ) >>= fun (record_params, _, new_typ_vars) ->
            let* record_fields =
              labeled_typs |> Monad.List.map ( fun { Types.ld_id; _ } ->
                  Name.of_ident false ld_id
                ) in
            (* We get the order of the type arguments from their order of
               introduction in the record fields. *)
            let typ_args =
              List.fold_left
                (fun typ_args new_typ_args ->
                   (typ_args @
                    Name.Set.elements (
                      Name.Set.diff new_typ_args (Name.Set.of_list typ_args)
                    ))
                )
                []
                (List.map Type.typ_args_of_typ record_params) in
            return (
              [
                Type.Apply (
                  MixedPath.PathName ({
                    path = [typ_name];
                    base = constructor_name;
                  }, false),
                  typ_args |> List.map (fun name ->
                      Type.Variable name
                    )
                )
              ],
              new_typ_vars,
              Some (
                {
                  RecordSkeleton.fields = record_fields;
                  module_name = constructor_name;
                  typ_name = Name.suffix_by_skeleton constructor_name;
                },
                typ_args,
                Type.Apply (
                  MixedPath.PathName ({
                    path = [typ_name];
                    base = Name.suffix_by_skeleton constructor_name;
                  }, false),
                  record_params
                )
              )
            ))
      end >>= fun (param_typs, typ_vars, records) ->
      let* (return_typ_params, new_typ_vars) =
        match cd_res with
        | Some typ ->
          Type.of_typ_expr false Name.Map.empty typ >>= fun (ty, _, new_typ_vars) ->
          begin match ty with
            | Type.Apply (_, typs) -> return (typs, new_typ_vars)
            | _ -> raise ([ty], new_typ_vars) Error.Category.Unexpected "Unexpected Type of record"
          end
        | None ->
          let new_typ_vars = List.fold_left (fun map typ_param ->
              (typ_param, Kind.Tag) :: map
            ) [] defined_typ_params in
          return (List.map (fun v -> Type.Variable v) defined_typ_params, List.rev new_typ_vars)
      in
      let typ_vars = VarEnv.union typ_vars new_typ_vars in
      let typ_name = MixedPath.of_name_gadt typ_name in
      let* param_typs = Monad.List.map (Type.decode_var_tags typ_vars None false) param_typs in
      let* return_typ_params = Monad.List.map (Type.decode_var_tags typ_vars (Some typ_name) false) return_typ_params in
      return (
        {
          constructor_name;
          param_typs;
          return_typ_params;
          typ_vars;
        },
        records
      ))

  let of_ocaml_row
      (defined_typ_params : AdtParameters.t)
      (row : Asttypes.label * Types.row_field)
    : t Monad.t =
    let (label, field) = row in
    let* constructor_name = Name.of_string false label in
    let typs = Type.type_exprs_of_row_field field in
    Type.of_typs_exprs true Name.Map.empty typs >>= fun (param_typs, _, typ_vars) ->
    return {
      constructor_name;
      param_typs;
      return_typ_params = List.map (fun x -> Type.Variable x) (AdtParameters.get_parameters defined_typ_params);
      typ_vars;
    }
end

let of_ocaml
    (single_constructors : Single.t list)
  : t Monad.t =
  let* constructors_and_arities  = single_constructors |> Monad.List.map (
      fun { Single.constructor_name; param_typs; return_typ_params; typ_vars; } ->
        return ({
            constructor_name;
            param_typs;
            res_typ_params = return_typ_params;
            typ_vars
          }, List.length return_typ_params)
    ) in

  let (constructors, constructors_arity) = List.split constructors_and_arities in
  let same_arities = List.for_all (fun y -> List.hd constructors_arity = y) constructors_arity in

  if not same_arities
  then
    raise constructors
      Error.Category.Unexpected
      "Unexpected error made the constructors have different return sizes"
  else
    return constructors

let type_arguments
  (constructors : t)
  : Type.t list =
  constructors |> List.map (fun { res_typ_params; _ } ->
            res_typ_params) |> List.flatten
