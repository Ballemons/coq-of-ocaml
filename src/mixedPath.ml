(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open SmartPrint
open Monad.Notations

(** [Access] corresponds to projections from first-class modules. *)
(** Second bool is to to flag gadt type constructors *)
type t =
  | Access of PathName.t * PathName.t list * bool * bool
  | PathName of PathName.t * bool

let dec_name : t =
  PathName ("decode_vtag" |> Name.of_string_raw |> PathName.of_name [], false)

(** Shortcut to introduce new local variables for example. *)
let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name, false)

let of_name_gadt (name : Name.t) : t =
  PathName (PathName.of_name [] name, true)

let is_gadt (path : t) : bool =
  match path with
  | Access (_, _, _, is_gadt) -> is_gadt
  | PathName (_, is_gadt) -> is_gadt

let is_tag (path : t) : bool =
  match path with
  | Access _ -> false
  | PathName ({ base; _ }, _) ->
    if Name.to_string base = "constr_tag"
    then true
    else false

let is_native_type (path : t) : bool =
  match path with
  | Access _ -> false
  | PathName ({ base; _ }, _) -> List.mem (Name.to_string base) Name.native_type_constructors

let to_string : t -> string = function
  | Access (path, fields, _, _) ->
    let fields = List.map PathName.to_string fields in
    let path = PathName.to_string path in
    List.fold_left (fun acc field -> acc ^ ".(" ^ field ^ ")") path fields
  | PathName (path, _) -> PathName.to_string path

let get_signature_path (path : Path.t) : Path.t option Monad.t =
  get_env >>= fun env ->
  match Env.find_module path env with
  | module_declaration ->
    let { Types.md_type; _ } = module_declaration in
    IsFirstClassModule.is_module_typ_first_class md_type >>= fun is_first_class ->
    begin match is_first_class with
    | IsFirstClassModule.Found signature_path -> return (Some signature_path)
    | IsFirstClassModule.Not_found _ -> return None
    end
  | exception _ -> return None

let rec of_path_aux (path : Path.t)
  : (Path.t * (Path.t * string) list * Path.t option) Monad.t =
  let* signature_path = get_signature_path path in
  let* configuration = get_configuration in
  let is_in_black_list =
    Configuration.is_in_first_class_module_backlist configuration path in
  let signature_path =
    if is_in_black_list then
      None
    else
      signature_path in
  begin match path with
  | Papply _ -> failwith "Unexpected path application"
  | Pdot (path', field_string) ->
    of_path_aux path' >>= fun (namespace_path, fields, signature_path) ->
    begin match signature_path with
    | Some signature_path ->
      return (
        namespace_path,
        (signature_path, field_string) :: fields
      )
    | None ->
      (* The sub-module of a first-class module is a first-class module too. *)
      return (path, [])
    end
  | Pident _ -> return (path, [])
  end >>= fun (path, fields) ->
  return (path, fields, signature_path)

(** If the module was declared in the current unbundled signature definition. *)
let is_module_path_local (path : Path.t) : bool Monad.t =
  get_env_stack >>= fun env_stack ->
  let envs_without_path = env_stack |> List.filter (fun env ->
    match Env.find_module path env with
    | _ -> false
    | exception _ -> true
  ) in
  return (List.length envs_without_path mod 2 = 1)

(** The current environment must include the potential first-class module
    signature definition of the corresponding projection in the [path]. *)
let of_path
  (is_value : bool)
  (path : Path.t)
  (long_ident : Longident.t option)
  : t Monad.t =
  let* is_gadt = PathName.is_gadt path in
  of_path_aux path >>= fun (base_path, fields, signature_path) ->
  match (fields, signature_path) with
  | ([], None) ->
    PathName.of_path_without_convert is_value base_path >>= fun path_name ->
    PathName.try_convert path_name >>= fun conversion ->
    begin match conversion with
    | None ->
      begin match long_ident with
      | None -> return (PathName (path_name, is_gadt))
      | Some long_ident ->
        PathName.of_long_ident is_value long_ident >>= fun path_name ->
        return (PathName (path_name, is_gadt))
      end
    | Some path_name -> return (PathName (path_name, is_gadt))
    end
  | _ ->
    is_module_path_local base_path >>= fun is_local ->
    PathName.of_path_with_convert is_value base_path >>= fun base_path_name ->
    (fields |> Monad.List.map (fun (signature_path, field_string) ->
      Name.of_string is_value field_string >>= fun field_name ->
      PathName.of_path_and_name_with_convert signature_path field_name
    )) >>= fun fields ->
    return (Access (base_path_name, List.rev fields, is_local, is_gadt))

let to_coq (path : t) : SmartPrint.t =
  match path with
  | Access (path, fields, is_local, _) ->
    let path = PathName.to_coq path in
    let path =
      if is_local then
        path
      else
        parens (!^ "|" ^-^ path ^-^ !^ "|") in
    let fields =
      fields |> List.map (fun field -> parens (PathName.to_coq field)) in
    separate (!^ ".") (path :: fields)
  | PathName (path_name, _) -> PathName.to_coq path_name
