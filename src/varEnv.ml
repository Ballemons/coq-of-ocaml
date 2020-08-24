open Monad.Notations
type t = (Name.t * Kind.t) list

let to_string (env : t) : string =
  "[ " ^
  (List.fold_left (fun s (name, k) ->
       s ^ ", " ^ (Name.to_string name) ^ " : " ^ (Kind.to_string k)
     )
     "" env)
  ^ " ]"

(* Union preserves the ordering of the first argument *)
let rec union_aux (env1 : t) (env2 : t) : t =
  match env1 with
  | [] -> env2
  | (name, kind) :: env ->
    match List.assoc_opt name env2 with
    | None ->
      (name, kind) :: union_aux env env2
    | Some kind' ->
      let env2 = List.remove_assoc name env2 in
      let kind = Kind.union kind kind' in
      (name, kind) :: union_aux env env2

let union (env1 : t) (env2 : t) : t =
  union_aux env1 env2

let merge (env : t list) : t =
  match env with
  | [] -> []
  | x :: xs -> List.fold_left (fun acc y -> union acc y) x xs

let rec group_by_kind_aux
    (m : t)
    (kind : Kind.t)
  : (Kind.t * Name.t list) list * Name.t list * Kind.t =
  match m with
  | [] -> ([], [], kind)
  | [(name, k)] -> ([], [name], k)
  | (name, k) :: ls ->
    let (ls, names, k') = group_by_kind_aux ls k in
    if k = k'
    then (ls, names @ [name], k)
    else ((k', names) :: ls, [name], k)

let group_by_kind
    (m : t)
  : ((Kind.t * Name.t list) list) =
  match m with
  | [] -> []
  | [ (name,k) ] -> [k, [name]]
  | (name, k) :: ls ->
    let (ls, names, k') = group_by_kind_aux ls k in
    if k = k'
    then ((k, names @ [name]) :: ls)
    else
      if List.length names = 0
      then ((k, [name]) :: ls)
      else ((k, [name]) :: (k', names) :: ls)

