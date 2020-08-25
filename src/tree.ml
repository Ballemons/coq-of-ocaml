open SmartPrint
open Monad.Notations

type 'a item =
  | Item of Name.t * 'a
  | Module of Name.t * 'a t

and 'a t = 'a item list

let rec map (f : 'a -> 'b) (tree : 'a t) : 'b t =
  let map_item (item : 'a item) : 'b item =
    match item with
    | Item (name, x) -> Item (name, f x)
    | Module (name, tree) -> Module (name, map f tree) in
  tree |> List.map map_item

let rec monad_map (f : 'a -> 'b Monad.t) (tree : 'a t) : 'b t Monad.t =
  let map_item (item : 'a item) : 'b item Monad.t =
    match item with
    | Item (name, x) ->
      let* x = f x in
      return @@ Item (name, x)
    | Module (name, tree) ->
      let* tree = monad_map f tree in
      return @@ Module (name, tree) in
  tree |> Monad.List.map map_item

let rec map_at (tree : 'a t) (path_name : PathName.t) (f : 'a -> 'a) : 'a t =
  let (head, tail) = PathName.get_head_and_tail path_name in
  tree |> List.map (fun item ->
    match item with
    | Item (name, x) ->
      if name = head && tail = None then
        Item (name, f x)
      else
        item
    | Module (name, tree) ->
      if name = head then
        begin match tail with
        | None -> item
        | Some tail -> Module (name, map_at tree tail f)
        end
      else
        item
  )

let rec flatten_aux (prefix : Name.t list) (tree : 'a t) : (PathName.t * 'a) list =
  List.flatten (tree |> List.map (fun item ->
    match item with
    | Item (name, x) -> [(PathName.of_name (List.rev prefix) name, x)]
    | Module (name, tree) -> flatten_aux (name :: prefix) tree
  ))

let flatten (tree : 'a t) : (PathName.t * 'a) list =
  flatten_aux [] tree

let rec size (tree : 'a t) : int =
  tree |> List.fold_left (fun s item ->
    match item with
    | Item _ -> s + 1
    | Module (_, tree) -> s + size tree
  ) 0

let rec pp (pp_a : 'a -> SmartPrint.t option) (tree : 'a t) : SmartPrint.t =
  let pp_item (item : 'a item) : SmartPrint.t =
    match item with
    | Item (name, value) ->
      Name.to_coq name ^-^
      (match pp_a value with
      | None -> empty
      | Some doc -> !^ ":" ^^ doc)
    | Module (name, tree) -> Name.to_coq name ^-^ !^ ":" ^^ pp pp_a tree in
  OCaml.list pp_item tree

let rec find_item (key : Name.t) (tree : 'a t) : 'a option =
  match tree with
  | [] -> None
  | Item (name, k) :: tree ->
    if name = key
    then Some k
    else find_item key tree
  | Module (name, k) :: tree ->
    find_item key tree

(* Updates the first Item found in tree *)
let rec update_item (key : Name.t) (item : 'a) (tree : 'a t) : 'a t =
  match tree with
  | [] -> []
  | Module (name, k) :: tree -> Module (name, k) :: update_item key item tree
  | Item (name, k) :: tree ->
    if name = key
    then Item (name, item) :: tree
    else Item (name, k) :: update_item key item tree

let update_items (l : (Name.t * 'a) list) (tree : 'a t) : 'a t =
  List.fold_left (fun acc (key, item) -> update_item key item acc) tree l

let rec remove_item (key : Name.t) (tree : 'a t) : 'a t =
  match tree with
  | [] -> []
  | Item (name, k) :: tree ->
    if name = key
    then tree
    else Item (name, k) :: remove_item key tree
  | tree' :: tree ->
    tree' :: remove_item key tree

let rec union_aux (env1 : Kind.t t) (env2 : Kind.t t) : Kind.t t =
  match env1 with
  | [] -> env2
  | Module (name, sub) :: env ->
    Module(name, sub) :: union_aux env env2
  | Item (name, kind) :: env ->
    match find_item name env2 with
    | None ->
      Item (name, kind) :: union_aux env env2
    | Some kind' ->
      let env2 = remove_item name env2 in
      let kind = Kind.union kind kind' in
      Item (name, kind) :: union_aux env env2

let union (env1 : Kind.t t) (env2 : Kind.t t) : Kind.t t =
  union_aux env1 env2
