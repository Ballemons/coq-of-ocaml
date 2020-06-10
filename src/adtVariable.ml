type variable =
  | Error
  | Parameter of string
  | Index of string
  | Unknown

module TypeHash =
struct
  type t = Types.type_expr
  let equal = Types.TypeOps.equal
  let hash = Types.TypeOps.hash
end

module TypeHashtbl = Hashtbl.Make(TypeHash)

type t = variable list TypeHashtbl.t
