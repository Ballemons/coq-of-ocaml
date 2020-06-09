type variable =
  | Error
  | Parameter of string
  | Index of string
  | Unknown

type t = (Path.t, variable list) Hashtbl.t
