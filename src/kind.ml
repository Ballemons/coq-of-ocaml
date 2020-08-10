open SmartPrint
open Monad.Notations

type t =
  | Set
  | Tag

let to_string (k : t) : string =
  match k with
  | Set -> "Set"
  | Tag -> "vtag"

let to_coq (k : t) : SmartPrint.t =
  !^ (to_string k)
