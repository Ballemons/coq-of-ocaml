open SmartPrint
open Monad.Notations

type t =
  | Set
  | Tag of MixedPath.t

let to_string (k : t) : string =
  match k with
  | Set -> "Set"
  | Tag name -> MixedPath.to_string name ^ "_tags"

let to_coq (k : t) : SmartPrint.t =
  !^ (to_string k)
