open SmartPrint
open Monad.Notations

type t =
  | Set
  | Tag
  | Arrow of t * t

let to_string (k : t) : string =
  match k with
  | Set -> "Set"
  | Tag -> "vtag"
  | _ -> ""

let to_coq (k : t) : SmartPrint.t =
  !^ (to_string k)

let union k1 k2 : t =
  match k1, k2 with
  | Arrow _ , _ -> k1
  | _, Arrow _ -> k2
  | Set, t | t, Set -> t
  | t, _ -> t
