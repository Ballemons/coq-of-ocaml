type _ t =
  | S : int -> int t
  | G : int t
  | D : string -> string t
[@@coq_tag_gadt]


let x : int t = S 3

let f (x : int t) : int =
  match[@coq_match_with_default] x with
  (* match x with *)
  | S x -> x
  | G -> 3
  | _ -> .

       
(* type 'b x = 'b list *)

(* type _ z = *)
  (* | Cz : int z *)

(* type _ t = *)
  (* | C1 : int t *)
  (* | C2 : string t *)
  (* | C3 : 'a * 'a z * 'a x -> ('a list) t *)

(* type ex = Ex : 'a -> ex
 * let rec of_list l =
 *   match l with
 *   | [] -> Ex ()
 *   | _ :: l -> Ex (of_list l) *)

(* Of C3z
 * [  ][ , a : vtag ]
 * [  ][ , a : vtag ]
 * x
 * list
 * [  ][ , b : Set ]
 * [  ][  ]
 * list
 * [  ][ , b : Set ]
 * [ , a : vtag ][  ]
 * t
 * list
 * [  ][ , a : Set ]
 * [  ][ , a : Set ]
 *
 * Final
 * [ , a : vtag ][ , a : Set ] *)

(* Of C3[  ][ , a : Set ]
 * z
 * [  ][  ]
 * [ , a : Set ][  ]
 * x
 * list
 * [  ][ , b : Set ]
 * [  ][  ]
 * list
 * [  ][ , b : Set ]
 * [ , a : Set ][  ]
 * t
 * list
 * [  ][ , a : Set ]
 * [  ][ , a : Set ]
 *
 * Final
 * [ , a : Set ][ , a : Set ] *)
