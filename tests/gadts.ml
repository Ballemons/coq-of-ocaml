(* type 'a gre = Arg o
 *
 * type ('a , 'b) foo =
 *   | Bar : 'a * 'b -> ('a, 'b) foo
 *   | Other of int *)

(* type 'a expr =
 *   | Int : int -> int expr
 *   | Sum : int expr * int expr -> int expr
 *   | String : string expr
 *   | Float : float expr
 *   | Option : 'a option expr
 *   | Arr : 'a expr -> ('a -> 'b -> 'c -> 'd) expr
 *   | Tup : 'a expr -> ('a * 'b * 'c * 'd) expr
 *   | Var : 'a -> 'a expr
 * 
 * let rec proj_int (e : int expr) : int =
 *   match [@coq_match_with_default] e with
 *   | Int n -> n
 *   | Sum (e1, e2) -> proj_int e1 + proj_int e2
 *   | Var n -> n *)

(* type 'a one_case = *)
  (* | SingleCase : int one_case *)
  (* | Impossible : bool one_case *)

(* let x : int =
 *   match [@coq_match_with_default] SingleCase with
 *   | SingleCase -> 0 *)

type (_, _) foo =
  | Constr : 'a * 'c * 'b -> ('a, 'b) foo

let asdf : (int, string) foo = Constr (1, 2.4, "asdf")

type _ term =
| Nat : int -> int term
| Bool: bool -> bool term
| Add : int term * int term -> int term
| Or : bool term * bool term -> bool term

let rec interp : type a. a term -> a =
function
| Nat n -> n
| Bool b -> b
| Add (n, m) -> interp n + interp m
| Or (x, y) -> interp x || interp y

(* let x : type a. a -> a option = fun x -> Some x *)

type f =
  | C1
  | C2

let funf (x : f) =
  match x with
  | C1 -> 1
  | C2 -> 2
