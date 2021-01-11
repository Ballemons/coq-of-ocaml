(* type _ bar =
 *   | BarC : int -> int bar
 *   | BarC2: string -> string bar
 *
 * type _ foo =
 *   | FooC : int -> int foo
 *   | FooC2 : bool -> bool foo
 *   (\* | FooC2 : bar -> bar foo *\) *)
(* and bar = *)
  (* | BarC : bool -> bar *)
  (* | BarC2: 'a foo -> bar *)
  (* | BarD : bool foo ->  bar *)

(* type (_) term =
 *   | Pair : 'a term * ('c -> 'b) term * 'c term -> ('a * 'b) term
 *   | Int : int -> int term
 *   | Bool : bool -> bool term
 *   | Lam : string * 'a term * 'b term -> ('a -> 'b) term
 *   | Foo : 'a term * 'b term -> ('a * 'b) term
 *   | List : 'a list -> ('a list) term
 *   | Unit : unit -> unit term
 *   | App : ('a -> 'b) term * 'a term -> 'b term
 *   | Arrow : ('u -> 'v) -> ('u -> 'v) term
 *   | Val : 'a -> 'a term *)
  (* | List : 'a * ('a list) -> ('a list) term *)
  (* | ASDF : 'a -> ('a) term *)
  (* | ASDF : ('a) term *)
  (* | Foo : 'a term list -> 'a option term *)


(* type ('a, 'f) sym_term = 'a foo * 'f *)

(* let x : (int, string) sym_term = (C 2, "asdf") *)

(* type _ baz = *)
  (* | CB : ('a, 'b) sym_term  -> 'b baz *)

(* type ('a, 'b) bar = {
 *   x : string ;
 *   y : ('a, 'b) sym_term ;
 *   z : 'a
 * } *)


type 'a foo =
  | C : 'a -> 'a foo

(* module S = struct *)
  (* module type SET = sig *)
    (* type x *)
    (* type z *)
    (* val f : x -> x *)
  (* end *)
(* end *)

module type Boxed_set = sig
  type a
  type 'b f
  val baz : a foo
  (* val faz : int *)
  (* val zaz : string *)
  (* module OS : S.SET with type x = a *)
  (* val access : OS.z *)
end


type ('a) set = (module Boxed_set with type a = 'a)

(* type _ baz =
 *   | C : 'a -> 'a baz
 *
 * module X = struct
 *   type a
 *   let z : a baz -> a =
 *     function
 *     | C a -> a
 * end *)

(* type 'elt voz = (module Boxed_set with type elt = 'elt) *)

(* type ('a, 'b) foo = *)
  (* | Bar : (int, string) foo *)

(* let evalFoo : type a. a foo -> a = function
 *   | FooC n -> n
 *   | FooC2 b -> b
 *
 * let evalBar : type a. a bar -> a = function
 *   | BarC2 s -> s
 *   | BarC n -> n
 *
 * let rec eval : type a. a term -> a = function
 *   | Int n -> n
 *   | Bool b -> b *)
  (* | Lam (x, ty, t) -> (function x -> eval t) *)
  (* | Pair (a, f, b) -> (eval a, (eval f)(eval b)) *)
  (* | Foo (f, b) -> (evalBar f, evalFoo b) *)
  (* | List xs -> xs *)
  (* | App (t1, t2) -> (eval t1) (eval t2) *)
  (* | Val a -> a *)
  (* | Arrow x -> x *)
  (* | List (x, xs) -> x :: xs *)
  (* | Foo ls -> *)
    (* begin match ls with *)
    (* | [] -> None *)
    (* | x :: _ -> Some (eval x) *)
    (* end *)

(* let get_int : int term -> int = function
 *   | Int n -> n
 *   | App (t1, t2) -> (eval t1) (eval t2) *)

(* type _ foo =
 *   | FooC : bar -> bar foo
 *   | FooC2 : 'a -> 'a foo
 * and
 *   bar =
 *   | BarC
 *
 *
 * type ('a , 'b) foo =
 *   | Bar : 'a * int * 'b * 'c -> ('b, string) foo
 *   | Other of int
 *
 * Translation we want:
 * Inductive pre_foo : Set :=
 * | Bar : forall {a b c : Set}, a -> int -> b -> c -> foo
 * | Other : int -> foo.
 *
 * Fixpoint foo_wf (t : foo) (a : Set) (b : Set) :=
 *    match t with
 *    | Bar _ _ _ _ => (a = unit) /\ (b = string)
 *    | Other => (a = unit) /\ (b = unit)
 *
 * type 'a expr =
 *   | Int : int -> int expr
 *   | String : string -> string expr
 *   | Sum : int expr * int expr -> int expr
 *   | Pair : 'a expr * 'b expr -> ('a * 'b) expr
 *
 * let rec proj_int (e : int expr) : int =
 *   match[@coq_match_with_default] e with
 *   | Int n -> n
 *   | Sum (e1, e2) -> proj_int e1 + proj_int e2
 *
 * type 'a one_case =
 *   | SingleCase : int one_case
 *   | Impossible : bool one_case
 *
 * let x : int =
 *   match[@coq_match_with_default] SingleCase with
 *   | SingleCase -> 0 *)
