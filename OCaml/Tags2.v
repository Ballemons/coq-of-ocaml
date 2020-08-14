Require Import Coq.Strings.String.

(*Inductive vsort : Type :=
| vstar : vsort
| vconstr0 : vsort
| vconstr1 : vsort
| vconstr2 : vsort. *)

Inductive vtag : Type :=
| constr0_tag : string -> vtag
| constr1_tag : string -> vtag -> vtag
| constr2_tag : string -> vtag -> vtag -> vtag
| app_tag : vtag vconstr -> vtag vstar -> vtag vstar
| arrow_tag : vtag -> vtag -> vtag
| tuple_tag : vtag -> vtag -> vtag
| string_tag : vtag
| int_tag : vtag
| empty_tag : vtag
| var_tag : forall (t0 : Set), vtag.

Open Scope type_scope.
(*Fixpoint decode_vsort (s : vsort) : Type :=
  match s with
  | vstar => Type
  | vconstr => forall {a}, vtag a -> Type
  end. *)

Fixpoint decode_vtag (tag : vtag)
         (f0 : string -> Type)
         (f1 : string -> vtag -> Type)
         (f2 : string -> vtag -> vtag -> Type)
         {struct tag} : Type.
  refine(match tag in vtag return Type
          with
          | @constr0_tag st => f0 st
          | @constr1_tag st t1 => f1 st t1
          | @constr2_tag st t1 t2 => f2 st t1 t2
          (*| app_tag t1 t2 => (decode_vtag _ t1 f) _ t2 *)
          | arrow_tag t1 t2 => decode_vtag t1 f0 f1 f2 -> decode_vtag t2 f0 f1 f2
          | tuple_tag t1 t2 => decode_vtag t1 f0 f1 f2 * decode_vtag t2 f0 f1 f2
          | empty_tag => unit
          | string_tag => string
          | int_tag => nat
          | var_tag t => t
          end).
Defined.

Open Scope string_scope.
Inductive foo : vtag -> Type :=
  | C3 : string -> foo string_tag
  | C1 : nat -> foo int_tag.

Inductive bar : vtag -> Type :=
  C2 : string -> bar (constr1_tag "foo" string_tag).

Program Definition map0 (st : string) : Type := unit.
Program Definition map2 (st : string) : vtag -> vtag -> Type := fun _ _ => unit.


(* type 'a expr = *)
(*   | Int : int -> int expr *)
(*   | Sum : int expr * int expr -> int expr *)
(*   | Var : 'a -> 'a expr *)
(*   | Arr : 'a expr -> ('a -> 'b -> 'c -> 'd) expr *)

(* Set Printing Universes. *)
Inductive pre_expr : Type :=
| Int : nat -> pre_expr
| Sum : pre_expr * pre_expr -> pre_expr
| Var : forall (X : Type), X -> pre_expr
| Arr : pre_expr -> pre_expr.

(* Check (Var _ (Int 1)). *)

Import EqNotations.

(* Unset Guard Checking. *)

Fixpoint expr_wf' (t : pre_expr) (tag : vtag) n {struct n}: Type :=
  match n with
  | O => False
  | S z =>
      let expr (t : vtag) n := { f & expr_wf' f t z } in
      let map1 (st : string) : vtag -> Type :=
          if st =? "foo"
          then fun t => foo t
          else if st =? "bar"
               then fun t => bar t
               else if st =? "expr"
                    then fun t => expr t z
                    else fun _ => unit in
    match t with
    | Int _ => tag = int_tag
    | Sum (lhs, rhs) =>
      (tag = int_tag) * expr_wf' lhs int_tag z * expr_wf' rhs int_tag z
    | Var ty x => ty = decode_vtag tag map0 map1 map2
    | Arr _ => { '(a, b) | tag = (arrow_tag a b) }
    end
  end.

Definition expr_wf t tag := { x & expr_wf' t tag (S x) }.
(* Opaque expr. *)

Definition expr (t : vtag) := sigT (fun f => expr_wf f t).

Definition map1 (st : string) : vtag -> Type :=
  if st =? "foo"
  then fun t => foo t
  else if st =? "bar"
       then fun t => bar t
       else if st =? "expr"
            then fun t => expr t
            else fun _ => unit.

(* Eval compute in (map1 "foo"). *)

Definition foo_tag := constr1_tag "foo".
Definition bar_tag := constr1_tag "bar".
Definition foo_int_tag := foo_tag int_tag.
Definition bar_str_tag := bar_tag (foo_tag string_tag).
(* Eval compute in (decode_vtag foo_int_tag map0 map1 map2). *)
(* Eval compute in (decode_vtag bar_str_tag map0 map1 map2). *)

Definition expr_tag := constr1_tag "expr".
Definition expr_int_tag := expr_tag int_tag.
(* Eval compute in (decode_vtag expr_int_tag map0 map1 map2). *)


Fixpoint get_Int (e : pre_expr) (wf_t : expr_wf e int_tag) {struct e }
  : decode_vtag int_tag map0 map1 map2.
  refine (match e as t0 return expr_wf t0 int_tag -> nat with
         | Int n => fun _ => n
         | Sum (lhs, rhs) => fun '(existT _ _ (p1, p2, p3)) =>
                              plus (get_Int lhs p2) (get_Int rhs p3)
         | Arr x => fun e =>
                     ltac:(destruct e as [x0]; destruct x0; discriminate)
         | Var ty x => _
                       (* fun e => _ *)
                        (* let eq := rew <- [fun t => ty = decode_tag t] eq1 in eq2 *)
                          (* in rew eq in x *)
  end wf_t).
Defined.


Definition get_int (e : expr int_tag) : int :=
  let '(existT _ e wf_e) := e in
  get_Int e wf_e.
