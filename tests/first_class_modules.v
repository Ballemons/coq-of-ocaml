(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module S.
  Module SET.
    Record signature {elt t : Type} : Type := {
      elt := elt;
      t := t;
      empty : t;
      is_empty : t -> bool;
      mem : elt -> t -> bool;
      add : elt -> t -> t;
      singleton : elt -> t;
      remove : elt -> t -> t;
      union : t -> t -> t;
      inter : t -> t -> t;
      diff : t -> t -> t;
      compare : t -> t -> int;
      equal : t -> t -> bool;
      subset : t -> t -> bool;
      iter : (elt -> unit) -> t -> unit;
      map : (elt -> elt) -> t -> t;
      fold : forall {a : Set}, (elt -> a -> a) -> t -> a -> a;
      for_all : (elt -> bool) -> t -> bool;
      __exists : (elt -> bool) -> t -> bool;
      filter : (elt -> bool) -> t -> t;
      partition : (elt -> bool) -> t -> t * t;
      cardinal : t -> int;
      elements : t -> list elt;
      min_elt_opt : t -> option elt;
      max_elt_opt : t -> option elt;
      choose_opt : t -> option elt;
      split : elt -> t -> t * bool * t;
      find_opt : elt -> t -> option elt;
      find_first_opt : (elt -> bool) -> t -> option elt;
      find_last_opt : (elt -> bool) -> t -> option elt;
      of_list : list elt -> t;
    }.
  End SET.
End S.

Inductive type_annot : Set :=
| Type_annot : string -> type_annot.

Inductive field_annot : Set :=
| Field_annot : string -> field_annot.

Definition pair (a b : Type) : Type := a * b.

Inductive comb : Set :=
| Comb : comb.

Inductive leaf : Set :=
| Leaf : leaf.

Inductive comparable_struct : vtag -> vtag -> Set :=
| Int_key : forall {position : vtag},
  option type_annot -> comparable_struct int_tag position
| String_key : forall {position : vtag},
  option type_annot -> comparable_struct string_tag position
| Bool_key : forall {position : vtag},
  option type_annot -> comparable_struct bool_tag position
| Pair_key : forall {a b position : vtag},
  comparable_struct a (constr_tag "leaf" leaf) * option field_annot ->
  comparable_struct b position * option field_annot -> option type_annot ->
  comparable_struct
    (constr_tag "pair_var a_var b" (pair (decode_vtag a) (decode_vtag b)))
    (constr_tag "comb" comb).

Definition comparable_ty (a : vtag) : Set :=
  comparable_struct a (constr_tag "comb" comb).

Definition zoo (a : vtag) (b : Type) : Type :=
  comparable_struct a (constr_tag "comb" comb) * b * list (decode_vtag a).

Module Boxed_set.
  Record signature {elt : vtag} {OPS_t : Type} : Type := {
    elt := elt;
    elt_ty : comparable_ty elt;
    OPS : S.SET.signature (elt := (decode_vtag elt)) (t := OPS_t);
    boxed : OPS.(S.SET.t);
    size : int;
  }.
End Boxed_set.

Definition set (elt : vtag) : Type :=
  {OPS_t : Type & Boxed_set.signature (elt := elt) (OPS_t := OPS_t)}.

Module IncludedFoo.
  Record signature {bar : Set} : Set := {
    bar := bar;
    foo : bar;
  }.
End IncludedFoo.

Module Triple.
  Record signature {a b c : Set} : Set := {
    a := a;
    b := b;
    c := c;
    va : a;
    vb : b;
    vc : c;
  }.
End Triple.
