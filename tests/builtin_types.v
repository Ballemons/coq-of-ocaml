Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition n : Z := 12.

Definition c1 : ascii := "a" % char.

Definition c2 : ascii := "010" % char.

Definition c3 : ascii := "009" % char.

Definition c4 : ascii := """" % char.

Definition s : string := "hi
	:)""" % string.

Definition f : Z :=
  (* ❌ Float constant 1.0 is approximated by the integer 1 *) 1.

Definition b1 : bool := false.

Definition b2 : bool := true.

Definition u : unit := tt.

Definition l1 {A : Type} : list A := [].

Definition l2 : list Z := cons 0 (cons 1 (cons 2 (cons 3 []))).

Definition o : option Z :=
  if b1 then
    None
  else
    Some n.
