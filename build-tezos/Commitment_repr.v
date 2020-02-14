(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Blinded_public_key_hash.
Require Tezos.Tez_repr.

Module t.
  Record record := Build {
    blinded_public_key_hash : Blinded_public_key_hash.t;
    amount : Tez_repr.t }.
  Definition with_blinded_public_key_hash blinded_public_key_hash
    (r : record) :=
    Build blinded_public_key_hash r.(amount).
  Definition with_amount amount (r : record) :=
    Build r.(blinded_public_key_hash) amount.
End t.
Definition t := t.record.

Definition encoding : Data_encoding.encoding t :=
  Data_encoding.conv
    (fun function_parameter =>
      let '{|
        t.blinded_public_key_hash := blinded_public_key_hash;
          t.amount := amount
          |} := function_parameter in
      (blinded_public_key_hash, amount))
    (fun function_parameter =>
      let '(blinded_public_key_hash, amount) := function_parameter in
      {| t.blinded_public_key_hash := blinded_public_key_hash;
        t.amount := amount |}) None
    (Data_encoding.tup2 Blinded_public_key_hash.encoding Tez_repr.encoding).

Definition not_first_class_module : unit := tt.
