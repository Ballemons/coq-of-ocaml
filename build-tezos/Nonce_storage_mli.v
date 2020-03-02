(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Import Tezos.Environment.
Import Environment.Notations.
Require Tezos.Level_repr.
Require Tezos.Nonce_hash.
Require Tezos.Raw_context.
Require Tezos.Seed_repr.
Require Tezos.Storage_mli. Module Storage := Storage_mli.

(* extensible_type_definition `error` *)

Definition t : Set := Seed_repr.nonce.

Definition nonce : Set := t.

Parameter encoding : Data_encoding.t nonce.

Definition unrevealed : Set := Storage.unrevealed_nonce.

Inductive status : Set :=
| Unrevealed : unrevealed -> status
| Revealed : Seed_repr.nonce -> status.

Parameter get :
  Raw_context.t -> Level_repr.t -> Lwt.t (Error_monad.tzresult status).

Parameter record_hash :
  Raw_context.t -> unrevealed -> Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter reveal :
  Raw_context.t -> Level_repr.t -> nonce ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter of_bytes : MBytes.t -> Error_monad.tzresult nonce.

Parameter __hash_value : nonce -> Nonce_hash.t.

Parameter check_hash : nonce -> Nonce_hash.t -> bool.
