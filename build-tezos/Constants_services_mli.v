(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Alpha_context.

Import Alpha_context.

Parameter errors : forall {E F H J K a b c i o q : Set},
  (((RPC_service.t
    ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit +
      (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
  Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t (RPC_context.t * a) q i o -> a ->
    a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o))
      *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (J * a * b * c * q * i * o)) * K))))
    * K * a -> a -> Lwt.t (Error_monad.shell_tzresult Data_encoding.json_schema).

Parameter all : forall {E F H J K a b c i o q : Set},
  (((RPC_service.t
    ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit +
      (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
  Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t (RPC_context.t * a) q i o -> a ->
    a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o))
      *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (J * a * b * c * q * i * o)) * K))))
    * K * a -> a -> Lwt.t (Error_monad.shell_tzresult Alpha_context.Constants.t).

Parameter register : unit -> unit.
