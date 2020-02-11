(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Contract_repr.
Require Tezos.Cycle_repr.
Require Tezos.Nonce_storage_mli. Module Nonce_storage := Nonce_storage_mli.
Require Tezos.Raw_context.
Require Tezos.Tez_repr.

Inductive balance : Set :=
| Contract : Contract_repr.t -> balance
| Rewards :
  (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) -> Cycle_repr.t ->
  balance
| Fees :
  (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) -> Cycle_repr.t ->
  balance
| Deposits :
  (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) -> Cycle_repr.t ->
  balance.

Inductive balance_update : Set :=
| Debited : Tez_repr.t -> balance_update
| Credited : Tez_repr.t -> balance_update.

Definition balance_updates := list (balance * balance_update).

Parameter balance_updates_encoding : Data_encoding.t balance_updates.

Parameter cleanup_balance_updates : balance_updates -> balance_updates.

Module frozen_balance.
  Record record := Build {
    deposit : Tez_repr.t;
    fees : Tez_repr.t;
    rewards : Tez_repr.t }.
  Definition with_deposit deposit (r : record) :=
    Build deposit r.(fees) r.(rewards).
  Definition with_fees fees (r : record) :=
    Build r.(deposit) fees r.(rewards).
  Definition with_rewards rewards (r : record) :=
    Build r.(deposit) r.(fees) rewards.
End frozen_balance.
Definition frozen_balance := frozen_balance.record.

Parameter init :
  Raw_context.t -> Contract_repr.t ->
  (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter remove :
  Raw_context.t -> Contract_repr.t -> Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter get :
  Raw_context.t -> Contract_repr.t ->
  Lwt.t
    (Error_monad.tzresult
      (option (|Signature.Public_key_hash|).(S.SPublic_key_hash.t))).

Parameter registered :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult bool).

Parameter set :
  Raw_context.t -> Contract_repr.t ->
  option (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Raw_context.t).

(* extensible_type error *)

Parameter fold : forall {a : Set},
  Raw_context.t -> a ->
  ((|Signature.Public_key_hash|).(S.SPublic_key_hash.t) -> a -> Lwt.t a) ->
  Lwt.t a.

Parameter __list_value :
  Raw_context.t ->
  Lwt.t (list (|Signature.Public_key_hash|).(S.SPublic_key_hash.t)).

Parameter freeze_deposit :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Tez_repr.t -> Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter freeze_fees :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Tez_repr.t -> Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter freeze_rewards :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Tez_repr.t -> Lwt.t (Error_monad.tzresult Raw_context.t).

Parameter cycle_end :
  Raw_context.t -> Cycle_repr.t -> list Nonce_storage.unrevealed ->
  Lwt.t
    (Error_monad.tzresult
      (Raw_context.t * balance_updates *
        list (|Signature.Public_key_hash|).(S.SPublic_key_hash.t))).

Parameter punish :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Cycle_repr.t -> Lwt.t (Error_monad.tzresult (Raw_context.t * frozen_balance)).

Parameter has_frozen_balance :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Cycle_repr.t -> Lwt.t (Error_monad.tzresult bool).

Parameter __frozen_balance_value :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Tez_repr.t).

Parameter frozen_balance_encoding : Data_encoding.t frozen_balance.

Parameter frozen_balance_by_cycle_encoding :
  Data_encoding.t ((|Cycle_repr.Map|).(S.MAP.t) frozen_balance).

Parameter frozen_balance_by_cycle :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t ((|Cycle_repr.Map|).(S.MAP.t) frozen_balance).

Parameter full_balance :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Tez_repr.t).

Parameter staking_balance :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Tez_repr.t).

Parameter delegated_contracts :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (list Contract_repr.t).

Parameter delegated_balance :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Tez_repr.t).

Parameter deactivated :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult bool).

Parameter grace_period :
  Raw_context.t -> (|Signature.Public_key_hash|).(S.SPublic_key_hash.t) ->
  Lwt.t (Error_monad.tzresult Cycle_repr.t).
