(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Import Tezos.Environment.
Import Environment.Notations.
Require Tezos.Alpha_context.
Require Tezos.Apply_results.

Module ConstructorRecords_validation_mode.
  Module validation_mode.
    Module Application.
      Record record {block_header baker block_delay : Set} : Set := Build {
        block_header : block_header;
        baker : baker;
        block_delay : block_delay }.
      Arguments record : clear implicits.
      Definition with_block_header {t_block_header t_baker t_block_delay}
        block_header (r : record t_block_header t_baker t_block_delay) :=
        Build t_block_header t_baker t_block_delay block_header r.(baker)
          r.(block_delay).
      Definition with_baker {t_block_header t_baker t_block_delay} baker
        (r : record t_block_header t_baker t_block_delay) :=
        Build t_block_header t_baker t_block_delay r.(block_header) baker
          r.(block_delay).
      Definition with_block_delay {t_block_header t_baker t_block_delay}
        block_delay (r : record t_block_header t_baker t_block_delay) :=
        Build t_block_header t_baker t_block_delay r.(block_header) r.(baker)
          block_delay.
    End Application.
    Definition Application_skeleton := Application.record.
    
    Module Partial_application.
      Record record {block_header baker block_delay : Set} : Set := Build {
        block_header : block_header;
        baker : baker;
        block_delay : block_delay }.
      Arguments record : clear implicits.
      Definition with_block_header {t_block_header t_baker t_block_delay}
        block_header (r : record t_block_header t_baker t_block_delay) :=
        Build t_block_header t_baker t_block_delay block_header r.(baker)
          r.(block_delay).
      Definition with_baker {t_block_header t_baker t_block_delay} baker
        (r : record t_block_header t_baker t_block_delay) :=
        Build t_block_header t_baker t_block_delay r.(block_header) baker
          r.(block_delay).
      Definition with_block_delay {t_block_header t_baker t_block_delay}
        block_delay (r : record t_block_header t_baker t_block_delay) :=
        Build t_block_header t_baker t_block_delay r.(block_header) r.(baker)
          block_delay.
    End Partial_application.
    Definition Partial_application_skeleton := Partial_application.record.
    
    Module Partial_construction.
      Record record {predecessor : Set} : Set := Build {
        predecessor : predecessor }.
      Arguments record : clear implicits.
      Definition with_predecessor {t_predecessor} predecessor
        (r : record t_predecessor) :=
        Build t_predecessor predecessor.
    End Partial_construction.
    Definition Partial_construction_skeleton := Partial_construction.record.
    
    Module Full_construction.
      Record record {predecessor protocol_data baker block_delay : Set} : Set := Build {
        predecessor : predecessor;
        protocol_data : protocol_data;
        baker : baker;
        block_delay : block_delay }.
      Arguments record : clear implicits.
      Definition with_predecessor
        {t_predecessor t_protocol_data t_baker t_block_delay} predecessor
        (r : record t_predecessor t_protocol_data t_baker t_block_delay) :=
        Build t_predecessor t_protocol_data t_baker t_block_delay predecessor
          r.(protocol_data) r.(baker) r.(block_delay).
      Definition with_protocol_data
        {t_predecessor t_protocol_data t_baker t_block_delay} protocol_data
        (r : record t_predecessor t_protocol_data t_baker t_block_delay) :=
        Build t_predecessor t_protocol_data t_baker t_block_delay
          r.(predecessor) protocol_data r.(baker) r.(block_delay).
      Definition with_baker
        {t_predecessor t_protocol_data t_baker t_block_delay} baker
        (r : record t_predecessor t_protocol_data t_baker t_block_delay) :=
        Build t_predecessor t_protocol_data t_baker t_block_delay
          r.(predecessor) r.(protocol_data) baker r.(block_delay).
      Definition with_block_delay
        {t_predecessor t_protocol_data t_baker t_block_delay} block_delay
        (r : record t_predecessor t_protocol_data t_baker t_block_delay) :=
        Build t_predecessor t_protocol_data t_baker t_block_delay
          r.(predecessor) r.(protocol_data) r.(baker) block_delay.
    End Full_construction.
    Definition Full_construction_skeleton := Full_construction.record.
  End validation_mode.
End ConstructorRecords_validation_mode.
Import ConstructorRecords_validation_mode.

Reserved Notation "'validation_mode.Application".
Reserved Notation "'validation_mode.Partial_application".
Reserved Notation "'validation_mode.Partial_construction".
Reserved Notation "'validation_mode.Full_construction".

Inductive validation_mode : Set :=
| Application : 'validation_mode.Application -> validation_mode
| Partial_application : 'validation_mode.Partial_application -> validation_mode
| Partial_construction :
  'validation_mode.Partial_construction -> validation_mode
| Full_construction : 'validation_mode.Full_construction -> validation_mode

where "'validation_mode.Application" :=
  (validation_mode.Application_skeleton Alpha_context.Block_header.t
    Alpha_context.public_key_hash Alpha_context.Period.t)
and "'validation_mode.Partial_application" :=
  (validation_mode.Partial_application_skeleton Alpha_context.Block_header.t
    Alpha_context.public_key_hash Alpha_context.Period.t)
and "'validation_mode.Partial_construction" :=
  (validation_mode.Partial_construction_skeleton (|Block_hash|).(S.HASH.t))
and "'validation_mode.Full_construction" :=
  (validation_mode.Full_construction_skeleton (|Block_hash|).(S.HASH.t)
    Alpha_context.Block_header.contents Alpha_context.public_key_hash
    Alpha_context.Period.t).

Module validation_mode.
  Include ConstructorRecords_validation_mode.validation_mode.
  Definition Application := 'validation_mode.Application.
  Definition Partial_application := 'validation_mode.Partial_application.
  Definition Partial_construction := 'validation_mode.Partial_construction.
  Definition Full_construction := 'validation_mode.Full_construction.
End validation_mode.

Module validation_state.
  Record record : Set := Build {
    mode : validation_mode;
    chain_id : (|Chain_id|).(S.HASH.t);
    ctxt : Alpha_context.t;
    op_count : int }.
  Definition with_mode mode (r : record) :=
    Build mode r.(chain_id) r.(ctxt) r.(op_count).
  Definition with_chain_id chain_id (r : record) :=
    Build r.(mode) chain_id r.(ctxt) r.(op_count).
  Definition with_ctxt ctxt (r : record) :=
    Build r.(mode) r.(chain_id) ctxt r.(op_count).
  Definition with_op_count op_count (r : record) :=
    Build r.(mode) r.(chain_id) r.(ctxt) op_count.
End validation_state.
Definition validation_state := validation_state.record.

Parameter Included_PROTOCOL :
  {'[block_header, operation] : [Set ** Set] &
    Updater.PROTOCOL.signature
      (block_header_data := Alpha_context.Block_header.protocol_data)
      (block_header := block_header)
      (block_header_metadata := Apply_results.block_metadata)
      (operation_data := Alpha_context.packed_protocol_data)
      (operation_receipt := Apply_results.packed_operation_metadata)
      (operation := operation) (validation_state := validation_state)}.

Definition max_block_length : int :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.max_block_length).

Definition max_operation_data_length : int :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.max_operation_data_length).

Definition validation_passes : list Updater.quota :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.validation_passes).

Definition block_header_data :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.block_header_data).

Definition block_header_data_encoding : Data_encoding.t block_header_data :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.block_header_data_encoding).

Definition block_header :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.block_header).

Definition block_header_metadata :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.block_header_metadata).

Definition block_header_metadata_encoding :
  Data_encoding.t block_header_metadata :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.block_header_metadata_encoding).

Definition operation_data :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.operation_data).

Definition operation_receipt :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.operation_receipt).

Definition operation := (|Included_PROTOCOL|).(Updater.PROTOCOL.operation).

Definition operation_data_encoding : Data_encoding.t operation_data :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.operation_data_encoding).

Definition operation_receipt_encoding : Data_encoding.t operation_receipt :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.operation_receipt_encoding).

Definition operation_data_and_receipt_encoding :
  Data_encoding.t (operation_data * operation_receipt) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.operation_data_and_receipt_encoding).

Definition acceptable_passes : operation -> list int :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.acceptable_passes).

Definition compare_operations : operation -> operation -> int :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.compare_operations).

Definition current_context :
  validation_state -> Lwt.t (Error_monad.tzresult Context.t) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.current_context).

Definition begin_partial_application :
  (|Chain_id|).(S.HASH.t) -> Context.t -> Time.t -> (|Fitness|).(S.T.t) ->
  block_header -> Lwt.t (Error_monad.tzresult validation_state) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.begin_partial_application).

Definition begin_application :
  (|Chain_id|).(S.HASH.t) -> Context.t -> Time.t -> (|Fitness|).(S.T.t) ->
  block_header -> Lwt.t (Error_monad.tzresult validation_state) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.begin_application).

Definition begin_construction :
  (|Chain_id|).(S.HASH.t) -> Context.t -> Time.t -> Int32.t ->
  (|Fitness|).(S.T.t) -> (|Block_hash|).(S.HASH.t) -> Time.t ->
  option block_header_data -> unit ->
  Lwt.t (Error_monad.tzresult validation_state) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.begin_construction).

Definition apply_operation :
  validation_state -> operation ->
  Lwt.t (Error_monad.tzresult (validation_state * operation_receipt)) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.apply_operation).

Definition finalize_block :
  validation_state ->
  Lwt.t
    (Error_monad.tzresult (Updater.validation_result * block_header_metadata))
  := (|Included_PROTOCOL|).(Updater.PROTOCOL.finalize_block).

Definition rpc_services : RPC_directory.t Updater.rpc_context :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.rpc_services).

Definition init :
  Context.t -> Block_header.shell_header ->
  Lwt.t (Error_monad.tzresult Updater.validation_result) :=
  (|Included_PROTOCOL|).(Updater.PROTOCOL.init).
