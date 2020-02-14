(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Constants_repr.
Require Tezos.Nonce_hash.
Require Tezos.State_hash.

Inductive seed : Set :=
| B : State_hash.t -> seed.

Inductive t : Set :=
| T : State_hash.t -> t.

Inductive sequence : Set :=
| S : State_hash.t -> sequence.

Definition nonce := MBytes.t.

Definition nonce_encoding : Data_encoding.encoding MBytes.t :=
  Data_encoding.Fixed.__bytes_value Constants_repr.nonce_length.

Definition initial_seed : string := "Laissez-faire les proprietaires.".

Definition zero_bytes : MBytes.t :=
  MBytes.of_string (String.make Nonce_hash.size "000" % char).

Definition state_hash_encoding : Data_encoding.encoding State_hash.t :=
  Data_encoding.conv State_hash.to_bytes State_hash.of_bytes_exn None
    (Data_encoding.Fixed.__bytes_value Nonce_hash.size).

Definition seed_encoding : Data_encoding.encoding seed :=
  Data_encoding.conv
    (fun function_parameter =>
      let 'B b := function_parameter in
      b) (fun b => B b) None state_hash_encoding.

Definition empty : seed :=
  B (State_hash.hash_bytes None [ MBytes.of_string initial_seed ]).

Definition __nonce_value (function_parameter : seed) : MBytes.t -> seed :=
  let 'B state := function_parameter in
  fun __nonce_value =>
    B (State_hash.hash_bytes None [ State_hash.to_bytes state; __nonce_value ]).

Definition initialize_new (function_parameter : seed) : list MBytes.t -> t :=
  let 'B state := function_parameter in
  fun append =>
    T
      (State_hash.hash_bytes None
        (cons (State_hash.to_bytes state) (cons zero_bytes append))).

Definition xor_higher_bits (i : int32) (b : MBytes.t) : MBytes.t :=
  let higher := MBytes.get_int32 b 0 in
  let r := Int32.logxor higher i in
  let res := MBytes.copy b in
  (* ❌ Sequences of instructions are ignored (operator ";") *)
  (* ❌ instruction_sequence ";" *)
  res.

Definition __sequence_value (function_parameter : t) : int32 -> sequence :=
  let 'T state := function_parameter in
  fun n =>
    Pervasives.op_pipegt
      (Pervasives.op_pipegt (State_hash.to_bytes state) (xor_higher_bits n))
      (fun b => S (State_hash.hash_bytes None [ b ])).

Definition take (function_parameter : sequence) : MBytes.t * sequence :=
  let 'S state := function_parameter in
  let b := State_hash.to_bytes state in
  let h := State_hash.hash_bytes None [ b ] in
  ((State_hash.to_bytes h), (S h)).

Definition take_int32 (s : sequence) (bound : (|Compare.Int32|).(Compare.S.t))
  : int32 * sequence :=
  if
    (|Compare.Int32|).(Compare.S.op_lteq) bound
      (* ❌ Constant of type int32 is converted to int *)
      0 then
    Pervasives.invalid_arg "Seed_repr.take_int32"
  else
    let fix loop (s : sequence) {struct s} : int32 * sequence :=
      let '(__bytes_value, s) := take s in
      let r := Int32.abs (MBytes.get_int32 __bytes_value 0) in
      let drop_if_over :=
        Int32.sub Int32.max_int (Int32.rem Int32.max_int bound) in
      if (|Compare.Int32|).(Compare.S.op_gteq) r drop_if_over then
        loop s
      else
        let v := Int32.rem r bound in
        (v, s) in
    loop s.

(* ❌ Structure item `typext` not handled. *)
(* type_extension *)

(* ❌ Top-level evaluations are ignored *)
(* top_level_evaluation *)

Definition make_nonce (__nonce_value : MBytes.t)
  : Error_monad.tzresult MBytes.t :=
  if
    (|Compare.Int|).(Compare.S.op_ltgt) (MBytes.length __nonce_value)
      Constants_repr.nonce_length then
    Error_monad.__error_value extensible_type_value
  else
    Error_monad.ok __nonce_value.

Definition __hash_value (__nonce_value : MBytes.t) : Nonce_hash.t :=
  Nonce_hash.hash_bytes None [ __nonce_value ].

Definition check_hash (__nonce_value : MBytes.t) (__hash_value : Nonce_hash.t)
  : bool :=
  Pervasives.op_andand
    ((|Compare.Int|).(Compare.S.op_eq) (MBytes.length __nonce_value)
      Constants_repr.nonce_length)
    (Nonce_hash.equal (Nonce_hash.hash_bytes None [ __nonce_value ])
      __hash_value).

Definition nonce_hash_key_part : Nonce_hash.t -> list string -> list string :=
  Nonce_hash.to_path.

Definition initial_nonce_0 : MBytes.t := zero_bytes.

Definition initial_nonce_hash_0 : Nonce_hash.t := __hash_value initial_nonce_0.

Definition deterministic_seed (__seed_value : seed) : seed :=
  __nonce_value __seed_value zero_bytes.

Definition initial_seeds (n : (|Compare.Int|).(Compare.S.t)) : list seed :=
  let fix loop
    (acc : list seed) (__elt_value : seed) (i : (|Compare.Int|).(Compare.S.t))
    {struct acc} : list seed :=
    if (|Compare.Int|).(Compare.S.op_eq) i 1 then
      List.rev (cons __elt_value acc)
    else
      loop (cons __elt_value acc) (deterministic_seed __elt_value)
        (Pervasives.op_minus i 1) in
  loop nil (B (State_hash.hash_bytes None nil)) n.
