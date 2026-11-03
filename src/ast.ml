open! Core
open Hardcaml
module Sequence_range = Property.Sva.Formula.Sequence_range

type sequence =
  [ `Sequence
  | `Property
  ]

type property = [ `Property ]

module Kind_witness = struct
  type _ t =
    | Sequence : sequence t
    | Property : property t
end

type (_, _) t =
  | True : ('var, sequence) t
  | Atomic_proposition : 'var -> ('var, sequence) t
  | Delay : Sequence_range.t -> ('var, sequence) t
  | Concat : ('var, sequence) t list -> ('var, sequence) t
  | Repeat : ('var, sequence) t * Sequence_range.t -> ('var, sequence) t
  | Sequence_as_property : ('var, sequence) t -> ('var, property) t
  | Not : ('var, property) t -> ('var, property) t
  | X : ('var, property) t -> ('var, property) t
  | Until : ('var, property) t * ('var, property) t -> ('var, property) t
  | Release : ('var, property) t * ('var, property) t -> ('var, property) t
  | Eventually : ('var, property) t -> ('var, property) t
  | Globally : ('var, property) t -> ('var, property) t
  | And : ('var, 'kind) binary_op -> ('var, 'kind) t
  | Or : ('var, 'kind) binary_op -> ('var, 'kind) t
  | Overlapping_implication :
      ('var, sequence) t list * ('var, property) t
      -> ('var, property) t
  | Property_implication : ('var, property) t * ('var, property) t -> ('var, property) t

and ('var, 'kind) binary_op =
  { kind : 'kind Kind_witness.t
  ; lhs : ('var, 'kind) t
  ; rhs : ('var, 'kind) t
  }

let kind : type var kind. (var, kind) t -> kind Kind_witness.t = function
  | True -> Sequence
  | Atomic_proposition (_ : var) -> Sequence
  | Delay (_ : Sequence_range.t) -> Sequence
  | Concat (_ : (var, sequence) t list) -> Sequence
  | Repeat ((_ : (var, sequence) t), (_ : Sequence_range.t)) -> Sequence
  | Sequence_as_property (_ : (var, sequence) t) -> Property
  | Not (_ : (var, property) t) -> Property
  | X (_ : (var, property) t) -> Property
  | Until ((_ : (var, property) t), (_ : (var, property) t)) -> Property
  | Release ((_ : (var, property) t), (_ : (var, property) t)) -> Property
  | Eventually (_ : (var, property) t) -> Property
  | Globally (_ : (var, property) t) -> Property
  | And { kind; lhs = _; rhs = _ } -> kind
  | Or { kind; lhs = _; rhs = _ } -> kind
  | Overlapping_implication ((_ : (var, sequence) t list), (_ : (var, property) t)) ->
    Property
  | Property_implication ((_ : (var, property) t), (_ : (var, property) t)) -> Property
;;
