open! Core
open Hardcaml
module Sequence_range = Property.Sva.Formula.Sequence_range

type sequence =
  [ `Sequence
  | `Property
  ]

type property = [ `Property ]

module Kind_witness : sig
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

val kind : ('var, 'kind) t -> 'kind Kind_witness.t
