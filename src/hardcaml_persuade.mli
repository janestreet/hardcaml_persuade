(** {1 Hardcaml_persuade}

    Hardcaml_persuade is a library to specify properties in Hardcaml designs.
    Hardcaml_persuade has sugar syntax on top of Linear Temporal Logic (LTL) and SVA
    sequences to represent common operations in more readable form (eg: #[1, 3] instead of
    stitching together the X operator in LTL) *)

open Hardcaml

type ('var, 'kind) t = ('var, 'kind) Ast.t

type sequence =
  [ `Sequence
  | `Property
  ]

type property = [ `Property ]

(** Directive controlling how the formal backend should interpret a property. *)
type directive = Property.Directive.t =
  | Assert
  | Assume
  | Cover

(** {2 Basic Operators on Sequences} *)

(** tautology -- matches every sequence *)
val t : (_, sequence) t

(** Atomic proposition over a hardware signal. Raises if the signal is not 1 bit wide. *)
val p : Signal.t -> (Signal.t, sequence) t

(** Atomic proposition over an arbitrary atom type . No width checking is (or can be)
    performed; when the property is ultimately evaluated the atom must correspond to a 1
    bit value. *)
val atom : 'var -> ('var, sequence) t

(** Overlapping sequence implication. The consequent is checked at each endpoint where the
    antecedent sequence matches. This operator returns a property, not a sequence. *)
val ( |-> ) : ('var, sequence) t list -> ('var, [> property ]) t -> ('var, property) t

(** Build a sequence from a longer sequence of items. *)
val concat : ('var, sequence) t list -> ('var, sequence) t

(** {2 Delay operators}

    Delay operators can be used as part of sequence concatenation to the amount of time to
    wait in cycles. *)

val delay : int -> (_, sequence) t
val delay_within : int -> int -> (_, sequence) t
val delay_at_least : int -> (_, sequence) t
val delay_at_most : int -> (_, sequence) t

(** {2 Repeat operators}

    Repeat operators operator can be used to express a sequence repeating in some number
    of times within a given range. *)

(** [repeat_within s from to_] matches between [from] and [to_] consecutive repetitions of
    [s]. Repetition does not add an extra cycle after the final match: when a repeated
    sequence is followed by another sequence in [concat], the next sequence is checked at
    the endpoint of the final repetition. For example, [concat [ repeat (p a) 2; p b ]] is
    equivalent to [a ##1 a ##0 b].

    If [from = 0], [compile_to_ltl] raises because SVA empty-sequence semantics do not
    behave like an ordinary endpoint-0 match. *)
val repeat_within : ('var, sequence) t -> int -> int -> ('var, sequence) t

(** [repeat_at_least s n] matches at least [n] consecutive repetitions of [s]. This
    compiles to SVA, but [compile_to_ltl] raises for this construct because preserving all
    possible repetition endpoints requires a recursive/fixpoint encoding that
    Hardcaml_persuade does not currently implement. *)
val repeat_at_least : ('var, sequence) t -> int -> ('var, sequence) t

(** [repeat_at_most s n] matches at most [n] consecutive repetitions of [s]. Because this
    includes a zero-repetition branch, [compile_to_ltl] raises for this construct. *)
val repeat_at_most : ('var, sequence) t -> int -> ('var, sequence) t

(** [repeat s n] matches exactly [n] consecutive repetitions of [s]. If [n = 0],
    [compile_to_ltl] raises because this is a zero-repeat branch. *)
val repeat : ('var, sequence) t -> int -> ('var, sequence) t

(** {2 Operators for LTL Formulae} *)

(** The [next] operator in LTL. [x p] is the LTL next operator: [p] must hold on the next
    cycle. *)
val x : ('var, [> property ]) t -> ('var, property) t

(** In [u a b] [a] holds at least until [b] holds *)
val u : ('var, [> property ]) t -> ('var, [> property ]) t -> ('var, property) t

(** In [r a b], [b] has to up to and including the point [a] becomes true. *)
val r : ('var, [> property ]) t -> ('var, [> property ]) t -> ('var, property) t

(** In [f a], [a] must eventually hold. *)
val f : ('var, [> property ]) t -> ('var, property) t

(** In [g a], [a] must hold forever. *)
val g : ('var, [> property ]) t -> ('var, property) t

(** {2 Operators on Properties and Sequences} *)

val negate : ('var, [> property ]) t -> ('var, property) t
val not_ : ('var, [> property ]) t -> ('var, property) t

(** Explicitly coerce a sequence (or property) to a property. Most property operators
    accept sequences directly; this is useful when a [('var, property) t] is required,
    e.g. to store mixed sequences and properties in one container. *)
val as_property : ('var, [> property ]) t -> ('var, property) t

val ( ==>: ) : ('var, [> property ]) t -> ('var, [> property ]) t -> ('var, property) t

(** [a &&: b] is conjunction. For properties, both properties must hold. For sequences,
    both sequences must match from the same start time; the resulting sequence ends at the
    later matched endpoint, matching SVA's sequence [and] operator.

    [compile_to_ltl] supports finite, non-empty sequence conjunctions, but raises for
    unbounded sequence conjunctions such as those involving [delay_at_least] or
    [repeat_at_least], and for zero-repeat branches. *)
val ( &&: ) : ('var, 'kind) t -> ('var, 'kind) t -> ('var, 'kind) t

(** [a ||: b] is disjunction. For properties, either property must hold. For sequences,
    either sequence may match, and each matching branch contributes its own endpoint,
    matching SVA's sequence [or] operator. *)
val ( ||: ) : ('var, 'kind) t -> ('var, 'kind) t -> ('var, 'kind) t

(** {2 Compilation functions}

    Both compilation functions will run through a validation function that will reject
    ill-defined properties, such as:

    - [ delay 1; p a; delay 2 ] - the dangling delay has unclear semantics.
    - [ delay_at_least 2; delay_at_most 3 ] - the at_most is ill-defined. *)

val compile_to_sva
  :  ('var, [> property ]) t
  -> ('var, [ `Property ]) Property.Sva.Formula.t

(** Compile to Hardcaml's LTL representation. This raises for SVA-sequence constructs
    whose endpoint semantics are not yet encoded in Hardcaml_persuade's LTL lowering,
    currently [repeat_at_least], zero-repeat branches, and unbounded sequence conjunction. *)
val compile_to_ltl : ('var, [> property ]) t -> 'var Property.LTL.Formula.t

(** {2 Interacting with Scope.t} *)

(** Set default arguments for properties added via [add_to_scope]. If [group] or [clocked]
    is provided, subsequent calls to [add_to_scope] use that value when their
    corresponding argument is not provided. Nested calls restore the previous defaults
    when they return or raise. *)
val with_defaults
  :  ?group:Property_manager.Group.t
  -> ?clocked:Signal.t Property.Clocked.t
  -> (unit -> 'a)
  -> 'a

(** [With_contract] does three things under the hood:

    - Calls [with_defaults] with the contract properties group
    - Wraps the provided [Signal.t O.t] with wires before passing it to the closure to
      apply the properties
    - Returns the wrapped version of the [Signal.t O.t]

    The wrapping helps the contract harness recognize that we want the particular wire to
    be abstract. You can still write properties against internal signals (or the design
    inputs) by passing them as free variables to the closure applying the properties. Note
    that the contract harness won't treat those as opaque signals. *)
module With_contract (O : Interface.S) : sig
  val with_contract
    :  ?clocked:Signal.t Property.Clocked.t
    -> (Signal.t O.t -> unit)
    -> Signal.t O.t
    -> Signal.t O.t
end

(** Add a persuade property into scope. [group] specifies the property group to associate
    the property with. If [group] is not supplied, the current default group is used. *)
val add_to_scope
  :  ?group:Property_manager.Group.t
  -> ?clocked:Signal.t Property.Clocked.t
  -> Scope.t
  -> string
  -> Property.Directive.t
  -> (Signal.t, [> property ]) t
  -> unit

module Parse = Parse

(** {2 Common property patterns} *)

module Handshake : sig
  (** Add properties that a [valid]/[ready] interface follows a handshake protocol: when a
      stall is observed ([valid && ~ready], gated by [enable] when provided), [valid] must
      stay asserted and every named payload must be unchanged on the following cycle. This
      is the generic analogue of the AXI4-Stream source handshake protocol.

      One property is added per payload, named [<payload-name>$stable_while_stalled], plus
      a [<valid_name>_stable_while_stalled] property for [valid] itself. *)
  val add_properties
    :  ?group:Property_manager.Group.t
    -> ?enable:Signal.t
         (** Only require the handshake to hold when [enable] is high. Default is always
             enabled. *)
    -> ?valid_name:string
         (** Name used for the [valid] stability property. Defaults to ["valid"]. *)
    -> Scope.t
    -> Property.Directive.t
    -> clocked:Signal.t Property.Clocked.t
         (** Clock and disable condition for the generated properties. *)
    -> register:(Signal.t -> Signal.t)
         (** Registers a signal for one cycle using the same clock/reset semantics as
             [clocked]. *)
    -> valid:Signal.t
    -> ready:Signal.t
    -> payloads:(string * Signal.t) list
    -> unit
end
