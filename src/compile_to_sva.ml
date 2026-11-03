open! Core
open Hardcaml
open Ast
module Sequence_range = Ast.Sequence_range

let bounded_exn ~from ~to_ =
  Sequence_range.bounded_exn { Property.Sva.Formula.Range.from; to_ }
;;

let rec compile_sequence_to_sva_sequence
  : type var.
    (var, sequence) t -> (var, Property.Sva.Formula.sequence) Property.Sva.Formula.t
  =
  fun sequence ->
  match sequence with
  | True -> True
  | Atomic_proposition signal -> Atom signal
  | Delay range -> Delay (None, range, True)
  | Concat sequence -> compile_sequence_list_to_sva_sequence sequence
  | Repeat (sequence, range) -> Repeat (compile_sequence_to_sva_sequence sequence, range)
  | And { kind = Sequence; lhs; rhs } ->
    And (compile_sequence_to_sva_sequence lhs, compile_sequence_to_sva_sequence rhs)
  | Or { kind = Sequence; lhs; rhs } ->
    Or (compile_sequence_to_sva_sequence lhs, compile_sequence_to_sva_sequence rhs)

and compile_sequence_to_sva_property
  : type var.
    (var, sequence) t -> (var, Property.Sva.Formula.property) Property.Sva.Formula.t
  =
  fun sequence -> Sequence_as_property (compile_sequence_to_sva_sequence sequence)

and compile_sequence_list_to_sva_property
  : type var.
    (var, sequence) t list -> (var, Property.Sva.Formula.property) Property.Sva.Formula.t
  =
  fun l -> Sequence_as_property (compile_sequence_list_to_sva_sequence l)

and compile_sequence_list_to_sva_sequence
  : type var.
    (var, sequence) t list -> (var, Property.Sva.Formula.sequence) Property.Sva.Formula.t
  = function
  | [] -> True
  | [ sequence ] -> compile_sequence_to_sva_sequence sequence
  | Delay range :: rest -> Delay (None, range, compile_sequence_list_to_sva_sequence rest)
  | sequence :: Delay range :: rest ->
    Delay
      ( Some (compile_sequence_to_sva_sequence sequence)
      , range
      , compile_sequence_list_to_sva_sequence rest )
  | sequence :: rest ->
    Delay
      ( Some (compile_sequence_to_sva_sequence sequence)
      , bounded_exn ~from:0 ~to_:0
      , compile_sequence_list_to_sva_sequence rest )
;;

let rec compile_without_validation
  : type var kind.
    (var, kind) t -> (var, Property.Sva.Formula.property) Property.Sva.Formula.t
  =
  fun property ->
  let module Formula = Property.Sva.Formula in
  match property with
  | True -> Sequence_as_property True
  | Atomic_proposition signal -> Sequence_as_property (Atom signal)
  | Delay range -> compile_sequence_to_sva_property (Delay range)
  | Concat sequence -> compile_sequence_list_to_sva_property sequence
  | Repeat (sequence, range) ->
    compile_sequence_to_sva_property (Repeat (sequence, range))
  | Sequence_as_property property -> compile_without_validation property
  | Not property -> Not (compile_without_validation property)
  | X property -> Nexttime (compile_without_validation property, None)
  | Until _ -> Formula.of_ltl (Compile_to_ltl.compile property)
  | Release _ -> Formula.of_ltl (Compile_to_ltl.compile property)
  | Eventually property -> S_eventually (compile_without_validation property, None)
  | Globally property -> Always (compile_without_validation property, None)
  | And { lhs; rhs; kind = _ } ->
    And (compile_without_validation lhs, compile_without_validation rhs)
  | Or { lhs; rhs; kind = _ } ->
    Or (compile_without_validation lhs, compile_without_validation rhs)
  | Overlapping_implication (sequence, consequent) ->
    Overlapping_implication
      ( compile_sequence_list_to_sva_sequence sequence
      , compile_without_validation consequent )
  | Property_implication (property, consequent) ->
    Property_implication
      (compile_without_validation property, compile_without_validation consequent)
;;

let compile t = Validate_and_simplify.run t |> compile_without_validation
