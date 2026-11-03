open! Core
open Hardcaml
open Ast
module Sequence_range = Ast.Sequence_range

let invalid message =
  raise_s [%message "Invalid Hardcaml_persuade property" (message : string)]
;;

let bounded_exn ~from ~to_ =
  Sequence_range.bounded_exn { Property.Sva.Formula.Range.from; to_ }
;;

let singleton_delay = function
  | Sequence_range.Bounded { from; to_ } when from = to_ -> Some from
  | Bounded _ | At_least _ | At_most _ -> None
;;

let offset_range range ~by =
  match range with
  | Sequence_range.Bounded { from; to_ } -> bounded_exn ~from:(from + by) ~to_:(to_ + by)
  | At_least n -> Sequence_range.at_least_exn (n + by)
  | At_most n -> bounded_exn ~from:by ~to_:(n + by)
;;

let add_delay_ranges a b =
  match singleton_delay a, singleton_delay b with
  | Some a, _ -> offset_range b ~by:a
  | _, Some b -> offset_range a ~by:b
  | None, None ->
    (match a, b with
     | Bounded { from = a_from; to_ = a_to }, Bounded { from = b_from; to_ = b_to } ->
       bounded_exn ~from:(a_from + b_from) ~to_:(a_to + b_to)
     | At_most a, At_most b -> Sequence_range.at_most_exn (a + b)
     | At_least a, At_least b -> Sequence_range.at_least_exn (a + b)
     | Bounded _, At_most _
     | At_most _, Bounded _
     | Bounded _, At_least _
     | At_least _, Bounded _
     | At_most _, At_least _
     | At_least _, At_most _ -> invalid "ill-defined adjacent delay ranges")
;;

let reject_dangling_delay = function
  | Delay _ -> invalid "dangling delay"
  | sequence -> sequence
;;

let rec simplify : type var kind. (var, kind) t -> (var, kind) t = function
  | True -> True
  | Atomic_proposition signal -> Atomic_proposition signal
  | Delay range -> Delay range
  | Concat sequence -> simplify_sequence_list sequence |> concat_simplified
  | Repeat (sequence, range) -> Repeat (simplify_sequence sequence, range)
  | Sequence_as_property sequence -> Sequence_as_property (simplify_sequence sequence)
  | Not property -> Not (simplify property)
  | X property -> X (simplify property)
  | Until (a, b) -> Until (simplify a, simplify b)
  | Release (a, b) -> Release (simplify a, simplify b)
  | Eventually property -> Eventually (simplify property)
  | Globally property -> Globally (simplify property)
  | And { kind; lhs; rhs } ->
    (match kind with
     | Sequence ->
       And { kind = Sequence; lhs = simplify_sequence lhs; rhs = simplify_sequence rhs }
     | Property -> And { kind = Property; lhs = simplify lhs; rhs = simplify rhs })
  | Or { kind; lhs; rhs } ->
    (match kind with
     | Sequence ->
       Or { kind = Sequence; lhs = simplify_sequence lhs; rhs = simplify_sequence rhs }
     | Property -> Or { kind = Property; lhs = simplify lhs; rhs = simplify rhs })
  | Overlapping_implication (sequence, consequent) ->
    Overlapping_implication (simplify_sequence_list sequence, simplify consequent)
  | Property_implication (antecedent, consequent) ->
    Property_implication (simplify antecedent, simplify consequent)

and simplify_sequence : type var. (var, sequence) t -> (var, sequence) t =
  fun sequence -> simplify sequence |> reject_dangling_delay

and concat_simplified : type var. (var, sequence) t list -> (var, sequence) t =
  fun sequence ->
  match sequence with
  | [] -> True
  | [ sequence ] -> sequence
  | sequence -> Concat sequence

and simplify_sequence_in_concat : type var. (var, sequence) t -> (var, sequence) t list =
  fun sequence ->
  match simplify sequence with
  | Concat sequence -> sequence
  | sequence -> [ sequence ]

and simplify_sequence_list : type var. (var, sequence) t list -> (var, sequence) t list =
  fun sequence ->
  sequence
  |> List.concat_map ~f:simplify_sequence_in_concat
  |> collapse_adjacent_delays
  |> reject_trailing_delay

and collapse_adjacent_delays : type var. (var, sequence) t list -> (var, sequence) t list
  = function
  | Delay a :: Delay b :: rest ->
    collapse_adjacent_delays (Delay (add_delay_ranges a b) :: rest)
  | first :: rest -> first :: collapse_adjacent_delays rest
  | [] -> []

and reject_trailing_delay : type var. (var, sequence) t list -> (var, sequence) t list =
  fun sequence ->
  match List.last sequence with
  | Some (Delay _) -> invalid "dangling delay"
  | Some _ | None -> sequence
;;

let run t = simplify t
