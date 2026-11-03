open! Core
open Hardcaml
module Sequence_range = Ast.Sequence_range

let bounded_exn ~from ~to_ =
  Sequence_range.bounded_exn { Property.Sva.Formula.Range.from; to_ }
;;

type t =
  | True
  | P of string
  | Delay of int
  | Delay_within of int * int
  | Delay_at_least of int
  | Delay_at_most of int
  | Concat of t list
  | Repeat of t * int
  | Repeat_within of t * int * int
  | Repeat_at_least of t * int
  | Repeat_at_most of t * int
  | Implies of t list * t
  | Not of t
  | And of t * t
  | Or of t * t
  | Property_implies of t * t
  | X of t
  | U of t * t
  | R of t * t
  | F of t
  | G of t
[@@deriving sexp]

type packed =
  | Seq of (string, Ast.sequence) Ast.t
  | Prop of (string, Ast.property) Ast.t

let as_property (type kind) (t : (string, kind) Ast.t) : (string, Ast.property) Ast.t =
  match Ast.kind t with
  | Sequence -> Sequence_as_property t
  | Property -> t
;;

let packed_property = function
  | Seq sequence -> as_property sequence
  | Prop property -> property
;;

let rec to_packed (formula : t) : packed =
  match formula with
  | True -> Seq True
  | P name -> Seq (Atomic_proposition name)
  | Delay n -> Seq (Delay (bounded_exn ~from:n ~to_:n))
  | Delay_within (from, to_) -> Seq (Delay (bounded_exn ~from ~to_))
  | Delay_at_least n -> Seq (Delay (Sequence_range.at_least_exn n))
  | Delay_at_most n -> Seq (Delay (Sequence_range.at_most_exn n))
  | Concat formulas -> Seq (concat_sequence formulas)
  | Repeat (formula, n) -> Seq (Repeat (to_sequence formula, bounded_exn ~from:n ~to_:n))
  | Repeat_within (formula, from, to_) ->
    Seq (Repeat (to_sequence formula, bounded_exn ~from ~to_))
  | Repeat_at_least (formula, n) ->
    Seq (Repeat (to_sequence formula, Sequence_range.at_least_exn n))
  | Repeat_at_most (formula, n) ->
    Seq (Repeat (to_sequence formula, Sequence_range.at_most_exn n))
  | Implies (antecedent, consequent) ->
    Prop
      (Overlapping_implication (List.map antecedent ~f:to_sequence, to_property consequent))
  | Not formula -> Prop (Not (to_property formula))
  | And (a, b) ->
    (match to_packed a, to_packed b with
     | Seq lhs, Seq rhs -> Seq (And { kind = Sequence; lhs; rhs })
     | a, b ->
       Prop (And { kind = Property; lhs = packed_property a; rhs = packed_property b }))
  | Or (a, b) ->
    (match to_packed a, to_packed b with
     | Seq lhs, Seq rhs -> Seq (Or { kind = Sequence; lhs; rhs })
     | a, b ->
       Prop (Or { kind = Property; lhs = packed_property a; rhs = packed_property b }))
  | Property_implies (a, b) -> Prop (Property_implication (to_property a, to_property b))
  | X formula -> Prop (X (to_property formula))
  | U (a, b) -> Prop (Until (to_property a, to_property b))
  | R (a, b) -> Prop (Release (to_property a, to_property b))
  | F formula -> Prop (Eventually (to_property formula))
  | G formula -> Prop (Globally (to_property formula))

and to_sequence (formula : t) : (string, Ast.sequence) Ast.t =
  match to_packed formula with
  | Seq sequence -> sequence
  | Prop (_ : (string, Ast.property) Ast.t) ->
    raise_s
      [%message
        "This construct requires a sequence, but was given a property" (formula : t)]

and to_property (formula : t) : (string, Ast.property) Ast.t =
  to_packed formula |> packed_property

and concat_sequence (formulas : t list) : (string, Ast.sequence) Ast.t =
  match List.map formulas ~f:to_sequence with
  | [] -> True
  | [ sequence ] -> sequence
  | sequence -> Concat sequence
;;
