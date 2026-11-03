(** Parse [Hardcaml_persuade] properties from sexps, with atomic propositions given by
    name ([string] atoms).

    Formulas are untyped at parse time; {!to_property} kind-checks them, raising a
    descriptive error when a property appears where a sequence is required (e.g. as an
    element of [Concat], [Repeat] or an [Implies] antecedent). Range validation (e.g.
    negative or decreasing delays) is inherited from the combinators. *)

open! Core

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
  (** Overlapping sequence implication ([|->]): antecedent sequence, consequent. *)
  | Not of t
  | And of t * t
  | Or of t * t
  | Property_implies of t * t (** Property implication ([==>:]). *)
  | X of t
  | U of t * t
  | R of t * t
  | F of t
  | G of t
[@@deriving sexp]

(** Kind-check a parsed formula into a persuade property. Raises on kind errors. *)
val to_property : t -> (string, Ast.property) Ast.t
