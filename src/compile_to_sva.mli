open! Core
open Hardcaml
open Ast

val compile
  :  ('var, 'kind) t
  -> ('var, Property.Sva.Formula.property) Property.Sva.Formula.t
