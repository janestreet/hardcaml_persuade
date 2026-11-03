open! Core
open Hardcaml
open Ast

val compile : ('var, 'kind) t -> 'var Property.LTL.Formula.t
