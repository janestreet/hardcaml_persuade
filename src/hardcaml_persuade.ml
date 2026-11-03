open! Core
open Hardcaml
open Ast
module Sequence_range = Ast.Sequence_range

type sequence = Ast.sequence
type property = Ast.property
type ('var, 'kind) t = ('var, 'kind) Ast.t

type directive = Property.Directive.t =
  | Assert
  | Assume
  | Cover

let bounded_exn ~from ~to_ =
  Sequence_range.bounded_exn { Property.Sva.Formula.Range.from; to_ }
;;

let t = True
let atom v = Atomic_proposition v

let p signal =
  if Signal.width signal <> 1
  then raise_s [%message "Atomic propositions must be 1 bit" (signal : Signal.t)];
  Atomic_proposition signal
;;

let delay n = Delay (bounded_exn ~from:n ~to_:n)
let delay_within from to_ = Delay (bounded_exn ~from ~to_)
let delay_at_least n = Delay (Sequence_range.at_least_exn n)
let delay_at_most n = Delay (Sequence_range.at_most_exn n)

let concat = function
  | [] -> True
  | [ t ] -> t
  | sequence -> Concat sequence
;;

let as_property (type var kind) (t : (var, kind) t) =
  match Ast.kind t with
  | Sequence -> Sequence_as_property t
  | Property -> t
;;

let ( |-> ) sequence consequent =
  Overlapping_implication (sequence, as_property consequent)
;;

let repeat_within sequence from to_ = Repeat (sequence, bounded_exn ~from ~to_)
let repeat_at_least sequence n = Repeat (sequence, Sequence_range.at_least_exn n)
let repeat_at_most sequence n = Repeat (sequence, Sequence_range.at_most_exn n)
let repeat sequence n = repeat_within sequence n n
let negate t = Not (as_property t)
let not_ = negate
let x t = X (as_property t)
let u a b = Until (as_property a, as_property b)
let r a b = Release (as_property a, as_property b)
let f t = Eventually (as_property t)
let g t = Globally (as_property t)
let ( &&: ) lhs rhs = And { kind = Ast.kind lhs; lhs; rhs }
let ( ||: ) lhs rhs = Or { kind = Ast.kind lhs; lhs; rhs }
let ( ==>: ) lhs rhs = Property_implication (as_property lhs, as_property rhs)
let compile_to_ltl = Compile_to_ltl.compile
let compile_to_sva = Compile_to_sva.compile
let default_clocked = ref None
let default_group = ref None

let with_defaults ?group ?clocked f =
  let previous_clocked = !default_clocked in
  let previous_group = !default_group in
  Option.iter clocked ~f:(fun clocked -> default_clocked := Some clocked);
  Option.iter group ~f:(fun group -> default_group := Some group);
  Exn.protect ~f ~finally:(fun () ->
    default_clocked := previous_clocked;
    default_group := previous_group)
;;

let with_contract_group ?clocked f =
  with_defaults ?clocked ~group:Property_manager.Group.contract f
;;

module With_contract (O : Interface.S) = struct
  let with_contract ?clocked f o =
    let o = O.map ~f:Signal.wireof o in
    with_contract_group ?clocked (fun () -> f o);
    o
  ;;
end

let add_to_scope ?group ?clocked (scope : Scope.t) name directive (t : _ t) =
  let clocked = Option.first_some clocked !default_clocked in
  let group = Option.first_some group !default_group in
  Scope.add_ltl_property
    ?group
    scope
    name
    (Property.LTL.create ?clocked directive (compile_to_ltl t));
  Scope.add_sva_property
    ?group
    scope
    name
    (Property.Sva.create ?clocked directive (compile_to_sva t))
;;

module Parse = Parse

module Handshake = struct
  let add_properties
    ?group
    ?enable
    ?(valid_name = "valid")
    scope
    directive
    ~clocked
    ~register
    ~valid
    ~ready
    ~payloads
    =
    with_defaults ?group ~clocked (fun () ->
      let open Signal in
      let stalled = valid &: ~:ready in
      let stalled =
        match enable with
        | None -> stalled
        | Some enable -> enable &: stalled
      in
      let%hw was_stalled = register stalled in
      add_to_scope
        scope
        [%string "%{valid_name}_stable_while_stalled"]
        directive
        (g ([ p was_stalled ] |-> p valid));
      List.iter payloads ~f:(fun (name, signal) ->
        let scope = Scope.sub_scope scope name in
        let%hw payload_unchanged =
          let%hw previous_signal = register signal in
          signal ==: previous_signal
        in
        add_to_scope
          scope
          "stable_while_stalled"
          directive
          (g ([ p was_stalled ] |-> p payload_unchanged))))
  ;;
end
