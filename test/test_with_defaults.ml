open! Core
open Hardcaml
open Hardcaml_persuade

let clock_name = function
  | None -> None
  | Some ({ clock; edge = _; disable_iff = _ } : Signal.t Property.Clocked.t) ->
    Signal.names clock |> List.hd
;;

let print_ltl_clock_names scope names =
  let property_manager = Scope.property_manager scope |> Option.value_exn in
  let properties = Property_manager.get_ltl_properties property_manager in
  List.map names ~f:(fun name ->
    let property = Hashtbl.find_exn properties name in
    [%message (name : string) ~clock:(clock_name property.clocked : string option)])
  |> Expectable.print
;;

let print_ltl_property_names_for_groups scope groups =
  let property_manager = Scope.property_manager scope |> Option.value_exn in
  List.map groups ~f:(fun group ->
    let properties =
      Property_manager.filter
        property_manager
        (Property_manager.Trace_properties.create ~enable_ltl:true ~groups:[ group ] ())
      |> Property_manager.get_ltl_properties
    in
    let property_names = Hashtbl.keys properties |> List.sort ~compare:String.compare in
    let group = Property_manager.Group.name group in
    [%message (group : string) (property_names : string list)])
  |> Expectable.print
;;

let%expect_test "with_defaults restores previous defaults after nested calls" =
  let scope = Scope.create ~trace_properties:Property_manager.Trace_properties.all () in
  let signal = Signal.input "signal" 1 in
  let clock_a = Signal.input "clock_a" 1 in
  let clock_b = Signal.input "clock_b" 1 in
  let property = g (p signal) in
  let clocked_a = Property.Clocked.create Rising clock_a in
  let clocked_b = Property.Clocked.create Rising clock_b in
  with_defaults ~clocked:clocked_a (fun () ->
    let%hw_persuade outer_before = Assert, property in
    with_defaults ~clocked:clocked_b (fun () ->
      let%hw_persuade inner = Assert, property in
      ());
    let%hw_persuade outer_after_inner = Assert, property in
    let (_ : Error.t) =
      match
        Or_error.try_with (fun () ->
          with_defaults ~clocked:clocked_b (fun () ->
            raise_s [%message "nested with_defaults failed"]))
      with
      | Ok () -> raise_s [%message "expected nested with_defaults to raise"]
      | Error error -> error
    in
    let%hw_persuade outer_after_exn = Assert, property in
    ());
  let%hw_persuade outside = Assert, property in
  print_ltl_clock_names
    scope
    [ "outer_before"; "inner"; "outer_after_inner"; "outer_after_exn"; "outside" ];
  [%expect
    {|
    ┌───────────────────┬─────────┐
    │ name              │ clock   │
    ├───────────────────┼─────────┤
    │ outer_before      │ clock_a │
    │ inner             │ clock_b │
    │ outer_after_inner │ clock_a │
    │ outer_after_exn   │ clock_a │
    │ outside           │         │
    └───────────────────┴─────────┘
    |}]
;;

let%expect_test "with_defaults applies and restores groups" =
  let scope = Scope.create ~trace_properties:Property_manager.Trace_properties.all () in
  let signal = Signal.input "signal" 1 in
  let property = g (p signal) in
  let group_a = Property_manager.Group.create "group_a" in
  let group_b = Property_manager.Group.create "group_b" in
  let%hw_persuade default_before = Assert, property in
  with_defaults ~group:group_a (fun () ->
    let%hw_persuade outer_before = Assert, property in
    with_defaults ~group:group_b (fun () ->
      let%hw_persuade inner = Assert, property in
      ());
    let%hw_persuade outer_after_inner = Assert, property in
    let (_ : Error.t) =
      match
        Or_error.try_with (fun () ->
          with_defaults ~group:group_b (fun () ->
            raise_s [%message "nested with_defaults failed"]))
      with
      | Ok () -> raise_s [%message "expected nested with_defaults to raise"]
      | Error error -> error
    in
    let%hw_persuade outer_after_exn = Assert, property in
    ());
  let%hw_persuade default_after = Assert, property in
  print_ltl_property_names_for_groups
    scope
    [ Property_manager.Group.default; group_a; group_b ];
  [%expect
    {|
    ┌─────────┬───────────────────┐
    │ group   │ property_names    │
    ├─────────┼───────────────────┤
    │ default │ default_after     │
    │         │ default_before    │
    │ group_a │ outer_after_exn   │
    │         │ outer_after_inner │
    │         │ outer_before      │
    │ group_b │ inner             │
    └─────────┴───────────────────┘
    |}]
;;
