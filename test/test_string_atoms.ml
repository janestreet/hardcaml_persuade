(* Persuade properties over [string] atoms must compile to the same LTL and SVA as the
   equivalent properties over signals with those names. *)

open! Core
open Expect_test_helpers_core
open Hardcaml
open Hardcaml_persuade

let names = [ "a"; "b"; "c" ]

let signals =
  List.map names ~f:(fun name -> name, Signal.input name 1) |> String.Map.of_alist_exn
;;

let signal_name signal =
  match List.hd (Signal.names signal) with
  | Some name -> name
  | None -> "<unnamed>"
;;

(* The same property built over string atoms and over signal atoms. *)
let make_property ap = [ ap "a"; delay_within 1 3; ap "b" ] |-> g (ap "c")
let of_strings = make_property atom
let of_signals = make_property (fun name -> p (Map.find_exn signals name))

let%expect_test "string and signal atoms compile to the same LTL" =
  let to_ltl_string property ~proposition =
    compile_to_ltl property |> Property.LTL.Formula.to_string ~proposition
  in
  let of_strings = to_ltl_string of_strings ~proposition:Fn.id in
  let of_signals = to_ltl_string of_signals ~proposition:signal_name in
  print_endline of_strings;
  [%expect
    {| ((!a) | (((X ((!b) | (G c))) & (X (X ((!b) | (G c))))) & (X (X (X ((!b) | (G c))))))) |}];
  require_equal (module String) of_strings of_signals;
  [%expect {| |}]
;;

let%expect_test "string and signal atoms compile to the same SVA" =
  let to_sva_string property ~proposition =
    compile_to_sva property |> Property.Sva.Formula.to_rope ~proposition |> Rope.to_string
  in
  let of_strings = to_sva_string of_strings ~proposition:Rope.of_string in
  let of_signals =
    to_sva_string of_signals ~proposition:(fun signal ->
      signal_name signal |> Rope.of_string)
  in
  print_endline of_strings;
  [%expect {| ((a) ##[1:3] (b)) |-> (always (c)) |}];
  require_equal (module String) of_strings of_signals;
  [%expect {| |}]
;;
