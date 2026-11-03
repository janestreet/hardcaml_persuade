open! Core
open Expect_test_helpers_core
open Hardcaml
open Hardcaml_persuade

let to_ltl_string property =
  compile_to_ltl property |> Property.LTL.Formula.to_string ~proposition:Fn.id
;;

let parse string = Sexp.of_string string |> Parse.t_of_sexp |> Parse.to_property

let%expect_test "parsed and combinator-built properties compile identically" =
  let parsed = parse "(Implies ((P a) (Delay_within 1 3) (P b)) (G (P c)))" in
  let built = [ atom "a"; delay_within 1 3; atom "b" ] |-> g (atom "c") in
  let parsed = to_ltl_string parsed in
  let built = to_ltl_string built in
  print_endline parsed;
  [%expect
    {| ((!a) | (((X ((!b) | (G c))) & (X (X ((!b) | (G c))))) & (X (X (X ((!b) | (G c))))))) |}];
  require_equal (module String) parsed built;
  [%expect {| |}]
;;

let%expect_test "sequences coerce to properties where needed" =
  let parsed = parse "(Concat ((P a) (Delay 1) (P b)))" in
  print_endline (to_ltl_string parsed);
  [%expect {| (a & (X b)) |}]
;;

let%expect_test "and/or of sequences stays a sequence" =
  (* If [And] were treated as a property connective, both operands would be checked from
     the same start cycle; as a sequence [b] must hold at the endpoint of the delay. *)
  let parsed = parse "(Implies ((And (P a) (Concat ((Delay 1) (P b))))) (P c))" in
  print_endline (to_ltl_string parsed);
  [%expect {| ((!(a & (X b))) | (X c)) |}]
;;

let%expect_test "kind errors are descriptive" =
  require_does_raise (fun () -> parse "(Concat ((G (P a))))");
  [%expect
    {|
    ("This construct requires a sequence, but was given a property"
     (formula (G (P a))))
    |}]
;;

let%expect_test "parse errors are descriptive" =
  (* Unknown constructor. *)
  require_does_raise (fun () -> parse "(Frobnicate (P a))");
  [%expect
    {|
    (Of_sexp_error
     "parse.ml.t_of_sexp: unexpected variant constructor; expected one of True P Delay Delay_within Delay_at_least Delay_at_most Concat Repeat Repeat_within Repeat_at_least ..."
     (invalid_sexp (Frobnicate (P a))))
    |}];
  (* Wrong arity. *)
  require_does_raise (fun () -> parse "(Delay_within 1)");
  [%expect
    {|
    (Of_sexp_error
     "parse.ml.t_of_sexp: sum tag \"Delay_within\" has incorrect number of arguments"
     (invalid_sexp (Delay_within 1)))
    |}];
  require_does_raise (fun () -> parse "(P a b)");
  [%expect
    {|
    (Of_sexp_error
     "parse.ml.t_of_sexp: sum tag \"P\" has incorrect number of arguments"
     (invalid_sexp (P a b)))
    |}];
  (* Payload of the wrong type. *)
  require_does_raise (fun () -> parse "(Delay not_an_int)");
  [%expect
    {|
    (Of_sexp_error
     "int_of_sexp: (Failure int_of_string)"
     (invalid_sexp not_an_int))
    |}];
  (* Constructor that requires a payload, given none. *)
  require_does_raise (fun () -> parse "Delay");
  [%expect
    {|
    (Of_sexp_error
     "parse.ml.t_of_sexp: this constructor requires arguments"
     (invalid_sexp Delay))
    |}]
;;
