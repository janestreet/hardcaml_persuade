open! Core
open Expect_test_helpers_core
open Hardcaml
open Hardcaml_persuade

let a = Signal.input "a" 1
let b = Signal.input "b" 1
let c = Signal.input "c" 1
let req = Signal.input "req" 1
let ack = Signal.input "ack" 1
let done_ = Signal.input "done" 1

let signal_name signal =
  match List.hd (Signal.names signal) with
  | Some name -> name
  | None -> "<unnamed>"
;;

let to_ltl_string property =
  property |> compile_to_ltl |> Property.LTL.Formula.to_string ~proposition:signal_name
;;

let to_sva_string property =
  property
  |> compile_to_sva
  |> Property.Sva.asserts
  |> Property.Sva.to_rope ~proposition:(fun signal ->
    signal_name signal |> Rope.of_string)
  |> Rope.to_string
;;

let print_both property =
  printf "LTL: %s\n" (to_ltl_string property);
  printf "SVA: %s\n" (to_sva_string property)
;;

let test_doesnt_support_ltl ~(here : [%call_pos]) p =
  print_endline (to_sva_string p);
  require_does_raise ~here (fun () -> to_ltl_string p)
;;

let%expect_test "atomic propositions and boolean connectives" =
  print_both t;
  [%expect
    {|
    LTL: TRUE
    SVA: assert property (1'b1)
    |}];
  print_both (concat []);
  [%expect
    {|
    LTL: TRUE
    SVA: assert property (1'b1)
    |}];
  print_both (concat [ p a ]);
  [%expect
    {|
    LTL: a
    SVA: assert property (a)
    |}];
  print_both (p a);
  [%expect
    {|
    LTL: a
    SVA: assert property (a)
    |}];
  print_both (f (p a) &&: f (p b));
  [%expect
    {|
    LTL: ((F a) & (F b))
    SVA: assert property ((s_eventually (a)) and (s_eventually (b)))
    |}];
  print_both (f (p a) ||: f (p b));
  [%expect
    {|
    LTL: ((F a) | (F b))
    SVA: assert property ((s_eventually (a)) or (s_eventually (b)))
    |}];
  print_both (not_ (p a));
  [%expect
    {|
    LTL: (!a)
    SVA: assert property (not (a))
    |}]
;;

let%expect_test "adjacent concat uses overlapping endpoints" =
  print_both (concat [ p a; p b ]);
  [%expect
    {|
    LTL: (a & b)
    SVA: assert property ((a) ##[0:0] (b))
    |}];
  print_both (concat [ p a; delay 1; p b ]);
  [%expect
    {|
    LTL: (a & (X b))
    SVA: assert property ((a) ##[1:1] (b))
    |}]
;;

let%expect_test "next shifts properties" =
  print_both (x (p a));
  [%expect
    {|
    LTL: (X a)
    SVA: assert property (nexttime (a))
    |}];
  print_both (x (f (p a)));
  [%expect
    {|
    LTL: (X (F a))
    SVA: assert property (nexttime (s_eventually (a)))
    |}]
;;

let%expect_test "delays" =
  print_both (concat [ p a; delay 1; p b ]);
  [%expect
    {|
    LTL: (a & (X b))
    SVA: assert property ((a) ##[1:1] (b))
    |}];
  print_both (concat [ p a; delay_within 1 3; p b ]);
  [%expect
    {|
    LTL: (a & (((X b) | (X (X b))) | (X (X (X b)))))
    SVA: assert property ((a) ##[1:3] (b))
    |}];
  print_both (concat [ p a; delay_at_most 2; p b ]);
  [%expect
    {|
    LTL: (a & ((b | (X b)) | (X (X b))))
    SVA: assert property ((a) ##[0:2] (b))
    |}];
  print_both (concat [ p a; delay_at_least 2; p b ]);
  [%expect
    {|
    LTL: (a & (X (X (F b))))
    SVA: assert property ((a) ##[2:$] (b))
    |}];
  print_both (concat [ delay 1; delay_at_least 2; p b ]);
  [%expect
    {|
    LTL: (X (X (X (F b))))
    SVA: assert property (##[3:$] (b))
    |}]
;;

let%expect_test "Invalid delay expressions" =
  require_does_raise (fun () ->
    print_both (concat [ delay 1; delay_at_least 2; p b; delay 1 ]));
  [%expect {| ("Invalid Hardcaml_persuade property" (message "dangling delay")) |}];
  require_does_raise (fun () ->
    print_both (concat [ delay_at_least 5; delay_at_most 6; p b ]));
  [%expect
    {|
    ("Invalid Hardcaml_persuade property" (
      message "ill-defined adjacent delay ranges"))
    |}]
;;

let%expect_test "repeat" =
  print_both (concat [ repeat (p a) 2; p b ]);
  [%expect
    {|
    LTL: ((a & (X a)) & (X b))
    SVA: assert property (((a) [*2:2]) ##[0:0] (b))
    |}];
  print_both (concat [ repeat (p a) 2; delay 1; p b ]);
  [%expect
    {|
    LTL: ((a & (X a)) & (X (X b)))
    SVA: assert property (((a) [*2:2]) ##[1:1] (b))
    |}];
  print_both (concat [ p a; delay 1; repeat_within (p b) 2 3; p c ]);
  [%expect
    {|
    LTL: (a & (X (((b & (X b)) & (X c)) | ((b & (X (b & (X b)))) & (X (X c))))))
    SVA: assert property ((a) ##[1:1] (((b) [*2:3]) ##[0:0] (c)))
    |}]
;;

let%expect_test "Unsupported LTL constructs with repeats" =
  test_doesnt_support_ltl (repeat_within (p a) 0 2);
  [%expect
    {|
    assert property ((a) [*0:2])
    ("Unsupported Hardcaml_persuade to LTL translation" (message zero-repeat))
    |}];
  test_doesnt_support_ltl (repeat_at_least (p a) 2);
  [%expect
    {|
    assert property ((a) [*2:$])
    ("Unsupported Hardcaml_persuade to LTL translation" (message repeat_at_least))
    |}];
  test_doesnt_support_ltl (repeat (p a) 0);
  [%expect
    {|
    assert property ((a) [*0:0])
    ("Unsupported Hardcaml_persuade to LTL translation" (message zero-repeat))
    |}];
  test_doesnt_support_ltl (repeat_at_most (p a) 1);
  [%expect
    {|
    assert property ((a) [*0:1])
    ("Unsupported Hardcaml_persuade to LTL translation" (message zero-repeat))
    |}];
  test_doesnt_support_ltl (concat [ repeat_at_most (p a) 1; p b ]);
  [%expect
    {|
    assert property (((a) [*0:1]) ##[0:0] (b))
    ("Unsupported Hardcaml_persuade to LTL translation"
     (message "zero-repeat with a continuation"))
    |}];
  test_doesnt_support_ltl ([ repeat_at_most (p a) 1 ] |-> p b);
  [%expect
    {|
    assert property (((a) [*0:1]) |-> (b))
    ("Unsupported Hardcaml_persuade to LTL translation"
     (message "zero-repeat in an implication antecedent"))
    |}];
  test_doesnt_support_ltl ([ p a; repeat_at_most (p b) 1; t ] |-> p c);
  [%expect
    {|
    assert property (((a) ##[0:0] (((b) [*0:1]) ##[0:0] (1'b1))) |-> (c))
    ("Unsupported Hardcaml_persuade to LTL translation"
     (message "zero-repeat in an implication antecedent"))
    |}];
  test_doesnt_support_ltl ([ repeat_at_least (p a) 2 ] |-> p b);
  [%expect
    {|
    assert property (((a) [*2:$]) |-> (b))
    ("Unsupported Hardcaml_persuade to LTL translation"
     (message "repeat_at_least in an implication antecedent"))
    |}]
;;

let%expect_test "temporal property operators" =
  print_both (f (p a));
  [%expect
    {|
    LTL: (F a)
    SVA: assert property (s_eventually (a))
    |}];
  print_both (g (p a));
  [%expect
    {|
    LTL: (G a)
    SVA: assert property (always (a))
    |}];
  print_both (u (p a) (p b));
  [%expect
    {|
    LTL: (a U b)
    SVA: assert property (((a) until (b)) and (s_eventually (b)))
    |}];
  print_both (r (p a) (p b));
  [%expect
    {|
    LTL: (a V b)
    SVA: assert property ((b) until ((b) and (a)))
    |}]
;;

let%expect_test "property implication" =
  print_both (p req ==>: p done_);
  [%expect
    {|
    LTL: ((!req) | done)
    SVA: assert property ((req) implies (done))
    |}];
  print_both (g (p req) ==>: f (p done_));
  [%expect
    {|
    LTL: ((!(G req)) | (F done))
    SVA: assert property ((always (req)) implies (s_eventually (done)))
    |}]
;;

let%expect_test "overlapping implication" =
  print_both ([ p req; delay 1; p ack ] |-> p done_);
  [%expect
    {|
    LTL: ((!req) | (X ((!ack) | done)))
    SVA: assert property (((req) ##[1:1] (ack)) |-> (done))
    |}];
  print_both ([ p req; delay_within 1 2; p ack ] |-> g (p done_));
  [%expect
    {|
    LTL: ((!req) | ((X ((!ack) | (G done))) & (X (X ((!ack) | (G done))))))
    SVA: assert property (((req) ##[1:2] (ack)) |-> (always (done)))
    |}];
  print_both ([ p req; delay_at_least 2; p ack ] |-> p done_);
  [%expect
    {|
    LTL: ((!req) | (X (X (G ((!ack) | done)))))
    SVA: assert property (((req) ##[2:$] (ack)) |-> (done))
    |}]
;;

let%expect_test "sequence and/or endpoints under overlapping implication" =
  let a_then_b_after_1 = concat [ p a; delay 1; p b ] in
  let c_then_done_after_3 = concat [ p c; delay 3; p done_ ] in
  (* [and] checks the consequent at the later branch endpoint. *)
  print_both ([ a_then_b_after_1 &&: c_then_done_after_3 ] |-> p ack);
  [%expect
    {|
    LTL: ((!((a & (X b)) & (c & (X (X (X done)))))) | (X (X (X ack))))
    SVA: assert property ((((a) ##[1:1] (b)) and ((c) ##[3:3] (done))) |-> (ack))
    |}];
  (* [or] lets each matching branch contribute its own endpoint. *)
  print_both ([ a_then_b_after_1 ||: c_then_done_after_3 ] |-> p ack);
  [%expect
    {|
    LTL: (((!(a & (X b))) | (X ack)) & ((!(c & (X (X (X done))))) | (X (X (X ack)))))
    SVA: assert property ((((a) ##[1:1] (b)) or ((c) ##[3:3] (done))) |-> (ack))
    |}];
  let a_then_b_after_1_to_3 = concat [ p a; delay_within 1 3; p b ] in
  let c_then_ack_after_2 = concat [ p c; delay 2; p ack ] in
  (* With ranges, [and]'s possible combined endpoints are the later matched endpoints. *)
  print_both ([ a_then_b_after_1_to_3 &&: c_then_ack_after_2 ] |-> p done_);
  [%expect
    {|
    LTL: ((((!((a & (X b)) & (c & (X (X ack))))) | (X (X done))) & ((!((a & (X (X b))) & (c & (X (X ack))))) | (X (X done)))) & ((!((a & (X (X (X b)))) & (c & (X (X ack))))) | (X (X (X done)))))
    SVA: assert property ((((a) ##[1:3] (b)) and ((c) ##[2:2] (ack))) |-> (done))
    |}];
  (* With ranges, [or] lets each range/branch match produce an endpoint. *)
  print_both ([ a_then_b_after_1_to_3 ||: c_then_ack_after_2 ] |-> p done_);
  [%expect
    {|
    LTL: (((((!(a & (X b))) | (X done)) & ((!(a & (X (X b)))) | (X (X done)))) & ((!(a & (X (X (X b))))) | (X (X (X done))))) & ((!(c & (X (X ack)))) | (X (X done))))
    SVA: assert property ((((a) ##[1:3] (b)) or ((c) ##[2:2] (ack))) |-> (done))
    |}]
;;

let%expect_test "Unbounded sequences with conjunctions doesn't compile into LTL" =
  let unbounded_and =
    concat [ p a; delay_at_least 1; p b ] &&: concat [ p c; delay 2; p ack ]
  in
  test_doesnt_support_ltl ([ unbounded_and ] |-> p done_);
  [%expect
    {|
    assert property ((((a) ##[1:$] (b)) and ((c) ##[2:2] (ack))) |-> (done))
    ("Unsupported Hardcaml_persuade to LTL translation"
     (message "unbounded sequence and"))
    |}];
  test_doesnt_support_ltl (concat [ unbounded_and; p done_ ]);
  [%expect
    {|
    assert property ((((a) ##[1:$] (b)) and ((c) ##[2:2] (ack))) ##[0:0] (done))
    ("Unsupported Hardcaml_persuade to LTL translation"
     (message "unbounded sequence and"))
    |}]
;;

let%expect_test "input validation" =
  require_does_raise (fun () -> ignore (p (Signal.input "wide" 2) : (_, sequence) t));
  [%expect
    {| ("Atomic propositions must be 1 bit" (signal (wire (names (wide)) (width 2)))) |}];
  require_does_raise (fun () -> ignore (delay (-1) : (_, sequence) t));
  [%expect {| ("SVA sequence range must be non-negative" (n -1)) |}];
  require_does_raise (fun () -> ignore (delay_within 3 1 : (_, sequence) t));
  [%expect
    {|
    ("SVA sequence range must be increasing" (
      range (
        (from 3)
        (to_  1))))
    |}];
  require_does_raise (fun () -> ignore (repeat_within (p a) 3 1 : (_, sequence) t));
  [%expect
    {|
    ("SVA sequence range must be increasing" (
      range (
        (from 3)
        (to_  1))))
    |}]
;;
