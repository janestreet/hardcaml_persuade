open! Core
open Hardcaml
open Ast
module Sequence_range = Ast.Sequence_range
module Ltl = Property.LTL.Formula

let bounded_exn ~from ~to_ =
  Sequence_range.bounded_exn { Property.Sva.Formula.Range.from; to_ }
;;

let delay n = Delay (bounded_exn ~from:n ~to_:n)
let ltl_x n t = Ltl.x ~n t

let ltl_or terms =
  match terms with
  | [] -> Ltl.gnd
  | hd :: tl -> List.fold tl ~init:hd ~f:Ltl.( |: )
;;

let ltl_and terms =
  match terms with
  | [] -> Ltl.vdd
  | hd :: tl -> List.fold tl ~init:hd ~f:Ltl.( &: )
;;

let rec repeated_sequence sequence count =
  match count with
  | 0 -> []
  | 1 -> [ sequence ]
  | count -> sequence :: delay 1 :: repeated_sequence sequence (count - 1)
;;

type 'var sequence_case =
  { endpoint : int
  ; condition : 'var Ltl.t
  }

let ltl_and2 a b =
  match a, b with
  | Ltl.True, b -> b
  | a, Ltl.True -> a
  | a, b -> Ltl.(a &: b)
;;

let ltl_implies a b =
  match a with
  | Ltl.True -> b
  | _ -> Ltl.(a ==>: b)
;;

let finite_offsets (range : Sequence_range.t) =
  match range with
  | Bounded { from; to_ } -> Some (List.init (to_ - from + 1) ~f:(fun i -> from + i))
  | At_most to_ -> Some (List.init (to_ + 1) ~f:Fn.id)
  | At_least _ -> None
;;

let range_includes_zero (range : Sequence_range.t) =
  match range with
  | Bounded { from; to_ = _ } -> from = 0
  | At_most (_ : int) -> true
  | At_least n -> n = 0
;;

let rec sequence_cases : type var. (var, sequence) t -> var sequence_case list option =
  fun sequence ->
  match sequence with
  | True -> Some [ { endpoint = 0; condition = Ltl.vdd } ]
  | Atomic_proposition atom -> Some [ { endpoint = 0; condition = Ltl.atom atom } ]
  | Delay range ->
    Option.map (finite_offsets range) ~f:(fun offsets ->
      List.map offsets ~f:(fun endpoint -> { endpoint; condition = Ltl.vdd }))
  | Concat sequence -> sequence_list_cases sequence
  | Repeat (sequence, range) ->
    (match range_includes_zero range with
     | true -> None
     | false ->
       Option.bind (finite_offsets range) ~f:(fun counts ->
         counts
         |> List.map ~f:(fun count ->
           repeated_sequence sequence count |> sequence_list_cases)
         |> Option.all
         |> Option.map ~f:List.concat))
  | And { kind = Sequence; lhs; rhs } ->
    Option.map2 (sequence_cases lhs) (sequence_cases rhs) ~f:(fun a_cases b_cases ->
      List.concat_map a_cases ~f:(fun a_case ->
        List.map b_cases ~f:(fun b_case ->
          { endpoint = Int.max a_case.endpoint b_case.endpoint
          ; condition = ltl_and2 a_case.condition b_case.condition
          })))
  | Or { kind = Sequence; lhs; rhs } ->
    Option.map2 (sequence_cases lhs) (sequence_cases rhs) ~f:(fun a_cases b_cases ->
      a_cases @ b_cases)

and sequence_list_cases
  : type var. (var, sequence) t list -> var sequence_case list option
  =
  fun sequence ->
  match sequence with
  | [] -> Some [ { endpoint = 0; condition = Ltl.vdd } ]
  | first :: rest ->
    Option.map2 (sequence_cases first) (sequence_list_cases rest) ~f:(fun first rest ->
      List.concat_map first ~f:(fun first_case ->
        List.map rest ~f:(fun rest_case ->
          { endpoint = first_case.endpoint + rest_case.endpoint
          ; condition =
              ltl_and2
                first_case.condition
                (ltl_x first_case.endpoint rest_case.condition)
          })))
;;

let compile_cases_to_ltl cases ~then_ =
  cases
  |> List.map ~f:(fun { endpoint; condition } ->
    ltl_and2 condition (ltl_x endpoint then_))
  |> ltl_or
;;

let compile_cases_implication_to_ltl cases ~then_ =
  cases
  |> List.map ~f:(fun { endpoint; condition } ->
    ltl_implies condition (ltl_x endpoint then_))
  |> ltl_and
;;

let ltl_for_each_offset (range : Sequence_range.t) ~f =
  match range with
  | Bounded { from; to_ } -> List.init (to_ - from + 1) ~f:(fun i -> f (from + i))
  | At_most to_ -> List.init (to_ + 1) ~f
  | At_least _ ->
    raise_s [%message "Expected a bounded sequence range" (range : Sequence_range.t)]
;;

let ltl_after_range (range : Sequence_range.t) t =
  match range with
  | Bounded _ | At_most _ -> ltl_for_each_offset range ~f:(fun n -> ltl_x n t) |> ltl_or
  | At_least n -> ltl_x n (Ltl.f t)
;;

let rec has_zero_repeat_with_continuation = function
  | [] | [ _ ] -> false
  | Repeat (_, range) :: _ :: _ when range_includes_zero range -> true
  | (_ : (_, sequence) t) :: rest -> has_zero_repeat_with_continuation rest
;;

let unsupported_ltl message =
  raise_s [%message "Unsupported Hardcaml_persuade to LTL translation" (message : string)]
;;

let rec compile_sequence_to_ltl
  : type var. (var, sequence) t -> then_:var Ltl.t -> var Ltl.t
  =
  fun sequence ~then_ ->
  match sequence_cases sequence with
  | Some cases -> compile_cases_to_ltl cases ~then_
  | None ->
    (match sequence with
     | True -> then_
     | Atomic_proposition signal ->
       (match then_ with
        | Ltl.True -> Ltl.atom signal
        | _ -> Ltl.(atom signal &: then_))
     | Delay range -> ltl_after_range range then_
     | Concat sequence -> compile_sequence_list_to_ltl sequence ~then_
     | Repeat (sequence, range) -> compile_repeat_to_ltl sequence range ~then_
     | And { kind = Sequence; lhs = _; rhs = _ } ->
       unsupported_ltl "unbounded sequence and"
     | Or { kind = Sequence; lhs; rhs } ->
       Ltl.(compile_sequence_to_ltl lhs ~then_ |: compile_sequence_to_ltl rhs ~then_))

and compile_sequence_list_to_ltl
  : type var. (var, sequence) t list -> then_:var Ltl.t -> var Ltl.t
  =
  fun sequence ~then_ ->
  match has_zero_repeat_with_continuation sequence with
  | true -> unsupported_ltl "zero-repeat with a continuation"
  | false ->
    List.fold_right sequence ~init:then_ ~f:(fun sequence then_ ->
      compile_sequence_to_ltl sequence ~then_)

and compile_repeat_to_ltl
  : type var. (var, sequence) t -> Sequence_range.t -> then_:var Ltl.t -> var Ltl.t
  =
  fun sequence range ~then_ ->
  if range_includes_zero range then unsupported_ltl "zero-repeat";
  let compile_exactly count =
    repeated_sequence sequence count |> compile_sequence_list_to_ltl ~then_
  in
  match range with
  | Bounded { from; to_ } ->
    List.init (to_ - from + 1) ~f:(fun i -> compile_exactly (from + i)) |> ltl_or
  | At_most to_ -> List.init (to_ + 1) ~f:compile_exactly |> ltl_or
  | At_least (_ : int) -> unsupported_ltl "repeat_at_least"
;;

let rec compile_sequence_implication_to_ltl
  : type var. (var, sequence) t -> then_:var Ltl.t -> var Ltl.t
  =
  fun sequence ~then_ ->
  match sequence_cases sequence with
  | Some cases -> compile_cases_implication_to_ltl cases ~then_
  | None ->
    (match sequence with
     | True -> then_
     | Atomic_proposition signal -> Ltl.(atom signal ==>: then_)
     | Delay range ->
       (match range with
        | Bounded _ | At_most _ ->
          ltl_for_each_offset range ~f:(fun n -> ltl_x n then_) |> ltl_and
        | At_least n -> ltl_x n (Ltl.g then_))
     | Concat sequence -> compile_sequence_list_implication_to_ltl sequence ~then_
     | Repeat (sequence, range) ->
       if range_includes_zero range
       then unsupported_ltl "zero-repeat in an implication antecedent";
       let compile_exactly count =
         repeated_sequence sequence count
         |> compile_sequence_list_implication_to_ltl ~then_
       in
       (match range with
        | Bounded { from; to_ } ->
          List.init (to_ - from + 1) ~f:(fun i -> compile_exactly (from + i)) |> ltl_and
        | At_most to_ -> List.init (to_ + 1) ~f:compile_exactly |> ltl_and
        | At_least (_ : int) ->
          unsupported_ltl "repeat_at_least in an implication antecedent")
     | And { kind = Sequence; lhs = _; rhs = _ } ->
       unsupported_ltl "unbounded sequence and"
     | Or { kind = Sequence; lhs; rhs } ->
       Ltl.(
         compile_sequence_implication_to_ltl lhs ~then_
         &: compile_sequence_implication_to_ltl rhs ~then_))

and compile_sequence_list_implication_to_ltl
  : type var. (var, sequence) t list -> then_:var Ltl.t -> var Ltl.t
  =
  fun sequence ~then_ ->
  match has_zero_repeat_with_continuation sequence with
  | true -> unsupported_ltl "zero-repeat in an implication antecedent"
  | false ->
    List.fold_right sequence ~init:then_ ~f:(fun sequence then_ ->
      compile_sequence_implication_to_ltl sequence ~then_)
;;

let rec compile_without_validation : type var kind. (var, kind) t -> var Ltl.t = function
  | True -> Ltl.vdd
  | Atomic_proposition signal -> Ltl.atom signal
  | Delay range -> compile_sequence_to_ltl (Delay range) ~then_:Ltl.vdd
  | Concat sequence -> compile_sequence_list_to_ltl sequence ~then_:Ltl.vdd
  | Repeat (sequence, range) -> compile_repeat_to_ltl sequence range ~then_:Ltl.vdd
  | Sequence_as_property property -> compile_without_validation property
  | Not property -> Ltl.( ~: ) (compile_without_validation property)
  | X property -> Ltl.x (compile_without_validation property)
  | Until (a, b) -> Ltl.u (compile_without_validation a) (compile_without_validation b)
  | Release (a, b) -> Ltl.r (compile_without_validation a) (compile_without_validation b)
  | Eventually property -> Ltl.f (compile_without_validation property)
  | Globally property -> Ltl.g (compile_without_validation property)
  | And ({ kind; lhs; rhs } as op) ->
    (match kind with
     | Sequence -> compile_sequence_to_ltl (And op) ~then_:Ltl.vdd
     | Property -> Ltl.(compile_without_validation lhs &: compile_without_validation rhs))
  | Or ({ kind; lhs; rhs } as op) ->
    (match kind with
     | Sequence -> compile_sequence_to_ltl (Or op) ~then_:Ltl.vdd
     | Property -> Ltl.(compile_without_validation lhs |: compile_without_validation rhs))
  | Overlapping_implication (sequence, consequent) ->
    compile_sequence_list_implication_to_ltl
      sequence
      ~then_:(compile_without_validation consequent)
  | Property_implication (p1, p2) ->
    Ltl.( ==>: ) (compile_without_validation p1) (compile_without_validation p2)
;;

let compile t = Validate_and_simplify.run t |> compile_without_validation
