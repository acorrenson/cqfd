open Parser
open Strategies__Strategies
open Lprop__Lprop
open Proof__Proof

let rec try_list l env p =
  match l with
  | [] -> raise ProofNotFound
  | f :: fs -> 
    try f env p
    with ProofNotFound -> try_list fs env p

let rec prove env p =
  try_list [
    strategy_1;
    strategy_2;
    strategy_3;
    strategy_4;
    strategy_5;
    strategy_6
  ] env p

and strategy_1 env p =
  print_endline "rule1";
  if hypothesis p env then Pr_axiom p
  else raise ProofNotFound

and strategy_2 env p =
  print_endline "rule2";
  search_immediate_rule env p

and strategy_3 env p =
  print_endline "rule3";
  search_contradiction env p

and strategy_4 env p =
  print_endline "rule4";
  match p with
  | And (a, b) ->
    let h1 = prove env a in
    let h2 = prove env b in
    Pr_Iand (h1, h2, p)
  | _ -> raise ProofNotFound

and strategy_5 env p =
  print_endline "rule5";
  match p with
  | Impl (a, b) ->
    let h = prove (a::env) b in
    Pr_Iimpl (h, p)
  | _ -> raise ProofNotFound

and strategy_6 env p =
  print_endline "rule6";
  match p with
  | Or (a, b) ->
    begin try
        let h = prove env a in
        Pr_Ior1 (h, p)
      with ProofNotFound ->
        let h = prove env b in
        Pr_Ior2 (h, p)
    end
  | _ -> raise ProofNotFound


let cqfd =
  match goals Sys.argv.(1) with
  | None -> failwith "parse error"
  | Some l ->
    print_endline "start";
    List.iter (fun g ->
        try 
          if prove [] g |> check_proof []
          then print_endline "proof found"
          else print_endline "proof found (but invalid)"
        with ProofNotFound -> print_endline "Proof not found"
      ) l