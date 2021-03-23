open Proof
open Parser

exception ProofNotFound

let is_or = function Or _ -> true | _ -> false

let is_impl x = function Impl (_, x') when x = x' -> true | _ -> false

let is_and1 x = function And (x', _) when x = x' -> true | _ -> false

let is_and2 x = function And (_, x') when x = x' -> true | _ -> false

let hyp f e = contain f e

let search_false env p =
  if hyp Bot env then Pr_Ebot (Pr_axiom Bot, p)
  else raise ProofNotFound

let search_raa env p =
  let nnp = Impl (Impl (p, Bot), Bot) in
  if hyp nnp env then Pr_RAA (Pr_axiom nnp, p)
  else raise ProofNotFound

let search_Eimpl env p =
  let test q =
    if is_impl p q then begin
      match q with
      | Impl (a, _) -> hyp a env
      | _ -> assert false
    end else false
  in
  try
    match List.find test env with
    | Impl (a, _) as h -> Pr_Eimpl (Pr_axiom a, Pr_axiom h, p)
    | _ -> assert false
  with Not_found -> raise ProofNotFound

let search_Eand env p =
  try
    let x = List.find (is_and1 p) env in
    Pr_Eand1 (Pr_axiom x, p)
  with Not_found -> try
      let x = List.find (is_and2 p) env in
      Pr_Eand2 (Pr_axiom x, p)
    with Not_found ->
      raise ProofNotFound

let search_Eor env p =
  let test q =
    if is_or q then begin
      match q with
      | Or (a, b) ->
        let h1, h2 = Impl (a, p), Impl (b, p) in
        hyp h1 env && hyp h2 env
      | _ -> assert false
    end else false
  in
  try
    match List.find test env with
    | Or (a, b) as h ->
      let h1 = Pr_axiom h in
      let h2 = Pr_axiom (Impl (a, p)) in
      let h3 = Pr_axiom (Impl (b, p)) in
      Pr_Eor (h1, h2, h3, p)
    | _ -> assert false
  with Not_found -> raise ProofNotFound

let search_contradiction env p =
  try
    let x = List.find (fun q -> hyp (Impl (q, Bot)) env) env in
    Pr_Eimpl (Pr_axiom x, Pr_axiom (Impl (x, Bot)), p)
  with Not_found -> raise ProofNotFound


let search_immediate_rule env p =
  match p with
  | And (x, y) when hyp x env && hyp y env ->
    Pr_Iand (Pr_axiom x, Pr_axiom y, p)
  | Or (x, _) when hyp x env ->
    Pr_Ior1 (Pr_axiom x, p)
  | Or (_, y) when hyp y env ->
    Pr_Ior2 (Pr_axiom y, p) 
  | Impl (_, b) when hyp b env ->
    Pr_Iimpl (Pr_axiom b, p)
  | _ ->
    try
      search_Eor env p
    with ProofNotFound -> try
        search_Eand env p
      with ProofNotFound -> try
          search_Eimpl env p
        with ProofNotFound ->
          search_raa env p

let rec prove env p =
  let rec try_list l =
    match l with
    | []    -> raise ProofNotFound
    | f::fs -> try f env p
      with ProofNotFound -> try_list fs
  in
  try_list [
    strategy_1;
    strategy_2;
    strategy_3;
    strategy_4;
    strategy_5;
    strategy_6;
  ]

and strategy_1 env p =
  print_endline "rule1";
  if hyp p env then Pr_axiom p
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