open Parser
open Strategies__Strategies
open Proof__Proof

let cqfd =
  match goals Sys.argv.(1) with
  | None -> failwith "parse error"
  | Some l ->
    List.iter (fun g ->
        try 
          if prove [] g |> check_proof []
          then print_endline "proof found"
          else print_endline "proof found (but invalid)"
        with ProofNotFound -> print_endline "Proof not found"
      ) l