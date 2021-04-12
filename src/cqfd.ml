open Parser
open Strategies__Strategies
open Proof__Proof

let cqfd =
  match goals Sys.argv.(1) with
  | None -> failwith "parse error"
  | Some l ->
    List.iteri (fun i g ->
        try
          if prove [] g |> check_proof []
          then Printf.printf "proof (%d) found\n" i
          else assert false
        with ProofNotFound -> print_endline "Proof not found"
      ) l