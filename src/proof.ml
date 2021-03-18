type l0 =
  | Atom of int
  | And of l0 * l0
  | Or of l0 * l0
  | Impl of l0 * l0
  | Bot

type proof_tree =
  | Pr_axiom of l0
  | Pr_Iimpl of proof_tree * l0
  | Pr_Eimpl of proof_tree * proof_tree * l0
  | Pr_Ior1 of proof_tree * l0
  | Pr_Ior2 of proof_tree * l0
  | Pr_Eor of proof_tree * proof_tree * proof_tree * l0
  | Pr_Eand1 of proof_tree * l0
  | Pr_Eand2 of proof_tree * l0
  | Pr_Iand of proof_tree * proof_tree * l0
  | Pr_RAA of proof_tree * l0
  | Pr_Ebot of proof_tree * l0

let conseq (pr: proof_tree) : l0 =
  match pr with
  | Pr_axiom p -> p
  | Pr_Iimpl (_, p) -> p
  | Pr_Eimpl (_, _, p) -> p
  | Pr_Ior1 (_, p) -> p
  | Pr_Ior2 (_, p) -> p
  | Pr_Eor (_, _, _, p) -> p
  | Pr_Eand1 (_, p) -> p
  | Pr_Eand2 (_, p) -> p
  | Pr_Iand (_, _, p) -> p
  | Pr_RAA (_, p) -> p
  | Pr_Ebot (_, p) -> p

let rec eqb (x: l0) (y: l0) : bool =
  match (x, y) with
  | (Atom n, Atom m) -> n = m
  | (And (a, b), And (a', b')) -> eqb a a' && eqb b b'
  | (Or (a, b), Or (a', b')) -> eqb a a' && eqb b b'
  | (Impl (a, b), Impl (a', b')) -> eqb a a' && eqb b b'
  | (Bot, Bot) -> true
  | (_, _) -> false

let rec contain (x: l0) (g: l0 list) : bool =
  match g with
  | [] -> false
  | y :: ys -> eqb y x || contain x ys

let rec check_proof (g: l0 list) (pr: proof_tree) : bool =
  match pr with
  | Pr_axiom p -> contain p g
  | Pr_Iimpl (prq,
              Impl (p,
                    q)) ->
    eqb (conseq prq) q && check_proof (p :: g) prq
  | Pr_Eimpl (pr1,
              pr2,
              p) ->
    begin match conseq pr1 with
      | Impl (a,
              b) ->
        eqb (conseq pr2) a && eqb p b && check_proof g pr1 && check_proof g pr2
      | _ -> false
    end
  | Pr_Ior1 (pr1, Or (a, _)) -> eqb (conseq pr1) a && check_proof g pr1
  | Pr_Ior2 (pr1, Or (_, b)) -> eqb (conseq pr1) b && check_proof g pr1
  | Pr_Eor (pru,
            pra,
            prb,
            q) ->
    begin match (conseq pru, conseq pra, conseq prb) with
      | (Or (a,
             b),
         Impl (x,
               cx),
         Impl (y,
               cy)) ->
        eqb a x && eqb b y && eqb cx q && eqb cy q && check_proof g pru && 
        check_proof g pra && 
        check_proof g
          prb
      | _ -> false
    end
  | Pr_Eand1 (pr1,
              p) ->
    begin match conseq pr1 with
      | And (a, _) -> eqb a p && check_proof g pr1
      | _ -> false
    end
  | Pr_Eand2 (pr1,
              p) ->
    begin match conseq pr1 with
      | And (_, a) -> eqb a p && check_proof g pr1
      | _ -> false
    end
  | Pr_Iand (pra,
             prb,
             And (a,
                  b)) ->
    eqb (conseq pra) a && eqb (conseq prb) b && check_proof g pra && 
    check_proof g
      prb
  | Pr_RAA (pra,
            p) ->
    begin match conseq pra with
      | Impl (Impl (a, Bot), Bot) -> eqb a p && check_proof g pra
      | _ -> false
    end
  | Pr_Ebot (pr1,
             _) ->
    begin match conseq pr1 with
      | Bot -> check_proof g pr1
      | _ -> false
    end
  | _ -> false

