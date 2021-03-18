type prop =
  | Atom of int
  | And of prop * prop
  | Or of prop * prop
  | Impl of prop * prop
  | Bot

type proof =
  | Pr_axiom of prop
  | Pr_Iimpl of proof * prop
  | Pr_Eimpl of proof * proof * prop
  | Pr_Ior1 of proof * prop
  | Pr_Ior2 of proof * prop
  | Pr_Eor of proof * proof * proof * prop
  | Pr_Eand1 of proof * prop
  | Pr_Eand2 of proof * prop
  | Pr_Iand of proof * proof * prop
  | Pr_RAA of proof * prop
  | Pr_Ebot of proof * prop

let conseq (pr: proof) : prop =
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

let rec infix_eqeq (x: prop) (y: prop) : bool =
  match (x, y) with
  | (Atom n, Atom m) -> n = m
  | (And (a, b), And (a', b')) -> infix_eqeq a a' && infix_eqeq b b'
  | (Or (a, b), Or (a', b')) -> infix_eqeq a a' && infix_eqeq b b'
  | (Impl (a, b), Impl (a', b')) -> infix_eqeq a a' && infix_eqeq b b'
  | (Bot, Bot) -> true
  | (_, _) -> false

let rec contain (x: prop) (g: prop list) : bool =
  match g with
  | [] -> false
  | y :: ys -> infix_eqeq y x || contain x ys

let rec check_proof (g: prop list) (pr: proof) : bool =
  match pr with
  | Pr_axiom p -> contain p g
  | Pr_Iimpl (prq,
              Impl (p,
                    q)) ->
    infix_eqeq (conseq prq) q && check_proof (p :: g) prq
  | Pr_Eimpl (pr1,
              pr2,
              p) ->
    begin match conseq pr1 with
      | Impl (a,
              b) ->
        infix_eqeq (conseq pr2) a && infix_eqeq p b && check_proof g pr1 && 
        check_proof g
          pr2
      | _ -> false
    end
  | Pr_Ior1 (pr1,
             Or (a,
                 _)) ->
    infix_eqeq (conseq pr1) a && check_proof g pr1
  | Pr_Ior2 (pr1,
             Or (_,
                 b)) ->
    infix_eqeq (conseq pr1) b && check_proof g pr1
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
        infix_eqeq a x && infix_eqeq b y && infix_eqeq cx q && infix_eqeq cy q && 
        check_proof g
          pru && check_proof g
          pra && 
        check_proof g
          prb
      | _ -> false
    end
  | Pr_Eand1 (pr1,
              p) ->
    begin match conseq pr1 with
      | And (a, _) -> infix_eqeq a p && check_proof g pr1
      | _ -> false
    end
  | Pr_Eand2 (pr1,
              p) ->
    begin match conseq pr1 with
      | And (_, a) -> infix_eqeq a p && check_proof g pr1
      | _ -> false
    end
  | Pr_Iand (pra,
             prb,
             And (a,
                  b)) ->
    infix_eqeq (conseq pra) a && infix_eqeq (conseq prb) b && check_proof g
      pra && 
    check_proof g
      prb
  | Pr_RAA (pra,
            p) ->
    begin match conseq pra with
      | Impl (Impl (a, Bot), Bot) -> infix_eqeq a p && check_proof g pra
      | _ -> false
    end
  | Pr_Ebot (pr1,
             _) ->
    begin match conseq pr1 with
      | Bot -> check_proof g pr1
      | _ -> false
    end
  | _ -> false

