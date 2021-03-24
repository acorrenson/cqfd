type proof =
  | Pr_axiom of Lprop__Lprop.prop
  | Pr_Iimpl of proof * Lprop__Lprop.prop
  | Pr_Eimpl of proof * proof * Lprop__Lprop.prop
  | Pr_Ior1 of proof * Lprop__Lprop.prop
  | Pr_Ior2 of proof * Lprop__Lprop.prop
  | Pr_Eor of proof * proof * proof * Lprop__Lprop.prop
  | Pr_Eand1 of proof * Lprop__Lprop.prop
  | Pr_Eand2 of proof * Lprop__Lprop.prop
  | Pr_Iand of proof * proof * Lprop__Lprop.prop
  | Pr_RAA of proof * Lprop__Lprop.prop
  | Pr_Ebot of proof * Lprop__Lprop.prop

let conseq (pr: proof) : Lprop__Lprop.prop =
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

let rec hypothesis (x: Lprop__Lprop.prop) (g: Lprop__Lprop.prop list) : 
  bool =
  match g with
  | [] -> false
  | y :: ys -> Lprop__Lprop.infix_eqeq y x || hypothesis x ys

let rec check_proof (g: Lprop__Lprop.prop list) (pr: proof) : bool =
  match pr with
  | Pr_axiom p -> hypothesis p g
  | Pr_Iimpl (prq,
    Lprop__Lprop.Impl (p,
    q)) ->
    Lprop__Lprop.infix_eqeq (conseq prq) q && check_proof (p :: g) prq
  | Pr_Eimpl (pr1,
    pr2,
    p) ->
    begin match conseq pr1 with
    | Lprop__Lprop.Impl (a,
      b) ->
      Lprop__Lprop.infix_eqeq (conseq pr2) a && Lprop__Lprop.infix_eqeq p b && 
                                                check_proof g pr1 && 
                                                check_proof g
                                                pr2
    | _ -> false
    end
  | Pr_Ior1 (pr1,
    Lprop__Lprop.Or (a,
    _)) ->
    Lprop__Lprop.infix_eqeq (conseq pr1) a && check_proof g pr1
  | Pr_Ior2 (pr1,
    Lprop__Lprop.Or (_,
    b)) ->
    Lprop__Lprop.infix_eqeq (conseq pr1) b && check_proof g pr1
  | Pr_Eor (pru,
    pra,
    prb,
    q) ->
    begin match (conseq pru, conseq pra, conseq prb) with
    | (Lprop__Lprop.Or (a,
      b),
      Lprop__Lprop.Impl (x,
      cx),
      Lprop__Lprop.Impl (y,
      cy)) ->
      Lprop__Lprop.infix_eqeq a x && Lprop__Lprop.infix_eqeq b y && Lprop__Lprop.infix_eqeq cx
                                                                    q && 
                                                                    Lprop__Lprop.infix_eqeq cy
                                                                    q && 
                                                                    check_proof g
                                                                    pru && 
                                                                    check_proof g
                                                                    pra && 
                                                                    check_proof g
                                                                    prb
    | _ -> false
    end
  | Pr_Eand1 (pr1,
    p) ->
    begin match conseq pr1 with
    | Lprop__Lprop.And (a,
      _) ->
      Lprop__Lprop.infix_eqeq a p && check_proof g pr1
    | _ -> false
    end
  | Pr_Eand2 (pr1,
    p) ->
    begin match conseq pr1 with
    | Lprop__Lprop.And (_,
      a) ->
      Lprop__Lprop.infix_eqeq a p && check_proof g pr1
    | _ -> false
    end
  | Pr_Iand (pra,
    prb,
    Lprop__Lprop.And (a,
    b)) ->
    Lprop__Lprop.infix_eqeq (conseq pra) a && Lprop__Lprop.infix_eqeq 
                                              (conseq prb)
                                              b && check_proof g pra && 
                                                   check_proof g
                                                   prb
  | Pr_RAA (pra,
    p) ->
    begin match conseq pra with
    | Lprop__Lprop.Impl (Lprop__Lprop.Impl (a,
      Lprop__Lprop.Bot),
      Lprop__Lprop.Bot) ->
      Lprop__Lprop.infix_eqeq a p && check_proof g pra
    | _ -> false
    end
  | Pr_Ebot (pr1,
    _) ->
    begin match conseq pr1 with
    | Lprop__Lprop.Bot -> check_proof g pr1
    | _ -> false
    end
  | _ -> false

