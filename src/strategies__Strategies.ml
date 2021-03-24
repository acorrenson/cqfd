exception ProofNotFound

let search_false (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  if Proof__Proof.hypothesis Lprop__Lprop.Bot env
  then Proof__Proof.Pr_Ebot (Proof__Proof.Pr_axiom Lprop__Lprop.Bot, p)
  else raise ProofNotFound

let search_axiom (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  if Proof__Proof.hypothesis p env
  then Proof__Proof.Pr_axiom p
  else raise ProofNotFound

let search_raa (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  let nnp =
    Lprop__Lprop.Impl (Lprop__Lprop.Impl (p, Lprop__Lprop.Bot),
    Lprop__Lprop.Bot) in
  if Proof__Proof.hypothesis nnp env
  then Proof__Proof.Pr_RAA (Proof__Proof.Pr_axiom nnp, p)
  else raise ProofNotFound

let search_Eimpl (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  try
    let h =
      Strategies__Finders.find (fun (q: Lprop__Lprop.prop) ->
                                  Strategies__Finders.do_implies q p env)
      env in
    match h with
    | Lprop__Lprop.Impl (a,
      _) ->
      Proof__Proof.Pr_Eimpl (Proof__Proof.Pr_axiom h,
      Proof__Proof.Pr_axiom a,
      p)
    | _ -> assert false (* absurd *)
  with
  | Strategies__Finders.Not_found -> raise ProofNotFound

let search_Eand (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  try
    let x = Strategies__Finders.find (Strategies__Finders.do_and_left p) env in
    Proof__Proof.Pr_Eand1 (Proof__Proof.Pr_axiom x, p)
  with
  | Strategies__Finders.Not_found ->
      begin
        try
        let x =
          Strategies__Finders.find (Strategies__Finders.do_and_right p) env in
        Proof__Proof.Pr_Eand2 (Proof__Proof.Pr_axiom x, p)
      with
      | Strategies__Finders.Not_found -> raise ProofNotFound
      end

let search_Eor (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  try
    let h =
      Strategies__Finders.find (fun (q1: Lprop__Lprop.prop) ->
                                  Strategies__Finders.do_case q1 p env)
      env in
    match h with
    | Lprop__Lprop.Or (a,
      b) ->
      (let h1 = Proof__Proof.Pr_axiom h in
       let h2 = Proof__Proof.Pr_axiom (Lprop__Lprop.Impl (a, p)) in
       let h3 = Proof__Proof.Pr_axiom (Lprop__Lprop.Impl (b, p)) in
       Proof__Proof.Pr_Eor (h1, h2, h3, p))
    | _ -> assert false (* absurd *)
  with
  | Strategies__Finders.Not_found -> raise ProofNotFound

let search_contradiction (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  try
    let x =
      Strategies__Finders.find (fun (q2: Lprop__Lprop.prop) ->
                                  Proof__Proof.hypothesis (Lprop__Lprop.Impl (q2,
                                                           Lprop__Lprop.Bot))
                                  env)
      env in
    Proof__Proof.Pr_Ebot (Proof__Proof.Pr_Eimpl (Proof__Proof.Pr_axiom 
                                                 (Lprop__Lprop.Impl (x,
                                                  Lprop__Lprop.Bot)),
                          Proof__Proof.Pr_axiom x,
                          Lprop__Lprop.Bot),
    p)
  with
  | Strategies__Finders.Not_found -> raise ProofNotFound

let search_immediate_rule (env: Lprop__Lprop.prop list)
                          (p: Lprop__Lprop.prop) : Proof__Proof.proof =
  let fall_back (_: unit) : Proof__Proof.proof =
    try search_Eimpl env p with
    | ProofNotFound ->
        begin try search_Eor env p with
        | ProofNotFound ->
            begin try search_Eor env p with
            | ProofNotFound ->
                begin try search_Eand env p with
                | ProofNotFound -> search_raa env p
                end
            end
        end in
  match p with
  | Lprop__Lprop.And (x,
    y) ->
    if Proof__Proof.hypothesis x env && Proof__Proof.hypothesis y env
    then
      Proof__Proof.Pr_Iand (Proof__Proof.Pr_axiom x,
      Proof__Proof.Pr_axiom y,
      p)
    else fall_back ()
  | Lprop__Lprop.Or (x,
    y) ->
    if Proof__Proof.hypothesis x env
    then Proof__Proof.Pr_Ior1 (Proof__Proof.Pr_axiom x, p)
    else
      begin
        if Proof__Proof.hypothesis y env
        then Proof__Proof.Pr_Ior2 (Proof__Proof.Pr_axiom y, p)
        else fall_back () end
  | _ -> fall_back ()

let rec prove (env: Lprop__Lprop.prop list) (p: Lprop__Lprop.prop) :
  Proof__Proof.proof =
  try search_axiom env p with
  | ProofNotFound ->
      begin try search_immediate_rule env p with
      | ProofNotFound ->
          begin try search_contradiction env p with
          | ProofNotFound ->
              begin match p with
              | Lprop__Lprop.And (a,
                b) ->
                (let pra = prove env a in let prb = prove env b in
                 Proof__Proof.Pr_Iand (pra, prb, p))
              | Lprop__Lprop.Or (a,
                b) ->
                begin try let o = prove env a in Proof__Proof.Pr_Ior1 (o, p)
                with
                | ProofNotFound ->
                    (let o = prove env b in Proof__Proof.Pr_Ior2 (o, p))
                end
              | Lprop__Lprop.Impl (a,
                b) ->
                (let o = prove (a :: env) b in Proof__Proof.Pr_Iimpl (o, p))
              | _ -> raise ProofNotFound
              end
          end
      end

