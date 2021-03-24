exception Not_found

let rec find (pred: Lprop__Lprop.prop -> (bool)) (l: Lprop__Lprop.prop list) :
  Lprop__Lprop.prop =
  match l with
  | [] -> raise Not_found
  | x :: xs -> if pred x then x else find pred xs

let do_implies (q: Lprop__Lprop.prop) (p: Lprop__Lprop.prop)
               (env: Lprop__Lprop.prop list) : bool =
  match q with
  | Lprop__Lprop.Impl (h,
    x) ->
    Lprop__Lprop.infix_eqeq x p && Proof__Proof.hypothesis h env
  | _ -> false

let do_and_left (p: Lprop__Lprop.prop) (q: Lprop__Lprop.prop) : bool =
  match q with
  | Lprop__Lprop.And (x, _) -> Lprop__Lprop.infix_eqeq p x
  | _ -> false

let do_and_right (p: Lprop__Lprop.prop) (q: Lprop__Lprop.prop) : bool =
  match q with
  | Lprop__Lprop.And (_, x) -> Lprop__Lprop.infix_eqeq p x
  | _ -> false

let do_case (q: Lprop__Lprop.prop) (p: Lprop__Lprop.prop)
            (env: Lprop__Lprop.prop list) : bool =
  match q with
  | Lprop__Lprop.Or (a,
    b) ->
    (let h1 = Lprop__Lprop.Impl (a, p) in
     let h2 = Lprop__Lprop.Impl (b, p) in
     Proof__Proof.hypothesis h1 env && Proof__Proof.hypothesis h2 env)
  | _ -> false

