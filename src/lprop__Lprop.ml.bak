type prop =
  | Atom of int
  | And of prop * prop
  | Or of prop * prop
  | Impl of prop * prop
  | Bot

let rec infix_eqeq (x: prop) (y: prop) : bool =
  match (x, y) with
  | (Atom n, Atom m) -> n = m
  | (And (a, b), And (a', b')) -> infix_eqeq a a' && infix_eqeq b b'
  | (Or (a, b), Or (a', b')) -> infix_eqeq a a' && infix_eqeq b b'
  | (Impl (a, b), Impl (a', b')) -> infix_eqeq a a' && infix_eqeq b b'
  | (Bot, Bot) -> true
  | (_, _) -> false

