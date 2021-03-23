open Opal
open Proof

let parens = between (exactly '(') (exactly ')')

let p_impl = token "->" >> return (fun p q -> Impl (p, q))
let p_and = token "/\\" >> return (fun p q -> And (p, q))
let p_or = token "\\/" >> return (fun p q -> Or (p, q))
let p_atom = spaces >> letter => (fun x -> Atom (int_of_char x))
let p_bot = token "Bot" >> return Bot
let p_not p = token "not" >> p => (fun x -> Impl (x, Bot))

let rec p_prop inp = between spaces spaces (chainr1 p_disj p_impl) inp
and p_disj inp = between spaces spaces (chainl1 p_conj p_or) inp
and p_conj inp = between spaces spaces (chainl1 p_min p_and) inp
and p_min inp = choice [p_not (p_prop); parens p_prop; p_bot; p_atom] inp

let goal = token "Goal" >> spaces >> p_prop

let goals file = parse
    (many1 (spaces >> goal << spaces))
    (LazyStream.of_channel (open_in file))