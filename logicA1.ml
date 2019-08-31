type prop = T | F | L of string | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type rho = (string * bool) list;;
type node = Node of (prop * bool * bool * bool * rho * int list );;
truth val * explored * contradictary * rho * intl
type tree = node * tree list ;;

select_node that selects an unexamined node on an open path as a candidate for further development.
step_develop that given a selected node on a path, develops the tableau according to the rules  specified above.

(Node(p, b1, b2, b3, rho, intl) , x)

let rec select_node t = match t with
  (Node(p, b1, true , b3, rho, intl) , x) -> (match x with []-> [] | [n1; n2] -> let o1= (select_node n1) in (if (o1=[]) then (select_node n2) else o1)  | [n1]-> (select_node n1))
| (Node(p, b1, false, false, rho, intl) , x) -> intl
| (Node(p, b1, false, true, rho, intl) , x) -> []
;;

