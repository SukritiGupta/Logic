type prop = T | F | L of string 
| Not of prop| And of prop * prop | Or of prop * prop 
| Impl of prop * prop | Iff of prop * prop;;

type leaf = Ass of prop list * prop | K of prop list * prop * prop 
| S of prop list * prop * prop * prop | R of prop list * prop * prop ;;

type hprooftree = MP of prop list * prop * prop * hprooftree * hprooftree | L of leaf;;

let rec member a l= match l with
	[]-> false
	| x::xs -> if a=x then true else (member a xs)
;;

let rec union l1 l2 = match l2 with
[] -> l1
| x::xs -> (if (member x l1) then (union l1 xs) else (union (l1@[x]) xs))
;;

let get_main_prop h = match h with
| Ass(gamma, p) -> p
| K(gamma,p,q) -> Impl(p,(Impl(q,p)))
| S(gamma,p,q,r) -> Impl((p,(Impl(q,r))) , (Impl((Impl(p,q)) , (Impl(p,r)))))
| R(gamma,p,q) -> Impl((Impl(Not(p),Not(q))) , (Impl(Impl(Not(p)),q),p))
;;

let get_prop h = match h with
MP(gamma, p,q, h1, h2) -> q
| L(x) -> (get_main_prop x)
;;


let rec valid_hprooftree t = match t with
| L(Ass(x,p)) -> (member p x)
| L(_) -> true
| MP(gamma, p,q, h1, h2) -> ( (Impl(p,q)=(get_prop h1)) && (p=(get_prop h2))  && (valid_hprooftree h1) && (valid_hprooftree h2))
;;

let rec pad h l = match h with
| MP(gamma, p,q, h1, h2) -> MP( (union gamma l), p,q, (pad h1 l), (pad h2 l))
| L(Ass(gamma, p)) -> L(Ass((union gamma l), p))
| L(K(gamma,p,q)) -> L(K((union gamma l),p,q))
| L(S(gamma,p,q,r)) -> L(S((union gamma l),p,q,r))
| L(R(gamma,p,q)) -> L(R((union gamma l),p,q))
;;

let rec get_all_prop h l = match h with
| MP(gamma, p,q, h1, h2) -> l@(get_all_prop h1)@(get_all_prop h2)
| L(Ass(gamma, p)) -> [p]
| L(_) -> l 
;;

let rec put_gamma h newgamma = match  h with
| MP(gamma, p,q, h1, h2) -> MP( newgamma, p,q, (put_gamma h1 newgamma), (put_gamma h2 newgamma))
| L(Ass(gamma, p)) -> L(Ass(newgamma, p))
| L(K(gamma,p,q)) -> L(K(newgamma,p,q))
| L(S(gamma,p,q,r)) -> L(S(newgamma,p,q,r))
| L(R(gamma,p,q)) -> L(R(newgamma,p,q))
;;

let rec prune h = ( let newgamma= (get_all_prop h []) in (put_gamma h newgamma));;

let get_gamma l = match l with
[] -> []
| MP(gamma, p,q, h1, h2)::xs -> gamma
| L(Ass(gamma, p))::xs -> gamma
| L(K(gamma,p,q)) ::xs-> gamma
| L(S(gamma,p,q,r))::xs -> gamma
| L(R(gamma,p,q))::xs -> gamma
;;

let graft h l =  let newgamma= (get_gamma l)




| MP(gamma, p,q, h1, h2) -> 
| L(Ass(gamma, p)) -> 
| L(K(gamma,p,q)) -> 
| L(S(gamma,p,q,r)) -> 
| L(R(gamma,p,q)) -> 

