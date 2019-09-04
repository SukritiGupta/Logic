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


let get_main_prop h = match h with
| Ass(gamma, p) -> p
| K(gamma,p,q) -> Impl(p,(Impl(q,p)))
| S(gamma,p,q,r) -> Impl((p,(Impl(q,r))) , (Impl((Impl(p,q)) , (Impl(p,r)))))
| R(gamma,p,q) -> Impl((Impl(Not(p),Not(q))) , (Impl(Impl(Not(p)),q),p))


let get_prop h = match h with
MP(gamma, p,q, h1, h2) -> q
| L(x) -> (get_main_prop x)

let rec valid_hprooftree t = match t with
| L(Ass(x,p)) -> (member p x)
| L(_) -> true
| MP(gamma, p,q, h1, h2) -> ( (Impl(p,q)=(get_prop h1)) && (p=(get_prop h2))  && (valid_hprooftree h1) && (valid_hprooftree h2))