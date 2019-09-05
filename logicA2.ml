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

let get_gamma h = match h with
| MP(gamma, p,q, h1, h2) -> gamma
| L(Ass(gamma, p)) -> gamma
| L(K(gamma,p,q)) -> gamma
| L(S(gamma,p,q,r)) -> gamma
| L(R(gamma,p,q)) -> gamma
;;

exception Proof_not_given;;
exception Prop_not_in_gamma;;

let rec replace p l = match l with
| [] -> raise Proof_not_given
| x::xs -> (if (p=(get_prop x)) then x else (replace p xs))
;;

let rec modify h l = match h with
| MP(gamma, p,q, h1, h2) -> MP(gamma, p,q, (modify h1 l), (modify h2 l))
| L(Ass(gamma, p)) -> (replace p l)
| L(x) -> L(x)
;;

let graft h l =  (if l=[] then h else let newgamma= (get_gamma l) in ( let interm=(put_gamma h newgamma) in (modify interm l)));;

let rec remove e l = match l with
| [] -> raise Prop_not_in_gamma
| x::xs -> if (x=e) then xs else ([x]@(remove e xs))
;;

let special_tree  gamma  p = MP(gamma,     Impl(p,Impl(Impl(L("Any_prop"),p), p)) ,     Impl(Impl(p,Impl(L("Any_prop"),p)),  Impl(p,p))     ,   
 L(S(gamma,p,Impl(L("Any_prop"),p),p)),
 L(K(gamma, p, Impl(L("Any_prop"),p)))      
);;


let dedthm p h = let q=(get_prop h) in (  if (p=q) then let temp = (remove p gamma) in (MP(temp,Impl(p,Impl(L("Any_prop"),p)) ,Impl(p,p),(special_tree temp p),L(K(temp, p, L("Any_prop")))))
else ( match h with
| L(Ass(gamma, p1)) -> L(Ass( (remove p gamma), p1))
| L(K(gamma,p1,q1)) -> L(K((remove p gamma),p1,q1))
| L(S(gamma,p1,q1,r)) -> L(S((remove p gamma),p1,q1,r))
| L(R(gamma,p1,q1)) -> 	L(R((remove p gamma),p1,q1))
| MP(gamma, r,q1, h1, h2) -> let temp = (remove p gamma) in (MP(temp ,Impl(p,r) ,Impl(p,q),MP(temp,Impl(p,(Impl(r,q))),Impl((Impl(p,r)),Impl(p,q)), L(S(temp,p,r,q)),(dedthm p h1)) ,(dedthm p h2)))
))
;;
