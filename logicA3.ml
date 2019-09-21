type prop = T | F | L of string 
| Not of prop| And of prop * prop | Or of prop * prop 
| Impl of prop * prop | Iff of prop * prop;;

type ndprooftree = Hyp of prop list * prop| TI of prop list| ImpI prop list * prop * prop * ndprooftree |
ImpE prop list * prop * prop * ndprooftree * ndprooftree | NotI prop list * prop * ndprooftree |
NotC prop list * prop * ndprooftree | AndI prop list * prop * prop * ndprooftree * ndprooftree| AndEL prop list * prop * prop * ndprooftree|
AndER prop list * prop * prop * ndprooftree | OrIL prop list * prop * prop * ndprooftree|
OrIR prop list * prop * prop * ndprooftree | 
OrE prop list * prop * prop * prop * ndprooftree * ndprooftree * ndprooftree

let rec member a l= match l with
  []-> false
  | x::xs -> if a=x then true else (member a xs)
;;

let rec union l1 l2 = match l2 with
[] -> l1
| x::xs -> (if (member x l1) then (union l1 xs) else (union (l1@[x]) xs))
;;

let get_judgement t = match t with
    Hyp(gamma,p)-> p
|    TI(gamma)-> T
|    ImpI(gamma,p,q,h1)-> Impl(p,q)
|    ImpE(gamma,p,q,h1,h2)-> q
|    NotI(gamma,p,h1)-> p
|    NotC(gamma,p,h1)-> p
|    AndI(gamma,p,q,h1,h2)-> And(p,q)
|    AndEL(gamma,p,q,h1)-> p
|    AndER(gamma,p,q,h1)-> q
|    OrIL(gamma,p,q,h1)-> Or(p,q)
|    OrIR(gamma,p,q,h1)-> Or(p,q)
|    OrE(gamma,p,q,r,h1,h2,h3)-> r


let rec valid_ndprooftree t = match t with

Hyp(gamma,p)->











let get_judgement t = match t with
    Hyp(gamma,p)->
|    TI(gamma)-> 
|    ImpI(gamma,p,q,h1)->
|    ImpE(gamma,p,q,h1,h2)->
|    NotI(gamma,p,h1)->
|    NotC(gamma,p,h1)->
|    AndI(gamma,p,q,h1,h2)->
|    AndEL(gamma,p,q,h1)->
|    AndER(gamma,p,q,h1)->
|    OrIL(gamma,p,q,h1)->
|    OrIR(gamma,p,q,h1)->
|    OrE(gamma,p,q,r,h1,h2,h3)->


