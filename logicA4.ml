type prop = T | F | L of string 
| Not of prop| And of prop * prop | Or of prop * prop 
| Impl of prop * prop | Iff of prop * prop;;

type ndprooftree = Hyp of prop list * prop| TI of prop list| ImpI of prop list * prop * prop * ndprooftree |
ImpE of prop list * prop * prop * ndprooftree * ndprooftree | NotI of prop list * prop * ndprooftree |
NotC of prop list * prop * ndprooftree | AndI of prop list * prop * prop * ndprooftree * ndprooftree| AndEL of prop list * prop * prop * ndprooftree|
AndER of prop list * prop * prop * ndprooftree | OrIL of prop list * prop * prop * ndprooftree|
OrIR of prop list * prop * prop * ndprooftree | 
OrE of prop list * prop * prop * prop * ndprooftree * ndprooftree * ndprooftree
;;

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
;;


let get_gamma t = match t with
    Hyp(gamma,p)-> gamma
|    TI(gamma)-> gamma
|    ImpI(gamma,p,q,h1)-> gamma
|    ImpE(gamma,p,q,h1,h2)-> gamma
|    NotI(gamma,p,h1)-> gamma
|    NotC(gamma,p,h1)-> gamma
|    AndI(gamma,p,q,h1,h2)-> gamma
|    AndEL(gamma,p,q,h1)-> gamma
|    AndER(gamma,p,q,h1)-> gamma
|    OrIL(gamma,p,q,h1)-> gamma
|    OrIR(gamma,p,q,h1)-> gamma
|    OrE(gamma,p,q,r,h1,h2,h3)-> gamma
;;



exception Proof_not_given;;

let rec graft_help t l gamma_new=  match t with
(* nahi mila toh same as generate hua ho skta *)
    Hyp(gamma,p)-> (replace p l gamma_new)
|    TI(gamma)->   TI(gamma_new)
|    ImpI(gamma,p,q,h1)->  ImpI(gamma_new,p,q,(graft_help h1 l (union gamma_new [p])))
|    ImpE(gamma,p,q,h1,h2)->  ImpE(gamma_new,p,q,(graft_help h1 l gamma_new),(graft_help h2 l gamma_new))
|    NotI(gamma,p,h1)->  NotI(gamma_new,p,(graft_help h1 l gamma_new))
|    NotC(gamma,p,h1)->  NotC(gamma_new,p,(graft_help h1 l  (union gamma_new [Not(p)])))
|    AndI(gamma,p,q,h1,h2)->  AndI(gamma_new,p,q,(graft_help h1 l gamma_new),(graft_help h2 l gamma_new))
|    AndEL(gamma,p,q,h1)->  AndEL(gamma_new,p,q,(graft_help h1 l gamma_new))
|    AndER(gamma,p,q,h1)->  AndER(gamma_new,p,q,(graft_help h1 l gamma_new))
|    OrIL(gamma,p,q,h1)->  OrIL(gamma_new,p,q,(graft_help h1 l gamma_new))
|    OrIR(gamma,p,q,h1)->  OrIR(gamma_new,p,q,(graft_help h1 l gamma_new))
|    OrE(gamma,p,q,r,h1,h2,h3)->  OrE(gamma_new,p,q,r,(graft_help h1 l gamma_new),(graft_help h2 l (union gamma_new [p])),(graft_help h3 l (union gamma_new [q])))

and replace p l gamma_new = match l with
| [] -> (if (member p gamma_new) then (Hyp(gamma_new,p)) else raise Proof_not_given)
| x::xs -> (if (p=(get_judgement x)) then (graft_help x [] gamma_new) else (replace p xs gamma_new))
;; 

let head l = match l with x::xs->x;;

let graft t l =  (if l=[] then t else (let gamma_new= (get_gamma (head l)) in (graft_help t l gamma_new)));;

exception Normalised;;


let get_name t = match t with
    Hyp(gamma,p)->  "Hyp"
|    TI(gamma)->  "TI"
|    ImpI(gamma,p,q,h1)->  "ImpI"
|    ImpE(gamma,p,q,h1,h2)-> "ImpE"
|    NotI(gamma,p,h1)-> "NotI"
|    NotC(gamma,p,h1)-> "NotC"
|    AndI(gamma,p,q,h1,h2)-> "AndI"
|    AndEL(gamma,p,q,h1)-> "AndEL"
|    AndER(gamma,p,q,h1)-> "AndER"
|    OrIL(gamma,p,q,h1)-> "OrIL"
|    OrIR(gamma,p,q,h1)-> "OrIR"
|    OrE(gamma,p,q,r,h1,h2,h3)-> "OrE"
;;

let rec find_rpair t = match t with
    Hyp(gamma,p)-> raise Normalised
|    TI(gamma)-> raise Normalised
|    ImpI(gamma,p,q,h1)-> (find_rpair h1)
|    ImpE(gamma,p,q,h1,h2)-> if ((get_name h1)="ImpI") then t else (try (find_rpair h1) with Normalised -> (find_rpair h2))
|    NotI(gamma,p,h1)-> (find_rpair h1)
|    NotC(gamma,p,h1)-> (find_rpair h1)
|    AndI(gamma,p,q,h1,h2)-> (try (find_rpair h1) with Normalised -> (find_rpair h2))
|    AndEL(gamma,p,q,h1)-> if ((get_name h1)="AndI") then t else (find_rpair h1)
|    AndER(gamma,p,q,h1)-> if ((get_name h1)="AndI") then t else (find_rpair h1)
|    OrIL(gamma,p,q,h1)-> (find_rpair h1)
|    OrIR(gamma,p,q,h1)-> (find_rpair h1)
|    OrE(gamma,p,q,r,h1,h2,h3)-> if (((get_name h1)="OrIL")||((get_name h1)="OrIR")) then t else (try (find_rpair h1) with Normalised -> (try (find_rpair h2) with Normalised-> (find_rpair h3)))
;;

let get_inner_tree t n = match t with
    ImpI(gamma,p,q,h1)-> h1
|    AndI(gamma,p,q,h1,h2)-> (if (n=0) then h1 else h2)
|    OrIL(gamma,p,q,h1)-> h1
|    OrIR(gamma,p,q,h1)-> h1
;;

let simplify1 t = match t with
    ImpE(gamma,p,q,h1,h2)-> (graft (get_inner_tree h1 0) ([h2]))
|    AndEL(gamma,p,q,h1)-> (get_inner_tree h1 0)
|    AndER(gamma,p,q,h1)-> (get_inner_tree h1 1)
|    OrE(gamma,p,q,r,h1,h2,h3)-> (if ((get_name h1)="OrIL") then (graft h2 [(get_inner_tree h1 0)]) else (graft h3 [(get_inner_tree h1 0)]))
;;


let rec find_and_replace t= match t with
    Hyp(gamma,p)-> Hyp(gamma,p)
|    TI(gamma)->  TI(gamma)
|    ImpI(gamma,p,q,h1)-> ImpI(gamma,p,q, (find_and_replace h1) )
|    ImpE(gamma,p,q,h1,h2)-> if ((get_name h1)="ImpI") then (find_and_replace (simplify1 t)) else ((ImpE(gamma,p,q,(find_and_replace h1),(find_and_replace h2))) )
|    NotI(gamma,p,h1)-> NotI(gamma,p,(find_and_replace h1))
|    NotC(gamma,p,h1)-> NotC(gamma,p,(find_and_replace h1))
|    AndI(gamma,p,q,h1,h2)-> AndI(gamma,p,q,(find_and_replace h1),(find_and_replace h2))
|    AndEL(gamma,p,q,h1)-> if ((get_name h1)="AndI") then (find_and_replace (simplify1 t)) else (AndEL(gamma,p,q,(find_and_replace h1)))
|    AndER(gamma,p,q,h1)-> if ((get_name h1)="AndI") then (find_and_replace (simplify1 t)) else (AndER(gamma,p,q,(find_and_replace h1)))
|    OrIL(gamma,p,q,h1)-> OrIL(gamma,p,q,(find_and_replace h1))
|    OrIR(gamma,p,q,h1)-> OrIR(gamma,p,q,(find_and_replace h1))
|    OrE(gamma,p,q,r,h1,h2,h3)-> if (((get_name h1)="OrIL")||((get_name h1)="OrIR")) then (find_and_replace (simplify1 t)) else (OrE(gamma,p,q,r,(find_and_replace h1),(find_and_replace h2),(find_and_replace h3)))
;;


let rec normalise t = try (let x=(find_rpair t) in (normalise (find_and_replace t))) with Normalised->t;;