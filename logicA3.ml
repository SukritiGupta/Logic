type prop = T | F | L of string 
| Not of prop| And of prop * prop | Or of prop * prop 
| Impl of prop * prop | Iff of prop * prop;;

type ndprooftree = Hyp of prop list * prop| TI of prop list| ImpI prop list * prop * prop * ndprooftree |
ImpE prop list * prop * prop * ndprooftree * ndprooftree | NotI prop list * prop * ndprooftree |
NotC prop list * prop * ndprooftree | AndI prop list * prop * prop * ndprooftree * ndprooftree| AndEL prop list * prop * prop * ndprooftree|
AndER prop list * prop * prop * ndprooftree | OrIL prop list * prop * prop * ndprooftree|
OrIR prop list * prop * prop * ndprooftree | 
OrE prop list * prop * prop * prop * ndprooftree * ndprooftree * ndprooftree
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

list_subset l1 l2 = match l2 with
    [] -> true
|    x::xs-> if (member x l1) then (list_subset l1 xs) else false
;;

list_equal l1 l2 = (list_subset l1 l2) && (list_subset l2 l1);;



let rec valid_ndprooftree t = match t with
    Hyp(gamma,p)-> (member p gamma)
|    TI(gamma)-> T
|    ImpI(gamma,p,q,h1)-> (valid_ndprooftree h1) && (q=(get_judgement h1)) && (list_equal (get_gamma h1) (union gamma [p])) && (not(member gamma p))
|    ImpE(gamma,p,q,h1,h2)->(valid_ndprooftree h1) && (valid_ndprooftree h2) && (Impl(p,q)=(get_judgement h1)) && (p=(get_judgement h2)) && (list_equal gamma (get_gamma h1)) && (list_equal gamma (get_gamma h2))
|    NotI(gamma,p,h1)-> (valid_ndprooftree h1) && (F=(get_judgement h1)) && (list_equal gamma (get_gamma h1))
|    NotC(gamma,p,h1)-> (valid_ndprooftree h1) && (F=(get_judgement h1)) &&(not(member (Not(p)) gamma)) && (list_equal (get_gamma h1) (union gamma [Not(p)]))
|    AndI(gamma,p,q,h1,h2)-> (valid_ndprooftree h1) && (valid_ndprooftree h2) && (p=(get_judgement h1)) && (q=(get_judgement h2)) && (list_equal gamma (get_gamma h1)) && (list_equal gamma (get_gamma h2))
|    AndEL(gamma,p,q,h1)-> (valid_ndprooftree h1) && (And(p,q)=(get_judgement h1)) && (list_equal gamma (get_gamma h1))
|    AndER(gamma,p,q,h1)-> (valid_ndprooftree h1) && (And(p,q)=(get_judgement h1)) && (list_equal gamma (get_gamma h1))
|    OrIL(gamma,p,q,h1)-> (valid_ndprooftree h1) && (p=(get_judgement h1)) && (list_equal gamma (get_gamma h1))
|    OrIR(gamma,p,q,h1)-> (valid_ndprooftree h1) && (q=(get_judgement h1)) && (list_equal gamma (get_gamma h1))
|    OrE(gamma,p,q,r,h1,h2,h3)-> (valid_ndprooftree h1) && (valid_ndprooftree h2) && (valid_ndprooftree h3) && (Or(p,q)=(get_judgement h1)) && (r=(get_judgement h2)) && (r=(get_judgement h3)) && 
(list_equal gamma (get_gamma h1)) && (list_equal (get_gamma h1) (union gamma [p])) && (list_equal (get_gamma h1) (union gamma [q]))
;;

let rec pad t l = match t with
    Hyp(gamma,p)-> Hyp((union gamma l),p)
|    TI(gamma)->   TI((union gamma l))
|    ImpI(gamma,p,q,h1)->  ImpI((union gamma l),p,q,(pad h1 l))
|    ImpE(gamma,p,q,h1,h2)->  ImpE((union gamma l),p,q,(pad h1 l),(pad h2 l))
|    NotI(gamma,p,h1)->  NotI((union gamma l),p,(pad h1 l))
|    NotC(gamma,p,h1)->  NotC((union gamma l),p,(pad h1 l))
|    AndI(gamma,p,q,h1,h2)->  AndI((union gamma l),p,q,(pad h1 l),(pad h2 l))
|    AndEL(gamma,p,q,h1)->  AndEL((union gamma l),p,q,(pad h1 l))
|    AndER(gamma,p,q,h1)->  AndER((union gamma l),p,q,(pad h1 l))
|    OrIL(gamma,p,q,h1)->  OrIL((union gamma l),p,q,(pad h1 l))
|    OrIR(gamma,p,q,h1)->  OrIR((union gamma l),p,q,(pad h1 l))
|    OrE(gamma,p,q,r,h1,h2,h3)->  OrE((union gamma l),p,q,r,(pad h1 l),(pad h2 l),(pad h3 l))
;;


(* Taken special care of change in gamma in some functions *)
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

and rec replace p l gamma_new = match l with
| [] -> (if (member p gamma_new) then Hyp(gamma_new,p) else raise Proof_not_given)
| x::xs -> (if (p=(get_judgement x)) then (graft_help x [] gamma_new) else (replace p xs))
;; 

let head l = match l with x::xs->x;;

let graft t l =  (if l=[] then t else (let gamma_new= (get_gamma (head l)) in (graft_help t l gamma_new)));;

let rec get_actual_not_generated t gen = match t with
    Hyp(gamma,p)-> if (member p gen) then [] else [p]
|    TI(gamma)-> []
|    ImpI(gamma,p,q,h1)-> (get_actual_not_generated h1 (union gen [p]))
|    ImpE(gamma,p,q,h1,h2)->(union (get_actual_not_generated h1 gen) (get_actual_not_generated h2 gen))
|    NotI(gamma,p,h1)->(get_actual_not_generated h1 gen)
|    NotC(gamma,p,h1)->(get_actual_not_generated h1 (union gen [Not(p)]))
|    AndI(gamma,p,q,h1,h2)->(union (get_actual_not_generated h1 gen) (get_actual_not_generated h2 gen))
|    AndEL(gamma,p,q,h1)->(get_actual_not_generated h1 gen)
|    AndER(gamma,p,q,h1)->(get_actual_not_generated h1 gen)
|    OrIL(gamma,p,q,h1)->(get_actual_not_generated h1 gen)
|    OrIR(gamma,p,q,h1)->(get_actual_not_generated h1 gen)
|    OrE(gamma,p,q,r,h1,h2,h3)->(union (union (get_actual_not_generated h1 gen) (get_actual_not_generated h2 (union gen [p]))) (get_actual_not_generated h2 (union gen [q])))
;;

let rec prune_helper t gamma_new= match t with
    Hyp(gamma,p)->  Hyp(gamma_new,p)
|    TI(gamma)->   TI(gamma_new)
|    ImpI(gamma,p,q,h1)->  ImpI(gamma_new,p,q,(prune_helper h1 (union gamma_new [p])))
|    ImpE(gamma,p,q,h1,h2)->  ImpE(gamma_new,p,q,(prune_helper h1 gamma_new),(prune_helper h2 gamma_new))
|    NotI(gamma,p,h1)->  NotI(gamma_new,p,(prune_helper h1 gamma_new))
|    NotC(gamma,p,h1)->  NotC(gamma_new,p,(prune_helper h1 (union gamma_new [Not(p)])))
|    AndI(gamma,p,q,h1,h2)->  AndI(gamma_new,p,q,(prune_helper h1 gamma_new),(prune_helper h2 gamma_new))
|    AndEL(gamma,p,q,h1)->  AndEL(gamma_new,p,q,(prune_helper h1 gamma_new))
|    AndER(gamma,p,q,h1)->  AndER(gamma_new,p,q,(prune_helper h1 gamma_new))
|    OrIL(gamma,p,q,h1)->  OrIL(gamma_new,p,q,(prune_helper h1 gamma_new))
|    OrIR(gamma,p,q,h1)->  OrIR(gamma_new,p,q,(prune_helper h1 gamma_new))
|    OrE(gamma,p,q,r,h1,h2,h3)->  OrE(gamma_new,p,q,r,(prune_helper h1 gamma_new),(prune_helper h2 (union gamma_new [p])),(prune_helper h3 (union gamma_new [q])))
;;

let prune t = let gamma_new=(get_actual_not_generated t []) in (prune_helper t gamma_new);;


