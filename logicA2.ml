type prop = T | F | L of string 
| Not of prop| And of prop * prop | Or of prop * prop 
| Impl of prop * prop | Iff of prop * prop;;

type leaf = Ass of prop list * prop | K of prop list * prop * prop 
| S of prop list * prop * prop * prop | R of prop list * prop * prop ;;

type hprooftree = MP of prop list * prop * prop * hprooftree * hprooftree | Lf of leaf;;

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
| S(gamma,p,q,r) -> Impl(Impl(p,(Impl(q,r))) , (Impl((Impl(p,q)) , (Impl(p,r)))))
| R(gamma,p,q) -> Impl((Impl(Not(p),Not(q))),Impl((Impl(Not(p),q),p)))
;;

let get_prop h = match h with
MP(gamma, p,q, h1, h2) -> q
| Lf(x) -> (get_main_prop x)
;;

let get_gamma h = match h with
| MP(gamma, p,q, h1, h2) -> gamma
| Lf(Ass(gamma, p)) -> gamma
| Lf(K(gamma,p,q)) -> gamma
| Lf(S(gamma,p,q,r)) -> gamma
| Lf(R(gamma,p,q)) -> gamma
;;

let rec valid_hprooftree t = match t with
| Lf(Ass(x,p)) -> (member p x)
| Lf(_) -> true
| MP(gamma, p,q, h1, h2) -> ( (Impl(p,q)=(get_prop h1)) && (p=(get_prop h2))  && (valid_hprooftree h1) && (valid_hprooftree h2)  &&  ((get_gamma h1)=(gamma))  &&   ((get_gamma h2)=(gamma)))
;;

let rec pad h l = match h with
| MP(gamma, p,q, h1, h2) -> MP( (union gamma l), p,q, (pad h1 l), (pad h2 l))
| Lf(Ass(gamma, p)) -> Lf(Ass((union gamma l), p))
| Lf(K(gamma,p,q)) -> Lf(K((union gamma l),p,q))
| Lf(S(gamma,p,q,r)) -> Lf(S((union gamma l),p,q,r))
| Lf(R(gamma,p,q)) -> Lf(R((union gamma l),p,q))
;;

let rec get_all_prop h = match h with
| MP(gamma, p,q, h1, h2) -> (get_all_prop h1)@(get_all_prop h2)
| Lf(Ass(gamma, p)) -> [p]
| Lf(_) -> []
;;

let rec put_gamma h newgamma = match  h with
| MP(gamma, p,q, h1, h2) -> MP( newgamma, p,q, (put_gamma h1 newgamma), (put_gamma h2 newgamma))
| Lf(Ass(gamma, p)) -> Lf(Ass(newgamma, p))
| Lf(K(gamma,p,q)) -> Lf(K(newgamma,p,q))
| Lf(S(gamma,p,q,r)) -> Lf(S(newgamma,p,q,r))
| Lf(R(gamma,p,q)) -> Lf(R(newgamma,p,q))
;;

let prune h = ( let newgamma= (get_all_prop h) in (put_gamma h newgamma));;

exception Proof_not_given;;
exception Prop_not_in_gamma;;

let rec replace p l = match l with
| [] -> raise Proof_not_given
| x::xs -> (if (p=(get_prop x)) then x else (replace p xs))
;;

let rec modify h l = match h with
| MP(gamma, p,q, h1, h2) -> MP(gamma, p,q, (modify h1 l), (modify h2 l))
| Lf(Ass(gamma, p)) -> (replace p l)
| Lf(x) -> Lf(x)
;;

let head = function 
x::xs->x;;

let graft h l =  (if l=[] then h else (let newgamma= (get_gamma (head l)) in ( let interm=(put_gamma h newgamma) in (modify interm l))));;

let rec remove e l = match l with
| [] -> raise Prop_not_in_gamma
| x::xs -> if (x=e) then xs else ([x]@(remove e xs))
;;

let special_tree  gamma  p = MP(gamma,     Impl(p,Impl(Impl(L("Any_prop"),p), p)) ,     Impl(Impl(p,Impl(L("Any_prop"),p)),  Impl(p,p))     ,   
 Lf(S(gamma,p,Impl(L("Any_prop"),p),p)),
 Lf(K(gamma, p, Impl(L("Any_prop"),p)))      
);;


let rec dedthm p h = let q=(get_prop h) in (  if (p=q) then 

(let temp = ( match h with
| Lf(Ass(gamma, p1)) -> (remove p gamma) 
| Lf(K(gamma,p1,q1)) -> (remove p gamma) 
| Lf(S(gamma,p1,q1,r)) -> (remove p gamma) 
| Lf(R(gamma,p1,q1)) -> 	(remove p gamma) 
| MP(gamma, r,q1, h1, h2) -> (remove p gamma) 
) in (MP(temp,Impl(p,Impl(L("Any_prop"),p)) ,Impl(p,p),(special_tree temp p),Lf(K(temp, p, L("Any_prop"))))))

else ( match h with
| Lf(Ass(gamma, p1)) ->let temp=(remove p gamma) in (MP(temp, p1 ,Impl(p,p1) , Lf(K(temp, p1,p)), Lf(Ass(temp,p1))    ))
| Lf(K(gamma,p1,q1)) -> let temp=(remove p gamma) in (MP(temp, Impl(p1,Impl(q1,p1)) ,Impl(p,Impl(p1,Impl(p1,q1))) , Lf(K(temp,  Impl(p1,Impl(q1,p1)) ,p)), Lf( K(temp,p1,q1) )    ))
| Lf(S(gamma,p1,q1,r)) -> let temp=(remove p gamma) in (MP(temp,       Impl(Impl(p1,(Impl(q1,r))) , (Impl((Impl(p1,q1)) , (Impl(p1,r)))))     ,Impl(p,    Impl(Impl(p1,(Impl(q1,r))) , (Impl((Impl(p1,q1)) , (Impl(p1,r)))))  ) , Lf(K(temp, Impl(Impl(p1,(Impl(q1,r))) , (Impl((Impl(p1,q1)) , (Impl(p1,r))))) ,p)),      Lf( S(temp,p1,q1,r)  )    ))
| Lf(R(gamma,p1,q1)) -> let temp=(remove p gamma) in (MP(temp,   Impl((Impl(Not(p1),Not(q1))),Impl((Impl(Not(p1),q1),p1)))    ,Impl(p,    Impl((Impl(Not(p1),Not(q1))),Impl((Impl(Not(p1),q1),p1)))   ) , Lf(K(temp,   Impl((Impl(Not(p1),Not(q1))),Impl((Impl(Not(p1),q1),p1)))  ,p)), Lf(  R(temp,p1,q1)  )    ))
| MP(gamma, r,q1, h1, h2) -> let temp = (remove p gamma) in (MP(temp ,Impl(p,r) ,Impl(p,q),MP(temp,Impl(p,(Impl(r,q))),Impl((Impl(p,r)),Impl(p,q)), Lf(S(temp,p,r,q)),(dedthm p h1)) ,(dedthm p h2)))
))
;;

 
(*
let p = Not(Impl(T,T));;
let b=(dedthm  p  (Lf(Ass([p],p))));;
val b : hprooftree =
MP ([], Impl (Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T)))),
 Impl (Not (Impl (T, T)), Not (Impl (T, T))),
 MP ([],
  Impl (Not (Impl (T, T)),
   Impl (Impl (L "Any_prop", Not (Impl (T, T))), Not (Impl (T, T)))),
  Impl (Impl (Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T)))),
   Impl (Not (Impl (T, T)), Not (Impl (T, T)))),
  Lf
   (S ([], Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T))),
     Not (Impl (T, T)))),
  Lf (K ([], Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T)))))),
 Lf (K ([], Not (Impl (T, T)), L "Any_prop")))


# valid_hprooftree (dedthm  p  (Lf(Ass([p],p))));;
- : bool = true

valid_hprooftree (Lf(Ass([p],p)));;
- : bool = true

# graft (Lf(Ass([p],p))) [b];;
Exception: Proof_not_given.


graft (Lf(Ass([Impl(p,p)], Impl(p,p) ))) [b];;

# b=graft (Lf(Ass([Impl(p,p)], Impl(p,p) ))) [b];;
- : bool = true

let pdummy= Impl(T,T);;
let c= MP ([pdummy], Impl (Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T)))),
 Impl (Not (Impl (T, T)), Not (Impl (T, T))),
 MP ([pdummy],
  Impl (Not (Impl (T, T)),
   Impl (Impl (L "Any_prop", Not (Impl (T, T))), Not (Impl (T, T)))),
  Impl (Impl (Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T)))),
   Impl (Not (Impl (T, T)), Not (Impl (T, T)))),
  Lf
   (S ([pdummy], Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T))),
     Not (Impl (T, T)))),
  Lf (K ([pdummy], Not (Impl (T, T)), Impl (L "Any_prop", Not (Impl (T, T)))))),
 Lf (K ([pdummy], Not (Impl (T, T)), L "Any_prop")));;

# b=(prune c);;
- : bool = true

c=(pad b [pdummy]);;
- : bool = true

let q= L("x");;
let px=Impl(T,q);;
let my_proof=MP([px;pdummy;Impl(px,q)],px,q , Lf(Ass([px;pdummy;Impl(px,q)],Impl(px,q)))  ,  Lf(Ass([px;pdummy;Impl(px,q)],px))  );;

(* dedthm px my_proof;; *)

dedthm (Impl(px,q)) my_proof;;

- : hprooftree =
MP ([Impl (T, L "x"); Impl (T, T)],
 Impl (Impl (Impl (T, L "x"), L "x"), Impl (T, L "x")),
 Impl (Impl (Impl (T, L "x"), L "x"), L "x"),
 MP ([Impl (T, L "x"); Impl (T, T)],
  Impl (Impl (Impl (T, L "x"), L "x"), Impl (Impl (T, L "x"), L "x")),
  Impl (Impl (Impl (Impl (T, L "x"), L "x"), Impl (T, L "x")),
   Impl (Impl (Impl (T, L "x"), L "x"), L "x")),
  Lf
   (S ([Impl (T, L "x"); Impl (T, T)], Impl (Impl (T, L "x"), L "x"),
     Impl (T, L "x"), L "x")),
  MP ([Impl (T, L "x"); Impl (T, T)],
   Impl (Impl (Impl (T, L "x"), L "x"),
    Impl (L "Any_prop", Impl (Impl (T, L "x"), L "x"))),
   Impl (Impl (Impl (T, L "x"), L "x"), Impl (Impl (T, L "x"), L "x")),
   MP ([Impl (T, L "x"); Impl (T, T)],
    Impl (Impl (Impl (T, L "x"), L "x"),
     Impl (Impl (L "Any_prop", Impl (Impl (T, L "x"), L "x")),
      Impl (Impl (T, L "x"), L "x"))),
    Impl
     (Impl (Impl (Impl (T, L "x"), L "x"),
       Impl (L "Any_prop", Impl (Impl (T, L "x"), L "x"))),
     Impl (Impl (Impl (T, L "x"), L "x"), Impl (Impl (T, L "x"), L "x"))),
    Lf
     (S ([Impl (T, L "x"); Impl (T, T)], Impl (Impl (T, L "x"), L "x"),
       Impl (L "Any_prop", Impl (Impl (T, L "x"), L "x")),
       Impl (Impl (T, L "x"), L "x"))),
    Lf
     (K ([Impl (T, L "x"); Impl (T, T)], Impl (Impl (T, L "x"), L "x"),
       Impl (L "Any_prop", Impl (Impl (T, L "x"), L "x"))))),
   Lf
    (K ([Impl (T, L "x"); Impl (T, T)], Impl (Impl (T, L "x"), L "x"),
      L "Any_prop")))),
 MP ([Impl (T, L "x"); Impl (T, T)], Impl (T, L "x"),
  Impl (Impl (Impl (T, L "x"), L "x"), Impl (T, L "x")),
  Lf
   (K ([Impl (T, L "x"); Impl (T, T)], Impl (T, L "x"),
     Impl (Impl (T, L "x"), L "x"))),
  Lf (Ass ([Impl (T, L "x"); Impl (T, T)], Impl (T, L "x")))))

  # valid_hprooftree (dedthm (Impl(px,q)) my_proof);;
- : bool = true
 *)