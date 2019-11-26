open Hashtbl;;
open List;;

type prop = T | F | L of int | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;

let mk tT tH i l h = if (l=h) then l else 
	if (Hashtbl.mem tH ([i;l;h])) then (Hashtbl.find tH ([i;l;h]))
	else (let u=(Hashtbl.length tT) in ((Hashtbl.add tT u [i;l;h]);(Hashtbl.add tH [i;l;h] u);u));;

let rec eval t partass = match t with
T -> true
| F -> false
| L(x)-> (Hashtbl.find partass x)
| Not(t1)-> not(eval t1 partass)
| And(t1,t2) -> ((eval t1 partass) && (eval t2 partass))
| Or(t1,t2)-> ((eval t1 partass) || (eval t2 partass))
| Impl(t1,t2)-> ((not(eval t1 partass)) || (eval t2 partass))
| Iff(t1,t2)-> (let a=(eval t1 partass) and b=(eval t2 partass) in ((not(a)||b) && (not(b)||a)))
;;

(* //varorder is a hashtbl from var name to int, partass is a Hashtbl between integer to true/false - have to copy ||  n is number of variables*)
let rec build tT tH t i partass n= 
	if (i>n) then (if (eval t partass) then 1 else 0)
	else
		let temp1=(Hashtbl.copy partass) and temp2=(Hashtbl.copy partass) in 
			((Hashtbl.add temp1 i true);(Hashtbl.add temp2 i false);
			(let v0=(build tT tH t (i+1) temp1 n) and v1=(build tT tH t (i+1) temp2 n) in (mk tT tH i v0 v1)));;

let get_bool x = match x with
| 0 -> false
| 1 -> true
;;

let send_int x = match x with
| true -> 1
| false -> 0

let boolt op u1 u2 = let a=(get_bool u1) and b=(get_bool u2) in match op with
| "AND" -> send_int (a && b)
| "OR" -> send_int (a || b)
| "IMPL" -> send_int ((not(a) || b))
| "IFF" -> send_int ((not(a) || b) && (not(b) || a))
;;


let rec apply tT tH op u1 u2 tG tT1 tT2= if (Hashtbl.mem tG ([u1;u2])) then (Hashtbl.find tG ([u1;u2]))
else if (((u1=1)||(u1=0))&&((u2=1)||(u2=0))) then (boolt op u1 u2) else
	let a=(List.nth (Hashtbl.find tT1 u1) 0) and b=(List.nth (Hashtbl.find tT2 u2) 0) in 
	if (a=b) then let u=(mk tT tH a (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 1) (List.nth (Hashtbl.find tT2 u2) 1) tG tT1 tT2)  (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 2) (List.nth (Hashtbl.find tT2 u2) 2) tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u) else
	if (a<b) then (let u=(mk tT tH a (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 1) u2 tG tT1 tT2)  (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 2) u2 tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u)) else
	(let u=(mk tT tH b (apply tT tH op u1 (List.nth (Hashtbl.find tT2 u2) 1) tG tT1 tT2)  (apply tT tH op u1 (List.nth (Hashtbl.find tT2 u2) 2) tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u))
;;

let rec restrict tT tH u j b = let a=(List.nth (Hashtbl.find tT u) 0) in 
	if (a>j) then u else
	if (a<j) then (mk tT tH a (restrict tT tH (List.nth (Hashtbl.find tT u) 1) j b) (restrict tT tH (List.nth (Hashtbl.find tT u) 2) j b))
else if (a=j && b=0) then (restrict tT tH (List.nth (Hashtbl.find tT u) 1) j b)
		else (restrict tT tH (List.nth (Hashtbl.find tT u) 2) j b)
;;

let pow mul a n =
  let rec g p x = function
  | 0 -> x
  | i ->
      g (mul p p) (if i mod 2 = 1 then mul p x else x) (i/2)
  in
  g a 1 n
;;
(* pow ( * ) 2 16;; *)

let rec satcount tT u = if (u=0) then 0 else if (u=1) then 1 else let a = (List.nth (Hashtbl.find tT u) 1) and b=(List.nth (Hashtbl.find tT u) 2) in
(
	(pow ( * ) 2 ((List.nth (Hashtbl.find tT a) 0)-(List.nth (Hashtbl.find tT u) 0)-1))*(satcount tT a)
	+(pow ( * ) 2 ((List.nth (Hashtbl.find tT b) 0)-(List.nth (Hashtbl.find tT u) 0)-1))*(satcount tT b)
)
;;

exception Error;;

let rec anysat tT u = if (u=0) then raise Error else if (u=1) then (Hashtbl.create 10) else
if ((List.nth (Hashtbl.find tT u) 1)=0) then let temp= (anysat tT (List.nth (Hashtbl.find tT u) 2)) in ((Hashtbl.add temp (List.nth (Hashtbl.find tT u) 0) true); temp)
else let temp= (anysat tT (List.nth (Hashtbl.find tT u) 1)) in ((Hashtbl.add temp (List.nth (Hashtbl.find tT u) 0) false); temp)
;;

let rec hashadd x y tbl_list = match tbl_list with
| h::tl -> [(Hashtbl.add h x y)]@(hashadd x y tl)
| _ -> []
;;

let rec allsat tT u = if (u=0) then [] else if (u=1) then [(Hashtbl.create 10)] else let a= (allsat tT (List.nth (Hashtbl.find tT u) 1)) and b=(allsat tT (List.nth (Hashtbl.find tT u) 2)) in
((hashadd (List.nth (Hashtbl.find tT u) 0) false a);(hashadd (List.nth (Hashtbl.find tT u) 0) true b);a@b)
;; 

let rec simplify tT tH tTd d u = if (d=0) then 0 else if (u<=1) then u else if (d=1) 
			then (mk tT tH (List.nth (Hashtbl.find tT u) 0) (simplify tT tH tTd d (List.nth (Hashtbl.find tT u) 1)) (simplify tT tH tTd d (List.nth (Hashtbl.find tT u) 2)))
else
	if ((List.nth (Hashtbl.find tT u) 0) = (List.nth (Hashtbl.find tTd d) 0) ) then
		if ((List.nth (Hashtbl.find tTd d) 1) =0) then (simplify tT tH tTd (List.nth (Hashtbl.find tTd d) 2) (List.nth (Hashtbl.find tT u) 2) )
		else if ((List.nth (Hashtbl.find tTd d) 2) =0) then (simplify tT tH tTd (List.nth (Hashtbl.find tTd d) 1) (List.nth (Hashtbl.find tT u) 1) )
			else (mk tT tH (List.nth (Hashtbl.find tT u) 0)     (simplify tT tH tTd (List.nth (Hashtbl.find tTd d) 1) (List.nth (Hashtbl.find tT u) 1) )     (simplify tT tH tTd (List.nth (Hashtbl.find tTd d) 2) (List.nth (Hashtbl.find tT u) 2) )  )
	else if ((List.nth (Hashtbl.find tT u) 0) > (List.nth (Hashtbl.find tTd d) 0)) then (mk tT tH  (List.nth (Hashtbl.find tTd d) 0)  (simplify tT tH tTd (List.nth (Hashtbl.find tTd d) 1) u )     (simplify tT tH tTd (List.nth (Hashtbl.find tTd d) 2) u )  )
	else (mk tT tH (List.nth (Hashtbl.find tT u) 0)  (simplify tT tH tTd d (List.nth (Hashtbl.find tT u) 1) )     (simplify tT tH tTd d (List.nth (Hashtbl.find tT u) 2))  )
;;