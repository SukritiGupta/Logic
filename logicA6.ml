type prop = T | F | L of int | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;

let mk tT tH i l h = if (l=h) then l else 
	if (Hashtbl.mem tH ([i;l;h])) then (Hashtbl.find tH ([i;l;h]))
	else (let u=(Hashtbl.length tT) in ((Hashtbl.add tT u [i;l;h]);(Hashtbl.add tH [i;l;h] u);u));;

let rec eval t assign = match t with
T -> true
| F -> false
| L(x)-> (Hashtbl.find assign x)
| Not(t1)-> not(eval t1 partass)
| And(t1,t2) -> ((eval t1 partass) && (eval t2 partass))
| Or(t1,t2)-> ((eval t1 partass) || (eval t2 partass))
| Impl(t1,t2)-> ((not(eval t1 partass)) || (eval t2 partass))
| Iff(t1,t2)-> (let a=(eval t1 partass) and b=(eval t2 partass) in ((not(a)||b) && (not(b)||a)))
;;

//varorder is a hashtbl from var name to int, partass is a Hashtbl between integer to true/false - have to copy
let build tT tH t i partass = 
	if (i>varorder.length) then (if (eval t partass varorder) then 1 else 0)
	else
		let temp1=(Hashtbl.copy partass) and temp2=(Hashtbl.copy partass) in 
			((Hashtbl.add temp1 i true);(Hashtbl.add temp2 i false);
			(let v0=(build tT tH t (i+1) temp1) and v1=(build tT tH t (i+1) temp2) in mk(i,v0,v1)));;

let boolt op u1 u2 = 


let rec apply tT tH op u1 u2 tG tT1 tT2= if (Hashtbl.mem tG ([u1,u2])) then (Hashtbl.find tG ([u1,u2]))
else if (((u1=1)||(u1=0))&&((u2=1)||(u2=0))) then (boolt op u1 u2) else
	let a=(List.nth (Hashtbl.find tT1 u1) 0) and b=(List.nth (Hashtbl.find tT2 u2) 0) in 
	if (a=b) then let u=(mk tT tH a apply(tT tH op (List.nth (Hashtbl.find tT1 u1) 1) (List.nth (Hashtbl.find tT2 u2) 1) tG tT1 tT2)  apply(tT tH op (List.nth (Hashtbl.find tT1 u1) 2) (List.nth (Hashtbl.find tT2 u2) 2) tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u) else
	if (a<b) then let u=(mk tT tH a apply(tT tH op (List.nth (Hashtbl.find tT1 u1) 1) u2 tG tT1 tT2)  apply(tT tH op (List.nth (Hashtbl.find tT1 u1) 2) u2 tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u) else
	let u=(mk tT tH b apply(tT tH op u1 (List.nth (Hashtbl.find tT2 u2) 1) tG tT1 tT2)  apply(tT tH op u1 (List.nth (Hashtbl.find tT2 u2) 2) tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u) 
;;

let rec restrict tT tH u j b = let a=(List.nth (Hashtbl.find tT1 u) 0) in 
	if (a>j) then u else
	if (a<j) then (mk tT tH a restrict(tT tH (List.nth (Hashtbl.find tT1 u) 1) j b) restrict(tT tH (List.nth (Hashtbl.find tT1 u) 2) j b))
else if (a=j && b=0) then (restrict(tT tH (List.nth (Hashtbl.find tT1 u) 1) j b))
		else (restrict(tT tH (List.nth (Hashtbl.find tT1 u) 2) j b))
;;



let rec satcount tT u = if (u=0) then 0 else if (u=1) then 1 else
(()+())

