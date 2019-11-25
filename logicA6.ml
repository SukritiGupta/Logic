type prop = T | F | L of string | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;

let mk tT tH i l h = if (l=h) then l else 
	if (Hashtbl.mem tH ([i;l;h])) then (Hashtbl.find tH ([i;l;h]))
	else (let u=(Hashtbl.length tT) in ((Hashtbl.add tT u [i;l;h]);(Hashtbl.add tH [i;l;h] u);u));;


let rec eval t assign varorder= match t with
T -> true
| F -> false
| L(x)-> (Hashtbl.find assign (Hashtbl.find varorder x))
| Not(t1)-> not(eval t1 partass varorder)
| And(t1,t2) -> ((eval t1 partass varorder) && (eval t2 partass varorder))
| Or(t1,t2)-> ((eval t1 partass varorder) || (eval t2 partass varorder))
| Impl(t1,t2)-> ((not(eval t1 partass varorder)) || (eval t2 partass varorder))
| Iff(t1,t2)-> (let a=(eval t1 partass varorder) and b=(eval t2 partass varorder) in ((not(a)||b) && (not(b)||a)))

//varorder is a hashtbl from var name to int, partass is a Hashtbl between integer to true/false - have to copy
let build tT tH t i partass varorder = 
	if (i>varorder.length) then (if (eval t partass varorder) then 1 else 0)
	else
		let temp1=(Hashtbl.copy partass) and temp2=(Hashtbl.copy partass) in 
			((Hashtbl.add temp1 i true);(Hashtbl.add temp2 i false);
			(let v0=(build tT tH t (i+1) temp1 varorder) and v1=(build tT tH t (i+1) temp2 varorder) in mk(i,v0,v1)));;


//varlist is int to string
let rec apply tT tH op u1 u2 tG varlist1 varlist2 = 