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
			(let v0=(build tT tH t (i+1) temp1 n) and v1=(build tT tH t (i+1) temp2 n) in (mk tT tH i v1 v0)));;

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
else if (((u1=1)||(u1=0))&&((u2=1)||(u2=0))) then (let u=(boolt op u1 u2) in ((Hashtbl.add tG ([u1;u2]) u);u)) else
	let a=(List.nth (Hashtbl.find tT1 u1) 0) and b=(List.nth (Hashtbl.find tT2 u2) 0) in 
	if (a=b) then let u=(mk tT tH a (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 1) (List.nth (Hashtbl.find tT2 u2) 1) tG tT1 tT2)  (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 2) (List.nth (Hashtbl.find tT2 u2) 2) tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u) else
	if (a<b) then (let u=(mk tT tH a (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 1) u2 tG tT1 tT2)  (apply tT tH op (List.nth (Hashtbl.find tT1 u1) 2) u2 tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u)) else
	(let u=(mk tT tH b (apply tT tH op u1 (List.nth (Hashtbl.find tT2 u2) 1) tG tT1 tT2)  (apply tT tH op u1 (List.nth (Hashtbl.find tT2 u2) 2) tG tT1 tT2)) in ((Hashtbl.add tG ([u1;u2]) u);u))
;;

let rec restrict tT tH u j b = let a=(List.nth (Hashtbl.find tT u) 0) in 
	if (a>j) then u else
	if (a<j) then (mk tT tH a (restrict tT tH (List.nth (Hashtbl.find tT u) 1) j b) (restrict tT tH (List.nth (Hashtbl.find tT u) 2) j b))
else if (b=0) then (restrict tT tH (List.nth (Hashtbl.find tT u) 1) j b)
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


(* ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- *)

let rec nnf = function
	T-> T
	| Not(T)-> F
	| F-> F
	| Not(F)-> T
    | L(x) -> L(x)
    | Not(L(x)) -> Not(L(x))
  	| And(x,y) -> And((nnf x), (nnf y))
  	| Not(And(x,y)) -> Or((nnf (Not(x))), (nnf (Not(y))))
  	| Or(x,y) -> Or((nnf x), (nnf y))
  	| Not(Or(x,y)) -> And((nnf (Not(x))), (nnf (Not(y))))
  	| Impl(x,y) -> Or((nnf (Not(x))), (nnf y))
  	| Not(Impl(x,y)) -> And((nnf x), (nnf (Not(y))))
  	| Iff(x,y) -> Or((And((nnf x),(nnf (y)))),(And((nnf (Not(x))),(nnf (Not(y))))))
  	| Not(Iff(x,y)) -> Or((And((nnf x),(nnf (Not(y))))),(And((nnf (Not(x))),(nnf y))))
  	| Not(Not(x)) -> (nnf x)
  ;;



let rec dnf_help = function
	T -> T
	| F -> F
	| L(x) -> L(x)
	| Not(L(x)) -> Not(L(x))
	| And(x, Or(y,z)) -> Or((dnf_help (And(x,y))),(dnf_help (And(x,z))))
	| And(Or(x,y), z) -> Or((dnf_help (And(x,z))),(dnf_help (And(y,z))))
	| And(x,y) -> And((dnf_help x),(dnf_help y))
	| Or(x,y) -> Or((dnf_help x),(dnf_help y))
;;



let dnf p = let s=ref (dnf_help (nnf p)) in (let quit_loop=ref false in (while not !quit_loop do let j=(dnf_help (!s)) in (if j=(!s) then quit_loop:=true else s:=j) done);(!s));;

let rec cnf_help = function
	T -> T
	| F -> F
	| L(x) -> L(x)
	| Not(L(x)) -> Not(L(x))
	| And(x,y) -> And((cnf_help x),(cnf_help y))
	| Or(x, And(y,z)) -> And((cnf_help (Or(x,y))),(cnf_help (Or(x,z))))
	| Or(And(x, y),z) -> And((cnf_help (Or(x,z))),(cnf_help (Or(y,z))))
	| Or(x,y) -> Or((cnf_help x),(cnf_help y))
;;

let cnf p = let s=ref (cnf_help (nnf p)) in (let quit_loop=ref false in (while not !quit_loop do let j=(cnf_help (!s)) in (if j=(!s) then quit_loop:=true else s:=j) done);(!s));;


let vx1 = L(1);;
let vx2 = L(2);;
let vx3 = L(3);;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

(* compute NNF, CNF of p1 and Not(p1) *)
let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;


let h1 = Hashtbl.create 10;; 
let t1 = Hashtbl.create 10;;
let pa = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1 0 ([1;-1;-1]);;
Hashtbl.add t1 1 ([1;-1;-1]);;

let tt = build t1 h1 T 1 pa 0;;			(* val tt : int = 1 *)
let tf = build t1 h1 F 1 pa 0;;			(* val tf : int = 0 *)


let h1 = Hashtbl.create 10;; 
let t1 = Hashtbl.create 10;;
let pa = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1 0 ([1;-1;-1]);;
Hashtbl.add t1 1 ([1;-1;-1]);;

let h1' = Hashtbl.create 10;; 
let t1' = Hashtbl.create 10;;
let pa' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1' 0 ([1;-1;-1]);;
Hashtbl.add t1' 1 ([1;-1;-1]);;

let h1'' = Hashtbl.create 10;; 
let t1'' = Hashtbl.create 10;;
let pa'' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1'' 0 ([1;-1;-1]);;
Hashtbl.add t1'' 1 ([1;-1;-1]);;

let tp1 = build t1 h1 p1 1 pa 3;;
let tp1' = build t1' h1' p1' 1 pa 3;;
let tp1'' = build t1' h1' p1'' 1 pa 3;;


let h1 = Hashtbl.create 10;; 
let t1 = Hashtbl.create 10;;
let pa = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1 0 ([1;-1;-1]);;
Hashtbl.add t1 1 ([1;-1;-1]);;

let h1' = Hashtbl.create 10;; 
let t1' = Hashtbl.create 10;;
let pa' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1' 0 ([1;-1;-1]);;
Hashtbl.add t1' 1 ([1;-1;-1]);;

let h1'' = Hashtbl.create 10;; 
let t1'' = Hashtbl.create 10;;
let pa'' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add t1'' 0 ([1;-1;-1]);;
Hashtbl.add t1'' 1 ([1;-1;-1]);;

let tnp1 = build t1 h1 np1 1 pa 3;;
let tnp1' = build t1' h1' np1' 1 pa 3;;
let tnp1'' = build t1' h1' np1'' 1 pa 3;;

(* Testcase #1 *)
tp1 == tp1';;
tp1 == tp1'';;
tnp1 == tnp1';;
tnp1 == tnp1'';;


(* -------------------------------------------------------------------------------------------------------- *)

let tG = Hashtbl.create 10;;

let h1 = Hashtbl.create 10;; 
let tTp1 = Hashtbl.create 10;;
let pa = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add tTp1 0 ([1;-1;-1]);;
Hashtbl.add tTp1 1 ([1;-1;-1]);;

let h1' = Hashtbl.create 10;; 
let tTnp1 = Hashtbl.create 10;;
let pa' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add tTnp1 0 ([1;-1;-1]);;
Hashtbl.add tTnp1 1 ([1;-1;-1]);;

let tH = Hashtbl.create 10;; 
let tT = Hashtbl.create 10;;
let pa' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add tT 0 ([1;-1;-1]);;
Hashtbl.add tT 1 ([1;-1;-1]);;

let tp1 = build tTp1 h1 p1 1 pa 3;;
let tnp1 = build tTnp1 h1' np1 1 pa' 3;;

let tp1anp1 = apply tT tH "AND" 0 0 tG tTp1 tTnp1;;
tp1anp1 == tf;;						(* bool = true *)


(* -------------------------------------------------------------------------------------------------------- *)



let tG = Hashtbl.create 10;;

let h1 = Hashtbl.create 10;; 
let tTp1 = Hashtbl.create 10;;
let pa = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add tTp1 0 ([1;-1;-1]);;
Hashtbl.add tTp1 1 ([1;-1;-1]);;

let h1' = Hashtbl.create 10;; 
let tTnp1 = Hashtbl.create 10;;
let pa' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add tTnp1 0 ([1;-1;-1]);;
Hashtbl.add tTnp1 1 ([1;-1;-1]);;

let tH = Hashtbl.create 10;; 
let tT = Hashtbl.create 10;;
let pa' = Hashtbl.create 10;;
(* init t1 0;; *)
Hashtbl.add tT 0 ([1;-1;-1]);;
Hashtbl.add tT 1 ([1;-1;-1]);;

let tp1 = build tTp1 h1 p1 1 pa 3;;
let tnp1 = build tTnp1 h1' np1 1 pa' 3;;

let tp1onp1 = apply tT tH "OR" 1 1 tG tTp1 tTnp1;;
tp1onp1 == tt;;	

(* --------------------------------------------------------------------------------------------------------------------------------------------------------------- *)