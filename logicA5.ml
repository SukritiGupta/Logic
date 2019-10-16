open List;;
open Hashtbl;;

exception NOT_UNIFIABLE;;
exception FAILED;;

(*Definition of basic types*)
type variable=Var of string;;
type symbol = Sym of string;;
type term = V of variable | Node of symbol*(term list);;
(* type clause = R of term*(term list);; *)

(*helper function defined for check_sig*)
let rec check_sig1 l arr za=  match l with 
	[]-> za
	|(s, a)::rl->
	  	if(a<0) then false
	  else if((List.mem s arr)) then false 
	else ( check_sig1 rl (s::arr)  ((a==0) || za)) ;;

(*returns true if valid signature*)
let check_sig l= (check_sig1 l [] false);;
(*val check_sig : ('a * int) list -> bool = <fun>*)


(*Searching for arity from list*)
let rec find sf l= match l with
	(s,a)::rl-> if(s=sf) then a else (find sf rl)
| []-> -2;; 
(*val find : 'a -> ('a * int) list -> int = <fun>*)

(*returns the and of all the elements in a boolean list*)
(*val andd : bool list -> bool = <fun>*)
let rec andd t= match t with
	a::l-> a && (andd l)
|   [] -> true;;

(*helper function for well formed term; called only if signature is valid*)
let rec wfterm1 sigs t = match t with 
	Node(s,l) -> if((find s sigs) == (List.length l))  then andd( map (wfterm1 sigs) l) else false
| V(x) -> true;;

let wfterm sigs t = if (check_sig sigs) then (wfterm1 sigs t) else false;;
(*val wfterm : (symbol * int) list -> term -> bool = <fun>*)


(*helper function that returns the max element of a list more than the second parameter*)
let rec max t b= match t with
	a::l-> if(a>b) then (max l a) else (max l b)
|   [] -> b;;


(*Height of a term*)
(*val ht : term -> int = <fun>*)
let rec ht t = match t with 
	Node(s, l)-> 1 + (max (map ht l) 0)
|   V(x) -> 0;;

(*helper function returning sum of a list*)
let rec sum t= match t with
	a::l-> a + (sum l)
|   [] -> 0;;

let rec size t = match t with 
	Node(s, l)-> 1 + (sum (map size l))
|   V(x) -> 1;;

let rec union l1 l2= match l2 with
		[]-> l1
	| a::rl -> if(List.mem a l1) then (union l1 rl) else (union (a::l1) rl );; 

(*Returns all the variables used in a term*)
let rec vars t = match t with 
	Node(s, l)-> (List.fold_left union [] (map vars l))
|   V(x) -> [x];;

(*Returns the substituted form of the term*)
let rec subst s t= match t with
	Node(sy, l) -> Node(sy, (map (subst s) l ))
|   V(x) -> if(Hashtbl.mem s x) then (Hashtbl.find s x) else V(x) 
;;


(*Helper function 1 for composition: simply replaces each term in range in of t1 with its substituted form*)
let comp t1 t2 answer= 
	let func a b=  (Hashtbl.replace answer a (subst t2 b))
in (Hashtbl.iter func t1) ;;


(*Helper function 2 for composition: Adds any variable of second substitution that was not in the domain of the first one*)
let composition t1 t2 answer=	
	let rep a b = if(mem answer a) then () else (Hashtbl.add answer a b)
in (Hashtbl.iter rep t2 );;


(*Actual composition function*)
(*val compf : (variable, term) Hashtbl.t ->  (variable, term) Hashtbl.t -> (variable, term) Hashtbl.t = <fun>*)
let compf t1 t2 = let answer=(Hashtbl.create 40) in
				let  t = (comp t1 t2 answer) in ((composition t1 t2 answer); answer);;



(*Function to find the most general unifier*)
(*val mgu : term -> term -> (variable, term) Hashtbl.t = <fun>*)
let rec mgu t1 t2 = let cmgu = (Hashtbl.create 30 )
	in match (t1,t2) with

	(V(x), V(y)) -> if(x=y) then cmgu else ((Hashtbl.add cmgu y (V(x)));cmgu)

|   (V(x), Node(s,[])) -> ((Hashtbl.add cmgu x (Node(s,[])));cmgu)

|   (V(x), Node(s,l))-> if(List.mem x (vars t2)) then raise NOT_UNIFIABLE
						else ((Hashtbl.add cmgu x (Node(s,l)));cmgu)

|   (Node(s,[]), V(x)) -> ((Hashtbl.add cmgu x (Node(s,[])));cmgu)

|   (Node(s,l), V(x))-> if(List.mem x (vars t1)) then raise NOT_UNIFIABLE
						else ((Hashtbl.add cmgu x (Node(s,l)));cmgu)

|  	(Node(s1,[]), Node(s2,[]))-> if(s1=s2) then cmgu
						else raise NOT_UNIFIABLE

|   (Node(s1,[]), Node(s2,l))-> raise NOT_UNIFIABLE

|   (Node(s1,l1), Node(s2,l2))->  if(not(s1=s2)) then  raise NOT_UNIFIABLE
	else 
		let rec unif ct t1 t2 =	(compf ct ((mgu (subst ct  t1) (subst ct t2)))  )
	in (fold_left2 unif cmgu  l1 l2 ) ;;


type literal = P of term| N of term;;

exception NO_UNIF_POSSIBLE;;

(* given two literals; can they be unified? *)
let literal_bool l1 l2 donelist c1i c2i= match (l1,l2) with
| (P(t1),N(t2)) | (N(t1),P(t2))-> if (List.mem (l1,l2,c1i,c2i) donelist ) then raise NO_UNIF_POSSIBLE 
								  else (try ((mgu t1 t2);(l1,l2,c1i,c2i)) with NOT_UNIFIABLE -> raise NO_UNIF_POSSIBLE)
| _ -> raise NO_UNIF_POSSIBLE
;;

let rec literal_list l1 c2 donelist c1i c2i= match c2 with
	[] -> raise NO_UNIF_POSSIBLE
|	x::xs -> try (literal_bool l1 x donelist c1i c2i) with NO_UNIF_POSSIBLE -> (literal_list l1 xs donelist c1i c2i)
;;

(* given two clauses can they be unified for any pair of literals? *)
let rec clause_bool c1 c2 donelist c1i = match c1 with
	[] -> raise NO_UNIF_POSSIBLE
|	x::xs -> try (literal_list x c2 donelist c1i c2) with NO_UNIF_POSSIBLE->(clause_bool xs c2 donelist c1i)
;;

let rec clause_list l donelist= match l with
| [] -> raise NO_UNIF_POSSIBLE
| x::xs -> (match xs with 
	[]->raise NO_UNIF_POSSIBLE 
	| y::ys -> try (clause_bool x y donelist x) with NO_UNIF_POSSIBLE->try (clause_list (x::ys) donelist) with NO_UNIF_POSSIBLE->(clause_list xs donelist)
;;


let one_step_resolution l1 l2 c1 c2 = match (l1,l2) with
(P(t1),N(t2)) | (N(t1),P(t2))-> (let unif=(mgu t1 t2) and c1n=(remove c1 l1) and c2n=(remove c2 l1) in (map (subst unif) (union c1n c2n)))
//remove duplicates created possibly dueto unification


//remove duplicates from initial clauses, complementary pair of predicate removal -> may not be a good idea if there is non identity unification involved