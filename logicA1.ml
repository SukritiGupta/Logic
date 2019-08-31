type prop = T | F | L of string | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type rho = (string * bool) list;;
type node = Node of (prop * bool * bool * bool * rho * int list );;
type tree = T of node * tree list ;;

(* hashtbl se saara?? hashtbl, open_list is complete tree *)

let rec select_node t = match t with
  T(Node(p, b1, true , false, rho, intl) , x) -> (match x with []-> [] | [n1; n2] -> let o1= (select_node n1) in (if (o1=[]) then (select_node n2) else o1)  | [n1]-> (select_node n1))
| T(Node(p, b1, false, false, rho, intl) , x) -> intl@[2]
| T(Node(p, b1, b2, true, rho, intl) , x) -> []
;;

let rec find_assign rho v = match rho with
  []->2
| (var, true)::xs ->(if (var=v) then 1 else (find_assign xs v) )
| (var, false)::xs ->(if (var=v) then 0 else (find_assign xs v) )
(* | x::xs -> (find_assign xs var) *)
;;

let rec pushdown_assign t incr = match t with
  T(Node(p, b1, b2, false, rho, intl) , []) -> T(Node(p, b1, b2, false, (incr::rho), intl) , [])
| T(Node(p, b1, b2, false, rho, intl) , [n1]) -> T(Node(p, b1, b2, false, (incr::rho), intl) , [(pushdown_assign n1 incr)])
| T(Node(p, b1, b2, false, rho, intl) , [n1;n2]) -> T(Node(p, b1, b2, false, (incr::rho), intl) , [(pushdown_assign n1 incr);(pushdown_assign n2 incr)])
| T(Node(p, b1, b2, true, rho, intl) , x) -> T(Node(p, b1, b2, true, rho, intl) , x)
;;

let rec pushdown t l = match t with
  T(Node(p, b1, b2, false, rho, intl) , []) -> (
  				match l with
  				[p',b'] -> T(Node(p, b1, b2, false, rho, intl) ,  [ T(Node(p', b', false, false, rho, (intl@[0]) ), []) ] )
  				|[(p',b');(p'',b'')] -> T(Node(p, b1, b2, false, rho, intl) ,  [ T(Node(p', b', false, false, rho, (intl@[0]) ), []) ;  T(Node(p'', b'', false, false, rho, (intl@[1]) ), [])])   
  				|[(p1,dummy1);(p2,dummy2);(dummyp, false)] ->
			T(Node(p, b1, b2, false, rho, intl) , [  T(Node(p1, false, false, false, rho, (intl@[0]) ), [ T(Node(p2, true, false, false, rho, (intl@[0]) ) , [])] ); 
													 T(Node(p1, true, false, false, rho, (intl@[1]) ), [ T(Node(p2, false, false, false, rho, (intl@[0]) ) , [])] )  ])

				|[(p1,dummy1);(p2,dummy2);(dummyp, true)] ->
			T(Node(p, b1, b2, false, rho, intl) , [  T(Node(p1, true, false, false, rho, (intl@[0]) ), [ T(Node(p2, true, false, false, rho, (intl@[0]) ) , [])] ); 
													 T(Node(p1, false, false, false, rho, (intl@[1]) ), [ T(Node(p2, false, false, false, rho, (intl@[0]) ) , [])] )  ])   )
| T(Node(p, b1, b2, false, rho, intl) , [n1]) -> T(Node(p, b1, b2, false, rho, intl) , [(pushdown n1 l)])
| T(Node(p, b1, b2, false, rho, intl) , [n1;n2]) -> T(Node(p, b1, b2, false, rho, intl) , [(pushdown n1 l);(pushdown n2 l)])
| T(Node(p, b1, b2, true, rho, intl) , x) -> T(Node(p, b1, b2, true, rho, intl) , x)
;;



let rec step_develop t l = match (t,l) with
  (T(Node(p, b1, b2, b3, rho, intl) , n1::nx), 0::xs) -> T(Node(p, b1, b2, b3, rho, intl) , (step_develop n1 xs)::nx)
| (T(Node(p, b1, b2, b3, rho, intl) , [n1;n2]), 1::xs) -> T(Node(p, b1, b2, b3, rho, intl) , [n1;(step_develop n2 xs)])
| (T(Node(p, b1, false, false, rho, intl) , cl), [2]) ->  (
	match (p,b1) with 
	(T,true) | (F, false) -> T(Node(p, b1, true, false, rho, intl) , cl)
	| (T, false) | (F, true) -> T(Node(p, b1, true, true, rho, intl) , cl)
	(* (contrad_up) *)
	| (L(s), true) -> (let o=(find_assign rho s) in (if (o=2) then (pushdown_assign (T(Node(p, b1, true, false, rho, intl) , cl)) (s, true)) 
														else (if (o=1) then (T(Node(p, b1, true, false, rho, intl) , cl)) else (T(Node(p, b1, true, true, rho, intl) , cl)) )))
	| (L(s), false) -> (let o=(find_assign rho s) in (if (o=2) then (pushdown_assign (T(Node(p, b1, true, false, rho, intl) , cl)) (s, false)) 
														else (if (o=0) then (T(Node(p, b1, true, false, rho, intl) , cl)) else (T(Node(p, b1, true, true, rho, intl) , cl)) )))
	| (Not(p'), b1) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p',(not(b1))] )
	| (And(p1,p2), true) -> let interm = (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p1,true]) in (pushdown interm [p2, true])
	| (Or(p1,p2), false) -> let interm = (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p1,false]) in (pushdown interm [p2, false])
	| (Impl(p1,p2), false) -> let interm = (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p1,true]) in (pushdown interm [p2, false])
	| (And(p1,p2), false) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [(p1,false); (p2,false)])
	| (Or(p1,p2), true) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [(p1,true); (p2,true)])
	| (Impl(p1,p2), true) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [(p1,false); (p2,true)])

	| (Iff(p1,p2), false) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl)) [(p1,b1);(p2,b1);(p,false)]   )
	| (Iff(p1,p2), true) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl)) [(p1,b1);(p2,b1);(p,true)]   )
)

| (T(Node(p, b1, true, b3, rho, intl) , cl), []) ->(T(Node(p, b1, true, b3, rho, intl) , cl))
;;

let rec contrad_path t = match t with
T(Node(p, b1, b2, b3, rho, intl) , [])   -> t
| T(Node(p, b1, b2, true, rho, intl) , x)  -> t
| T(Node(p, b1, b2, false, rho, intl) , [n1]) -> (let a= (contrad_path n1) in ( match a with
	T(Node(_,_,_,true,_,_),_) -> (T(Node(p, b1, b2, true, rho, intl) , [a]))
	|T(Node(_,_,_,false,_,_),_) -> (T(Node(p, b1, b2, false, rho, intl) , [a]))
))

| T(Node(p, b1, b2, false, rho, intl) , [n1;n2]) -> (let a1= (contrad_path n1) in ( let a2=(contrad_path n2)  in (match a1 with
	T(Node(_,_,_,true,_,_),_) -> (match a2 with T(Node(_,_,_,true,_,_),_) -> (T(Node(p, b1, b2, true, rho, intl) , [a1;a2]))| _ -> (T(Node(p, b1, b2, false, rho, intl) , [a1;a2])) ) 
	|T(Node(_,_,_,false,_,_),_) -> (T(Node(p, b1, b2, false, rho, intl) , [a1;a2]))
)))
;;


let rec full_develop root = (let interm=(select_node root) in (if (interm=[]) then root else (full_develop (contrad_path (step_develop root interm)))));;
(* let rec temp_develop root = (let interm=(select_node root) in (if (interm=[]) then root else ((contrad_path root))));; *)

let rec send_assign t = match t with
 T(Node(p, b1, b2, true, rho, intl) , x)  -> [[]]
| T(Node(p, b1, b2, false, rho, intl) , []) -> [rho]
| T(Node(p, b1, b2, false, rho, intl) , [n1]) -> (send_assign n1)
| T(Node(p, b1, b2, false, rho, intl) , [n1;n2]) -> (send_assign n1)@(send_assign n2)
;;

let find_assignments root = (send_assign (full_develop root));;

let head = function 
x::xs->x;;

type ret_type = Proof of tree | Assign of rho;;

let check_tautology p = (let l=(find_assignments (T(Node(p,false,false,false,[],[]),[]))) in (if (l=[[]]) then (Proof(full_develop (T(Node(p,false,false,false,[],[]),[])))) else (Assign(head l))  ));;

let check_contradiction p = (let l=(find_assignments (T(Node(p,true,false,false,[],[]),[]))) in (if (l=[[]]) then (Proof(full_develop (T(Node(p,true,false,false,[],[]),[])))) else (Assign(head l))  ));;


let a=And(L("a"),Not(L("a")));;
let b= Impl(a,a);;

(*  
check_contradiction a;;
- : ret_type =
Proof
 (T (Node (And (L "a", Not (L "a")), true, true, true, [], []),
   [T (Node (L "a", true, true, true, [("a", true)], [0]),
     [T (Node (Not (L "a"), true, true, true, [("a", true)], [0; 0]),
       [T (Node (L "a", false, true, true, [("a", true)], [0; 0; 0]), [])])])]))

check_tautology a;;
- : ret_type = Assign [("a", false)]


check_tautology b;;
- : ret_type =
Proof
 (T
   (Node
     (Impl (And (L "a", Not (L "a")), And (L "a", Not (L "a"))), false, true,
      true, [], []),
   [T (Node (And (L "a", Not (L "a")), true, true, true, [], [0]),
     [T (Node (And (L "a", Not (L "a")), false, true, true, [], [0; 0]),
       [T (Node (L "a", true, true, true, [("a", true)], [0; 0; 0]),
         [T
           (Node (Not (L "a"), true, true, true, [("a", true)], [0; 0; 0; 0]),
           [T
             (Node (L "a", false, true, true, [("a", true)], [0; 0; 0; 0; 0]),
             [T
               (Node
                 (L "a", false, false, false, [("a", true)],
                  [0; 0; 0; 0; 0; 0]),
               [])]);
            T
             (Node
               (Not (L "a"), false, true, true, [("a", true)],
                [0; 0; 0; 0; 1]),
             [T
               (Node
                 (L "a", false, true, true, [("a", true)],
                  [0; 0; 0; 0; 1; 0]),
               [T
                 (Node
                   (L "a", true, false, false, [("a", true)],
                    [0; 0; 0; 0; 1; 0; 0]),
                 [])])])])])])])]))
*)



let rec multi_select_node t = match t with
  T(Node(p, b1, true , false, rho, intl) , x) -> (match x with []-> [] | [n1; n2] -> (multi_select_node n1)@(multi_select_node n2)  | [n1]-> (multi_select_node n1))
| T(Node(p, b1, false, false, rho, intl) , x) -> (match x with []-> [intl@[2]] | [n1; n2] -> [intl@[2]]@(multi_select_node n1)@(multi_select_node n2)  | [n1]-> [intl@[2]]@(multi_select_node n1))
| T(Node(p, b1, b2, true, rho, intl) , x) -> []
;;

open List;;
let rec partial_match t1 t2 =match (t1,t2) with
(    T(Node(p,b1,b2,b3,rho1, l), x)            ,       T(Node(phh,b1hh,b2',b3',rho1', lhh), x')         ) -> 

(   if   ((p=phh) && (l=lhh) && (b1=b1hh))   then (if ((((List.length x ) >= (List.length x' ) ) && ((List.length x' ) !=1))||  ((List.length x ) = (List.length x' ) ) ) then
	(
		match x' with 
		[]->true
		| [n1] -> (partial_match (head x) n1)
		| [n1;n2] -> (match x with [a;b] -> ((partial_match a n1) && (partial_match b n2)))
	)
else false)  else false)
|(_,_) -> false
;;

let belongs a2 elem = (mem elem a2);;

let rho_match a1 a2 = (for_all    (belongs a2)     a1) && (for_all    (belongs a1)     a2);;

let rec complete_match t1 t2 =match (t1,t2) with
(    T(Node(p,b1,b2,b3,rho1, l), x)            ,       T(Node(phh,b1hh,b2hh,b3hh,rho1', lhh), x')         ) -> 

(if  ((p=phh) && (l=lhh) && (b1=b1hh) && (b2=b2hh) && (b3=b3hh)) then (if ( ((List.length x ) = (List.length x' ) ) ) then
	(
		match x' with 
		[]->true
		| [n1] -> ((partial_match (head x) n1) && (rho_match rho1 rho1'))
		| [n1;n2] -> (match x with [a;b] -> ((partial_match a n1) && (partial_match b n2)   && (rho_match rho1 rho1') )  )
	)
else false) else false)
|(_,_) -> false
;;


let rec helper t1 t2 = (if (partial_match t1 t2) then (if (complete_match t1 t2) then true else (vtableau t1 t2)) else false)
and 
vtableau t1 t2 =   let pd = (map (step_develop t2) (multi_select_node t2)) in ( exists (helper t1) pd);;



let valid_tableau t = match t with T(Node(p,b1,b2,b3,rho1, l), x) -> (vtableau t (T(Node(p,b1,false,false,[],[]),[])) );;