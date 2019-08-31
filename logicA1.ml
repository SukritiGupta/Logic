type prop = T | F | L of string | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type rho = (string * bool) list;;
type node = Node of (prop * bool * bool * bool * rho * int list );;
type tree = T of node * tree list ;;

hashtbl se saara?? hashtbl, open_list is complete tree
step_develop that given a selected node on a path, develops the tableau according to the rules  specified above.
T(Node(p, b1, b2, b3, rho, intl) , x)

let rec select_node t = match t with
  T(Node(p, b1, true , false, rho, intl) , x) -> (match x with []-> [] | [n1; n2] -> let o1= (select_node n1) in (if (o1=[]) then (select_node n2) else o1)  | [n1]-> (select_node n1))
| T(Node(p, b1, false, false, rho, intl) , x) -> intl
| T(Node(p, b1, b2, true, rho, intl) , x) -> []
;;

//optional let rec contrad_up t l=

let rec find_assign rho var = match rho with
  []->2
| [(var, true)::xs] ->1
| [(var, false)::xs] ->0
| [x::xs] -> (find_assign xs var)
;;

truth val * explored * contradictary * rho * intl

let rec pushdown_assign t incr = match t with
  T(Node(p, b1, b2, false, rho, intl) , []) -> T(Node(p, b1, b2, false, (incr::rho), intl) , [])
| T(Node(p, b1, b2, false, rho, intl) , [n1]) -> T(Node(p, b1, b2, false, (incr::rho), intl) , [(pushdown_assign n1 incr)])
| T(Node(p, b1, b2, false, rho, intl) , [n1;n2]) -> T(Node(p, b1, b2, false, (incr::rho), intl) , [(pushdown_assign n1 incr)::(pushdown_assign n2 incr)])
| T(Node(p, b1, b2, true, rho, intl) , x) -> T(Node(p, b1, b2, true, rho, intl) , x)
;;


let rec pushdown t l = match t with
  T(Node(p, b1, b2, false, rho, intl) , []) -> (
  				match l with
  				[p',b'] -> T(Node(p, b1, b2, false, rho, intl) ,  [ T(Node(p', b', false, false, rho, (intl::0) ), []) ] )
  				[(p',b');(p'',b'')] -> T(Node(p, b1, b2, false, rho, intl) ,  [ T(Node(p', b', false, false, rho, (intl::0) ), []) ;  T(Node(p'', b'', false, false, rho, (intl::1) ), [])])   )
  				[(p1,dummy1);(p2,dummy2);(dummyp, false)] ->
			T(Node(p, b1, b2, false, rho, intl) , [  T(Node(p1, false, false, false, rho, (intl::0) ), [ T(Node(p2, true, false, false, rho, (intl::0) ) , [])] ); 
													 T(Node(p1, true, false, false, rho, (intl::1) ), [ T(Node(p2, false, false, false, rho, (intl::0) ) , [])] )  ])

				[(p1,dummy1);(p2,dummy2);(dummyp, true)] ->
			T(Node(p, b1, b2, false, rho, intl) , [  T(Node(p1, true, false, false, rho, (intl::0) ), [ T(Node(p2, true, false, false, rho, (intl::0) ) , [])] ); 
													 T(Node(p1, false, false, false, rho, (intl::1) ), [ T(Node(p2, false, false, false, rho, (intl::0) ) , [])] )  ])

| T(Node(p, b1, b2, false, rho, intl) , [n1]) -> T(Node(p, b1, b2, false, rho, intl) , [(pushdown n1 l)])
| T(Node(p, b1, b2, false, rho, intl) , [n1;n2]) -> T(Node(p, b1, b2, false, rho, intl) , [(pushdown n1 l)::(pushdown n2 l)])
| T(Node(p, b1, b2, true, rho, intl) , x) -> T(Node(p, b1, b2, true, rho, intl) , x)
;;

let rec step_develop t l = match (t,l) with
  (T(Node(p, b1, b2, b3, rho, intl) , [n1::nx]), [0::xs]) -> T(Node(p, b1, b2, b3, rho, intl) , [(step_develop n1 xs)::nx])
| (T(Node(p, b1, b2, b3, rho, intl) , [n1::n2]), [1::xs]) -> T(Node(p, b1, b2, b3, rho, intl) , [n1::(step_develop n2 xs)])
| (T(Node(p, b1, false, false, rho, intl) , cl), []) ->  (
	match (p,b1) with 
	(T,true) | (F, false) -> T(Node(p, b1, true, false, rho, intl) , cl)
	| (T, false) | (F, true) -> T(Node(p, b1, true, true, rho, intl) , cl)
	(* (contrad_up) *)
	| (L(s), true) -> (let o=(find_assign rho s) in (if (o=2) then (pushdown_assign (T(Node(p, b1, true, false, rho, intl) , cl)) (var, true)) 
														else (if (o=1) then (T(Node(p, b1, true, false, rho, intl) , cl)) else (T(Node(p, b1, true, true, rho, intl) , cl)) )))
	| (L(s), false) -> (let o=(find_assign rho s) in (if (o=2) then (pushdown_assign (T(Node(p, b1, true, false, rho, intl) , cl)) (var, false)) 
														else (if (o=0) then (T(Node(p, b1, true, false, rho, intl) , cl)) else (T(Node(p, b1, true, true, rho, intl) , cl)) )))

	| (Not(p'), b1) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p',(not(b1))] )
	| (And(p1,p2), true) -> let interm = (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p1,true]) in (pushdown interm [p2, true])
	| (Or(p1,p2), false) -> let interm = (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p1,false]) in (pushdown interm [p2, false])
	| (Impl(p1,p2), false) -> let interm = (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [p1,true]) in (pushdown interm [p2, false])
	| (And(p1,p2), false) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [(p1,false); (p2,false)])
	| (Or(p1,p2), true) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl))  [(p1,true); (p2,true)])

	| (Impl(p1,p2), false) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl)) [(p1,b1);(p2,b1);(p,false)]   )
	| (Impl(p1,p2), true) -> (pushdown (T(Node(p, b1, true, false, rho, intl) , cl)) [(p1,b1);(p2,b1);(p,true)]   )
)

| (T(Node(p, b1, true, b3, rho, intl) , cl), []) ->(T(Node(p, b1, true, b3, rho, intl) , cl))
;;





