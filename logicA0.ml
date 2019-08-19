type prop = T | F | L of string | Not of prop| And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;

let rec ht = function
	T->0 
	| F->0
    | L(x) -> 0
    | Not(x) -> 1+ (ht x)
  	| And(x,y) -> 1+ max (ht x) (ht y)
  	| Or(x,y) -> 1+ max (ht x) (ht y)
  	| Impl(x,y) -> 1+ max (ht x) (ht y)
  	| Iff(x,y) -> 1+ max (ht x) (ht y)
  ;;


let rec size = function
	T->1
	| F->1
    | L(x) -> 1
    | Not(x) -> 1+ (size x)
  	| And(x,y) -> 1+  (size x) + (size y)
  	| Or(x,y) -> 1+  (size x) + (size y)
  	| Impl(x,y) -> 1+  (size x) + (size y)
  	| Iff(x,y) -> 1+  (size x) + (size y)
;;


let rec member a l= match l with
	[]-> false
	| x::xs -> if a=x then true else (member a xs)
;;

let rec union l1 l2 = match (l1,l2) with
	([], l2)-> l2
	| (l1, []) -> l1
	| (x::xs, l2) -> if member x l2 then union xs l2 else union xs (x::l2)
;;


let rec letters = function
	T-> []
	| F->[]
    | L(x) -> [x]
    | Not(x) -> letters x
  	| And(x,y) -> union (letters x) (letters y)
  	| Or(x,y) -> union (letters x) (letters y)
  	| Impl(x,y) -> union (letters x) (letters y)
  	| Iff(x,y) -> union (letters x) (letters y)
  ;;	

let rec subprop_at_me p1 p2 = match (p1,p2) with
	(T,T) | (F,F)  -> true
	| (L(x),L(y)) -> if x=y then true else false
	| (Not(x), Not(y)) -> (subprop_at_me x y)
	| (And(x1,y1), And(x2,y2)) -> ((subprop_at_me x1 x2) && (subprop_at_me y1 y2))
	| (Or(x1,y1), Or(x2,y2)) -> ((subprop_at_me x1 x2) && (subprop_at_me y1 y2))
	| (Impl(x1,y1), Impl(x2,y2)) -> ((subprop_at_me x1 x2) && (subprop_at_me y1 y2))
	| (Iff(x1,y1), Iff(x2,y2)) -> ((subprop_at_me x1 x2) && (subprop_at_me y1 y2))
	| _ -> false
;;

let rec concat a l = match l with
	[]->[]
	| [[]]-> [[a]]
	| x::xs -> (a::x)::(concat a xs)
;;


let rec subprop_at p1 p2 = if (subprop_at_me p1 p2) then [[]] else (match p2 with
	| F | T  -> []
	| L(x) -> []
	| Not(x)-> (subprop_at p1 x)
	| And(x,y) -> (concat 0 (subprop_at p1 x))@(concat 1 (subprop_at p1 y))
	| Or(x,y) -> (concat 0 (subprop_at p1 x))@(concat 1 (subprop_at p1 y))
	| Impl(x,y) -> (concat 0 (subprop_at p1 x))@(concat 1 (subprop_at p1 y))
	| Iff(x,y) -> (concat 0 (subprop_at p1 x))@(concat 1 (subprop_at p1 y)))
;;


let rec truth p rho = match p with
	T-> true
	| F->false
    | L(x) -> (rho x)
    | Not(x) -> not(truth x rho)
  	| And(x,y) -> (truth x rho) && (truth y rho)
  	| Or(x,y) -> (truth x rho) || (truth y rho)
  	| Impl(x,y) -> ( (not (truth x rho)) || (truth y rho))
  	| Iff(x,y) -> ((truth x rho) && (truth y rho)) || ((not (truth x rho)) && (not (truth y rho)))
  ;;	


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
  	| Impl(x,y) -> Impl((nnf x), (nnf y))
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


(* Or(Or(And(L("a"), L("b")), And(L("c"), L("d"))), And(L("e"), L("f")));; *)

(* dnf (And(And(Or(L("a"), L("b")), Or(L("c"), L("d"))), Or(L("e"), L("f"))));;
- : prop =
Or
 (Or (Or (And (And (L "a", L "c"), L "e"), And (And (L "b", L "c"), L "e")),
   Or (And (And (L "a", L "d"), L "e"), And (And (L "b", L "d"), L "e"))),
 Or (Or (And (And (L "a", L "c"), L "f"), And (And (L "b", L "c"), L "f")),
  Or (And (And (L "a", L "d"), L "f"), And (And (L "b", L "d"), L "f"))))
 *)


(* # dnf (And(And(Or(L("a"), L("b")), And(L("c"), L("d"))), Or(L("e"), L("f"))));;
- : prop =
Or
 (Or (And (And (L "a", And (L "c", L "d")), L "e"),
   And (And (L "b", And (L "c", L "d")), L "e")),
 Or (And (And (L "a", And (L "c", L "d")), L "f"),
  And (And (L "b", And (L "c", L "d")), L "f"))) *)




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

(* # cnf (Or(Or(And(L("a"), L("b")), And(L("c"), L("d"))), And(L("e"), L("f"))));;
- : prop =
And
 (And (And (Or (Or (L "a", L "c"), L "e"), Or (Or (L "b", L "c"), L "e")),
   And (Or (Or (L "a", L "d"), L "e"), Or (Or (L "b", L "d"), L "e"))),
 And (And (Or (Or (L "a", L "c"), L "f"), Or (Or (L "b", L "c"), L "f")),
  And (Or (Or (L "a", L "d"), L "f"), Or (Or (L "b", L "d"), L "f"))))
 *)