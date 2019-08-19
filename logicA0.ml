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


