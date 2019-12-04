type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type types = Hyp | T_I | Impl_I | Impl_E | N_int | N_cl | And_I | And_El | And_Er | Or_Il | Or_Ir | Or_E;;
type node = Node1 of prop list * prop * types | Node2 of prop list * prop * types * node | Node3 of prop list * prop * types * node * node | Node4 of prop list * prop * types * node * node * node;;
exception Invalid_Tree;;

let rec find_assign lis ter = match lis with
		a::b -> if a = ter then true else find_assign b ter
	|   [] -> false;; 

let extract_prop a = match a with
		Node1(x,b,c) -> b
	|   Node2(x,b,c,d) -> b 
	|   Node3(x,b,c,d,e) -> b
	|   Node4(x,b,c,d,e,f) -> b;;

let extract_gam a = match a with
		Node1(x,b,c) -> x
	|   Node2(x,b,c,d) -> x 
	|   Node3(x,b,c,d,e) -> x
	|   Node4(x,b,c,d,e,f) -> x;;

let rec mods a b c = match a,b with
		Impl(q,w), Impl(e,r) -> if (q = b && w = c) || (e = a && r = c) then true else false
	|	Impl(q,w), x -> if q = b && w = c then true else false
	|	x, Impl(e,r) -> if e = a && r = c then true else false
	|	_, _ -> false;;

let rec join1 lst term = match (lst,term) with
		((a::xs), b) -> if a = b then lst else a::(join1 xs term)
	|   ([], b) -> [b]
	|   (a, _) -> a;;

let rec join lst1 lst2 = match lst2 with
		[]  -> lst1
	|   a::xs -> join (join1 lst1 a) xs;;

let rec find_eq a b = match b with
		[] -> []
	|	x::xs -> if x = a then (find_eq a xs) else x::(find_eq a xs);;

let rec set_eq a b = match a,b with
		[],[] -> true
	|   [],_ -> false
	|   _,[] -> false
	|   x::xs,y -> set_eq (find_eq x xs) (find_eq x y);;

let rec valid_ndprooftree tree = match tree with
		Node1(a,b,c) -> if ((c = T_I) && (b = T)) then true else if (c = Hyp) && (find_assign a b) then true else false
	|   Node2(a,b,c,d) -> let ex = extract_prop d in let gam = extract_gam d in ( 
						match b,c with
								Impl(p,q), Impl_I -> if (set_eq (a@[p]) gam) && (ex = q) then (valid_ndprooftree d) else false 
							|   p, N_int -> if (ex = F && (set_eq gam a)) then (valid_ndprooftree d) else false
							|   p, N_cl -> if (ex = F && (set_eq (a@[Not(p)]) gam)) then (valid_ndprooftree d) else false
							|   p, And_El -> ( match ex with
													And(w,e) -> if (p = w && set_eq gam a) then (valid_ndprooftree d) else false
												|   _ -> false
											)
							|   p, And_Er -> ( match ex with
													And(w,e) -> if (p = e && set_eq gam a) then (valid_ndprooftree d) else false
												|   _ -> false
											)
							|   Or(p,q), Or_Il -> if (ex = p && (set_eq gam a)) then (valid_ndprooftree d) else false
							|   Or(p,q), Or_Ir -> if (ex = q && (set_eq gam a)) then (valid_ndprooftree d) else false
							|   _ -> false
						)
	|   Node3(a,b,c,d,e) -> let ex1 = extract_prop d in let gam1 = extract_gam d in let ex2 = extract_prop e in let gam2 = extract_gam e in( 
						match b,c with
								q, Impl_E -> if (set_eq a gam1) && (set_eq a gam2) && (mods ex1 ex2 q) then (valid_ndprooftree d) && (valid_ndprooftree e) else false 
							|   And(p,q), And_I -> if (set_eq a gam1) && (set_eq a gam2) && ((ex1 = p && ex2 = q) || (ex1 = q && ex2 = p)) then  (valid_ndprooftree d) && (valid_ndprooftree e) else false
							|   _ -> false
						)
	|   Node4(a,b,c,d,e,f) -> let ex1 = extract_prop d in let gam1 = extract_gam d in 
							 let ex2 = extract_prop e in let gam2 = extract_gam e in 
							 let ex3 = extract_prop f in let gam3 = extract_gam f in ( 
						match b,c with
								r, Or_E -> if (set_eq a gam1) then ( 
											match ex1 with 
												Or(p,q)	-> if ((set_eq (a@[p]) gam2) && (set_eq (a@[q]) gam3)) && (ex2 = r && ex3 = r) then (valid_ndprooftree d)&&(valid_ndprooftree e)&&(valid_ndprooftree f) else 
														   if ((set_eq (a@[q]) gam2) && (set_eq (a@[p]) gam3)) && (ex2 = r && ex3 = r) then (valid_ndprooftree d)&&(valid_ndprooftree e)&&(valid_ndprooftree f) else false 
											) else if (set_eq a gam2) then ( 
											match ex2 with 
												Or(p,q)	-> if ((set_eq (a@[p]) gam1) && (set_eq (a@[q]) gam3)) && (ex1 = r && ex3 = r) then (valid_ndprooftree d)&&(valid_ndprooftree e)&&(valid_ndprooftree f) else 
														   if ((set_eq (a@[q]) gam1) && (set_eq (a@[p]) gam3)) && (ex1 = r && ex3 = r) then (valid_ndprooftree d)&&(valid_ndprooftree e)&&(valid_ndprooftree f) else false 
											) else if (set_eq a gam3) then ( 
											match ex3 with 
												Or(p,q)	-> if ((set_eq (a@[p]) gam1) && (set_eq (a@[q]) gam2)) && (ex1 = r && ex2 = r) then (valid_ndprooftree d)&&(valid_ndprooftree e)&&(valid_ndprooftree f) else 
														   if ((set_eq (a@[q]) gam1) && (set_eq (a@[p]) gam2)) && (ex1 = r && ex2 = r) then (valid_ndprooftree d)&&(valid_ndprooftree e)&&(valid_ndprooftree f) else false 
											) else false
							|   _ -> false
						);;

let rec pad tree del = match tree with
		Node1(a,b,c) -> Node1(join a del, b, c)
	|	Node2(a,b,c,d) -> Node2(join a del, b, c, pad d del)
	|	Node3(a,b,c,d,e) -> Node3(join a del, b, c, pad d del, pad e del)
	|	Node4(a,b,c,d,e,f) -> Node4(join a del, b, c, pad d del, pad e del, pad f del);;

let rec find_sub tree l = match tree with
		Node1(a,b,c) -> if (c = Hyp) && ((find_assign l b) == false) && ((find_assign a b) == true) then [b] else []
	|   Node2(a,b,c,d) -> (
 						match c with 
 							Impl_I -> (
 								match b with
 										Impl(x,y) -> find_sub d (l@[x])
 									|   _ -> find_sub d l
 									)
 						|   N_cl -> find_sub d (l@[Not(b)])
 						|   _ -> find_sub d l
 						)
	|   Node3(a,b,c,d,e) -> (find_sub d l)@(find_sub e l)
	|   Node4(a,b,c,d,e,f) -> ( 
 						match c with
 								Or_E -> (
 									let x = extract_prop d in match x with
 											Or(p,q) -> (find_sub d l)@(find_sub e (l@[p]))@(find_sub f (l@[q]))
 										|   _ -> (find_sub d l)@(find_sub e l)@(find_sub f l)
 								)
 							|	_ -> (find_sub d l)@(find_sub e l)@(find_sub f l)
 						);;

let rec replace tree del =  match tree with
 		Node1(a,b,c) -> Node1(del,b,c)
 	|   Node2(a,b,c,d) -> (
 						match c with 
 							Impl_I -> (
 								match b with
 										Impl(x,y) -> Node2(del,b,c,replace d (del@[x]))
 									|   _ -> Node2(del,b,c,replace d del)
 									)
 						|   N_cl -> Node2(del,b,c,replace d (del@[Not(b)]))
 						|   _ -> Node2(del,b,c,replace d del)
 						)
 	|   Node3(a,b,c,d,e) -> Node3(del,b,c,replace d del,replace e del)
 	|   Node4(a,b,c,d,e,f) -> ( 
 						match c with
 								Or_E -> (
 									let x = extract_prop d in match x with
 											Or(p,q) -> Node4(del,b,c,replace d del,replace e (del@[p]),replace f (del@[q]))
 										|   _ -> Node4(del,b,c,replace d del,replace e del,replace f del)
 								)
 							|	_ -> Node4(del,b,c,replace d del,replace e del,replace f del)
 						);;

let rec prune tree = let del = find_sub tree [] in replace tree del;;

let rec find_match tree tree_list = match (tree, tree_list) with
		Node1(a,b,c), [] -> tree 
	|	Node1(a,b,c), x::xs -> if c = Hyp then ( 
							match x with 
							Node1(d,e,f) -> if b = e then Node1(d,e,f) else find_match tree xs
						|	Node2(d,e,f,g) -> if b = e then Node2(d,e,f,g) else find_match tree xs
						|	Node3(d,e,f,g,h) -> if b = e then Node3(d,e,f,g,h) else find_match tree xs
						|	Node4(d,e,f,g,h,i) -> if b = e then Node4(d,e,f,g,h,i) else find_match tree xs
						)else tree;;

let rec replace_del tree tree_list = match tree_list with
		[] -> tree
	|   (Node1(a,b,c))::xs -> replace tree a
	|   (Node2(a,b,c,d))::xs -> replace tree a
	|   (Node3(a,b,c,d,e))::xs -> replace tree a
	|   (Node4(a,b,c,d,e,f))::xs -> replace tree a;;

let rec graft_2 my_tree tree_list = match my_tree with
		Node1(a,b,c) -> find_match my_tree tree_list
	|   Node2(a,b,c,d) -> Node2(a,b,c, graft_2 d tree_list) 
	|   Node3(a,b,c,d,e) -> Node3(a,b,c, graft_2 d tree_list, graft_2 e tree_list) 
	|   Node4(a,b,c,d,e,f) -> Node4(a,b,c, graft_2 d tree_list, graft_2 e tree_list, graft_2 f tree_list);;

let rec graft tree tree_list = let my_tree = replace_del tree tree_list in graft_2 my_tree tree_list;;
								
(* let gamma1 = [L "p"; Impl(L "p", L "q"); Impl(Not(L "p"), Not(L "q"))];;
let gamma2 = [Not(L "p"); Impl(Not(L "p"), L "q"); Impl(L "p", Not(L "q"))];;
let gamma3 = [Impl(Impl(L "p", L "p"), L "q"); Impl(L "p", L "p")];;

let val_tree1 = Node3(gamma1, L "q", Impl_E, Node1(gamma1, L "p", Hyp), Node1(gamma1, Impl(L "p", L "q"), Hyp));;
let inval_tree1 = Node3(gamma2, L "q", Impl_E, Node1(gamma2, L "p", Hyp), Node1(gamma2, Impl(L "p", L "q"), Hyp));;
let val_tree2 = Node3(gamma3, L "q", Impl_E, Node1(gamma3, Impl(Impl(L "p", L "p"), L "q"), Hyp), Node1(gamma3, Impl(L "p", L "p"), Hyp));;
let val_tree3 = Node2(gamma3, (Impl(L "p", L "p")), Impl_I, Node1((gamma3@[L "p"]), L "p", Hyp));;

let test1 = valid_ndprooftree val_tree1;; (* true *)
let test2 = valid_ndprooftree inval_tree1;; (* false *)
let test3 = pad val_tree1 gamma2;;  (* padded tree *)
let test4 = pad inval_tree1 gamma1;; (* padded tree *)
let test5 = valid_ndprooftree test4;; (* true *)
let test6 = prune val_tree1;;
let test6_1 = prune val_tree3;;
let test7 = valid_ndprooftree test6;; (* true *)
let test7_1 = valid_ndprooftree test6_1;; (* true *)
let test9 = valid_ndprooftree val_tree2;; (* true *)
 *)
(* let test10 = graft val_tree2 [Hyp(gamma3, Impl(Impl(L "p", L "p"), L "q")); proof_p_impl_p gamma3 (L "p")];; *)





(* 
(* Test Case 1 - Hyp, ImpInt*)
let a = Node2([], Impl(L "x", L "x"), Impl_I, 
					Node1([L "x"], L "x", Hyp)
			);;
valid_ndprooftree a;;
let b = pad a ([L("y")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;
*)

(* (* Test Case 2 - ImpEli, OrEli*)
let a = Node3([L("y");Impl(L("y"),L("x"))], L("x"), Impl_E, 
					Node1([L("y");Impl(L("y"),L("x"))], Impl(L("y"), L("x")), Hyp), 
					Node1([L("y");Impl(L("y"),L("x"))], L "y", Hyp)
			);;
valid_ndprooftree a;;
let b = pad a ([L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;
let gamma = [Or(L("p"),L("q")); L("p"); L("q"); Impl(L("p"), L("y")); Impl(L("q"), L("y")); Impl(L("p"), L("x"))];;
let gr = Node4(gamma, L "y", Or_E, 
					Node1(gamma, Or(L("p"),L("q")), Hyp), 
					Node3(gamma, L "y", Impl_E, 
								Node1(gamma, Impl(L "p", L "y"), Hyp), 
								Node1(gamma, L "p", Hyp)
						), 
					Node3(gamma, L "y", Impl_E, 
								Node1(gamma, Impl(L "q", L "y"), Hyp), 
								Node1(gamma, L "q", Hyp)
						)
				);;
valid_ndprooftree gr;;
let gr2 = Node2(gamma, Impl(L("y"),L("x")), Impl_I, 
					Node3((L "y")::gamma, L "x", Impl_E, 
								Node1((L "y")::gamma, Impl(L "p", L "x"), Hyp), 
								Node1((L "y")::gamma, L "p", Hyp)
						)
				);;
let d = graft a [gr;gr2];;
valid_ndprooftree d;;
 *)
(* (* Test Case 3 - AndInt, OrIntL, Tr *)
let gamma = [L("p");L("q")];;
let a = Node3(gamma, And(Or(L("p"), L("q")), And(T, L("q"))), And_I, 
				Node2(gamma, Or(L("p"), L("q")), Or_Il, 
						Node1(gamma, L "p", Hyp)
					), 
				Node3(gamma, And(T, L("q")), And_I, 
						Node1(gamma, T, T_I), 
						Node1(gamma, L "q", Hyp)
					)
			);;
valid_ndprooftree a;;
let b = pad a ([L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;
 *)

(* Test Case 4 - AndElL, AndElR *)
(* let gamma = [And(L("r"),And(L("p"), L("q")))];;
let a = Node2(gamma, L("p"), And_El, 
				Node2(gamma, And(L("p"), L("q")), And_Er, 
							Node1(gamma, And(L("r"),And(L("p"), L("q"))), Hyp)
					)
			);;
valid_ndprooftree a;;
let b = pad a ([L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;;
 *)
(* Test Case 5 - OrIntR,NotItu *)

(* let gamma = [L("p"); Not(L("p"))];;
let a = Node2(gamma, Or(L("p"),L("q")), Or_Ir, 
					Node2(gamma, L "q", N_int, 
								Node3(gamma, F , Impl_E, 
											Node1(gamma, Impl(L("p"), F), Hyp), 
											Node1(gamma, L("p"), Hyp)
									)
						)
			);;
valid_ndprooftree a;;
let b = pad a ([L("z")]);;
valid_ndprooftree b;;
let c = prune b;;
valid_ndprooftree c;; *)