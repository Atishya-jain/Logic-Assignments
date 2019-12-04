type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type types = Hyp | T_I | Impl_I | Impl_E | N_int | N_cl | And_I | And_El | And_Er | Or_Il | Or_Ir | Or_E;;
type node = Node1 of prop list * prop * types | Node2 of prop list * prop * types * node | Node3 of prop list * prop * types * node * node | Node4 of prop list * prop * types * node * node * node;;
exception Invalid_Tree;;
exception Normalised;;

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

(* let rec graft tree tree_list = let my_tree = replace_del tree tree_list in graft_2 my_tree tree_list;; *)
let rec graft tree tree_list = let my_tree = graft_2 tree tree_list in replace_del my_tree tree_list;;


let rec substitute tree pt ot = let pr = extract_prop pt in let gam = extract_gam pt in 
					match tree with
							Node1(a,b,c) -> if (a = gam && pr = b && tree = ot) then pt else tree
						|	Node2(a,b,c,d) -> if (a = gam && pr = b && tree = ot) then pt else Node2(a, b, c, (substitute d pt ot))
						|	Node3(a,b,c,d,e) -> if (a = gam && pr = b && tree = ot) then pt else Node3(a, b, c, substitute d pt ot, substitute e pt ot)
						|	Node4(a,b,c,d,e,f) -> if (a = gam && pr = b && tree = ot) then pt else Node4(a, b, c, substitute d pt ot, substitute e pt ot, substitute f pt ot);;

let rec find_rpair tree = match tree with
		Node1(a,b,c) -> raise (Normalised)
	|	Node2(a,b,c,d) ->   if c = And_El 
							then(
								match d with
										Node3(q,w,e,r,t) -> if e = And_I then ( 
															match w with
																	And(y,u) -> if b = y then tree else find_rpair d
																|   _ -> find_rpair d
															)else find_rpair d
									|	_ -> find_rpair d
							)else if c = And_Er 
							then(
								match d with
										Node3(q,w,e,r,t) -> if e = And_I then ( 
															match w with
																	And(y,u) -> if b = u then tree else find_rpair d
																|	_ -> find_rpair d
															)else find_rpair d
									|	_ -> find_rpair d
							) 
							else find_rpair d
	|	Node3(a,b,c,d,e) -> (
							if c = Impl_E 
							then( 
								let p = extract_prop e in 
								match d with
										Node2(q,w,x,r) -> if x = Impl_I then ( 
															match w with
																	Impl(y,u) -> if b = u && y = p then tree else ( try( find_rpair d ) with Normalised -> find_rpair e )
																|	_ ->  (try( find_rpair d ) with Normalised -> find_rpair e)
															)else  (try( find_rpair d ) with Normalised -> find_rpair e)
									|	_ -> ( try( find_rpair d ) with Normalised -> find_rpair e)
							)else try( find_rpair d ) with Normalised -> find_rpair e
						)
	|   Node4(a,b,c,d,e,f) -> (
							if c = Or_E 
							then( 
								match d with
										Node2(q,w,x,r) ->   if x = Or_Il then tree
															else if x = Or_Ir then tree
															else  (try( find_rpair d ) with Normalised -> (try( find_rpair e ) with Normalised -> find_rpair f))
									|	_ -> (try( find_rpair d ) with Normalised -> (try( find_rpair e ) with Normalised -> find_rpair f))
							)else (try( find_rpair d ) with Normalised -> (try( find_rpair e ) with Normalised -> find_rpair f))
						)

let simplify1 tree = match tree with
		Node1(a,b,c) -> tree
	|   Node2(a,b,c,d) -> if c = And_El 
						  then (
						  		match d with
										Node3(q,w,e,r,t) -> if e = And_I then r else tree
									|	_ -> tree
							)
						  else if c = And_Er
						  then (
						  		match d with
										Node3(q,w,e,r,t) -> if e = And_I then t else tree
									|	_ -> tree
							)
						  else tree
	|   Node3(a,b,c,d,e) -> (
							if c = Impl_E 
							then( 
								let p = extract_prop e in 
								match d with
										Node2(q,w,x,r) -> if x = Impl_I then ( graft r ([e]) ) 
														  else  tree
									|	_ -> tree
							)else tree
						)
	|   Node4(a,b,c,d,e,f) -> (
							if c = Or_E 
							then( 
								match d with
										Node2(q,w,x,r) ->   if x = Or_Il then graft e ([r])
															else if x = Or_Ir then graft f ([r])
															else  tree
									|	_ -> tree
							)else tree
						);;

let rec normalise tree = match tree with
		a -> try( 
				let new_tree = find_rpair tree in 
					let mod_tree = simplify1 new_tree in 
						normalise (substitute tree mod_tree new_tree)
			)with Normalised -> tree;;


let gamma1 = [L "p"; L "q"; Impl(L "p", L "q"); Impl(Not(L "p"), Not(L "q"))];;
let gamma2 = [Not(L "p"); Impl(Not(L "p"), L "q"); Impl(L "p", Not(L "q"))];;
let gamma3 = [Impl(Impl(L "p", L "p"), L "q"); Impl(L "p", L "p")];;

let a = Node2(gamma1, L "p", And_El, Node3(gamma1, And(L "p", L "q"), And_I, Node1(gamma1, L "p", Hyp), Node1(gamma1, L "q", Hyp)));;
let b = Node3(gamma1, L "q", Impl_E, 
			Node2(gamma1, Impl(L "p", L "q"), Impl_I, Node1(gamma1, L "q", Hyp)),
			Node1(gamma1, L "p", Hyp));;
let c = Node4(gamma1, L "p", Or_E, 
			Node2(gamma1, Or(L "p", L "q"), Or_Il, Node1(gamma1, L "p", Hyp)),
			Node1(gamma1, L "p", Hyp), 
			Node1(gamma1, L "p", Hyp));;
let d = Node3(gamma1, L "q", Impl_E, a, Node1(gamma1, Impl(L "p", L "q"), Hyp));;
let e = Node3(gamma1, L "q", Impl_E, c, Node1(gamma1, Impl(L "p", L "q"), Hyp));;
let f = Node2(gamma1, Impl(L "p", L "q"), Impl_I, b);;

let x = find_rpair a;;
let y = find_rpair d;;
x = y;;
let x = find_rpair c;;
let y = find_rpair e;;
x = y;;
let x = find_rpair b;;
let y = find_rpair f;;
x = y;;

simplify1 a;;
simplify1 b;;
simplify1 c;;

let zz = normalise d;;
normalise e;;
normalise f;;

let x = find_rpair d;;
let y = simplify1 x;;
let z = substitute d y x;;
z = zz;;