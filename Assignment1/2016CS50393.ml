type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type pair = P of string*bool;;
type leaf = X of prop*bool;;
type node = Alpha of prop * bool * node | Assign of prop * bool * node | Beta of prop * bool * node * node | Leaf of prop * bool * pair list * bool;;
type answer = Tree of node | Val of pair list list;;

let select_node_2 leaves = match leaves with
	x::xs -> [x]
	| [] -> [];;

let rec add_leaf leaves term = match (leaves,term) with
		((a::xs), [b]) -> if a = b then leaves else a::(add_leaf xs term)
	|   ([], [b]) -> [b]
	|   (a, _) -> a;;

let rec remove_leaf leaves term = match (leaves,term) with
		((a::xs), [b]) -> if a = b then xs else a::(remove_leaf xs term)
	|   ([], _) -> []
	|   (a, []) -> a
	|   (a, _) -> a;;

let rec find_assign lis ter = match lis with
		a::b -> if a = ter then true else find_assign b ter
	|   [] -> false;; 

let rec remove_last lis = match lis with
	    [] -> []
	|   [a] -> []
	|	a::xs -> a::(remove_last xs);;

let rec select_node_3 tab e count leaves = match tab with
		Alpha(x, y, z) -> (
							match (x,y) with 
									Not(s),_ -> let q = select_node_3 z (e@[0]) (count+1) leaves in 
												if List.length q > count then q
												else remove_last e 
								|   And(s,d),true -> let q = select_node_3 z (e@[0]) (count+1) (add_leaf leaves [X(d, true)]) in
													if List.length q > count then q
													else remove_last e 
								|   Or(s,d),false -> let q = select_node_3 z (e@[0]) (count+1) (add_leaf leaves [X(d, false)]) in
													if List.length q > count then q
													else remove_last e 
								|   Impl(s,d),false -> let q = select_node_3 z (e@[0]) (count+1) (add_leaf leaves [X(d, false)]) in
													if List.length q > count then q
													else remove_last e 
								|   _ -> remove_last e
						)
	|	Assign(x, y, z) -> let q = select_node_3 z (e@[0]) (count+1) (remove_leaf leaves (select_node_2 leaves)) in 
							if List.length q > count then q
							else remove_last e 
	|	Beta(x, y, z, a) -> (
								match x with
									Iff(s,d) -> (
													if y == true then 
													(
														let q = select_node_3 z (e@[0]) (count+1) (add_leaf leaves [X(d,false)]) in
														if List.length q > count then q
														else select_node_3 a (e@[1]) (count+1) (add_leaf leaves [X(d,true)]) 
													)else(
														let q = select_node_3 z (e@[0]) (count+1) (add_leaf leaves [X(d,true)]) in
														if List.length q > count then q
														else select_node_3 a (e@[1]) (count+1) (add_leaf leaves [X(d,false)]) 
													)
												)
								|  		_    ->	(
													let q = select_node_3 z (e@[0]) (count+1) leaves in
													if List.length q > count then q
													else let qq = select_node_3 a (e@[1]) (count+1) leaves in 
													if List.length qq > count then qq
													else remove_last e
												)
							)
	|	Leaf(x, y, z, a) -> if List.length leaves > 0 then e 
							else if a = true then remove_last e
							else (
								match x with 
										T -> remove_last e
									|	F -> remove_last e
									|	L s -> if find_assign z (P(s,y)) then remove_last e else e
									|	_   -> e
							);;

let select_node tab = select_node_3 tab [] 0 [];;

let rec step_develop tab index leaves = match (tab, index) with 
		Alpha(x, y, z), l::xs -> (
									match (x,y) with 
											Not(s),_ -> Alpha(x, y, step_develop z xs leaves)
										|   And(s,d),true -> Alpha(x, y, step_develop z xs (add_leaf leaves [X(d, true)]))
										|   Or(s,d),false -> Alpha(x, y, step_develop z xs (add_leaf leaves [X(d, false)]))
										|   Impl(s,d),false -> Alpha(x, y, step_develop z xs (add_leaf leaves [X(d, false)]))
										|   _ -> Alpha(x,y,z)

								)
	|	Assign(x, y, z), l::xs -> Assign(x, y, step_develop z xs (remove_leaf leaves (select_node_2 leaves)))
	|	Beta(x, y, z, a), l::xs -> (
									match x with
										Iff(s,d) -> (
													if l == 0 && y == true then Beta(x,y,step_develop z xs (add_leaf leaves [X(d,false)]),a) 
													else if l == 1 && y == true then Beta(x,y,z,step_develop a xs (add_leaf leaves [X(d,true)]))
													else if l == 0 && y == false then Beta(x,y,step_develop z xs (add_leaf leaves [X(d,true)]),a)
													else Beta(x,y,z,step_develop a xs (add_leaf leaves [X(d,false)]))
													)
									|	_ ->  if l == 0 then Beta(x,y,step_develop z xs leaves,a) else Beta(x,y,z,step_develop a xs leaves)
								)
	|	Leaf(x, y, z, a), _ -> let next = select_node_2 leaves in 
								( if (y == true) then
									(
										match x with 
												T -> (
													match next with
															[] -> Leaf(x,y,z,false)
														|   [X(e,r)] -> Assign(x, y, (Leaf(e, r, z, false)))
												)
											|   F -> Leaf(x,y,z,true)
											|   Not(s) -> Alpha(x, y, Leaf(s, not y, z, a))
											|   And(s,d) -> Alpha(x, y, Leaf(s, true, z, a))
											|   Or(s,d) -> Beta(x, y, Leaf(s, true, z, a), Leaf(d, true, z, a))
											|   Impl(s,d) -> Beta(x, y, Leaf(s, false, z, a), Leaf(d, true, z, a))
											|   Iff(s,d) -> Beta(x, y, Leaf(s, false, z, a), Leaf(s, true, z, a))
											|   L s ->  match next with 
															[] -> Leaf(x, y, (z@[P(s,true)]), false)
														|   [X(e,r)] -> Assign(x, y, Leaf(e, r, (z@[P(s,true)]), false))
									)
								 else 
								 	(
										match x with 
												T -> Leaf(x,y,z,true)
											|   F -> (
													match next with
															[] -> Leaf(x,y,z,false)
														|   [X(e,r)] -> Assign(x, y, (Leaf(e, r, z, false)))
												)
											|   Not(s) -> Alpha(x, y, Leaf(s, not y, z, a))
											|   And(s,d) -> Beta(x, y, Leaf(s, false, z, a), Leaf(d, false, z, a))
											|   Or(s,d) -> Alpha(x, y, Leaf(s, false, z, a))
											|   Impl(s,d) -> Alpha(x, y, Leaf(s, true, z, a))
											|   Iff(s,d) -> Beta(x, y, Leaf(s, false, z, a), Leaf(s, true, z, a))
											|   L s ->  match next with 
															[] -> Leaf(x, y, (z@[P(s,false)]), false)
														|   [X(e,r)] -> Assign(x, y, Leaf(e, r, (z@[P(s,false)]), false))
								 	)
								)
		|   a, [] -> a;;

let rec compare_tab tab1 tab2 = match (tab1,tab2) with
		Alpha(x, y, z), Alpha(a, b, c) -> if x = a && y = b then compare_tab z c else false
	|	Leaf(x, y, z, w), Alpha(a, b, c) -> if x = a && y = b then true else false
	|	_, Alpha(a, b, c) -> false
	|	Beta(x, y, z, w), Beta(a, b, c, d) -> if x = a && y = b then (compare_tab z c) && (compare_tab w d) else false
	|	Leaf(x, y, z, w), Beta(a, b, c, d) -> if x = a && y = b then true else false
	|	_, Beta(a, b, c, d) -> false
	|	Assign(x, y, z), Assign(a, b, c) -> if x = a && y = b then compare_tab z c else false
	|	Leaf(x, y, z, w), Assign(a, b, c) -> if x = a && y = b then true else false
	|	_, Assign(a, b, c) -> false
	|	Leaf(x, y, z, w), Leaf(a, b, c, d) -> if x = a && y = b then true else false
	|	_, Leaf(a, b, c, d) -> false;;


let rec proof_tree root leaves = match root with
		Alpha(x, y, z) -> Alpha(x, y, proof_tree z leaves)
	|	Assign(x, y, z) -> Assign(x, y, proof_tree z leaves)
	|	Beta(x, y, z, a) -> Beta(x, y, proof_tree z leaves, proof_tree a leaves)
	|	Leaf(x, y, z, a) -> let next = select_node_2 leaves in 
								( if (y == true) then
									(
										match x with 
												T -> (
													match next with
															[] -> Leaf(x,y,z,false)
														|   [X(e,r)] -> Assign(x, y, proof_tree (Leaf(e, r, z, false)) (remove_leaf leaves next))
												)
											|   F -> Leaf(x,y,z,true)
											|   Not(s) -> Alpha(x, y, proof_tree (Leaf(s, not y, z, a)) leaves)
											|   And(s,d) -> Alpha(x, y, proof_tree (Leaf(s, true, z, a)) (add_leaf leaves [X(d, true)]))
											|   Or(s,d) -> Beta(x, y, proof_tree (Leaf(s, true, z, a)) leaves, proof_tree (Leaf(d, true, z, a)) leaves)
											|   Impl(s,d) -> Beta(x, y, proof_tree (Leaf(s, false, z, a)) leaves, proof_tree (Leaf(d, true, z, a)) leaves)
											|   Iff(s,d) -> Beta(x, y, proof_tree (Leaf(s, false, z, a)) (add_leaf leaves [X(d,false)]), proof_tree (Leaf(s, true, z, a)) (add_leaf leaves [X(d, true)]))
											|   L s ->  if find_assign z (P(s,false)) 
													    then Leaf(x, y, z, true) 
													    else 
															match next with 
															[] -> Leaf(x, y, (z@[P(s,true)]), false)
														|   [X(e,r)] -> Assign(x, y, proof_tree (Leaf(e, r, (z@[P(s,true)]), false)) (remove_leaf leaves next))
									)
								 else 
								 	(
										match x with 
												T -> Leaf(x,y,z,true)
											|   F -> (
													match next with
															[] -> Leaf(x,y,z,false)
														|   [X(e,r)] -> Assign(x, y, proof_tree (Leaf(e, r, z, false)) (remove_leaf leaves next))
												)
											|   Not(s) -> Alpha(x, y, proof_tree (Leaf(s, not y, z, a)) leaves)
											|   And(s,d) -> Beta(x, y, proof_tree (Leaf(s, false, z, a)) leaves, proof_tree (Leaf(d, false, z, a)) leaves)
											|   Or(s,d) -> Alpha(x, y, proof_tree (Leaf(s, false, z, a)) (add_leaf leaves [X(d,false)]))
											|   Impl(s,d) -> Alpha(x, y, proof_tree (Leaf(s, true, z, a)) (add_leaf leaves [X(d,false)]))
											|   Iff(s,d) -> Beta(x, y, proof_tree (Leaf(s, false, z, a)) (add_leaf leaves [X(d, true)]), proof_tree (Leaf(s, true, z, a)) (add_leaf leaves [X(d,false)]))
											|   L s -> if find_assign z (P(s,true)) 
													   then Leaf(x, y, z, true) 
													   else 
															match next with 
															[] -> Leaf(x, y, (z@[P(s,false)]), false)
														|   [X(e,r)] -> Assign(x, y, proof_tree (Leaf(e, r, (z@[P(s,false)]), false)) (remove_leaf leaves next))
								 	)
								);;

let rec valid_tableau tab = match tab with 
		Alpha(x, y, z) -> compare_tab tab (proof_tree (Leaf(x,y,[],false)) [])
	|	Assign(x, y, z) -> compare_tab tab (proof_tree (Leaf(x,y,[],false)) [])
	|	Beta(x, y, z, a) -> compare_tab tab (proof_tree (Leaf(x,y,[],false)) [])
	|	Leaf(x, y, z, a) -> compare_tab tab (proof_tree (Leaf(x,y,[],false)) []);;

let rec find_assignments root = match root with
		Alpha(x, y, z) -> find_assignments z
	|	Assign(x, y, z) -> find_assignments z
	|	Beta(x, y, z, a) -> (find_assignments z)@(find_assignments a)
	|	Leaf(x, y, z, a) -> if a = false then [z] else [];;

let rec chk_open root = match root with
		Alpha(x, y, z) -> chk_open z
	|	Assign(x, y, z) -> chk_open z
	|	Beta(x, y, z, a) -> (chk_open z) || (chk_open a)
	|	Leaf(x, y, z, a) -> if a = false then true else false;;

let rec contrad z = match z with 
		(P(a,b))::xs -> if find_assign xs (P(a, not b)) then true else contrad xs
	|   [] -> false;;

let rec contrad_path tab = match tab with
		Alpha(x, y, z) -> Alpha(x,y, contrad_path z)
	|	Assign(F, true, z) -> Leaf(F,true,[], true)
	|	Assign(T, false, z) -> Leaf(T,false, [], true)
	|	Assign(x, y, z) -> Assign(x,y, contrad_path z)
	|	Beta(x, y, z, a) -> Beta(x,y,(contrad_path z), (contrad_path a))
	|	Leaf(T, false, z, a) -> Leaf(T,false,z,true)
	|	Leaf(F, true, z, a) -> Leaf(F,true,z,true)
	|	Leaf(x, y, z, a) -> if contrad z then Leaf(x,y,z,true) else Leaf(x,y,z,false);;

let rec check_tautology root = let x = proof_tree (Leaf(root, false, [], false)) [] in 
									let z = chk_open x in 
										if z then
										( 
											Val (find_assignments x)
										)else(
											Tree(x)
										);;

let rec check_contradiction root = let x = proof_tree (Leaf(root, true, [], false)) [] in 
									let z = chk_open x in 
										if z then
										( 
											Val (find_assignments x)
										)else(
											Tree(x)
										);;

Printf.printf("\n\n------------------ test1 ----------------\n\n")

let test1 = Or(T, And(L "a", F));;
let taut1 = check_tautology test1;;
let contra1 = check_contradiction test1;;
let contra_path1 = contrad_path (proof_tree (Leaf(test1, true, [], false)) []);;
let valid1 = valid_tableau (proof_tree (Leaf(test1, true, [], false)) []);;

let sel11 = select_node (Leaf(test1, true, [], false));;
let step11 = step_develop (Leaf(test1, true, [], false)) sel11 [];;
let contra_path11 = contrad_path step11;;
let valid11 = valid_tableau contra_path11;;
let ass11 = find_assignments contra_path11;;

let sel12 = select_node contra_path11;;
let step12 = step_develop contra_path11 sel12 [];;
let contra_path12 = contrad_path step12;;
let valid12 = valid_tableau contra_path12;;
let ass12 = find_assignments contra_path12;;

let sel13 = select_node contra_path12;;
let step13 = step_develop contra_path12 sel13 [];;
let contra_path13 = contrad_path step13;;
let valid13 = valid_tableau contra_path13;;
let ass13 = find_assignments contra_path13;;

Printf.printf("\n\n------------------ test2 ----------------\n\n")

let test2 = Or(T, L "a");;
let taut2 = check_tautology test2;;
let contra2 = check_contradiction test2;;
let contra_path2 = contrad_path (proof_tree (Leaf(test2, false, [], false)) []);;
let valid2 = valid_tableau (proof_tree (Leaf(test2, false, [], false)) []);;

let sel21 = select_node (Leaf(test2, false, [], false));;
let step21 = step_develop (Leaf(test2, false, [], false)) sel21 [];;
let contra_path21 = contrad_path step21;;
let valid21 = valid_tableau contra_path21;;
let ass21 = find_assignments contra_path21;;

Printf.printf("\n\n------------------ test3 ----------------\n\n")

let test3 = Impl(Impl(L "p", Impl(L "q", L "r")), Impl(Impl(L "p", L "q"), Impl(L "p", L "r")));;
let taut3 = check_tautology test3;;
let contra3 = check_contradiction test3;;
let contra_path3 = contrad_path (proof_tree (Leaf(test3, false, [], false)) []);;
let valid3 = valid_tableau (proof_tree (Leaf(test3, false, [], false)) []);;

let sel31 = select_node (Leaf(test3, false, [], false));;
let step31 = step_develop (Leaf(test3, false, [], false)) sel31 [];;
let contra_path31 = contrad_path step31;;
let valid31 = valid_tableau contra_path31;;
let ass31 = find_assignments contra_path31;;

let sel32 = select_node contra_path31;;
let step32 = step_develop contra_path31 sel32 [];;
let contra_path32 = contrad_path step32;;
let valid32 = valid_tableau contra_path32;;
let ass32 = find_assignments contra_path32;;

let sel33 = select_node contra_path32;;
let step33 = step_develop contra_path32 sel33 [];;
let contra_path33 = contrad_path step33;;
let valid33 = valid_tableau contra_path33;;
let ass33 = find_assignments contra_path33;;

let sel34 = select_node contra_path33;;
let step34 = step_develop contra_path33 sel34 [];;
let contra_path34 = contrad_path step34;;
let valid34 = valid_tableau contra_path34;;
let ass34 = find_assignments contra_path34;;

let sel35 = select_node contra_path34;;
let step35 = step_develop contra_path34 sel35 [];;
let contra_path35 = contrad_path step35;;
let valid35 = valid_tableau contra_path35;;
let ass35 = find_assignments contra_path35;;

let sel36 = select_node contra_path35;;
let step36 = step_develop contra_path35 sel36 [];;
let contra_path36 = contrad_path step36;;
let valid36 = valid_tableau contra_path36;;
let ass36 = find_assignments contra_path36;;

let sel37 = select_node contra_path36;;
let step37 = step_develop contra_path36 sel37 [];;
let contra_path37 = contrad_path step37;;
let valid37 = valid_tableau contra_path37;;
let ass37 = find_assignments contra_path37;;

let sel38 = select_node contra_path37;;
let step38 = step_develop contra_path37 sel38 [];;
let contra_path38 = contrad_path step38;;
let valid38 = valid_tableau contra_path38;;
let ass38 = find_assignments contra_path38;;

Printf.printf("\n\n------------------ test3 ----------------\n\n")

let test4 = Iff(L "p", Impl(L "q", L "r"));;
let taut4 = check_tautology test4;;
let contra4 = check_contradiction test4;;
let contra_path4 = contrad_path (proof_tree (Leaf(test4, false, [], false)) []);;
let valid4 = valid_tableau (proof_tree (Leaf(test4, false, [], false)) []);;

let sel41 = select_node (Leaf(test4, false, [], false));;
let step41 = step_develop (Leaf(test4, false, [], false)) sel41 [];;
let contra_path41 = contrad_path step41;;
let valid41 = valid_tableau contra_path41;;
let ass41 = find_assignments contra_path41;;

let sel42 = select_node contra_path41;;
let step42 = step_develop contra_path41 sel42 [];;
let contra_path42 = contrad_path step42;;
let valid42 = valid_tableau contra_path42;;
let ass42 = find_assignments contra_path42;;

let sel43 = select_node contra_path42;;
let step43 = step_develop contra_path42 sel43 [];;
let contra_path43 = contrad_path step43;;
let valid43 = valid_tableau contra_path43;;
let ass43 = find_assignments contra_path43;;

let sel44 = select_node contra_path43;;
let step44 = step_develop contra_path43 sel44 [];;
let contra_path44 = contrad_path step44;;
let valid44 = valid_tableau contra_path44;;
let ass44 = find_assignments contra_path44;;

let sel45 = select_node contra_path44;;
let step45 = step_develop contra_path44 sel45 [];;
let contra_path45 = contrad_path step45;;
let valid45 = valid_tableau contra_path45;;
let ass45 = find_assignments contra_path45;;

Printf.printf("\n\n------------------ test4 ----------------\n\n")

let test5 = Impl(L "p", Impl(L "q", L "p"));;
let taut5 = check_tautology test5;;
let contra5 = check_contradiction test5;;
let contra_path5 = contrad_path (proof_tree (Leaf(test5, false, [], false)) []);;
let valid5 = valid_tableau (proof_tree (Leaf(test5, false, [], false)) []);;
let ass5 = find_assignments (proof_tree (Leaf(test5, true, [], false)) []);;

let sel51 = select_node (Leaf(test5, false, [], false));;
let step51 = step_develop (Leaf(test5, false, [], false)) sel51 [];;
let contra_path51 = contrad_path step51;;
let valid51 = valid_tableau contra_path51;;
let ass51 = find_assignments contra_path51;;

let sel52 = select_node contra_path51;;
let step52 = step_develop contra_path51 sel52 [];;
let contra_path52 = contrad_path step52;;
let valid52 = valid_tableau contra_path52;;
let ass52 = find_assignments contra_path52;;

let sel53 = select_node contra_path52;;
let step53 = step_develop contra_path52 sel53 [];;
let contra_path53 = contrad_path step53;;
let valid53 = valid_tableau contra_path53;;
let ass53 = find_assignments contra_path53;;

let sel54 = select_node contra_path53;;
let step54 = step_develop contra_path53 sel54 [];;
let contra_path54 = contrad_path step54;;
let valid54 = valid_tableau contra_path54;;
let ass54 = find_assignments contra_path54;;

let sel55 = select_node contra_path54;;
let step55 = step_develop contra_path54 sel55 [];;
let contra_path55 = contrad_path step55;;
let valid55 = valid_tableau contra_path55;;
let ass55 = find_assignments contra_path55;;

