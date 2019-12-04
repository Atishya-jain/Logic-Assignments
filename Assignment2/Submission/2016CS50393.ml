type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type gamma = X of prop;;
type node = Hyp of gamma list * prop | KSR of gamma list * prop | Mod of gamma list * prop * node * node;;
exception Invalid_Tree;;

let rec find_assign lis ter = match lis with
		X(a)::b -> if a = ter then true else find_assign b ter
	|   [] -> false;; 

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

let rec valid_hprooftree tree = match tree with
		Hyp(a,b) -> if find_assign a b then true else false
	|	KSR(a,(Impl(p,Impl(q,r)))) -> if p = r then true else(
			match tree with
					KSR(aa,(Impl(Impl(z,x), Impl(Impl(c,s),t)))) -> if (z = c) && x = Not(s) && z = Not(t) then true else(
					match tree with
						KSR(aaa,(Impl(Impl(j,Impl(k,l)), Impl(Impl(v,g), Impl(n,m))))) -> if j = v && g = k && n = j && m = l then true else false 
						|	_ -> false
					)
				(* |   KSR(a,(Impl(Impl(p,q), Impl(Impl(r,s),t)))) -> if (p = r) && q = Not(s) && p = Not(t) then true else false *)
				|   _ -> false
			)
	|   Mod(a, b, c, d) -> (
					match (c,d) with 
					Hyp(q,w), Hyp(e,r) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	Hyp(q,w), KSR(e,r) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	KSR(q,w), Hyp(e,r) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	KSR(q,w), KSR(e,r) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	Mod(q,w,t,y), Hyp(e,r) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	Mod(q,w,t,y), KSR(e,r) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	Hyp(q,w), Mod(e,r,t,y) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	KSR(q,w), Mod(e,r,t,y) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				|	Mod(q,w,u,i), Mod(e,r,t,y) -> if mods w r b then (valid_hprooftree c) && (valid_hprooftree d) else false
				)
	|   _ -> false;;

let rec pad tree del = match tree with
		Hyp(a,b) -> Hyp(join a del, b)
	|	KSR(a,b) -> KSR(join a del, b)
	|	Mod(a,b,c,d) -> Mod(join a del, b, pad c del, pad d del);;

let rec find_sub tree = match tree with
		Hyp(a,b) -> [X(b)]
	|   KSR(a,b) -> []
	|   Mod(a,b,c,d) -> (find_sub c)@(find_sub d);;

let rec replace tree del =  match tree with
 		Hyp(a,b) -> Hyp(del, b)
 	|   KSR(a,b) -> KSR(del, b)
 	|   Mod(a,b,c,d) -> Mod(del, b, replace c del, replace d del);;

let rec prune tree = let del = find_sub tree in replace tree del;;

let rec find_match tree tree_list = match (tree, tree_list) with
		Hyp(a,b), [] -> tree 
	|	KSR(a,b), _ -> tree 
	|	Hyp(a,b), x::xs -> ( 
							match x with 
							Hyp(c,d) -> if b = d then Hyp(c,d) else find_match tree xs
						|	KSR(c,d) -> if b = d then KSR(c,d) else find_match tree xs
						|	Mod(c,d,e,f) -> if b = d then Mod(c,d,e,f) else find_match tree xs
						);;

let rec replace_del tree tree_list = match tree_list with
		[] -> tree
	|   (Hyp(a,b))::xs -> replace tree a
	|   (KSR(a,b))::xs -> replace tree a
	|   (Mod(a,b,c,d))::xs -> replace tree a;;

let rec graft tree tree_list = let my_tree = replace_del tree tree_list in 
								match my_tree with
		Hyp(a,b) -> find_match my_tree tree_list
	|   KSR(a,b) -> find_match my_tree tree_list 
	|   Mod(a,b,c,d) -> Mod(a,b, graft c tree_list, graft d tree_list);;

let help2 p = Impl(p, Impl(Impl(p,p) ,p));;
let help1 p = Impl(help2 p, Impl(Impl(p, Impl(p, p)), Impl(p, p)));;
let proof_p_impl_p del p = Mod(del, Impl(p,p), Mod(del, Impl(Impl(p,Impl(p,p)), Impl(p,p)), KSR(del, help1 p), KSR(del, help2 p)), KSR(del, Impl(p,Impl(p,p))));;

let subsume a b = match (a,b) with
		Impl(p,q), r -> if p = r then true else false
	|	_ -> false;;

let extract_prop a = match a with
		Hyp(x,b) -> b
	|   KSR(x,b) -> b 
	|   Mod(x,b,c,d) -> b;;

let rec dedthm tree = match tree with 
		Hyp(X(p)::xs, q) -> if p = q then proof_p_impl_p xs p else Mod(xs, Impl(p,q), Hyp(xs,q), KSR(xs, Impl(q,Impl(p,q))))
	|	KSR(X(p)::xs, q) -> if p = q then proof_p_impl_p xs p else Mod(xs, Impl(p,q), KSR(xs,q), KSR(xs, Impl(q,Impl(p,q))))
	|	Mod(X(p)::xs, q, c, d) -> if p = q then proof_p_impl_p xs p else let r_q = extract_prop c in let r = extract_prop d in 
				if subsume r_q r || subsume r r_q then 
					if subsume r_q r then Mod(xs, Impl(p,q), (Mod(xs, Impl(Impl(p,r), Impl(p,q)), KSR(xs, Impl(Impl(p,Impl(r,q)), Impl(Impl(p,r), Impl(p,q)))), dedthm c)), dedthm d)
					else  Mod(xs, Impl(p,q), (Mod(xs, Impl(Impl(p,r_q), Impl(p,q)), KSR(xs, Impl(Impl(p,Impl(r_q,q)), Impl(Impl(p,r_q), Impl(p,q)))), dedthm d)), dedthm c)
				else
					raise Invalid_Tree;;


let gamma1 = [X(L "p"); X(Impl(L "p", L "q")); X(Impl(Not(L "p"), Not(L "q")))];;
let gamma2 = [X(Not(L "p")); X(Impl(Not(L "p"), L "q")); X(Impl(L "p", Not(L "q")))];;
let gamma3 = [X(Impl(Impl(L "p", L "p"), L "q")); X(Impl(L "p", L "p"))];;

let val_tree1 = Mod(gamma1, L "q", Hyp(gamma1, L "p"), Hyp(gamma1, Impl(L "p", L "q")));;
let inval_tree1 = Mod(gamma2, L "q", Hyp(gamma2, L "p"), Hyp(gamma2, Impl(L "p", L "q")));;
let val_tree2 = Mod(gamma3, L "q", Hyp(gamma3, Impl(Impl(L "p", L "p"), L "q")), Hyp(gamma3, Impl(L "p", L "p")));;

let test1 = valid_hprooftree val_tree1;; (* true *)
let test2 = valid_hprooftree inval_tree1;; (* false *)
let test3 = pad val_tree1 gamma2;;  (* padded tree *)
let test4 = pad inval_tree1 gamma1;; (* padded tree *)
let test5 = valid_hprooftree test4;; (* true *)
let test6 = prune val_tree1;;
let test7 = valid_hprooftree test6;; (* true *)
let test7_5 = valid_hprooftree (proof_p_impl_p gamma1 (L "p"));; (* true *)
let test8 = prune (proof_p_impl_p gamma1 (L "p"));; (* empty delta tree *)
let test9 = valid_hprooftree val_tree2;; (* true *)
let test10 = graft val_tree2 [Hyp(gamma3, Impl(Impl(L "p", L "p"), L "q")); proof_p_impl_p gamma3 (L "p")];;
let test10_5 = valid_hprooftree test10;;
let test11 = dedthm val_tree1;;
let test11_5 = valid_hprooftree test11;; 
let test12 = dedthm test11;; 
let test12_5 = valid_hprooftree test12;; 
let test13 = dedthm test12;; 
let test13_5 = valid_hprooftree test13;; 
