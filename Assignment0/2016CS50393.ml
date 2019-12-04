(* In subprotp At, going down at Not has been encoded going left *)

type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
type pair = P of string * bool;;
exception Invalid of prop;;
exception NotSubProp;;
exception VariableNotInitialised of string;;

let rec ht term = match term with
			T -> 0
		|   F -> 0
		|   L(x) -> 0
		|   Not(a) -> ht(a) + 1
		|   And(a,b) -> 1 + (max (ht(a)) (ht(b)))
		|   Impl(a,b) -> 1 + (max (ht(a)) (ht(b)))
		|   Iff(a,b) -> 1 + (max (ht(a)) (ht(b)))
		|   Or(a,b) -> 1 + (max (ht(a)) (ht(b)))
		|   _ -> raise(Invalid term);;

let rec size term = match term with
			T -> 1
		|   F -> 1
		|   L(x) -> 1
		|   Not(a) -> size(a) + 1
		|   And(a,b) -> 1 + size(a) + size(b)
		|   Impl(a,b) -> 1 + size(a) + size(b)
		|   Iff(a,b) -> 1 + size(a) + size(b)
		|   Or(a,b) -> 1 + size(a) + size(b)
		|   _ -> raise(Invalid term);;

let rec setify e x = match e with
			[] -> [x]
		|	a::b -> if a = x then e else a::(setify b x);;

let rec letters e term = match term with
			T -> e
		|   F -> e
		|   Not(a) -> letters e a
		|   L(x) -> setify e x
		|   And(a,b) -> letters (letters e a) b
		|   Impl(a,b) -> letters (letters e a) b
		|   Iff(a,b) -> letters (letters e a) b
		|   Or(a,b) -> letters (letters e a) b
		|   _ -> raise(Invalid term);;

let rec subprop e p tree = if p=tree then [e]
							else match tree with
								T -> []
							|   F -> []
							|   L(x) -> []								
							|   Not(a) -> subprop (e@[0]) p a
							|   And(a,b) -> (subprop (e@[0]) p a) @ (subprop (e@[1]) p b)
							|   Impl(a,b) -> (subprop (e@[0]) p a) @ (subprop (e@[1]) p b)
							|   Iff(a,b) -> (subprop (e@[0]) p a) @ (subprop (e@[1]) p b)
							|   Or(a,b) -> (subprop (e@[0]) p a) @ (subprop (e@[1]) p b)
							|   _ -> raise(Invalid tree);;

let rec subprop_at p tree = let x = (subprop [] p tree) in if x = [] then raise NotSubProp else x;;

let rec nnf term = match term with
			T -> T
		|   F -> F
		|   L(x) -> L(x) 
		|   Not(T) -> F
		|   Not(F) -> T
		|   Not(L(x)) -> Not(L(x))
		|   Not(And(a,b)) -> Or(nnf (Not(a)), nnf (Not(b)))
		|   Not(Or(a,b)) -> And(nnf (Not(a)), nnf (Not(b)))
		|   Not(Impl(a,b)) -> And(nnf a, nnf (Not(b)))
		|   Not(Iff(a,b)) -> And(Or(nnf (Not(a)), nnf (Not(b))), Or(nnf a, nnf b))
		|   Not(Not(a)) -> a
		|   And(a,b) -> And(nnf a, nnf b)
		|   Or(a,b) -> Or(nnf a, nnf b)
		|   Impl(a,b) -> Or(nnf (Not(a)), nnf b)
		|   Iff(a,b) -> Or(And(nnf (Not(a)), nnf (Not(b))), And(nnf a, nnf b))
		|   _ -> raise(Invalid term);;
		(* |   Not(Iff(a,b)) -> Or(And(nnf a, nnf (Not(b))), And(nnf (Not(a)), nnf b)) *)

let rec only_cnf term = match term with
					T -> T
				|   F -> F
				|   L(x) -> L(x) 
				|   Not(x) -> Not(x)
				|   Or(And(a,c),b) -> And(only_cnf (Or(a,b)) , only_cnf (Or(c,b)))
				|   Or(b,And(a,c)) -> And(only_cnf (Or(b,a)) , only_cnf (Or(b,c)))
				|   And(a,b) -> And(only_cnf a, only_cnf b)
				|   Or(a,b) -> let x = only_cnf a in let y = only_cnf b in 
								match (x,y) with
									(And(q,w), z) -> only_cnf(Or(x,y))
								|	(z, And(e,r)) -> only_cnf(Or(x,y))
								|   _ -> Or(x,y);;

let rec cnf term = match term with
		_ -> let e = nnf term in only_cnf e;; 	

let rec only_dnf term = match term with
					T -> T
				|   F -> F
				|   L(x) -> L(x) 
				|   Not(x) -> Not(x)
				|   Or(a,b) -> Or(only_dnf a, only_dnf b)
				|   And(b,Or(a,c)) -> Or(only_dnf (And(b,a)),only_dnf (And(b,c)))
				|   And(Or(a,c),b) -> Or(only_dnf (And(a,b)),only_dnf (And(c,b)))
				|   And(a,b) -> let x = only_dnf a in let y = only_dnf b in 
								match (x,y) with
									(Or(q,w), z) -> only_dnf (And(x,y))
								|	(z, Or(e,r)) -> only_dnf (And(x,y))
								|   _ -> And(x,y);;

let rec dnf term = match term with
		_ -> let e = nnf term in only_dnf e;;	

let rec subst rho term = match rho with
			[] -> raise (VariableNotInitialised term)
		|   P(a,c)::b -> if term = a then c else (subst b term);;

let rec truth rho term = match term with
			T -> true
		|   F -> false
		|   L(x) -> subst rho x 
		|   Not(a) -> not(truth rho a)
		|   And(a,b) -> truth rho a && truth rho b
		|   Or(a,b) -> truth rho a || truth rho b
		|   Impl(a,b) -> not(truth rho a) || truth rho b
		|   Iff(a,b) -> (not(truth rho a) || truth rho b) && (truth rho a || not(truth rho b));;


Printf.printf("\n\n--------------------------Test Cases--------------------------");;
Printf.printf("\n\nTest Case 1:");;
let rho1 = [P("x", true); P("y", false)];;
let test1 = And(Or(T,F),And(L("x"), L("y")));;
let sub1 = Or(T,F);;
let letters1 = letters [] test1;;
let p1 = subprop_at sub1 test1;;
let cnf1 = cnf test1;;
let dnf1 = dnf test1;;
let nnf1 = nnf test1;;
let ht1_prop = ht test1;;
let ht1_cnf = ht cnf1;;
let ht1_dnf = ht dnf1;;
let ht1_nnf = ht nnf1;;
let siz1_prop = size test1;;
let siz1_cnf = size cnf1;;
let siz1_dnf = size dnf1;;
let siz1_nnf = size nnf1;;
let r1 = truth rho1 test1;;
let r1_cnf = truth rho1 cnf1;;
let r1_dnf = truth rho1 dnf1;;
let r1_nnf = truth rho1 nnf1;;


Printf.printf("\n\nTest Case 2:");;
let rho2 = [P("a", true); P("v", false)];;
let rho2_1 = [P("a", true); P("v", true)];;
let rho2_2 = [P("a", false); P("v", false)];;
let test2 = And(Or(L("a"),L("v")),Not(And(L("a"),L("a"))));;
let sub2 = L("a");;
let letters2 = letters [] test2;;
let p2 = subprop_at sub2 test2;;
let cnf2 = cnf test2;;
let dnf2 = dnf test2;;
let nnf2 = nnf test2;;
let ht2_prop = ht test2;;
let ht2_cnf = ht cnf2;;
let ht2_dnf = ht dnf2;;
let ht2_nnf = ht nnf2;;
let siz2_prop = size test2;;
let siz2_cnf = size cnf2;;
let siz2_dnf = size dnf2;;
let siz2_nnf = size nnf2;;
let r2 = truth rho2 test2;;
let r2_cnf = truth rho2 cnf2;;
let r2_dnf = truth rho2 dnf2;;
let r2_nnf = truth rho2 nnf2;;
let r21 = truth rho2_1 test2;;
let r21_cnf = truth rho2_1 cnf2;;
let r21_dnf = truth rho2_1 dnf2;;
let r21_nnf = truth rho2_1 nnf2;;
let r22 = truth rho2_2 test2;;
let r22_cnf = truth rho2_2 cnf2;;
let r22_dnf = truth rho2_2 dnf2;;
let r22_nnf = truth rho2_2 nnf2;;


Printf.printf("\n\nTest Case 3:");;
let test3 = And(Or(Not(T),Not(F)),And(T, And(T,T)));;
let rho3 = [];;
let sub3 = T;;
let letters3 = letters [] test3;;
let p3 = subprop_at sub3 test3;;
let cnf3 = cnf test3;;
let dnf3 = dnf test3;;
let nnf3 = nnf test3;;
let ht3_prop = ht test3;;
let ht3_cnf = ht cnf3;;
let ht3_dnf = ht dnf3;;
let ht3_nnf = ht nnf3;;
let siz3_prop = size test3;;
let siz3_cnf = size cnf3;;
let siz3_dnf = size dnf3;;
let siz3_nnf = size nnf3;;
let r3 = truth rho3 test3;;
let r3_cnf = truth rho3 cnf3;;
let r3_dnf = truth rho3 dnf3;;
let r3_nnf = truth rho3 nnf3;;


Printf.printf("\n\nTest Case 4 (Contingency):");;
let test4 = Not(And(Impl(L("f"), T), Or(F, Iff(L("t"), T))));;
let rho4 = [P("t", true); P("f", false)];;
let rho4_1 = [P("t", true); P("f", true)];;
let rho4_2 = [P("t", false); P("f", false)];;
let rho4_3 = [P("t", false); P("f", true)];;
let sub4 = Iff(L("t"),T);;
let letters4 = letters [] test4;;
let p4 = subprop_at sub4 test4;;
let cnf4 = cnf test4;;
let dnf4 = dnf test4;;
let nnf4 = nnf test4;;
let ht4_prop = ht test4;;
let ht4_cnf = ht cnf4;;
let ht4_dnf = ht dnf4;;
let ht4_nnf = ht nnf4;;
let siz4_prop = size test4;;
let siz4_cnf = size cnf4;;
let siz4_dnf = size dnf4;;
let siz4_nnf = size nnf4;;
let r4 = truth rho4 test4;;
let r4_cnf = truth rho4 cnf4;;
let r4_dnf = truth rho4 dnf4;;
let r4_nnf = truth rho4 nnf4;;
let r4_1 = truth rho4_1 test4;;
let r4_cnf_1 = truth rho4_1 cnf4;;
let r4_dnf_1 = truth rho4_1 dnf4;;
let r4_nnf_1 = truth rho4_1 nnf4;;
let r4_2 = truth rho4_2 test4;;
let r4_cnf_2 = truth rho4_2 cnf4;;
let r4_dnf_2 = truth rho4_2 dnf4;;
let r4_nnf_2 = truth rho4_2 nnf4;;
let r4_3 = truth rho4_3 test4;;
let r4_cnf_3 = truth rho4_3 cnf4;;
let r4_dnf_3 = truth rho4_3 dnf4;;
let r4_nnf_3 = truth rho4_3 nnf4;;


Printf.printf("\n\nTest Case 5 (Tautology):");;
let test5 = Impl(L("f"), Or(Impl(L("t"),And(T,F)), Not(And(L("t"), Not(L("f"))))));;
let rho5 = [P("t", true); P("f", false)];;
let rho5_1 = [P("t", false); P("f", false)];;
let rho5_2 = [P("t", false); P("f", true)];;
let rho5_3 = [P("t", true); P("f", true)];;
let sub5 = L("f");;
let letters5 = letters [] test5;;
let p5 = subprop_at sub5 test5;;
let cnf5 = cnf test5;;
let dnf5 = dnf test5;;
let nnf5 = nnf test5;;
let ht5_prop = ht test5;;
let ht5_cnf = ht cnf5;;
let ht5_dnf = ht dnf5;;
let ht5_nnf = ht nnf5;;
let siz5_prop = size test5;;
let siz5_cnf = size cnf5;;
let siz5_dnf = size dnf5;;
let siz5_nnf = size nnf5;;
let r5 = truth rho5 test5;;
let r5_cnf = truth rho5 cnf5;;
let r5_dnf = truth rho5 dnf5;;
let r5_nnf = truth rho5 nnf5;;
let r5_1 = truth rho5_1 test5;;
let r5_cnf_1 = truth rho5_1 cnf5;;
let r5_dnf_1 = truth rho5_1 dnf5;;
let r5_nnf_1 = truth rho5_1 nnf5;;
let r5_2 = truth rho5_2 test5;;
let r5_cnf_2 = truth rho5_2 cnf5;;
let r5_dnf_2 = truth rho5_2 dnf5;;
let r5_nnf_2 = truth rho5_2 nnf5;;
let r5_3 = truth rho5_3 test5;;
let r5_cnf_3 = truth rho5_3 cnf5;;
let r5_dnf_3 = truth rho5_3 dnf5;;
let r5_nnf_3 = truth rho5_3 nnf5;;


Printf.printf("\n\nTest Case 6 (Contradiction):");;
let test6 = Impl(Impl(L("t"),Impl(L("f"),L("t"))), Or(F,F));;
let rho6 = [P("t", true); P("f", false)];;
let rho6_1 = [P("t", false); P("f", false)];;
let rho6_2 = [P("t", true); P("f", true)];;
let rho6_3 = [P("t", false); P("f", true)];;
let sub6 = Or(F,F);;
let letters6 = letters [] test6;;
let p6 = subprop_at sub6 test6;;
let cnf6 = cnf test6;;
let dnf6 = dnf test6;;
let nnf6 = nnf test6;;
let ht6_prop = ht test6;;
let ht6_cnf = ht cnf6;;
let ht6_dnf = ht dnf6;;
let ht6_nnf = ht nnf6;;
let siz6_prop = size test6;;
let siz6_cnf = size cnf6;;
let siz6_dnf = size dnf6;;
let siz6_nnf = size nnf6;;
let r6 = truth rho6 test6;;
let r6_cnf = truth rho6 cnf6;;
let r6_dnf = truth rho6 dnf6;;
let r6_nnf = truth rho6 nnf6;;
let r6_1 = truth rho6_1 test6;;
let r6_cnf_1 = truth rho6_1 cnf6;;
let r6_dnf_1 = truth rho6_1 dnf6;;
let r6_nnf_1 = truth rho6_1 nnf6;;
let r6_2 = truth rho6_2 test6;;
let r6_cnf_2 = truth rho6_2 cnf6;;
let r6_dnf_2 = truth rho6_2 dnf6;;
let r6_nnf_2 = truth rho6_2 nnf6;;
let r6_3 = truth rho6_3 test6;;
let r6_cnf_3 = truth rho6_3 cnf6;;
let r6_dnf_3 = truth rho6_3 dnf6;;
let r6_nnf_3 = truth rho6_3 nnf6;;

