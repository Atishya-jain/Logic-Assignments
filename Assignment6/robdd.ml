type prop = T | F | L of int | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
exception Error;;
type pair = P of int * bool;;
exception Invalid of prop;;
exception NotSubProp;;
exception VariableNotInitialised of int;;

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



let rec member hh i l h = try Hashtbl.find hh (i,l,h) with Not_found -> -1;;
let rec add tt i l h = let u = Hashtbl.length tt in let y = Hashtbl.add tt u (i,l,h) in u;;
let rec insert hh i l h u = Hashtbl.add hh (i,l,h) u;;

let rec mk hh tt i l h = if l = h then l 
						  else (let mem = (member hh i l h) in 
						  			if not(mem = -1) then mem 
						  			else (
						  				 let a = (add tt i l h) in 
						  				 let b = (insert hh i l h a) in 
						  				 a
						  				)
						  		);; 

let rec truth term = match term with
			T -> true
		|   F -> false
		(* |   L(x) -> subst x  *)
		|   Not(a) -> not(truth a)
		|   And(a,b) -> truth a && truth b
		|   Or(a,b) -> truth a || truth b
		|   Impl(a,b) -> not(truth a) || truth b
		|   Iff(a,b) -> (not(truth a) || truth b) && (truth a || not(truth b));;

let rec subst t b i = match t with
		T -> T
	|	F -> F
	|	L x -> if x = i then b else L x
	|  	Not x -> Not(subst x b i)
	|   And(a,c) -> And(subst a b i, subst c b i)
	|   Or(a,c) -> Or(subst a b i, subst c b i)
	|   Impl(a,c) -> Impl(subst a b i, subst c b i)
	|   Iff(a,c) -> Iff(subst a b i, subst c b i);;
	(* | 	x -> raise(NotSubProp x) *)

let rec build2 n hh tt t i = if i > n then (
								if truth t = true then 1 else 0
							)
							else (
									let v0 = build2 n hh tt (subst t F i) (i+1) in
									let v1 = build2 n hh tt (subst t T i) (i+1) in
									mk hh tt i v0 v1
								);;

(* let rec solve op a b = match op with
		And -> truth And(a,b)
	|   Or -> truth Or(a,b)
	|   Impl -> truth Impl(a,b)
	|   Iff -> truth Iff(a,b);;
 *)
let find a x = match (a,x) with
		(b,c,d),0 -> b
	|   (b,c,d),1 -> c
	|   (b,c,d),2 -> d;;

let get_all a = match a with
		(b,c,d) -> [|b;c;d|];;

let rec var tt u = let vall = get_all (Hashtbl.find tt u) in Array.get vall 0;;
let rec low tt u = let vall = get_all (Hashtbl.find tt u) in Array.get vall 1;;
let rec high tt u = let vall = get_all (Hashtbl.find tt u) in Array.get vall 2;;

let rec apply2 tt1 tt2 tt hh gg op u1 u2 = try (Hashtbl.find gg (u1, u2)) with Not_found -> (
								if (u1 = 0 || u1 = 1) && (u2 = 0 || u2 = 1) then(
									let temp = Hashtbl.add gg (u1,u2) (op u1 u2) in Hashtbl.find gg (u1, u2)
								) else (
									 if (((var tt1 u1) = (var tt2 u2))) then (
									 let temp = Hashtbl.add gg (u1,u2) (mk hh tt (var tt1 u1) (apply2 tt1 tt2 tt hh gg op (low tt1 u1) (low tt2 u2)) (apply2 tt1 tt2 tt hh gg op (high tt1 u1) (high tt2 u2))) in Hashtbl.find gg (u1,u2)
									 )else if (((var tt1 u1) < (var tt2 u2))) then (
									 let temp = Hashtbl.add gg (u1,u2) (mk hh tt (var tt1 u1) (apply2 tt1 tt2 tt hh gg op (low tt1 u1) u2) (apply2 tt1 tt2 tt hh gg op (high tt1 u1) u2)) in Hashtbl.find gg (u1,u2)
									 )else(
									 let temp = Hashtbl.add gg (u1,u2) (mk hh tt (var tt2 u2) (apply2 tt1 tt2 tt hh gg op u1 (low tt2 u2)) (apply2 tt1 tt2 tt hh gg op u1 (high tt2 u2))) in Hashtbl.find gg (u1,u2)
									 )
								)
								);;

let rec restrict2 hh tt tu u j b = if var tu u > j then u
							  else if var tu u < j then let temp1 = restrict2 hh tt tu (low tu u) j b in 
							  							let temp2 = restrict2 hh tt tu (high tu u) j b in 
							  							mk hh tt (var tu u) temp1 temp2  
							  else if b = 0 then restrict2 hh tt tu (low tu u) j b
							  else restrict2 hh tt tu (high tu u) j b;;

let rec count tt u = if u = 0 then 0.0
					 else if u = 1 then 1.0
					 else (2.0**float_of_int((var tt (low tt u)) - (var tt u) - 1) *. (count tt (low tt u))) +. (2.0**float_of_int((var tt (high tt (u))) - (var tt u) - 1) *. (count tt (high tt u)));;

let rec sat_count2 tt u = if Hashtbl.length tt >= 3 then (
						 let x = (var tt 2) + 1 in 
						 let xx = Hashtbl.replace tt 0 (x, 0, 0) in 
						 let yy = Hashtbl.replace tt 1 (x, 0, 0) in 
						 let vall = get_all (Hashtbl.find tt u) in 
						 let ans = ((2.0**float_of_int((var tt u) - 1)) *. (count tt u)) in
						 let qq = Hashtbl.replace tt 0 (100000000, 0, 0) in 
						 let ww = Hashtbl.replace tt 1 (100000000, 0, 0) in
						 ans 
						) else (
						 (2.0**float_of_int((var tt u) - 1)) *. (count tt u)	
						);;

let rec sat_count tt = let u = Hashtbl.length tt in 
						sat_count2 tt (u-1);;

let rec anysat2 tt u = if u = 0 then raise(Error)
				   else if u = 1 then []
				   else if (low tt u) = 0 then (var tt u, 1)::(anysat2 tt (high tt u))
				   else (var tt u, 0)::(anysat2 tt (low tt u));;

let rec anysat tt = let u = Hashtbl.length tt - 1 in 
					anysat2 tt u;;

let rec append a b = match b with
		[] -> []
	|	x::xs -> (a::x)::(append a xs);;

let rec allsat2 tt u = if u = 0 then []
				   else if u = 1 then [[]]
				   else (append (var tt u, 0) (allsat2 tt (low tt u))) @ (append (var tt u, 1) (allsat2 tt (high tt u)));;

let rec allsat tt = let u = Hashtbl.length tt - 1 in 
					allsat2 tt u;;

let rec simplify2 hh tt td tu d u = if d = 0 then 0
						  else if u <= 1 then u
						  else if d = 1 then let temp1 = simplify2 hh tt td tu d (low tu u) in 
						  					 let temp2 = simplify2 hh tt td tu d (high tu u) in 
						  					  mk hh tt (var tu u) temp1 temp2
						  else if (var td d) = (var tu u) then (
						  	if low td d = 0 then simplify2 hh tt td tu (high td d) (high tu u)
						  	else if high td d = 0 then simplify2 hh tt td tu (low td d) (low tu u)
						    else let temp1 = simplify2 hh tt td tu (low td d) (low tu u) in 
			  					 let temp2 = simplify2 hh tt td tu (high td d) (high tu u) in 
			  					  mk hh tt (var tu u) temp1 temp2
						  )
					  	  else if (var td d) < (var tu u) then let temp1 = simplify2 hh tt td tu (low td d) u in 
											  				   let temp2 = simplify2 hh tt td tu (high td d) u in 
											  				   mk hh tt (var tu u) temp1 temp2
						  else let temp1 = simplify2 hh tt td tu d (low tu u) in 
			  				   let temp2 = simplify2 hh tt td tu d (high tu u) in 
			  				   mk hh tt (var tu u) temp1 temp2;;

let rec simplify t1 t2 = let tt = Hashtbl.create 1234 in
				  let hh = Hashtbl.create 1234 in
				  let yy = Hashtbl.add tt 0 (100000000000, 0, 0) in
				  let uu = Hashtbl.add tt 1 (100000000000, 0, 0) in
				  let d = Hashtbl.length t1 - 1 in
				  let u = Hashtbl.length t2 - 1 in 
				  let final = simplify2 hh tt t1 t2 d u in tt;;

let rec build t maxi = let tt = Hashtbl.create 1234 in
				  let hh = Hashtbl.create 1234 in
				  let yy = Hashtbl.add tt 0 (100000000000, 0, 0) in
				  let uu = Hashtbl.add tt 1 (100000000000, 0, 0) in
				  let xx = build2 maxi hh tt t 1 in tt;;  

let rec apply op t1 t2 = let tt = Hashtbl.create 1234 in
				  let hh = Hashtbl.create 1234 in
				  let gg = Hashtbl.create 1234 in
				  let yy = Hashtbl.add tt 0 (100000000000, 0, 0) in
				  let uu = Hashtbl.add tt 1 (100000000000, 0, 0) in
				  let u1 = Hashtbl.length t1 -1 in
				  let u2 = Hashtbl.length t2 -1 in
				  let xx = apply2 t1 t2 tt hh gg op u1 u2 in tt;;  

let rec restrict t j b =let tt = Hashtbl.create 1234 in
				  let hh = Hashtbl.create 1234 in
				  let yy = Hashtbl.add tt 0 (100000000000, 0, 0) in
				  let uu = Hashtbl.add tt 1 (100000000000, 0, 0) in
				  let u = Hashtbl.length t -1 in
				  let xx = restrict2 hh tt t u j b in tt;;  

(* let p1 = And(L 1, L 2);;
let tt1 = build p1 2;; 
Hashtbl.find tt1 3;;
Hashtbl.find tt1 2;;

let p1 = Or(L 1, L 2);;
let tt2 = build p1 2;; 
Hashtbl.find tt2 3;;
Hashtbl.find tt2 2;;

let andd u1 u2 = match (u1, u2) with
		(1,1) -> 1
	|   _ -> 0;;

let orr u1 u2 = match (u1, u2) with
		(0,0) -> 0
	|   _ -> 1;;

let iff u1 u2 = if u1 = u2 then 1 else 0;;

let tt3 = apply iff tt1 tt2;;
Hashtbl.length tt3;;
Hashtbl.find tt3 4;;
Hashtbl.find tt3 3;;
Hashtbl.find tt3 2;;

sat_count tt3;;
allsat tt3;;
anysat tt3;;
 *)

(* build 2 h1 t1 (Iff(L 1, L 2)) 1;; *)
(* Hashtbl.length t1;; *)

(* let p1 = L 1;;
let p2 = L 2;;
let t1 = build p1 1;;
let t2 = build p2 2;;
Hashtbl.find t1 2;;
Hashtbl.find t2 2;;
let t3 = apply iff t1 t2;;
Hashtbl.length t3;;
Hashtbl.find t3 4;;
Hashtbl.find t3 3;;
Hashtbl.find t3 2;;
 *)


(* let andd u1 u2 = match (u1, u2) with
		(1,1) -> 1
	|   _ -> 0;;

let p1 = Iff(L 1, L 2);;
let p2 = Iff(L 3, L 4);;
let p = And(p1, p2);;
let t1 = build p 4;;
Hashtbl.length t1;;
Hashtbl.find t1 0;;
Hashtbl.find t1 1;;
Hashtbl.find t1 2;;
Hashtbl.find t1 3;;
Hashtbl.find t1 4;;
Hashtbl.find t1 5;;
Hashtbl.find t1 6;;
Hashtbl.find t1 7;;

let t1 = build p1 2;;
let t2 = build p2 4;;
Hashtbl.length t1;;
Hashtbl.length t2;;
let t3 = apply andd t1 t2;;
Hashtbl.length t3;;
Hashtbl.find t3 0;;
Hashtbl.find t3 1;;
Hashtbl.find t3 2;;
Hashtbl.find t3 3;;
Hashtbl.find t3 4;;
Hashtbl.find t3 5;;
Hashtbl.find t3 6;;
Hashtbl.find t3 7;;
 *)

let andd u1 u2 = match (u1, u2) with
		(1,1) -> 1
	|   _ -> 0;;

let orr u1 u2 = match (u1, u2) with
		(0,0) -> 0
	|   _ -> 1;;

(*
 Ordering: x1 < x2 < x3
 *)
let vx1 = L(1);;
let vx2 = L(2);;
let vx3 = L(3);;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

(* compute NNF, CNF of p1 and Not(p1) *)
let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

(* build ROBDDs *)
let tt = build T 0;;
Hashtbl.length tt;;

let tf = build F 0;;
Hashtbl.length tf;;

let tvx1 = build vx1 1;;
let tp2 = build p2 3;;
let tp0 = build p0 2;;
let tp1 = build p1 3;;
let tp1' = build p1' 3;;
let tp1'' = build p1'' 3;;

let tnp1 = build np1 3;;
let tnp1' = build np1' 3;;
let tnp1'' = build np1'' 3;;

(* Testcase #1 *)
tp1 = tp1';;
tp1 = tp1'';;
tnp1 = tnp1';;
tnp1 = tnp1'';;

(* Testcase #2 *)
let tp1anp1 = apply andd tp1 tnp1;;
tp1anp1 = tf;;
let tp1onp1 = apply orr tp1 tnp1;;
tp1onp1 = tt;;

(* Testcase #3 *)
let tp1rv30 = restrict tp1 3 0;;
tp1rv30 = tp0;;
Hashtbl.length tp1rv30;;
Hashtbl.length tp0;;
Hashtbl.find tp1rv30 0;;
Hashtbl.find tp1rv30 1;;
Hashtbl.find tp1rv30 2;;
Hashtbl.find tp1rv30 3;;
Hashtbl.find tp1rv30 4;;
let tp1rv31 = restrict tp1 3 1;;
tp1rv31 =  tt;;

(* Testcase #4 *)
allsat tp1;; (* 4 solutions: { {x1 = 0, x2 = 0}, {x1 = 1, x2 = 1}, {x1 = 1, x2 = 0, x3 = 1}, {x1 = 0, x2 = 1, x3 = 1}} *)
anysat tp1;; (* any of the above *)
sat_count tp1;;

(* Testcase #5 *)
let tstp2tp1 = simplify tp2 tp1;;
tstp2tp1 = tt;;
let tstvx1tp1 = simplify tvx1 tp1;;
tstvx1tp1 = tp2;;
