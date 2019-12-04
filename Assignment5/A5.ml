type term = V of string | Node of string * (term list);;
type pair = Pair of string * int;;
type sigma = Subs of (term * term);;
exception Error of string;;

exception Wrong_term;;
exception NON_UNIFIABLE;;

(* Helper Functions *)
(* Returns false if pair is found *)
let rec chk_Presence a b = match (a,b) with
			([],z) -> true
		|   ((Pair(x,l))::xs,(Pair(c,d))) -> if (x = c) then false else if (l<0) then false else chk_Presence xs b;;

let rec chkArity x y = match y with
			[] -> raise (Wrong_term)
		|   (Pair(q,w))::xs -> if (x = q) then w else chkArity x xs;;

let rec find_Var var li = match li with
			[] -> false	
		|	V(z)::xs -> if (var = V(z)) then true else find_Var var xs;;

let rec find_var_sig var li = match li with
			[] -> raise(Wrong_term)	
		|	Subs(V(z),b)::xs -> if (var = V(z)) then b else find_var_sig var xs;;

(* -------------------Main Program starts -------------------- *)

(* 1st func *)
let rec check_sig1 a iter count = match a with
				[] -> if ((count = 0)&&(iter <> 0)) then false else true
			|   (Pair(x,y)) :: xs -> if (y<0) then false 
										else if ((chk_Presence xs (Pair(x,y))) = false) then false 
										else if (y = 0) then check_sig1 xs (iter+1) (count+1)
										else check_sig1 xs (iter+1) count;;

(* a = signature list of type Pair*)
let check_sig a = check_sig1 a 0 0;;

(* 2nd func *)
(* Checking if arity of every term in signature matches with that in term *)
let rec wfterm1 signList e term = match term with
			V(z) -> e
		|   Node(x,y) -> let arri = chkArity x signList in 
							if ((arri = 0) && (List.length y = 0)) then e 
							else if (arri = List.length y) then List.fold_left (wfterm1 signList) true y 
							else false ;;

(* signList = signature list and term = Term *)
let wfterm signList term = wfterm1 signList true term;;							  

(* 3rd Func *)
let rec ht term = match term with
			V(z) -> 0
		|   Node (a,[]) -> 0
		|   Node (a,x) -> 1 + List.fold_left max (-1) (List.map ht x);;

(* 4th function *)
let rec size1 e term = match term with
			V(z) -> 1+e
		|   Node (a,[]) -> 1+e
		|   Node (a,x) -> List.fold_left size1 (e+1) x;;
let size term = size1 0 term;;		

(* 5th function *)
let rec vars1 l term = match term with
			V(z) -> if (List.mem (V(z)) l) then l else l@[V(z)]
		|   Node(x,y) -> List.fold_left vars1 l y;;
let vars term = vars1 [] term;;

(* 7th function *)
(* Traverses a tree and applies all substitutions just once and non recursive *)
let rec subst s term = match term with
		    Node(q,[]) -> Node(q,[])
		|   Node(q,x) -> Node(q,(List.map (subst s) x))
		|	V(z) -> try find_var_sig (V(z)) s with Wrong_term -> V(z);; 

(* 6th function *)
(* if a subst is there in s1 and s2 both then removed from s1, if its like x->y and y->z then we set it to x->z rest union*)
let rec composition1 l s1 s2 = match s1 with
			[] -> l@s2
		|   (Subs(a,b))::xs -> let v1 = (subst s2 b) in if (v1 = a) then composition1 l xs s2 else composition1 (l@[Subs(a,v1)]) xs s2;;
let composition s1 s2 = composition1 [] s1 s2;; 

(* 8th function *)
(* MyMap applies updated subst to future terms and goes on like this *)
let rec myMap f e l1 l2 = match (l1,l2) with
			([],[]) -> e
		|   (x::xs,y::ys) -> myMap f (composition e (f [] (subst e x) (subst e y))) xs ys;;

let rec mgu1 l t1 t2 = match (t1,t2) with
		    (V(z), V(y)) -> if (z <> y) then l@[Subs(V(z),V(y))] else l
	    |   (Node(a,b), V(z)) -> if (b = []) then l@[Subs(V(z),Node(a,b))] 
								   else if ((find_Var (V(z)) (vars(Node(a,b)))) = false) then l@[Subs(V(z),Node(a,b))] 
								   		else raise (NON_UNIFIABLE)
	    |   (V(z), Node(a,b)) -> if (b = []) then l@[Subs(V(z),Node(a,b))]
								   else if ((find_Var (V(z)) (vars(Node(a,b)))) = false) then l@[Subs(V(z),Node(a,b))] 
								   		else raise (NON_UNIFIABLE)	     
		|   (Node(a,b), Node(c,d)) -> if (b = []) then 
										if (d = []) then 
										  if (a = c) then l else raise (NON_UNIFIABLE)
										else raise(NON_UNIFIABLE)
									  else if (d = []) then raise(NON_UNIFIABLE) 
									  else if (a = c) then myMap mgu1 l b d else raise(NON_UNIFIABLE);;
let mgu t1 t2 = mgu1 [] t1 t2;;

let rec remove a l = match l with
			[] -> []
		|   x::xs -> if x = a then remove a xs else [x]@(remove a xs);;

let rec join1 lst term = match (lst,term) with
		((a::xs), b) -> if a = b then lst else a::(join1 xs term)
	|   ([], b) -> [b]
	|   (a, _) -> a;;

let rec union lst1 lst2 = match lst2 with
		[]  -> lst1
	|   a::xs -> union (join1 lst1 a) xs;;

let rec t_str a = match a with
		V(p) -> p
	|   Node(a, [b]) -> a;; 

let r_not a = match a with
		Node("NOT", [y]) -> y
	|   _ -> a;;

let rec resolve k = match k with 
			a::[l1]::b::[l2]::xs -> let d = remove l1 a in let e = remove l2 b in ((* Printf.printf "%s %s\n" (t_str l1) (t_str (r_not l2));  *)let s = mgu l1 (r_not l2) in (let uni = union d e in List.map (subst s) uni))
		|   _ -> raise(Error "Not able to resolve");;

(* let mgus a b = try (let x = mgu a b in Node("NOT", [b])) with NON_UNIFIABLE -> raise(NON_UNIFIABLE);; *)

let rec final_find b a = match a with
			[] -> []
		|   x::xs -> ( 
					match x with 
							Node("NOT", [q]) -> (try let yy = mgu b q in [[x]] with NON_UNIFIABLE -> final_find b xs)
				        |   _ -> final_find b xs 
		    		);;
		        (* if Node("NOT",[b]) = x then [[x]] else final_find b xs;; *)

let rec find_in b bs = match bs with
			[] -> []
		|   a::xs -> let x = final_find b a in if List.length x = 1 then ([a]@x) else find_in b xs;;

(* Optimise for set comparison for x and a *)
let rec present a l = match l with
		[] -> false
	|	x::xs -> if x = a then true else present a xs;;

let rec find_clause a xs = match a with
			[] -> []
		|  b::bs -> let l = find_in b xs in if List.length l == 2 
															then let xx = ([a]@[[b]]@l) in let yy = resolve xx in 
															( 
																if yy = a then match xs with
																			[] -> []
																		|   n::nn -> let aa = find_clause a nn in if List.length aa == 0 then find_clause bs xs else aa
																else if present yy xs then match xs with
																			[] -> []
																		|   n::nn -> let aa = find_clause a nn in if List.length aa == 0 then find_clause bs xs else aa 
																else xx
															)
															else find_clause bs xs;;

let rec sel_clause e l = match l with
			[] -> raise(Error "No more clause found to unify")
		|   a::xs -> let b = (find_clause a (e@xs)) in if List.length b  == 4 then b else sel_clause (e@[a]) xs;;

let rec resolution l = match l with 
			[] -> true
		|   x -> let cs = sel_clause [] l in let cl = resolve cs in if List.length cl = 0 then false else resolution (l@[cl]);;

(* Example 1 *)
let goal = [Node("NOT", [V("x")]); Node("NOT", [V("y")])];;
let rule1 = [V("x"); Node("NOT", [V("y")])];;
let rule2 = [Node("NOT", [V("x")]); V("y")];;
let test1 = [rule1; rule2; goal];;
resolution test1;;

(* Example 2 (Variables renamed) *)
let goal = [Node("NOT", [V("x")]); Node("NOT", [V("y")])];;
let rule1 = [V("z"); Node("NOT", [V("w")])];;
let rule2 = [Node("NOT", [V("q")]); V("r")];;
let test1 = [rule1; rule2; goal];;
resolution test1;;

(* Example 3 *)
let goal1 = [Node("NOT", [V("y")])];;
let rule1 = [V("z"); Node("NOT", [V("w")])];;
let test1 = [rule1; goal1];;
resolution test1;;

(* Example 4 *)
let goal1 = [Node("NOT", [V("y")]); Node("NOT", [Node("OR", [V("w"); V("q")])])];;
let fact1 = [V("y")];;
let fact2 = [V("w")];;
let test1 = [goal1; fact1; fact2];;
resolution test1;;

(* Example 5 (Does not resolve but terminates) *)
let test1 = [[V("x"); V("y"); V("z")]; [Node("NOT", [V("x")]); V("y"); V("z")]];;
resolution test1;;


(* let aval = [[Node("NOT", [V("x")])]; [V("y"); V("z")]];;
resolution aval;;

let aval = [[V("x")]; [V("y")]; [Node("NOT", [V("x")]); Node("NOT", [V("y")])]];;
resolution aval;;
 
let aval = [[Node("NOT", [V("x")]); Node("NOT", [V("y")])]; [V("y")]; [Node("SYM", [])]];;
resolution aval;;

let aval = [[V("x");Node("NOT", [V("y")])]; [Node("NOT", [V("x")]); Node("NOT", [V("z")]); V("d")]; [V("y")]; [V("z")]; [Node("NOT", [V("d")])]];;
resolution aval;;
 *)
(* 
(* Example 1 *)
let goal = [Node("NOT", [V("x")])];;
let fact = [Node("And",[Node("T",[]);Node("T",[])])];;
let form = [goal;fact];;
resolution form;;

(* Example 2 *)
let goal = [Node("NOT", [V("x")]); Node("NOT", [Node("And",[V("x");Node("x1",[])])])];;
let fact1 = [V("y")];;
let fact2 = [Node("And",[V("z");Node("z1",[])])];;
let form = [goal;fact1;fact2];;
resolution form;;

(* Example 3 *)
let goal = [Node("NOT", [Node("T",[])]); Node("NOT", [Node("F",[])])];;
let rule1 = [Node("T",[]); Node("NOT", [Node("F",[])])];;
let rule2 = [Node("NOT", [Node("T",[])]); Node("F",[])];;
let fact = [Node("T",[])];;
let form = [goal;rule1;rule2;fact];;
resolution form;;

(* Example 4 *)
let goal = [Node("NOT", [Node("x",[])])];;
let rule1 = [Node("x",[]); Node("NOT", [Node("y",[])])];;
let rule2 = [Node("y",[]); Node("NOT", [Node("z",[])])];;
let rule3 = [Node("z",[]); Node("NOT", [Node("w",[])])];;
let fact = [Node("w",[])];;
let form = [goal;rule1;rule2;rule3;fact];;
resolution form;; *)

(* let sym0 = Node("0",[]);;
let sym1 = Node("1",[sym0]);;
let sym1' = Node("1'",[V("x")]);;
 *)
(* 
let a = [Node("NOT", [sym0]); Node("NOT", [sym1])];; (* Goal clause *)
let b = [sym0];;
let c = [sym1];;
resolution [a;b;c];;

let a = [Node("p", [V("x"); V("y")])];;
let b = [Node("NOT", [Node("p", [sym0; sym0])])];;
resolution [a;b];;

let a = [Node("NOT", [sym0]); Node("NOT", [sym1]); Node("NOT", [sym1'])];; (* Goal clause *)
let b = [sym0];;
let c = [sym1];;
let d = [Node("1'", [sym0])];;
resolution [a;b;c;d];;
 *)
(* let a = [Node("NOT", [sym0]); Node("NOT", [sym1]); Node("NOT", [sym1'])];; (* Goal clause *)
let b = [sym0; Node("NOT", [sym1]); Node("NOT", [sym1'])];;
let c = [sym1; Node("NOT", [sym1'])];;
let d = [Node("1'", [sym0])];;
resolution [a;b;c;d];;

let a = [sym0; sym1; Node("NOT", [sym1])];;
let b = [Node("NOT", [sym0])];;
let c = [Node("NOT", [sym1])];;
let d = [sym0];;
resolution [a;b;c;d];;

let a = [sym0; sym1];;
let b = [Node("NOT", [sym0]); sym1];;
let c = [sym0; Node("NOT", [sym1])];;
let d = [Node("NOT", [sym0]); Node("NOT", [sym1])];;
resolution [a;b;c;d];; *)