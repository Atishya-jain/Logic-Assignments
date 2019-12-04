
let rec find_clause a xs = match a with
			[] -> []
		|  b::bs -> let l = find_in (Node("NOT", [b])) xs in if List.length l == 2 then (
																match l with
																	z::[x]::y -> let aa = remove b a in let bb = remove x z in 
																		(try faltu (List.map (mgu aa) bb) ([a]@[[b]]@l) with NON_UNIFIABLE -> find_clause bs xs)
															) else find_clause bs xs;;