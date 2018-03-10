open Lambda

type peano = Z | S of peano

(* Basic Peano operations*)

let rec peano_of_int n = match n with
	0 -> Z
	| n -> S (peano_of_int (n - 1));;

let rec int_of_peano p = match p with
	Z -> 0
	| S x -> 1 + int_of_peano x;;

let rec peano_to_string peano_num = match peano_num with
	Z -> "0"
	| S x -> (peano_to_string x) ^ "'";;

let inc peano_num =
	S peano_num;;

let rec add a b = match b with
	Z -> a
	| S prev -> S(add a prev);;

let rec sub a b = match (a, b) with 
	(a, Z) -> a
	| (Z, b) -> Z
	| (S a, S b) -> sub a b;;

let rec mul a b = match (a, b) with
	(b, Z) -> Z
	| (a, S b) -> add (mul a b) a;;

let rec power a b = match (a, b) with
	(a, Z) -> S Z
	| (a, S b) -> mul (power a b) a;;


(*Reverse & MergeSort*)


let rec rev xs =
	let rec rev_impl xs rxs = match xs with
		[] -> rxs
		| x::xs -> rev_impl xs (x::rxs) in
	rev_impl xs [];; 

let rec print_list_int xs = match xs with
	[] -> print_string "\n"; ()
        | x::xs -> print_int x; print_list_int xs;;

let merge_sort xs =
	let split_in_two_equal xs =
		let rec split_impl xs ls rs = match xs with
			h1::h2::t -> split_impl t (h1::ls) (h2::rs)
			| h1::[] -> ((h1::ls), rs)
			| [] -> (ls, rs) in
		split_impl xs [] [] in

	let merge_two_sorted l1 l2 =
		let rec merge_impl l1 l2 ans =
			match (l1, l2) with
			([], []) -> ans
			| ([], h::t) -> merge_impl l1 t (h::ans)
			| (h::t, []) -> merge_impl t l2 (h::ans)
			| (h1::t1, h2::t2) -> 
				if h1 < h2 then merge_impl t1 l2 (h1::ans)
					   else merge_impl l1 t2 (h2::ans) in
		let tup = merge_impl l1 l2 [] in
		rev tup in

	let rec merge_impl xs =
		match xs with
		[] -> xs
		| x::[] -> xs
		| h::t -> 
			(let tup = split_in_two_equal xs in
			let (f, s) = tup in
			merge_two_sorted (merge_impl f) (merge_impl s)) in
	merge_impl xs;; 	


(* Lambda expressions *)

(* lambda -> string *)
let string_of_lambda l =
	let rec impl l s =
		match l with
		Var v -> s ^ v 
		| Abs (v, x) -> s ^ "(" ^ "\\" ^ v ^ "." ^ (impl x "") ^ ")" 
		| App (x, y) -> s ^ "(" ^ (impl x "") ^ " " ^ (impl y "") ^ ")" in
	impl l "";;

(* string -> lambda *)
let lambda_of_string s =
	let s = s ^ ";" in
	let pos = ref 0 in (*pos of first unprocessed element*)
	let get () = s.[!pos] in (*get next unprocessed element*)
	let next () = if !pos < String.length s - 1 then pos := !pos + 1 in (*increment pos*)
	let eat x = if get () = x then next () else failwith "Incorrect input string" in
	let is_end () = if (get ()) = ';' then true else false in		
		
	(* unit -> string *)
	let parse_name_str () =
		let rec impl s =
			if (get ()) <> ' ' && (get ()) <> '.' && (get ()) <> ')' && not (is_end ())  
				then 
					let c = get() in
					next();
					impl (s ^ String.make 1 c)
				else s in
		impl "" in	

	(* unit -> lambda *)
	let parse_name () = 
		Var(parse_name_str ()) in


	(* unit -> lambda *)
	let rec parse_lambda () =
		let ans = 	
			match (get ()) with 
			'\\' -> 
				parse_abs ()
			| '(' -> 
				(eat '(';
				let ret = parse_lambda () in
				eat ')'; 
				ret)
			| _ ->  
				parse_name () in
		try_parse_application ans 

	(* unit -> lambda *)
	and parse_abs () = 
		eat '\\';
		let name = parse_name_str () in
		eat '.';
		Abs(name, parse_lambda ())

	(* function checks if expression continues and makes app left associative *)
	(* lambda -> lambda *)	
	and try_parse_application prev = 
		if (is_end () || s.[!pos] = ')') then prev 
		else    (eat ' '; 
			match (get ()) with 
			'\\' -> 
				(let ans = parse_abs () in
				 try_parse_application (App (prev, ans))) 
			| '(' -> 
				(eat '(';
				let ans = parse_lambda () in
				eat ')'; 
				try_parse_application (App(prev, ans)))
			| _ ->  
				(let ans = (parse_name ()) in
				try_parse_application (App(prev, ans)))
			) in

	parse_lambda ();;

(*
Printf.printf "%d\n" (int_of_peano (peano_of_int 10000));;
print_string (peano_to_string (peano_of_int 10)); print_string "\n";;

print_string (string_of_lambda (lambda_of_string "(x)")); print_string "\n";; 
print_string (string_of_lambda (lambda_of_string "(((((((\\y.y)))))))")); print_string "\n";; 
print_string (string_of_lambda (lambda_of_string "((z)) (\\x.\\y.((x y)))")); print_string "\n";;
print_string (string_of_lambda (lambda_of_string "x y z")); print_string "\n";;
print_string (string_of_lambda (lambda_of_string "\\l.\\i.\\f.\\e.(l) (i) (f) (longnaame)")); print_string "\n";;


print_string (string_of_lambda (lambda_of_string "x y z")); print_string "\n";;
print_string (string_of_lambda (lambda_of_string "(x y) z")); print_string "\n";;

*)