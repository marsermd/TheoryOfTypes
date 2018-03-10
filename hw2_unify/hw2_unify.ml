open List

type algebraic_term = Var of string | Fun of string * (algebraic_term list)

exception NotSolvable;;

(* algebraic_term -> string *)
let term_to_string at =
	let rec impl at =
		match at with
			Var v -> v
			| Fun(f, args) -> f ^ "(" ^ (impl_l args) ^ ")"
	and impl_l l =
		match l with
			[] -> "" 
			| (h::[]) -> (impl h) (* for last arg no last space *)
			| (h::t) -> (impl h) ^ " " ^ (impl_l t) in
	impl at;;

(* eq -> string *)
let equation_to_string eq =
	let lhs, rhs = eq in
	term_to_string lhs ^ " = " ^ term_to_string rhs
;;

(* sys -> string *)
let rec system_to_string sys =
	List.fold_left (^) "" (List.map (fun (l) -> (equation_to_string l) ^ "\n") sys)
;;			

(* solution line -> string *)
let solution_line_to_string sol =
	let lhs, rhs = sol in
	lhs ^ " = " ^ term_to_string rhs
;;

(* solution -> string *)
let solution_to_string sol =
	List.fold_left (^) "" (List.map (fun (l) -> (solution_line_to_string l) ^ "\n") sol)
;;			

(* Println algebraic term *)
let pat at = 
	print_string (term_to_string at);
	print_string "\n"
;;

(* Println equation *)
let peq eq =
	print_string (equation_to_string eq);
	print_string "\n"
;;

let psys sys = 
	print_string (system_to_string sys);
	print_string "\n"
;;

(* Println solution *)
let psol sol =
	print_string (solution_to_string sol);
	print_string "\n"
;;

let rec get_fresh_name sys =
	let rec get_name term = 
		match term with
		| Var x -> x
		| Fun (f, args) -> f ^ (List.fold_left (^) "" (List.map get_name args))
	in let names = List.map (fun (l, r) -> get_name l ^ get_name r) sys in
	"x" ^ (List.fold_left (^) "" names)
;;

let system_to_equation system = 
	let name = get_fresh_name system and (lhs, rhs) = List.split system in 
	(Fun (name, lhs), Fun (name, rhs))
;;

let rec apply_substitution rules term = 
	match term with
	| Var x -> 
		(try let (v, e) = List.find (fun (var, expr) -> var = x) rules in e 
		with Not_found -> term)
	| Fun (f, args) -> Fun (f, List.map (fun arg -> apply_substitution rules arg) args)
;;

let rec equals t1 t2 = 
	match (t1, t2) with
	| (Var x, Var y) -> x = y
	| (Fun (f, args1), Fun (g, args2)) -> f = g && List.length args1 == List.length args2 && List.for_all2 equals args1 args2
	| _ -> false
;;

let rec check_solution subst system = 
	List.for_all 
		(fun (l, r) -> equals (apply_substitution subst l) (apply_substitution subst r)) 
		system
;;

let rec used var expr = 
	match expr with
	| Var x -> x = var
	| Fun (f, args) -> List.exists (used var) args
;;

let rec unify todo processed = 
	match todo with
	| [] -> 
		List.map 
			(fun (l, r) -> 
				match (l, r) with 
				| (Var x, _) -> (x, r) 
				| _ -> failwith "Something went wrong"
			) processed
	| (l, r) :: tail ->
		if equals l r then unify tail processed else
		match (l, r) with
		| (Var x, _) ->
			if used x r then raise NotSolvable else
			let mapping = 
				fun (a, b) -> (apply_substitution [(x, r)] a, apply_substitution [(x, r)] b) in
			unify (List.map mapping todo) ((l, r) :: (List.map mapping processed))
		| (Fun (_, _), Var _) -> unify ((r, l) :: tail) processed
		| (Fun (f, a1), Fun (g, a2)) -> 
			if f = g then 
				(try let decomposed = List.combine a1 a2 in unify (decomposed @ tail) processed
				with Invalid_argument msg -> raise NotSolvable)
			else raise NotSolvable
;;

let rec solve_system system = (try Some (unify system []) with NotSolvable -> None);;


let sys0 = [(Var "a", Var "b"); (Var "c", Var "d")];;
let sys1 = [(Fun("f",[Var "x"]), Fun("f",[Fun("g",[Var "y"])])); (Var "y", Fun("h",[Var "p"]))];;
let sys2 = [(Fun("f",[Var "a"]), Var "b")];;
let sys3 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"])];;

let isys0 = [Fun("f",[Var "x"]), Fun("f",[Var "x"; Var "y"])];;
let isys1 = [Fun("f",[Var "y"; Fun("h",[Var "x"; Var "y"])]), Fun("f",[Fun("g",[Var "a"; Var "b"]); Fun("h", [Var "x"; Var "x"])]); Fun("h", [Var "x"; Var "y"]), Fun("h", [Var "a"; Var "a"])];;

(*
let to_solve = sys3 in
	psys(to_solve);
	print_string "--------------- \n";
	let solved = solve_system (to_solve) in 
		match solved with
		| None -> 
			print_string "None \n"
		| Some solved -> 
			psol solved
;;*)