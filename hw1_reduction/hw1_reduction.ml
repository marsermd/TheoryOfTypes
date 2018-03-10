open Lambda
open Hw1
open List
open Map

type lambda_memo = 
	| Var_ref of string
	| Abs_ref of string * lambda_memo ref
	| App_ref of lambda_memo ref * lambda_memo ref

module StringMap = Map.Make(String);;


let counter = ref 0;;

(* unit -> string *)
let unusedVar () = 
	counter := !counter + 1;
	"#" ^ (string_of_int !counter)
;;

(* lambda -> string *)
let rec get_fresh_name expr = 
	match expr with
	| Var x -> x ^ x
	| App (p, q) -> (get_fresh_name p) ^ (get_fresh_name q)
	| Abs (x, p) -> x ^ (get_fresh_name p)
;;


(* lambda -> string list -> string list -> string list *)
let rec get_free_vars expr free except = 
	match expr with
	| Var x -> 
		if not (List.mem x free) && not (List.mem x except) then x :: free 
		else free
	| App (p, q) -> get_free_vars p (get_free_vars q free except) except
	| Abs (x, p) -> get_free_vars p free (x :: except)
;;

(* lambda -> string list *)
let free_vars expr = get_free_vars expr [] [];;

(* lambda -> lambda -> string -> bool *)
let rec free_to_subst what expr var = 
	match expr with
	| Var _ -> true
	| Abs (x, p) -> x = var || (not (List.mem x (free_vars what)) && free_to_subst what p var)
	| App (p, q) -> free_to_subst what p var && free_to_subst what q var
;;

(* lambda -> lambda -> string -> lambda *)
let rec subst what expr var = 
	match expr with
	| Var x -> if x = var then what else expr
	| App (p, q) -> App (subst what p var, subst what q var)
	| Abs (x, p) -> if x = var then expr else Abs (x, subst what p var)
;;

(* lambda -> bool *)
let rec is_normal_form expr = 
	match expr with
	| Var _ -> true
	| Abs (_, p) -> is_normal_form p
	| App (Abs (_, _), _) -> false
	| App (p, q) -> is_normal_form p && is_normal_form q
;;

(* lambda -> lambda -> bool *)
let rec is_alpha_equivalent l1 l2 =
	(* fresh_name := (get_fresh_name l1) ^ (get_fresh_name l2); *)
	match l1, l2 with
		| Var x1, Var x2 -> x1 = x2
		| App (p1, q1), App (p2, q2) -> is_alpha_equivalent p1 p2 && is_alpha_equivalent q1 q2
		| Abs (x1, p1), Abs (x2, p2) -> 
			let t = Var (unusedVar()) in
			is_alpha_equivalent (subst t p1 x1) (subst t p2 x2)
		| _ -> false
;;

(* lambda -> lambda StringMap.t -> lambda *)
let rec real_rename expr vars = 
	match expr with
	| Var x -> (try StringMap.find x vars with Not_found -> expr)
	| Abs (x, p) -> let name = unusedVar() in Abs (name, real_rename p (StringMap.add x (Var name) vars))
	| App (p, q) -> App (real_rename p vars, real_rename q vars)
;;

(* lambda -> lambda *)
let rename expr = real_rename expr StringMap.empty;;

(* lambda -> lambda *)
let rec reduce_normal expr = 
	if is_normal_form expr then expr 
	else match expr with
	| Var _ -> expr
	| Abs (x, p) -> Abs (x, reduce_normal p)
	| App (Abs (x, p), q) -> subst q p x
	| App (p, q) -> if is_normal_form p then App (p, reduce_normal q) else App (reduce_normal p, q)
;;

(* lambda -> lambda *)
let normal_beta_reduction expr = reduce_normal (rename expr);;

(* lambda_memo ref -> lambda *)
let rec from_ref expr = 
	match !expr with
	| Var_ref x -> Var x
	| Abs_ref (x, p) -> Abs (x, from_ref p)
	| App_ref (p, q) -> App (from_ref p, from_ref q)
;;

(* lambda -> lambda_memo ref*)
let rec to_ref expr = 
	match expr with
	| Var x -> ref (Var_ref x)
	| Abs (x, p) -> ref (Abs_ref (x, to_ref p))
	| App (p, q) -> ref (App_ref (to_ref p, to_ref q))
;;

(* lambda_memo ref -> lambda_memo StringMap.t -> lambda_memo ref *)
let rec copy_renaming expr vars = 
	match !expr with
	| Var_ref x -> (try ref (StringMap.find x vars) with _ -> ref (Var_ref x))
	| Abs_ref (x, p) -> 
		let name = unusedVar() in ref (Abs_ref (name, copy_renaming p (StringMap.add x (Var_ref name) vars)))
	| App_ref (p, q) -> ref (App_ref (copy_renaming p vars, copy_renaming q vars))
;;

(* lambda_memo ref -> lambda_memo ref *)
let copy expr = copy_renaming expr StringMap.empty;;

(* lambda_memo ref -> lambda_memo ref -> string -> unit *)
let rec subst_lref what expr var = 
	match !expr with
	| Var_ref x -> if x = var then expr := !what
	| Abs_ref (x, p) -> if x <> var then subst_lref what p var
	| App_ref (p, q) -> subst_lref what p var; subst_lref what q var
;;

(* lambda_memo ref -> bool *)
let rec reduction_with_memoisation expr = 
	match !expr with
	| Var_ref _ -> false
	| Abs_ref (x, p) -> reduction_with_memoisation p
	| App_ref (p, q) -> 
		match !p with
		| Abs_ref(x, m) -> expr := !(copy m); subst_lref q expr x; true
		| _ -> reduction_with_memoisation p || reduction_with_memoisation q 
;;

(* lambda -> lambda *)
let reduce_to_normal_form expr = 
	(* fresh_name := get_fresh_name expr; *)
	let expr_ref = copy (to_ref expr) in 
		while reduction_with_memoisation expr_ref do () done; from_ref expr_ref
;;

let t0 = "(\\f.\\x.f x) x a";; (* x a *)
let k = "(\\x.\\y.x)";;
let i = "(\\x.x)";;
let s = "(\\x.\\y.\\z.x z (y z))";;
let w = "(\\x.x x)";;
let omega = "(" ^ w ^ " " ^ w ^ ")";; (* no normal form *)

let t1 = k ^ " a " ^ omega;; (* a *)
let t2 = "(\\x.x) x x";; (* x x *)
let t3 = "(\\f.\\x.f x) (\\f.\\x.x)";; 
let t4 = "(\\x.((\\f.(\\x.x)) x))";;

let t5 = "(\\f.\\x.f (f (f (f x)))) (\\f.\\x.f (f (f (f x))))";; (* 4 ^ 4 *)
let t6 = "(\\f.\\x.f (f (f (f (f x))))) (\\f.\\x.f (f (f (f (f x)))))";; (* 5 ^ 5*)

let t7 = "(\\x.(x x x)) ((\\x.x) x)";;

(*
print_string (Hw1.string_of_lambda (reduce_to_normal_form (Hw1.lambda_of_string t7)));;print_string "\n";;
*)