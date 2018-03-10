open List
open Lambda
open Hw1
open Hw2_unify

type simp_type = 
	| S_Elem of string 
	| S_Arrow of simp_type * simp_type

type hm_lambda = 
	| HM_Var of string 
	| HM_Abs of string * hm_lambda 
	| HM_App of hm_lambda * hm_lambda 
	| HM_Let of string * hm_lambda * hm_lambda

type hm_type = 
	| HM_Elem of string 
	| HM_Arrow of hm_type * hm_type 
	| HM_ForAll of string * hm_type

module StringMap = Map.Make(String);;
module StringSet = Set.Make(String);;

exception NoSolution;;

let counter = ref 0;;
let basic_typename = "α";;
let basic_fun_name = "f";;
let arrow = "->";;
let forall = "∀";;

let sm_union m1 m2 = StringMap.fold (fun k v m -> StringMap.add k v m) m1 m2;;

let unused_name () = 
	counter := !counter + 1;
	"#" ^ (string_of_int !counter)

let unused_type () = 
	counter := !counter + 1;
	Var ("α" ^ (string_of_int !counter))

let unused_hm_type () =
	counter := !counter + 1;
	HM_Elem ("α" ^ (string_of_int !counter))

let rec get_system context expr goal equations = 
	match expr with
	| Lambda.Var x -> 
		(try (context, (let (_, e) = List.find (fun (t, e) -> t = x) context in e, goal) :: equations)
		with Not_found -> failwith "Not enough context")
	| Lambda.Abs (x, p) -> 
		let x_type = unused_type () and p_type = unused_type () in
		get_system ((x, x_type) :: context) p p_type ((goal, Fun (basic_fun_name, [x_type; p_type])) :: equations) 
	| Lambda.App (p, q) -> 
		let q_type = unused_type () in let p_type = Fun (basic_fun_name, [q_type; goal]) in
		let (c1, e1) = (get_system context p p_type equations) and 
			(c2, e2) = (get_system context q q_type equations) in (c1 @ c2, e1 @ e2)
;;

let rec remove_dups lst = 
	let rec impl lst res = 
		match lst with
		| [] -> res
		| h :: tail -> if List.mem h res then impl tail res else impl tail (h :: res) in
	impl lst []
;;

let build_system expr = 
	let (context, system) = get_system [] expr (unused_type()) [] in 
	(remove_dups context, remove_dups system);;

let rec term_to_type term = 
	match term with
	| Var x -> S_Elem x
	| Fun (basic_fun_name, l :: r :: []) -> S_Arrow (term_to_type l, term_to_type r)
	| _ -> failwith "unexpected algebraic term"
;;

let infer_simp_type expr = 
	counter := 0; 
	let (context, sys) = build_system expr in
	match solve_system sys with
	| Some solution -> Some (
		List.map (fun (x, t) -> (x, term_to_type t)) 
			(List.map (fun (x, t) -> (x, apply_substitution solution t)) context), 
		let (_, tmp) = List.find (fun (x, t) -> x = basic_typename ^ "1") solution in term_to_type tmp)
	| None -> None
;;

let rename_vars expr = 
	let rec sub_vars expr vars = 
		match expr with
		| HM_Elem t -> (try StringMap.find t vars with Not_found -> expr)
		| HM_Arrow (t1, t2) -> HM_Arrow (sub_vars t1 vars, sub_vars t2 vars)
		| HM_ForAll (_, _) -> failwith "internal quantifier found" in

	let rec rnm_vars expr vars = 
		match expr with
		| HM_ForAll (x, t) -> rnm_vars t (StringMap.add x (unused_hm_type ()) vars)
		| _ -> sub_vars expr vars in
	rnm_vars expr StringMap.empty
;;

let rec subst_to_hm_type subst t = 
	match t with
	| HM_Elem x -> (try let (v, e) = List.find (fun (var, expr) -> var = x) subst in e with Not_found -> t) 
	| HM_Arrow (t1, t2) -> HM_Arrow (subst_to_hm_type subst t1, subst_to_hm_type subst t2)
	| HM_ForAll (x, t1) -> HM_ForAll (x, subst_to_hm_type (List.filter (fun (v, e) -> v <> x) subst) t1)
;;

let subst_to_context subst context = 
	StringMap.map (fun t -> subst_to_hm_type subst t) context
;;

let rec alg_of_hm expr = 
	match expr with
	| HM_Elem x -> Var x
	| HM_Arrow (t1, t2) -> Fun (arrow, [alg_of_hm t1; alg_of_hm t2])
	| HM_ForAll (x, t) -> Fun (forall, [Var x; alg_of_hm t])
;;

let rec hm_of_alg term = 
	match term with
	| Var x -> HM_Elem x
	| Fun (f, l :: r :: []) when f = arrow -> HM_Arrow (hm_of_alg l, hm_of_alg r)
	| Fun (f, Var x :: r :: []) when f = forall -> HM_ForAll (x, hm_of_alg r)
	| _ -> failwith "unexpected algebraic term"
;;

let compose2 s1 s2 = 
	let substed = List.map (fun (x, t) -> (x, subst_to_hm_type s1 t)) s2 in
	let filtered = List.filter (fun (x1, t1) -> 
		(try let _ = List.find (fun (x2, t2) -> x1 = x2) s1 in false with Not_found -> true)) substed in 
		s1 @ filtered
;;

let rec compose subst_list = 
	match subst_list with 
	| [] -> []
	| h :: [] -> h
	| h :: tail -> compose2 h (compose tail)
;;

let free_vars expr = 
	let rec impl expr free except = 
		match expr with
		| HM_Elem x -> if not (List.mem x except || List.mem x free) then x :: free else free
		| HM_ForAll (x, p) -> impl p free (x :: except)
		| HM_Arrow (p, q) -> (impl p free except) @ (impl q free except) in
	impl expr [] [];;

let free_vars_context context = 
	StringMap.fold (fun k v l -> (free_vars v) @ l) context []
;;

let rec abstract context t = 
	let fv_t = free_vars t and fv_c = free_vars_context context in 
	List.fold_left (fun t v -> if List.mem v fv_c then t else HM_ForAll (v, t)) t fv_t
;;

let rec infer_hm_type context expr = 
	match expr with
	| HM_Var x -> (try ([], rename_vars (StringMap.find x context)) with Not_found -> raise NoSolution)
	| HM_App (e1, e2) -> 
		let (s1, t1) = infer_hm_type context e1 in 
		let (s2, t2) = infer_hm_type (subst_to_context s1 context) e2 and beta = unused_hm_type () in 
		(match solve_system [(alg_of_hm (subst_to_hm_type s2 t1), alg_of_hm (HM_Arrow (t2, beta)))] with
		| Some v -> let s = List.map (fun (x, t) -> (x, hm_of_alg t)) v in (compose [s; s2; s1], subst_to_hm_type s beta)
		| None -> raise NoSolution)
	| HM_Abs (x, e) -> 
		let beta = unused_hm_type () in 
		let (s, t) = infer_hm_type (StringMap.add x beta context) e in 
		(s, HM_Arrow (subst_to_hm_type s beta, t))
	| HM_Let (x, e1, e2) -> 
		let (s1, t1) = infer_hm_type context e1 in let new_context = subst_to_context s1 context in
		let (s2, t2) = infer_hm_type (StringMap.add x (abstract new_context t1) new_context) e2 in 
		(compose [s2; s1], t2)
;;

let get_context expr = 
	let rec impl expr free except = 
		match expr with
		| HM_Var x -> 
			if not (List.mem x except || StringMap.mem x free) 
			then StringMap.add x (unused_hm_type ()) free else free
		| HM_Abs (x, p) -> impl p free (x :: except)
		| HM_App (p, q) -> sm_union (impl p free except) (impl q free except)
		| HM_Let (x, p, q) -> sm_union (impl p free except) (impl q free (x :: except)) in
	impl expr StringMap.empty [];;

let rename expr = 
	let rec impl expr vars = 
		match expr with
		| HM_Var x -> (try StringMap.find x vars with Not_found -> expr)
		| HM_Abs (x, p) -> let v = unused_name () in HM_Abs (v, impl p (StringMap.add x (HM_Var v) vars))
		| HM_App (p, q) -> HM_App (impl p vars, impl q vars)
		| HM_Let (x, p, q) -> let v = unused_name () in let vs = StringMap.add x (HM_Var v) vars in 
			HM_Let (v, impl p vs, impl q vs) in

	impl expr StringMap.empty
;;

let algorithm_w expr = 
	counter := 0; 
	let e = rename expr in (try Some (infer_hm_type (get_context e) e) with NoSolution -> None)
;;


let p s = (print_string (s ^ "\n"));;

(* print map of string -> simple type *)
let pst_map m =
	let rec impl l =
		match l with
		|[] -> print_string "\n"
		|((k, (S_Elem e))::t) -> print_string (k ^ " "); p e; impl t 
		|_ -> () in

	impl (StringMap.bindings m)
;; 

let string_of_simp_type st = 
	let rec impl st str = 
		match st with 
		| S_Elem v -> str ^ v
		| S_Arrow (x, y) -> str ^ (impl x "") ^ " -> " ^ (impl y "") in
	impl st ""
;;

(* print string *)
let ps s = 
	print_string s;
	print_string "\n"
;;

(* string of hindley milner type *)
let rec string_of_hmt hmt = 
	match hmt with
    | HM_Elem v -> v
    | HM_Arrow(hmt1, hmt2) -> "(" ^ (string_of_hmt hmt1) ^ " -> " ^ (string_of_hmt hmt2) ^ ")" 
    | HM_ForAll(v, hmt) -> "∀" ^ v ^ "." ^ (string_of_hmt hmt)
;;

(* string of hindley milner lambda ie term *)
let rec string_of_hml hml =
	match hml with 
	| HM_Var v -> v
	| HM_Abs(v, hml) -> ("\\" ^ v ^ "." ^ "(" ^ (string_of_hml hml) ^ ")")
	| HM_App(hml1, hml2) -> ("(" ^ (string_of_hml hml1) ^ " " ^ (string_of_hml hml2) ^ ")")
	| HM_Let(v, hml1, hml2) -> ("let " ^ v ^ " = (" ^ (string_of_hml hml1) ^ ") in (" ^ (string_of_hml hml2)) ^ ")"
;;


(* print context *)
let pcxt m = StringMap.iter (fun k v -> (print_string ("{" ^ k ^ " " ^ (string_of_hmt v) ^ "}\n"))) m;;

(* print set of strings *)
let print_set s = StringSet.iter (fun s -> (print_string (s ^ "\n"))) s;;



let t1t = "let id = \\x.x in \\f.\\x.id (id (id x))";;
let t2t = "let id = \\x.x in \\f.\\x.id f (id (id x))";; 
let t3t = "let id = \\x.x in \\f.\\x.id f (id x (id x))";;
let t4t = "let id = \\t.t in \\f.\\x.(id f) (id x)";;
let t5t = "\\f.\\x.f (f x)";; (* (a -> a) -> a -> a *)
let t6t = "let id = \\t.t in (id f) (id x)";; 
let pow = "\\a.\\b.b a";;

let t1t = HM_Let ("id", HM_Abs ("x", HM_Var ("x")), HM_Abs ("f", HM_Abs ("x", HM_App (HM_Var ("id"), HM_App (HM_Var ("id"), HM_App (HM_Var ("id"), HM_Var ("x")))))));;
let t2t = HM_Let ("id", HM_Abs ("x", HM_Var ("x")), HM_Abs ("f", HM_Abs ("x", HM_App (HM_App (HM_Var ("id"), HM_Var ("f")), HM_App (HM_Var ("id"), HM_App (HM_Var ("id"), HM_Var ("x")))))));;
let t3t = HM_Let ("id", HM_Abs ("x", HM_Var ("x")), HM_Abs ("f", HM_Abs ("x", HM_App (HM_App (HM_Var ("id"), HM_Var ("f")), HM_App (HM_App (HM_Var ("id"), HM_Var ("x")), HM_App (HM_Var ("id"), HM_Var ("x")))))));;
let t4t = HM_Let ("id", HM_Abs ("t", HM_Var ("t")), HM_Abs ("f", HM_Abs ("x", HM_App (HM_App (HM_Var ("id"), HM_Var ("f")), HM_App (HM_Var ("id"), HM_Var ("x"))))));;
let t5t = HM_Abs ("f", HM_Abs ("x", HM_App (HM_Var ("f"), HM_App (HM_Var ("f"), HM_Var ("x")))));;
let t6t = HM_Let ("id", HM_Abs ("t", HM_Var ("t")), HM_App (HM_App (HM_Var ("id"), HM_Var ("f")), HM_App (HM_Var ("id"), HM_Var ("x"))));;
let pow = HM_Abs ("a", HM_Abs ("b", HM_App (HM_Var ("b"), HM_Var ("a"))));;

let test expr =
	ps (string_of_hml expr);
	match algorithm_w expr with
	| None -> ps "Unable to infer type with W"
	| Some (cxt, hmt) -> 
		(ps ("Infered type: " ^ (string_of_hmt hmt));
		List.iter (fun (v, hmt) -> ps ("{" ^ v ^ " : " ^ (string_of_hmt hmt) ^ "}")) cxt;
		ps "\n");; 

test t1t;;

match infer_simp_type (Hw1.lambda_of_string "\\x.\\y.x") with
	| Some (f, s) ->print_string (("Resulting type: " ^ (string_of_simp_type s)) ^ "\n")
	| None -> p "No type";;