type peano = Z | S of peano;;
type 'a list = Nil | Cons of 'a*('a list);;

let rec peano_of_int x = 
	if (x == 0) then 	Z 
	else 				S (peano_of_int (x - 1));;

let rec int_of_peano p = match p with
		| Z -> 0
		| S x -> 1 + int_of_peano x;;

let inc x = S x;;

let rec add x y = match y with 
		| Z -> x 
		| S y -> S(add x y);;

let rec sub x y = match (x, y) with
		| (Z, _) -> Z
		| (x, Z) -> x
		| (S x, S y) -> sub x y;;
		
let rec mul x y =  match y with
		| Z -> Z
		| S y -> add (mul x y) x;;

let rec power x y = match y with
		| Z -> S Z
		| S y -> mul (power x y) x;;

let rec append x y = match x with
		| Nil -> y
		| Cons(n, x) -> Cons(n, append x y);;
                     
let rev x = 
	let rec reverse x y = match x with
		| Nil -> y
		| Cons(n, x) -> reverse x (Cons(n, y)) in
	reverse x Nil;;

let merge_sort x = failwith "Not implemented";;
                     					 
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda

let string_of_lambda x = failwith "Not implemented";;
let lambda_of_string x = failwith "Not implemented";;