open Hw1;;

let print_peano x = print_int (int_of_peano x);;

let first_list lst = match lst with
	| Nil -> failwith "empty list"
	| Cons(x, a) -> x;;
	
let rec print_list lst = match lst with
	| Nil -> ()
	| Cons(x, a) -> 
		print_int x;
		print_string " ";
		print_list a;;

print_list (merge_sort (rev (Cons(9, (Cons(10,(Cons(1,Cons(2,Nil)))))))));;


(*
print_string (Hw1.string_of_lambda (Hw1.lambda_of_string "\\x.\\y.x"));;
*)