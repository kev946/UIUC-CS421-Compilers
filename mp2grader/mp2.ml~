(* CS421 - Summer 2013
 * MP2 
 *
 * Please keep in mind that there may be more than one
 * way to solve a problem.  You will want to change how a number of these starts.
 *)

(* Problem 1 *)
let polar_prod r = match r with ((x, y),(w, z)) ->  (x *. w, y +. z);;

(* Problem 2 *)
let rec s n = if n <= 0 then 0 
				else if n mod 2 = 0 then 3*s(n-2) + 2*n
				else 2*s(n-1) + n;;

(* Problem 3 *)
let rec filter p xs = match xs with [] -> [] |
						x::xs -> if p x then x::filter p xs else filter p xs;;
				
(* Problem 4 helper function *)
let rec has_two_helper p xs = match xs with [] -> 0 |
								x::xs ->  if p x then 1 + has_two_helper p xs
								else 0 + has_two_helper p xs;;
					
(* Problem 4 *)
let has_two p xs = if has_two_helper p xs > 1 then true else false;;

(* Problem 5 helper *)
let rec sum_length xs = match xs with [] -> 0 |
	x::xs -> 1 + sum_length xs;;

(* Problem 5 *)
let rec sum_helper xs ys = match xs with [] -> [] |
	x::xs -> match ys with [] -> [] |
	y::ys -> (x+y)::sum_helper xs (ys@[0]);;

let sum xs ys = let x = sum_length xs in let y = sum_length ys in if x > y then sum_helper xs ys
																	else if x < y then sum_helper ys xs else sum_helper xs ys;;

(* Problem 6 *)
let rec split xs = match xs with [] -> ([],[]) |
					x::xs -> match split xs with (a,b) -> if x >= 0 then (x::a,b) else (a,x::b);;		
							
(* Problem 7 helper *)
let rec find_mean xs = match xs with [] -> float_of_int 0 | x::xs -> x +. find_mean xs;;

(* Problem 7 helper *)
let rec diff_from_mean_helper xs m = match xs with [] -> [] | x::xs -> (x -. m)::diff_from_mean_helper xs m;;

(* Problem 7 *)
let diff_from_mean xs = diff_from_mean_helper xs ((find_mean xs)/.float_of_int(List.length xs));;

(* Problem 8 helper *)
let rec check_jth m p (i,j) k = match m with [] -> false | 
	x::m -> if k = j then p x else check_jth m p (i,j) (k+1);; 

(* Problem 8 helper *)
let rec check_ith m p (i,j) k = match m with [] -> false | 
	x::m -> if k = i then check_jth x p (i,j) 0 else check_ith m p (i,j) (k+1);; 

(* Problem 8 *)
let check_ijth matrix p (i,j) = if i < 0 then false 
	else if j < 0 then false else check_ith matrix p (i,j) 0;; 

(* Extra Credit Problem 9 helper *)
let p x = if x > 0 then true else false;;

(* Extra Credit Problem 9 helper *)
let rec is_diagonal_j ms i j = match ms with [] -> true |
	m::ms -> if i = j then p m else is_diagonal_j ms i (j+1);;

(* Extra Credit Problem 9 helper *)
let rec is_diagonal_i ms i j = match ms with [] -> true |
	m::ms -> if is_diagonal_j m i 0 then true else is_diagonal_i ms (i+1) 0;;

(* Extra Credit Problem 9 *)
let is_diagonal matrix = is_diagonal_i matrix 0 0;;

