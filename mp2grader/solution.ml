(* CS421 - Summer 2013
 * MP2 
 *
 * Please keep in mind that there may be more than one
 * way to solve a problem.  You will want to change how a number of these start.
 *)

(* Problem 1 *)
let polar_prod ((r1,t1),(r2,t2)) =
    (r1 *. r2, t1 +. t2)

(* Problem 2 *)
let rec s n = 
   if n <= 0 then 0
   else if n mod 2 = 1 then 2 * (s (n - 1)) + n
   else 3 * (s (n - 2)) + 2 * n

(* Problem 3 *)
let rec filter p xs =
   match xs with
   | [] -> []
   | x::xs -> if p x then x :: filter p xs else filter p xs

(* Problem 4 *)
let rec length xs =
 match xs with
   | [] -> 0
   | x::xs -> 1 + length xs

let rec has_two p xs =
   length (filter p xs) > 1

(* Problem 5 *)
let rec sum xs ys =
   match (xs,ys) with
      ([],ys) -> ys
    | (xs,[]) -> xs
    | (x::xs',y::ys') -> (x + y)::(sum xs' ys')

(* Problem 6 *)
let rec split xs =
   match xs with
      [] -> ([],[])
    | (x::ys) -> let (bs,cs) = split ys 
                 in if x >= 0 then (x::bs,cs) else (bs, x::cs)

(* Problem 7 *)
let rec diff xs n =
  match xs with
     | [] -> []
     | x::xs -> (x -. n) :: diff xs n

let rec diff_from_mean xs =
    let rec total lst = match lst with 
       | [] -> 0.0 
       | x::xs -> x +. total xs
    in let mean = total xs /. float_of_int (List.length xs) 
    in diff xs mean

(* Problem 8 *)
let rec check_nth p xs n = 
 match xs with
   | [] -> false
   | x::xs -> if n = 0 then p x else check_nth p xs (n - 1)

let rec check_ijth matrix p (i,j) =
   check_nth (fun col -> check_nth p col j) matrix i

(* Extra Credit Problem 9 *)
let rec length xs =
 match xs with
   | [] -> 0
   | x::xs -> 1 + length xs

let rec diag row n =
 match row with
   | [] -> true
   | x::xs -> (n = 0 || x = 0) && diag xs (n - 1)

let rec diagonal lists n len =
 match lists with
   | [] -> true
   | x::xs -> length x = len && diag x n && diagonal xs (n + 1) len

let is_diagonal matrix =
 match matrix with
   | [] -> true
   | x::xs -> diagonal matrix 0 (length x)
