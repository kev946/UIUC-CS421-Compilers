(* CS421 - Summer 2013
 * MP3
 *
 * Please keep in mind that there may be more than one
 * way to solve a problem.  You will want to change how a number of these start.
 *)

open Mp3common

(* Problem 1 *)
let rec concat list =
    match list with [] -> ""
        | x::xs -> x ^ (concat xs)

(* Problem 2 *)
let rec part_concat list =
    match list with [] -> []
        | x::xs ->
          let p = part_concat xs in
              match p with [] -> [x]
                  | (s::ss) -> (x ^ s) :: p

(* Problem 3 *)
let min list =
  let rec min_aux list min =
    match list with [] -> min
        | x::xs -> min_aux xs (if x < min then x else min)
  in match list with [] -> -1 | x::xs -> min_aux xs x

(* Problem 4 *)
let dup list =
   let rec dup_aux l acc =
       match l with [] -> acc
           | x::xs -> dup_aux xs (acc @ [x; x])
   in dup_aux list []

(* Problem 5 *)
let concat_base = ""
let concat_step x r = x ^ r

(* Problem 6 *)
let min2 list = match list with [] -> -1
  | x::xs -> 
    List.fold_left (fun min x -> if x < min then x else min) x xs

(* Problem 7 *)
let cross_sum xs ys = 
  List.map (fun x -> List.map (fun y -> x + y) ys) xs

(* Problem 8 *)
let calck a b c d k = addk c d (fun r -> addk a b (fun s -> subk s r k));;

(* Problem 9 *)
let rec part_concatk list k =
    match list with [] -> k []
        | x::xs -> 
          part_concatk xs (fun p -> match p with [] -> consk x [] k
                  | (s::ss) -> concatk x s (fun r -> consk r p k))

(* Problem 10 *)
let dupk list k =
  let rec dup_auxk l acc k = 
     match l with [] -> k acc
         | x::xs -> consk x [] (fun r -> consk x r (fun r ->
                               appk acc r (fun r -> dup_auxk xs r k)))
  in dup_auxk list [] k