(* CS421 - Summer 2013
 * MP1 
 *
 * Please keep in mind that there may be more than one
 * way to solve a problem.
 *)

open Mp1common

(* Problem 1 *)
let e = 2.71828;;

(* Problem 2 *)
let welcome = "Hello and welcome!";;

(* Problem 3 *)
let ten_less n = n - 10;;

(* Problem 4 *)
let e_to_the_square y = e ** (y *. y);;

(* Problem 5 *)
let recognize name =
    if name = "Elsa" then print_string "Ah, I know you.\n"
    else (print_string "Your name is "; print_string name;
          print_string ", you say? Welcome to CS 421.\n");;

(* Problem 6 *)
let has_smallest_floor m n = if floor m < floor n || m < n then m else n;;

(* Problem 7 *)
let first_two (x,y,z) = (x,y);;

(* Problem 8 *)
let app_triple f (x,y,z) = (f x, f y, f z);;
