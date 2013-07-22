let report x =
   print_string "Result: ";
   print_int x;
   print_newline();;


let addk x y k = k (x + y);;
let subk x y k = k (x - y);;
let concatk x y k = k (x ^ y);;
let consk x y k = k (x::y);;
let appk x y k = k (x @ y);;