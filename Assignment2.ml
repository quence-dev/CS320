(* 
First Name: Spencer
Last Name: Vilicic
BU ID: U07828843
 *)

(************ PROBLEM safe dot-product ************)

(***
   Please, write a function that compute the dot product of two lists in a safe way.
   This function should produce a output no matter what input lists it is provided with.

   Note: dot product only exists for two vector of the same length:
   https://en.wikipedia.org/wiki/Dot_product#Algebraic_definition

   Example
   >>>> safe_dot_product [1;2;3] [2;2;0] = Some 6
   >>>> safe_dot_product [1;2] [2;3] = Some 8
*)

let rec dotHelper (vect1: int list) (vect2: int list) : int =
  match (vect1, vect2) with
    [],[] -> 0
  |
    _::_, [] -> 0 (* unequal lengths *)
  |
    [], _::_ -> 0 (* unequal lengths *)
  |
    h1::t1, h2::t2 -> (h1*h2) + (dotHelper t1 t2)

let rec safe_dot_product (vect1: int list) (vect2: int list) : int option = 
  match (vect1, vect2) with
    [],[] -> Some 0 (* empty lists returns 0*)
  |
    _, [] -> None (* unequal lengths *)
  |
    [], _ -> None (* unequal lengths *)
  |
    h1::t1, h2::t2 -> 
    match safe_dot_product t1 t2 with
      None -> None
    |
      Some v -> Some (dotHelper vect1 vect2)

(***
   Please, write another version of safe dot product which is tail recursive.
*)

let rec safe_dot_product_tail_rec (vect1: int list) (vect2: int list): int option =
  let rec aux v1 v2 accum =
    match (v1, v2) with
    | h1::t1, h2::t2 -> aux t1 t2 (accum + (h1*h2))
    | [],[] -> Some accum
    | [],_::_ -> None (* unequal lengths *)
    | _::_,[] -> None (* unequal lengths *)
  in aux vect1 vect2 0

(************ PROBLEM Bunny's Fibonacci ************)


(***
   Please, write a function that given a positive integer i returns the  number
   in position i in the bunny's Fibonacci Sequence defined as follows.

   The Bunny's Fibonacci Sequence looks like this [0;1;2;3;2;4;4;7;6;11;10...]
   where
   - the start of the sequence is 0;1;2;3
   - a number on an even index i is the sum of the numbers on the previous even
     indices, i.e. the numbers in positions (i-2) and (i-4).
     For example `2` on index 4 is a sum of `0` on index 0 and `2` on index 2
   - a number on an odd index j is the sum of the numbers on the previous odd
     indices   i.e. the numbers in positions (j-2) and (j-4).
     For example, `7` on index 7 is a sum of `3` on index 3 and `4` on index 5

   Example:
   (*The first element (index 0) of bunny's Fibonacci Sequence*)
   >>>> bunny_fib_idx 0 = 0
   (*The 5th element of (index 4) of bunny's Fibonacci Sequence*)
   >>>> bunny_fib_idx 4 = 2
   (*The 9th element of (index 8) of bunny's Fibonacci Sequence*)
   >>>> bunny_fib_idx 8 = 6
*)

let rec bunny_fib_idx (idx: int) (*Assume idx is positive*): int =
  match idx with
  | 0 -> 0
  | 1 -> 1
  | 2 -> 2
  | 3 -> 3
  | _ -> bunny_fib_idx (idx - 2) + bunny_fib_idx (idx - 4)

(***
   Implement a tail recursive version of bunny_fib_idx
   Your function should run in linear time.
*)
let bunny_fib_idx_tail_rec (idx: int) (*Assume idx is positive*): int =
  let rec aux a1 a2 idx current =
    if (idx != current) then
      aux a2 (a1 + a2) idx (current+2) (* set accum1 to accum2, set accum2 to the sum of accum1 and accum2 *)
    else
      a1
  in
  if (idx mod 2) == 0 then
    aux 0 2 idx 0 (* even case, start at 0 and 2 *)
  else
    aux 1 3 idx 1 (* odd case, start at 1 and 3 *)

(************ PROBLEM Binary Addition ************)

(**
   Please, write a function to convert a list of integers 0 and 1 into boolean
   bits (true for 1, and false for 0).

   Your code needs to check whether there is any illegal number (non-0 and 1) in the list
*)
let rec int_list_to_bits (int_lst: int list): bool list option =
  match int_lst with
  | [] -> Some []
  | 0::tl -> (match int_list_to_bits tl with
      | None -> None
      | Some v -> Some (false::v))
  | 1::tl -> 
    (match int_list_to_bits tl with
     | None -> None
     | Some v -> Some (true::v))
  | _::tl -> None

(***
   Please, write a function that takes in input two bits (booleans) and returns a pair where 
   - The first element is a boolean asserting whether there is a bit carrying over.
   - The second element is the resulting bit.
 ***)
let sum_bit (bit1: bool) (bit2: bool): (bool * bool) =
  match (bit1, bit2) with
  | true, true -> (true, false)
  | true, false -> (false, true)
  | false, true -> (false, true)
  | false, false -> (false, false)


(***
   Please, write a function that returns the sum of two list of bits (bool). 

   PRECONDITION:
   When adding bits1 and bits2 you can assume that the least significant bit is at the 
   head of the list and the most signifcant bit is at the end of the list. 

   --So for example the number 18 in binary starting from the most signifcant bit to the 
   least significant bit is 10010. 

   However the binary representation of 18 when passed into the sum_bits method  is 
   represented as 0 1 0 0 1 (i.e., starting from the least significant bit to the 
   most significant bit) which is equivalent to [false;true;false;false;true]

   --the number 8 in binary starting from the most signifcant bit to the 
   least significant bit is 1000. 

   However the binary representation of 8 when passed into the sum_bits method is 
   represented as 0 0 0 1 (i.e., starting from the least significant bit to the 
   most significant bit) which is equivalent to [false;false;false;true]

   POSTCONDITION:
   Now the result (18+8=26) of adding these two lists of bools is [false;true;false;true;true]
   i.e., in the output you also again put the least significant bit at the head of the list 
   and the most significant bit at the end of the list. 

   Here are some more examples:
   Example:
   (* 1 + 1 = 10 *)
   >>>> sum_bits [true] [true] = [false; true]
   (*11 + 1110 = 10001*)
   >>>> sum_bits [true; true] [false; true; true; true] = [true; false; false; false; true]
   (*0 + 110 = 110*)
   >>>> sum_bits [false] [false; true; true] = [false; true; true]

*)


let rec sum_bits (bits1: bool list) (bits2: bool list): bool list = 
  match (bits1, bits2) with
  | [], [] -> []
  | _, [] -> bits1
  | [], _ -> bits2
  | h1::t1, h2::t2 -> match (sum_bit h1 h2) with
    | true, v -> v::sum_bits [true] (sum_bits t1 t2)
    | false, v -> v::sum_bits t1 t2

(***
   Please, write a function that converts a list of bits back to a list of 0s and 1s
   (true for 1, and false for 0).
*)
let rec bits_to_int_list (bits: bool list): int list = 
  match bits with
  | [] -> []
  | h::t -> 
    match h with
    | true -> 1::bits_to_int_list t
    | false -> 0::bits_to_int_list t


(***
   Please write a function that sums two binary number, 
   where each number is represented by a list of 0s and 1s.
   For example the binary number 10010 will be represented by the list [1;0;0;1;0]

   Your function needs to deal carefully with invalid inputs like the following:
   - the input list is empty (return None)
   - the input list contains elements that are not 0 or 1 (return None)
   - the input list is a non-singleton list starting with 0 (like [0,1,1,1]) (0::_ return None)

   Hint: use the functions that you defined previously, in this exercise, as helper functions. 

   Example:
   >>>> sum_bin [1] [1] = Some [1;0]
   >>>> sum_bin [1;1] [1;1;1;0] = Some [1;0;0;0;1]
   >>>> sum_bin [0] [1;1;0] = Some [1;1;0]
 ***)

(* use currying, reverse lists to order Significant Bits *)
let rec sum_bin (b_num1: int list) (b_num2: int list): int list option =
  match (b_num1, b_num2) with
  | [], [] -> None
  | [], _ -> None
  | _, [] -> None
  | 0::tl, _ -> None
  | _, 0::tl -> None
  | _,_ -> 
    (match (int_list_to_bits b_num1, int_list_to_bits b_num2) with
     | None, None -> None
     | None, Some z -> None
     | Some z, None -> None
     | Some y, Some z -> Some (List.rev (bits_to_int_list (sum_bits (List.rev y) (List.rev z)))))


(* printer function for int options *)
let print_int_option x=
  match x with
    None -> print_string "None"
  |
    Some v -> print_int v

let rec print_bool_list (list: bool list): unit =
  match list with
    [] -> ()
  | 
    e::l -> if e then print_string "true " else print_string "false "; print_bool_list l


let print_bool_list_option x=
  match x with
    None -> print_string "None"
  |
    Some v -> print_bool_list v

(* my test cases *)
let safeDotTest() = 
  Printf.printf "the result of `safe_dot_product [1;2;3] [4;5;6]` is ";
  print_int_option (safe_dot_product [1;2;3] [4;5;6]);
  print_newline();
  Printf.printf "the result of `safe_dot_product [1;2;3] [2;10]` is ";
  print_int_option (safe_dot_product [1;2;3] [2;10]);
  print_newline();
  Printf.printf "the result of `safe_dot_product [] []` is ";
  print_int_option (safe_dot_product [] []);
  print_newline()

let safeDotTailTest() =
  Printf.printf "the result of `safe_dot_product_tail_rec [1;2;3] [4;5;6]` is ";
  print_int_option (safe_dot_product_tail_rec [1;2;3] [4;5;6]);
  print_newline();
  Printf.printf "the result of `safe_dot_product_tail_rec [1;2;3] [2;10]` is ";
  print_int_option (safe_dot_product_tail_rec [1;2;3] [2;10]);
  print_newline();
  Printf.printf "the result of `safe_dot_product_tail_rec [] []` is ";
  print_int_option (safe_dot_product_tail_rec [] []);
  print_newline()

let bunnyFibTest() = 
  Printf.printf "the result of `bunny_fib_idx 1 should be 1` is ";
  print_int (bunny_fib_idx 1);
  print_newline();
  Printf.printf "the result of `bunny_fib_idx 4 should be 2` is ";
  print_int (bunny_fib_idx 4);
  print_newline();
  Printf.printf "the result of `bunny_fib_idx 8 should be 6` is ";
  print_int (bunny_fib_idx 8);
  print_newline()

let bunnyFibTailTest() = 
  Printf.printf "the result of `bunny_fib_idx_tail_rec 1 should be 1` is ";
  print_int (bunny_fib_idx_tail_rec 1);
  print_newline();
  Printf.printf "the result of `bunny_fib_idx_tail_rec 9 should be 11` is ";
  print_int (bunny_fib_idx_tail_rec 9);
  print_newline();
  Printf.printf "the result of `bunny_fib_idx_tail_rec 8 should be 6` is ";
  print_int (bunny_fib_idx_tail_rec 8);
  print_newline()

let int_list_to_bitsTest() =
  Printf.printf "the result of `int_list_to_bits [1;0;1;0]` is ";
  print_bool_list_option (int_list_to_bits [1]);
  print_newline();
  Printf.printf "the result of `int_list_to_bits [1;0;1;0]` is ";
  print_bool_list_option (int_list_to_bits [0]);
  print_newline();
  Printf.printf "the result of `int_list_to_bits [1;0;1;0]` is ";
  print_bool_list_option (int_list_to_bits [1;0;1;0]);
  print_newline();
  Printf.printf "the result of `int_list_to_bits [1;0;1;0]` is ";
  print_bool_list_option (int_list_to_bits [1;2;3;4]);
  print_newline()

let sum_bitsTest() = 
  Printf.printf "the result of `sum_bits [false][false]` is ";
  print_bool_list (sum_bits [false][false]);
  print_newline();
  Printf.printf "the result of `sum_bits [true][true]` is ";
  print_bool_list (sum_bits [true][true]);
  print_newline();
  Printf.printf "the result of `sum_bits [true; false; true][true; true; false; true]` is ";
  print_bool_list (sum_bits [true; false; true][true; true; false; true]);
  print_newline()

let testAll() =
  safeDotTest();
  print_newline();
  safeDotTailTest();
  print_newline();
  bunnyFibTest();
  print_newline();
  bunnyFibTailTest();
  print_newline();
  int_list_to_bitsTest();
  print_newline();
  sum_bitsTest();
  print_newline()

let main =
  testAll()