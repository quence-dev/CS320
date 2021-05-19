(*
Honor code comes here:

First Name: Spencer
Last Name: Vilicic
BU ID: U07828843

I pledge that this program represents my own
program code and that I have coded on my own. I received
help from no one in designing and debugging my program.
I have read the course syllabus of CS 320 and have read the sections on Collaboration
and Academic Misconduct. I also understand that I may be asked to meet the instructor
or the TF for a follow up interview on Zoom. I may be asked to explain my solution in person and
may also ask you to solve a related problem.
*)



(* We are providing you with the print_list function that you can use for printing of list
     and we hope that you find it useful for debugging purposes.

     The type signature of this function is

     int list -> unit
*)


let rec print_list (list: int list): unit =
  match list with
    [] -> ()
  | e::l -> print_int e ; print_string " " ; print_list l

(* Problems *)

(*
TODO: Write a function called count_from that takes in as input as two integers n, e and returns back a list that starts
at n and counts e numbers.

For example if n is 2 and e is 4 then you would return back a list [2;3;4;5]

The type signature of this method is: int ->int -> int list
*)


let rec count_from (n:int) (e:int): int list =
  if e<1 then []
  else
    n::(count_from (n+1) (e-1))

(*
TODO: Write a function called dotProduct that has the following signature:
int list -> int list -> int

i.e., it takes in as input two list of integers and returns back the dot product of the two list.
For instance if the two inputs are [1;2;3;4] and [6;7;8;9]
then the output is 1*6+2*7+3*8+4*9 i.e. 80.

If the two list are of unequal lengths then you return back the partial dotProduct up to the shorter length.
For instance if the two inputs are [1;2;3;4]  and [6; 7]
the the output is 1*6 + 2*7 i.e. 20. The extra 3, 4, elements from the first list are not used.

You must use recursion for this method. You are free to use normal or tail recursion for this.
*)

let rec dotProduct (x: int list) (y: int list): int =
  match x with
    []->0
  |
    h1::t1 -> match y with
      []->0
    |
      h2::t2 -> (h1*h2) + (dotProduct t1 t2)

(*
TODO: Write a function called stitch that has the following signature:
int list -> int list -> (int*int) list

i.e., it takes in as input two list of integers and stitches them together to product a list of tuples.
For instance if the two inputs are [1;2;3;5] and [6;7;8;9]
then the output is [(1,6);(2,7);(3,8);(5,9)]

If the two input list are of unequal lengths then you must just return back an empty list.
You must use recursion for this method.
*)

let rec length l=
  match l with
    []->0
  |
    _::t->1+length t

let rec stitch (a: int list) (b: int list): ((int * int) list) =
  if (length a) != (length b) then []
  else
    match a with
      []->[]
    |
      h1::t1 -> match b with
        []->[]
      |
        h2::t2 -> (h1,h2)::(stitch t1 t2)


(* TODO: Write a function that takes in as input a list of tuples and returns back a string.
   For instance if the input is [(1,2);(3,4);(5,6)] then you would return back a string that is as follows:

   [ (1,2); (3,4); (5,6) ]

   Formatting for spacing is not required, but symbols such as ',', ';', etc. must be present at the correct
   relative positions.

   The type signature of this method is:
   (int*int) list-> string.
*)



let get_list_of_tuple_as_string (list: (int*int) list): string =
  let rec tuple_string_helper (list: (int*int) list): string =
    match list with
    |[] -> ""
    |[(a,b)]-> "(" ^ string_of_int a ^ "," ^ string_of_int b ^ ")"
    |(a,b)::t -> "(" ^ string_of_int a ^ "," ^ string_of_int b ^ ")" ^ ";" ^ tuple_string_helper t
  in "[ " ^ (tuple_string_helper list) ^ " ]"


(* TODO: Write a quicksort function in OCaml that has the following function signature:
   int list->int list

   i.e., it takes in as input a list of integers and gives back
   as input a list of integers.

   So for example, if the input list is [6;7;1] you will then
   return back a sorted list that is [1;6;7].

   Choose the first element of the input list
   as the pivot element. The quicksort must use recursion

   You can create as many helper methods as you like.
*)

let rec partition_low (pivot: int)(list: int list): int list =
  match list with
  | []->[]
  | h::tail -> (* recursively concat head to list if head is less than or equal to than pivot *)
    if h <= pivot then [h] @ (partition_low pivot tail)
    else partition_low pivot tail

let rec partition_high (pivot: int)(list: int list): int list =
  match list with
  | []->[]
  | h::tail -> (* recursively concat head to list if head is greater than pivot *)
    if h > pivot then [h] @ (partition_high pivot tail)
    else partition_high pivot tail

let rec quicksort (list: int list): int list =
  match list with
    []->[]
  | (* recurse over list to create separate low and high lists of integers *)
    pivot::t -> quicksort (partition_low pivot t) @ [pivot] @ quicksort (partition_high pivot t)



(*
TODO:
Write any starter code that you see fit to write here to test out your code.
*)

let myCountFromTest ()=
  Printf.printf "the result of `count_from 2 4` is ";
  print_list(count_from 2 4);
  print_newline();
  Printf.printf "the result of `count_from 1 10` is ";
  print_list(count_from 1 10);
  print_newline()

let myDotProductTest()=
  Printf.printf "the result of `dotProduct [1;2;3;4] [6;7;8;9]` is %i\n" (dotProduct [1;2;3;4] [6;7;8;9]);
  Printf.printf "the result of `dotProduct [1;2;3;4] [6;7]` is %i\n" (dotProduct [1;2;3;4] [6;7]);
  print_newline()

let myStitchTest()=
  Printf.printf "the result of `stitch [1;2;3;5] [6;7;8;9]` is ";
  Printf.printf "%s"(get_list_of_tuple_as_string (stitch [1;2;3;5] [6;7;8;9]));
  print_newline()

let get_list_of_tuple_as_stringTest()=
  Printf.printf "the result of `get list of tuple as string [(1,2);(3,4);(5,6)]` is ";
  Printf.printf "%s"(get_list_of_tuple_as_string [(1,2);(3,4);(5,6)]);
  print_newline()

let quicksortTest()=
  Printf.printf "the result of `quicksort [3;2;-5;10;7]` is ";
  print_list(quicksort [3;2;-5;10;7]);
  print_newline()

let testAll()=
  myCountFromTest();
  myDotProductTest();
  myStitchTest();
  get_list_of_tuple_as_stringTest();
  quicksortTest()

let main=
  testAll()