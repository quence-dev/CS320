(****
   Please read `Assignment3.pdf` before starting the implementation.
   The pdf provides more detailed description, motivation, and hints about this assignment.
 ****)

(****
   Spencer Vilicic
   CS320 - Programming Assignment 3
   10/22/2020
 ****)

(*************** warm up ***************)

(****  
   Take a filename and a list of strings, and write the strings to the file
   indicated by the filename.

   Remember to close any possible channel before ending.

   @param f_name: the name of the file to write to
   @param content: a list of string to write to file
*)
let write_list_str (f_name: string) (content: string list): unit =
  let oc = open_out f_name in
  let rec aux clist = 
    match clist with
    | h::t ->  Printf.fprintf oc "%s\n" h; aux t
    | [] -> close_out oc; ()
  in aux content



(****
   Take a file and reads it line by line and returns a list of
   all the strings of each line in order.

   Remember to close any input channel before ending.

   @param f_name: file name to read from
   @return: each line as one element of the list in reverse order

   Example:
   That is if the file looks like this:
   ```
   Hello
   World
   CS320
   ```
   the returned list should be `["Hello"; "World"; "CS320"]` .
*)
let read_list_str (f_name: string): (string list) =
  let ic = open_in f_name in 
  let rec aux accum =
    match input_line ic with
    | s ->  aux (s::accum)
    | exception End_of_file -> close_in ic; List.rev accum
  in aux []

(*************** Functions over ciltrees ***************)

(* Definition of ciltree *)
type ciltree = L of int list | I of int | T of ciltree * char * ciltree

(* Some examples of biltrees *)
let ex1 = T (T (I 1, 'a' , T (I (-34), 'b', L [-21; 53; 12])), 'c', T (I (-18), 'd' , I 1))

let ex2 = T (T (T (T (I 31, 'h', L [9; 34; -45]), 'e', L [70; 58; -36; 28]), 'l', I 3), 
             'l', T (I 2, 'o', I 49))

let ex3 = T (T (T (L [9; 4; -1; 0; -5], 'c', L [40]), 's', I 1), '3', T (L [420; 69], '2', I (-3)))



(****
   Count the number of int in the input tree

   "Int" is all the node with constructor `I`

   @param tree: the tree to count in
   @return: the number of int in the input `tree`

   Example:
   count_ints ex1 = 4
   count_ints ex2 = 4
   count_ints ex3 = 2
*)
let rec count_ints (tree: ciltree): int =
  match tree with
  | L _ -> 0
  | I _ -> 1
  | T (left, _, right) -> count_ints left + count_ints right


(****
   Map the `func` onto all the elements in the list of `tree`

   "list" is all the node that with constructor `L`
   We will apply func on to all the **elements** of the list in constructor `L`

   @param func: the function to apply to the element
   @param tree: input tree
   @return: the new tree after the map appends

   Example:
   map_on_all_lists_elem (fun n -> n * 2) 
      (T (L [1;2;3], 't', L [3;2;1])) = T (L [2;4;6], 't', L [6;4;2])

   map_on_all_lists_elem (fun n -> 0) 
    (T (T (L [1], 'a', I 10), 't', L [3; 2; 1])) = 
    T (T (L [0], 'a', I 10), 't', L [0; 0; 0])

   map_on_all_lists_elem ((+) 1) 
    (T (T (L [1], 'a', I 10), 't', L [3; 2; 1])) = 
    T (T (L [2], 'a', I 10), 't', L [4; 3; 2])
*)
let rec map_on_all_lists_elem (func: int -> int) (tree: ciltree): ciltree =
  match tree with
  | T (left, char, I num) -> T (map_on_all_lists_elem func left , char, I num)
  | T (I num, char, right) -> T (I num, char, map_on_all_lists_elem func right)
  | T (left, char, right) -> T (map_on_all_lists_elem func left, char, map_on_all_lists_elem func right)
  | L list -> L (List.map func list)
  | I _ -> tree


(****
   shift the entire tree to the right

   Here is the shift

       r                       p
     /   \                   /   \
    p     u   shift_right   x     r
   / \   / \    ======>    / \   / \
   x  T3 T4 T5             T1 T2 T3  u
   / \                               / \
   T1  T2                            T4 T5
   If the tree do not have the structure in the given picture, 
   return the original input tree.

   @param tree: the tree before the shift
   @return: the tree after the shift

   Example:
   shift_right (L [1; 2; 3]) = (L [1; 2; 3])
   shift_right (T (L [1], 't', T (I 1, 'r', T (I 69, 'e', L[14])))) =
    (T (L [1], 't', T (I 1, 'r', T (I 69, 'e', L[14]))))

   (*the minimum tree to shift*)
   shift_right (T( T (I 12, 'b', L [1]), 'c', T (I 12, 'd', L [34; 96]))) =
   T( I 12, 'b', T (L [1], 'c', T (I 12, 'd', L [34; 96])) )
   (*a general tree*)
   shift_right (
    T( 
      T (
        T (I 1, 'r', T (I 69, 'e', L[14])), 
        'b', 
        T (L [34], 'r', T (L [420;69], 'e', I 44))
      ), 
      'c', 
      T (T (I 44, 'm', L []), 'd', L [])
    )
   ) =
   T( 
    T (I 1, 'r', T (I 69, 'e', L[14])), 
    'b', 
    T (
      T (L [34], 'r', T (L [420;69], 'e', I 44)), 
      'c', 
      T (T (I 44, 'm', L []), 'd', L [])
    ) 
   )
*)
let shift_right (tree: ciltree): ciltree =
  match tree with
  | T (left, char, (L _ | I _)) -> tree
  | T (left, char, right) -> (match left with
      | T (l2, char2, r2 ) -> T (l2, char2, T(r2, char, right))
      | L _ -> tree
      | I _ -> tree
    )
  | L _ -> tree
  | I _ -> tree

(****
   Whether `tree` contains the `subtree_to_find`

   Return whether the given `tree` contains the subtree (a node with all of its descendent) 
   exactly equals the input `subtree_to_find`

   @param tree: the tree to find in
   @param subtree_to_find: the subtree that we need to find in `tree`
   @return: whether `tree` contains the `subtree_to_find`

   Example:
   (*a tree always contains itself*)
   tree_contains (L [1, 2, 3]) (L [1,2,3]) = true
   (*the right most subtree*)
   tree_contains (T (L [1], 't', T (I 1, 'r', T (I 69, 'e', L[14]))))
    (T (I 69, 'e', L[14])) = true

   tree_contains (T (L [1], 't', T (I 1, 'r', T (I 69, 'e', L[14]))))
    (I 1) = true

   (*there is no subtree that exactly matches the input*)
   tree_contains (T (L [1], 't', T (I 1, 'r', T (I 69, 'e', L[14]))))
    (T (L [1], 't', I 1)) = false
*)
let rec tree_contains (tree: ciltree) (subtree_to_find: ciltree): bool =
  match tree with
  | T (left, char, right) -> (match subtree_to_find with
      | T (l2,c2, r2) -> if ((l2 = left) && (c2 = char) && (r2 = right)) 
        then true
        else ((tree_contains left subtree_to_find) || (tree_contains right subtree_to_find))
      | _ -> ((tree_contains left subtree_to_find) || (tree_contains right subtree_to_find)))
  | L lst -> (match subtree_to_find with
      | L lst2 -> if (lst2 = lst) then true else false
      | _ -> false)
  | I num -> (match subtree_to_find with
      | I num2 -> if (num2 = num) then true else false
      | _ -> false)

(*************** cil and cilbtree ***************)

(****
   cil is a type that can contain a list of int, a int, or a char
*)
type cil = L of int list | I of int | C of char


(****
   a general tree where each node is a cil
*)
type cil_gtree = Empty | Node of cil * cil_gtree list


(****
   construct a empty cil_gtree
*)
let mk_empty_cil_gtree: cil_gtree = Empty

(****
   Construct a cil_gtree given the value of the root and its children
*)
let rec mk_cil_gtree (root_val: cil) (children: cil_gtree list) : cil_gtree = 
  Node (root_val, children)


(****
   get the root value of a cil_gtree
*)
let cil_gtree_root (tree: cil_gtree): cil option =
  match tree with
  | Node (root_val, _) -> Some root_val
  | Empty -> None


(****
   get the children of a cil_gtree
*)
let cil_gtree_children (tree: cil_gtree): cil_gtree list option =
  match tree with
  | Node (root, children) -> Some children
  | _ -> None


(****
   converts the input `tree` into a cil_gtree
*)
let rec cil_tree_to_cil_gtree (tree: ciltree): cil_gtree =
  match tree with
  | I num -> Node(I num, [])
  | L lst -> Node(L lst, [])
  | T(left, char, right) -> Node(C char, cil_tree_to_cil_gtree left::cil_tree_to_cil_gtree right::[])


(****
   converts the input `tree` into a ciltree
*)
let gtreeHelper (lst: cil_gtree list): cil_gtree =
  match lst with
  | hd::_ -> hd
  | [] -> Empty

let rec cil_gtree_to_cil_tree (tree: cil_gtree): ciltree option =
  match tree with
  (* terminal cases *)
  | Node (I num, []) -> Some (I num)
  | Node (L lst, []) -> Some (L lst)
  | Node (C char, []) -> None
  | Node (I num, _) -> None
  | Node (L lst, _) -> None
  | Empty -> None
  (* non-terminal case *)
  | Node (C char, hd::tl) -> if List.length tl <> 1 then None 
    else
      (match (cil_gtree_to_cil_tree hd) with
       | None -> None
       | Some v -> match (cil_gtree_to_cil_tree (gtreeHelper tl)) with
         | None -> None
         | Some w -> Some (T (v, char, w))
      )


let count_intsTest() =
  Printf.printf "the result of `count_ints ex1` is ";
  print_int (count_ints ex1);
  print_newline();
  Printf.printf "the result of `count_ints ex2` is ";
  print_int (count_ints ex2);
  print_newline();
  Printf.printf "the result of `count_ints ex3` is ";
  print_int (count_ints ex3);
  print_newline()

let testAll() =
  count_intsTest()

let main () = 
  testAll()