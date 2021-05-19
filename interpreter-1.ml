(* Interpreter assignment for CS320F20
   Spencer Vilicic
   11/15/2020
*)
(*************************************************************************************************)
(* HELPER FUNCTIONS *)
(*************************************************************************************************)

open String
open List

let explode (s: string) : char list = 
  let rec expl i l = 
    if i < 0 then l 
    else expl (i - 1) (String.get s i :: l) in 
  expl (String.length s - 1) []

let implode (cl: char list) : string = 
  String.concat "" (List.map (String.make 1) cl)

let is_alpha = function 
  'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
let is_digit = function 
  '0' .. '9' -> true | _ -> false

let rec print_stack s =
  match s with
    [] -> []
  |
    hd::tl -> print_string hd; print_string " "; print_stack tl

(*************************************************************************************************)

(* define Parser *)
type 'a parser = Parser of (string -> ('a * string) list)

(* define parse/runParser function *)
let parse p inp=
  match p with 
    Parser f -> f inp

(* bind operator *)
let (>>=) (p: 'a parser) (f: 'a -> 'b parser): 'b parser = 
  Parser (
    fun inp-> 
      match (parse p inp) with 
        []->[]
      |
        (v,out)::_->parse (f v) out )

(* redefine bind operator as prefix operator *)
let (let*) = (>>=)  

(* reads out first char from input *)
let item_p = 
  Parser ( 
    fun inp -> 
      match explode inp with 
        []->[] (*check whether the string is empty *)
      | 
        x::xs->[(x,implode xs)] )

(* define fail/empty function *)
let empty_p = 
  Parser ( fun inp -> [] )

(* define return function *)
let return_p (x: 'a): 'a parser = 
  Parser ( fun inp -> [(x,inp)] )

(* choice parser *)
let (<|>) (p: 'a parser) (q: 'a parser): 'a parser = 
  Parser 
    (
      fun inp -> 
        match parse p inp with 
          []->parse q inp (*return the result of the second parser if the first parser fails *)
        |
          d->d  (* return the result of the first parser *)
    )

(* satisfy parser *)
let sat_p p = 
  item_p >>= (fun x->if p x then return_p x else empty_p)

(* define digit parser *)        
let digit_p = sat_p is_digit
(* define letter parser *)      
let letter_p = sat_p is_alpha
(* define character parser *)      
let char_p x = sat_p (fun y -> y=x)

(* runs parser multiple times *)
let rec many_p (p: 'a parser): 'a list parser =
  (let* a = p in
   let* ls = many_p p in
   return_p (a :: ls))
  <|>
  return_p []

let many1_p (p: 'a parser): 'a list parser =
  let* a = p in
  let* ls = many_p p in
  return_p
    (a :: ls)

(* returns a natural number *)
let nat_p = 
  many1_p digit_p >>= fun xs-> return_p
    (int_of_string (implode xs))

(* returns an integer *)
let int_p = 
  (char_p '-' >>= fun _-> 
   nat_p >>= fun n -> 
   return_p (-n)) <|> nat_p

(* define whitespace parser *)
let whitespace_p = 
  char_p ' ' <|> char_p '\n' <|> char_p '\t' <|> char_p '\r' 

let space_p = many_p whitespace_p 

let token_p p = space_p >>= fun _->p >>=fun v->space_p >>= fun _-> return_p v

(* reads out the first n chars from an input string *)
let rec read_n (n: int): string parser =
  if n > 0 then
    let* c = item_p in 
    let* cs = read_n (n-1) in 
    return_p (String.make 1 c^cs)
  else 
    return_p ""

(* parses a matching string from input string if present *)
let string (str: string): string parser =
  let len=String.length str in 
  read_n len >>= fun x->
  if str=x then return_p x
  else empty_p

(*************************************************************************************************)
(* GRAMMAR *)
(*************************************************************************************************)
(* Constants
   const ::= int | bool | error | string | name | unit
   int ::= [−] digit { digit }
   bool ::= <true> | <false>
   error ::= <error>
   unit ::= <unit>
   string ::= "simpleASCII { simpleASCII }"
   simpleASCII ::= ASCII \ {'\', '"'}
   name ::= {_} letter {letter | digit | _} *)

(* Programs
   prog ::= coms
   com ::= Push const | Swap | Pop |
   Add | Sub | Mul | Div | Rem | Neg |
   And | Or | Not |
   Lte | Lt | Gte | Gt | Eq |
   Cat |
   Bnd |
   Begin coms End |
   If coms Then coms Else coms EndIf |
   Fun name1 name2 coms EndFun |
   Call | Return |
   Try coms With coms EndTry |
   Quit
   coms ::= com {com} *)

type stack_val = 
  | I of int (* num *)
  | S of string
  | B of bool
  | N of string (* name *)
  | Error (* error *)
  | Unit (* unit () *)
  | Empty

type command =
  | Push of stack_val
  | Pop
  | Add
  | Sub
  | Mul 
  | Div
  | Rem (* modulus *)
  | Neg (* negation *)
  | Swap (* swap top 2 stack elements *)
  | Quit (* stops interpreter and prints stack to output file *)

(* UNUSED *)
type prog = command list

(* boolean parser *)
let bool_p = (string "<true>" >>= fun _-> return_p true) <|>
             (string "<false>" >>= fun _-> return_p false)
(* error parser *)
let error_p = string "<error>" >>= fun _-> return_p "<error>"
(* unit parser *)
let unit_p = string "<unit>" >>= fun _-> return_p "<unit>"

(* name parser 
   It will always be a sequence of letters, digits, and underscores, starting with a letter (uppercase or
   lowercase) or an underscore. *)
let name_p = 
  (many_p (char_p '_') >>= fun a -> 
   many1_p (letter_p) >>= fun b -> 
   many_p (letter_p <|> (char_p '_') <|> digit_p) >>= fun c -> 
   if (a@b@c = []) then empty_p 
   else return_p (implode (a@b@c)))

(* quotation mark parser *)
let quotation_p = char_p '\"'
(* backslash parser - UNUSED *)
let backslash_p = char_p '\\'
(* "" = 34 , \ = 92 *)
let simpleASCII = function
    '\"' -> false | '\\' -> false | ' ' .. '~' -> true | _ -> false

(* simple ascii parser *)
let ascii_p = sat_p simpleASCII

(* string parser
   You can assume that the string value would always be legal and not contain quotations or escape sequences
   within the string itself, i.e. neither double quotes nor backslashes will appear inside a string. *)
let string_p = 
  quotation_p >>= fun _ -> 
  (many_p (ascii_p <|> whitespace_p)) >>= fun x -> 
  quotation_p >>= fun _ -> 
  return_p (implode x)

(*************************************************************************************************)

(* extract push command from input *)
let push: command parser = 
  string "Push" >>= fun _->
  whitespace_p >>= fun _-> 
  (int_p >>= fun i -> return_p (Push (I i)))
  <|> (bool_p >>= fun b -> return_p (Push (B b)))
  <|> (string_p >>= fun i -> return_p (Push (S i)))
  <|> (name_p >>= fun n -> return_p (Push (N n)))
  <|> (error_p >>= fun _ -> return_p (Push (Error)))
  <|> (unit_p >>= fun _ -> return_p (Push (Unit))) 

let pop: command parser = 
  string "Pop" >>= fun _-> return_p (Pop)

let add: command parser =
  string "Add" >>= fun _-> return_p (Add)

let sub: command parser =
  string "Sub" >>= fun _-> return_p (Sub)

let mul: command parser =
  string "Mul" >>= fun _-> return_p (Mul)

let div: command parser =
  string "Div" >>= fun _-> return_p (Div)

let rem: command parser =
  string "Rem" >>= fun _-> return_p (Rem)

let neg: command parser =
  string "Neg" >>= fun _-> return_p (Neg)

let swap: command parser =
  string "Swap" >>= fun _-> return_p (Swap)

let quit: command parser =
  string "Quit" >>= fun _-> return_p (Quit)

(* flips arguments of function f *)
let flip f x y = f y x
(* function composition *)
let ($) f g = fun x -> f (g x)

let parse_command s = 
  parse (push 
         <|> pop 
         <|> add 
         <|> sub 
         <|> mul 
         <|> div 
         <|> rem 
         <|> neg 
         <|> swap 
         <|> quit) s

let commandStringTuples (l: string list) = 
  List.map (flip List.nth 0 $ parse_command) l

let commandList (tuple: (command * string) list): command list =
  List.map (fun (x,_)->x) tuple

(*************************************************************************************************)
(* INTERPRETER FUNCTION *)
(*************************************************************************************************)

(* Take a file and read it line by line and return a list of
   all the strings of each line in order. *)
let read_list_str (f_name: string): (string list) =
  let ic = open_in f_name in 
  let rec aux accum =
    match input_line ic with
    | s ->  aux (s::accum)
    | exception End_of_file -> close_in ic; List.rev accum
  in aux []

(* Take a filename and a list of strings, and write the strings to the file
   indicated by the filename. *)
let write_list_str (f_name: string) (content: stack_val list): unit =
  let oc = open_out f_name in
  let rec aux clist = 
    match clist with
    | [] -> close_out oc; ()
    | h::t ->  (match h with
        | I x -> output_string oc (string_of_int x^"\n"); aux t
        | S x -> output_string oc (x^"\n"); aux t
        | B x -> output_string oc ("<"^string_of_bool x^">\n"); aux t
        | N x -> output_string oc (x^"\n"); aux t
        | Error -> output_string oc ("<error>\n"); aux t
        | Unit -> output_string oc ("<unit>\n"); aux t
        | Empty -> aux t )             
  in aux content

(* evaluate a list of commands and build a stack *)
let rec eval coms stack = 
  match coms, stack with 
  | Push v::coms', _ -> eval coms' (v::stack)
  | Pop::coms', v::stack' -> eval coms' (stack')
  | Add::coms', x::y::stack' -> (match x, y with 
      | I x, I y -> eval coms' (I (x+y)::stack')
      | _,_ -> eval coms' (Error::stack))
  | Sub::coms', x::y::stack' -> (match x, y with 
      | I x, I y -> eval coms' (I (x-y)::stack')
      | _,_ -> eval coms' (Error::stack))
  | Mul::coms', x::y::stack' -> (match x, y with 
      | I x, I y -> eval coms' (I (x*y)::stack')
      | _,_ -> eval coms' (Error::stack))
  | Div::coms', x::y::stack' -> (match x, y with 
      | I x, I y -> (if y = 0 (* cannot divide by 0 *)
                     then eval coms' (Error::I x::I y::stack') 
                     else eval coms' (I (x/y)::stack'))
      | _,_ -> eval coms' (Error::stack))
  | Rem::coms', x::y::stack' -> (match x, y with 
      | I x, I y -> (if y = 0 (* cannot divide by 0 *)
                     then eval coms' (Error::I x::I y::stack') 
                     else eval coms' (I (x mod y)::stack'))
      | _,_ -> eval coms' (Error::stack))
  | Neg::coms', x::stack' -> (match x with 
      | I x ->  eval coms' (I (-x)::stack') 
      | _ -> eval coms' (Error::stack))
  | Swap::coms', x::y::stack' -> eval coms' (y::x::stack')
  | _::coms', x::[] -> eval coms' (Error::x::stack)
  | _::coms', [] -> eval coms' (Error::stack)
  | Quit::_ , _ -> stack
  | _, _ -> stack

let interpreter (inputFile: string) (outputFile: string): unit =
  let inputCommands = read_list_str inputFile in 
  let listOfCommandinTuple = commandStringTuples inputCommands in 
  let listOfCommands = commandList listOfCommandinTuple in 
  let valueOfStack = eval listOfCommands [] in 
  write_list_str outputFile valueOfStack

(* let main() = 
   interpreter "./part1/input/input1.txt" "./part1/test/test1.txt";
   interpreter "./part1/input/input2.txt" "./part1/test/test2.txt";
   interpreter "./part1/input/input3.txt" "./part1/test/test3.txt";
   interpreter "./part1/input/input4.txt" "./part1/test/test4.txt";
   interpreter "./part1/input/input5.txt" "./part1/test/test5.txt";
   interpreter "./part1/input/input6.txt" "./part1/test/test6.txt";
   interpreter "./part1/input/input7.txt" "./part1/test/test7.txt";
   interpreter "./part1/input/input8.txt" "./part1/test/test8.txt";
   interpreter "./part1/input/input9.txt" "./part1/test/test9.txt";
   interpreter "./part1/input/input10.txt" "./part1/test/test10.txt";
   interpreter "./part1/input/input11.txt" "./part1/test/test11.txt";
   interpreter "./part1/input/input12.txt" "./part1/test/test12.txt";
   interpreter "./part1/input/input13.txt" "./part1/test/test13.txt";
   interpreter "./part1/input/input14.txt" "./part1/test/test14.txt";
   interpreter "./part1/input/input15.txt" "./part1/test/test15.txt";
   interpreter "./part1/input/input16.txt" "./part1/test/test16.txt";
   interpreter "./part1/input/input17.txt" "./part1/test/test17.txt";
   interpreter "./part1/input/input18.txt" "./part1/test/test18.txt";
   interpreter "./part1/input/input19.txt" "./part1/test/test19.txt";
   interpreter "./part1/input/input20.txt" "./part1/test/test20.txt";

   interpreter "./par1-more-test/input/add1.txt" "./par1-more-test/test/add1.txt";
   interpreter "./par1-more-test/input/add2.txt" "./par1-more-test/test/add2.txt";
   interpreter "./par1-more-test/input/add3.txt" "./par1-more-test/test/add3.txt";
   interpreter "./par1-more-test/input/add4.txt" "./par1-more-test/test/add4.txt";
   interpreter "./par1-more-test/input/add5.txt" "./par1-more-test/test/add5.txt";

   interpreter "./par1-more-test/input/div1.txt" "./par1-more-test/test/div1.txt";
   interpreter "./par1-more-test/input/div2.txt" "./par1-more-test/test/div2.txt";
   interpreter "./par1-more-test/input/div3.txt" "./par1-more-test/test/div3.txt";
   interpreter "./par1-more-test/input/div4.txt" "./par1-more-test/test/div4.txt";

   interpreter "./par1-more-test/input/mul1.txt" "./par1-more-test/test/mul1.txt";
   interpreter "./par1-more-test/input/mul2.txt" "./par1-more-test/test/mul2.txt";
   interpreter "./par1-more-test/input/mul3.txt" "./par1-more-test/test/mul3.txt";
   interpreter "./par1-more-test/input/mul4.txt" "./par1-more-test/test/mul4.txt";

   interpreter "./par1-more-test/input/neg1.txt" "./par1-more-test/test/neg1.txt";
   interpreter "./par1-more-test/input/neg2.txt" "./par1-more-test/test/neg2.txt";
   interpreter "./par1-more-test/input/neg3.txt" "./par1-more-test/test/neg3.txt";
   interpreter "./par1-more-test/input/neg4.txt" "./par1-more-test/test/neg4.txt";

   interpreter "./par1-more-test/input/pop1.txt" "./par1-more-test/test/pop1.txt";
   interpreter "./par1-more-test/input/pop2.txt" "./par1-more-test/test/pop2.txt";

   interpreter "./par1-more-test/input/push1.txt" "./par1-more-test/test/push1.txt";
   interpreter "./par1-more-test/input/push2.txt" "./par1-more-test/test/push2.txt";
   interpreter "./par1-more-test/input/push3.txt" "./par1-more-test/test/push3.txt";
   interpreter "./par1-more-test/input/push4.txt" "./par1-more-test/test/push4.txt";
   interpreter "./par1-more-test/input/push5.txt" "./par1-more-test/test/push5.txt";
   interpreter "./par1-more-test/input/push6.txt" "./par1-more-test/test/push6.txt";
   interpreter "./par1-more-test/input/push7.txt" "./par1-more-test/test/push7.txt";

   interpreter "./par1-more-test/input/rem1.txt" "./par1-more-test/test/rem1.txt";
   interpreter "./par1-more-test/input/rem2.txt" "./par1-more-test/test/rem2.txt";

   interpreter "./par1-more-test/input/sub1.txt" "./par1-more-test/test/sub1.txt";
   interpreter "./par1-more-test/input/sub2.txt" "./par1-more-test/test/sub2.txt";
   interpreter "./par1-more-test/input/sub3.txt" "./par1-more-test/test/sub3.txt";
   interpreter "./par1-more-test/input/sub4.txt" "./par1-more-test/test/sub4.txt";

   interpreter "./par1-more-test/input/swap1.txt" "./par1-more-test/test/swap1.txt";
   interpreter "./par1-more-test/input/swap2.txt" "./par1-more-test/test/swap2.txt";
   interpreter "./par1-more-test/input/swap3.txt" "./par1-more-test/test/swap3.txt";
   interpreter "./par1-more-test/input/swap4.txt" "./par1-more-test/test/swap4.txt"; *)