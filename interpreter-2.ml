
(* Reference implementation of full interpreter for BU Fall2020 CS320
   Spencer Vilicic
   11/23/20
*)

(* utility functions *)

let rec implode (cs: char list): string =
  match cs with
  | c :: cs -> (String.make 1 c) ^ implode cs
  | [] -> ""

let rec explode (s: string): char list =
  let len = String.length s in
  let rec loop i =
    if i < len then (String.get s i) :: loop (i + 1)
    else []
  in loop 0

let readlines fname =
  let ic = open_in fname in
  let rec loop ic =
    match input_line ic with
    | s -> s :: loop ic
    | exception _ -> []
  in
  let s = loop ic in
  let () = close_in ic in
  s

(* Abstract syntax and printing *)

type name = string

type value =
  | B of bool
  | I of int
  | S of string
  | N of name
  | U
  | E

and command =
  | Push of value | Swap | Pop
  | Add | Sub | Mul | Div | Rem | Neg
  | Quit | Cat | And | Or | Not | Eq
  | Lte | Lt | Gte | Gt | Bnd 
  | BeginEnd of commands 
  | IfThenElse of commands list | EndIf

and commands = command list

and stack = value list

and environment = Root of stack * ((name * value) list) | Child of environment * stack * ((name * value) list)
(* and environment = (name * value) list *)

(* for scope of begin/end and if/then/else *)
(* and block = commands list *)

let fprint_value oc cst =
  Printf.
    (match cst with
     | B b -> fprintf oc "<%b>" b
     | I i -> fprintf oc "%d" i
     | S s -> fprintf oc "%s" s
     | N n -> fprintf oc "%s" n
     | U -> fprintf oc "<unit>"
     | E -> fprintf oc "<error>")

let rec fprint_command oc com =
  Printf.
    (match com with
     | Push cst ->
       fprintf oc "Push %a\n" fprint_value cst;
     | Swap -> fprintf oc "Swap\n"
     | Pop -> fprintf oc "Pop\n"
     | Add -> fprintf oc "Add\n"
     | Sub -> fprintf oc "Sub\n"
     | Mul -> fprintf oc "Mul\n"
     | Div -> fprintf oc "Div\n"
     | Rem -> fprintf oc "Rem\n"
     | Neg -> fprintf oc "Neg\n"
     | Quit -> fprintf oc "Quit\n"
     | Cat -> fprintf oc "Cat\n"
     | And -> fprintf oc "And\n"
     | Or -> fprintf oc "Or\n"
     | Not -> fprintf oc "Not\n"
     | Eq -> fprintf oc "Eq\n"
     | Lte -> fprintf oc "Lte\n"
     | Lt -> fprintf oc "Lt\n"
     | Gte -> fprintf oc "Gte\n"
     | Gt -> fprintf oc "Gt\n"
     | Bnd -> fprintf oc "Bnd\n"
     | BeginEnd coms -> fprintf oc "Begin\n"; fprint_commands oc coms; fprintf oc "End\n"
     | IfThenElse coms -> ( match coms with
         | _if::_then::_else::_ -> fprintf oc "If\n"; fprint_commands oc _if;
           fprintf oc "Then\n"; fprint_commands oc _then;
           fprintf oc "Else\n"; fprint_commands oc _else;
         | _ -> fprintf oc ""
       )
     | EndIf -> fprintf oc "EndIf\n")

and fprint_commands oc coms =
  List.iter (fprint_command oc) coms

let fprint_stack oc st =
  Printf.
    (List.iter (fun sv -> fprint_value oc sv; fprintf oc "\n") st)

let print_value = fprint_value stdout
let print_command = fprint_command stdout
let print_commands = fprint_commands stdout
let print_stack = fprint_stack stdout

(* Parser *)

type 'a parser = char list -> 'a option * char list

let return (a: 'a): 'a parser  = fun cs -> (Some a, cs)

let bind (p: 'a parser) (f: 'a -> 'b parser): 'b parser =
  fun cs ->
  let a, cs' = p cs in
  match a with
  | Some a -> f a cs'
  | None -> (None, cs)

let (let*) = bind

let (|>>) (p: 'a parser) (f: 'a -> 'b): 'b parser =
  let* a = p in
  return (f a)

let (>>) (p: 'a parser) (q: 'b parser): 'b parser =
  let* _ = p in
  q

let (<<) (p: 'a parser) (q: 'b parser): 'a parser =
  let* a = p in
  let* _ = q in
  return a

let fail: 'a parser = fun cs -> (None, cs)

let delay (): unit parser = return ()

let (<|>) (p: 'a parser) (q: 'a parser): 'a parser =
  fun cs ->
  match p cs with
  | (Some a, cs) -> (Some a, cs)
  | (None, _) -> q cs

let choice (ps: 'a parser list): 'a parser =
  List.fold_right (fun p acc -> p <|> acc) ps fail

let rec many (p: 'a parser): 'a list parser =
  (let* a = p in
   let* ls = many p in
   return(a :: ls))
  <|>
  return[]

let many1 (p: 'a parser): 'a list parser =
  let* a = p in
  let* ls = many p in
  return(a :: ls)

let opt (p: 'a parser): 'a option parser =
  (let* a = p in
   return (Some a))
  <|>
  return None

let read: char parser =
  fun cs ->
  match cs with
  | c :: cs -> (Some c, cs)
  | [] -> (None, cs)

let rec readn (n: int): string parser =
  if n > 0 then
    let* c = read in
    let* cs = readn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let rec peak: char parser =
  fun cs ->
  match cs with
  | c :: _ -> (Some c, cs)
  | [] -> (None, cs)

let rec peakn (n: int): string parser =
  if n > 0 then
    let* c = read in
    let* cs = peakn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let sat (f: char -> bool): char parser =
  let* c = read in
  if f c then return c
  else fail

let char (c: char): char parser =
  sat ((=) c)

let digit: char parser =
  sat (fun x -> '0' <= x && x <= '9')

let lower: char parser =
  sat (fun x -> 'a' <= x && x <= 'z')

let upper: char parser =
  sat (fun x -> 'A' <= x && x <= 'Z')

let alpha: char parser =
  lower <|> upper

let alphanum: char parser =
  alpha <|> digit

let string (str: string): unit parser =
  let len = String.length str in
  let* str' = readn len in
  if str = str' then return ()
  else fail

(* whitespace parsers *)
let w: unit parser =
  let* _ = sat (String.contains " \r\n\t") in
  return ()

let ws: unit parser =
  let* _ = many w in
  return ()

let ws1: unit parser =
  let* _ = w in
  let* _ = ws in
  return ()

let reserved (s: string): unit parser =
  string s >> ws

let delimit l p r =
  let* _ = l in
  let* res = p in
  let* _ = r in
  return res

let int: int parser =
  let* sgn = opt (reserved "-") in
  let* cs = many1 digit in
  let n = List.fold_left
      (fun acc c -> acc * 10 + (int_of_char c) - (int_of_char '0'))
      0 cs
  in
  match sgn with
  | Some _ -> return (-n)
  | None -> return n

let bool: bool parser =
  (string "<true>" >> return true) <|>
  (string "<false>" >> return false)

let error: unit parser =
  string "<error>"

let unit: unit parser =
  string "<unit>"

let str: string parser =
  let* cs = delimit (char '"') (many (sat ((!=) '"'))) (char '"') in
  return (implode cs)

let name: string parser =
  let* os = many (char '_') in
  let* c = alpha in
  let* cs = many (alphanum <|> char '_') in
  return ((implode os) ^ (implode (c :: cs)))

let value: value parser =
  choice
    [ (int   |>> fun n -> I n);
      (bool  |>> fun b -> B b);
      (error |>> fun e -> E);
      (str   |>> fun s -> S s);
      (name  |>> fun n -> N n);
      (unit  |>> fun u -> U); ]

let push: command parser =
  let* _ = reserved "Push" in
  let* cst = value << ws in
  return (Push cst)

let swap: command parser =
  let* _ = reserved "Swap" in
  return Swap

let pop: command parser =
  let* _ = reserved "Pop" in
  return Pop

let add: command parser =
  let* _ = reserved "Add" in
  return Add

let sub: command parser =
  let* _ = reserved "Sub" in
  return Sub

let mul: command parser =
  let* _ = reserved "Mul" in
  return Mul

let div: command parser =
  let* _ = reserved "Div" in
  return Div

let rem: command parser =
  let* _ = reserved "Rem" in
  return Rem

let neg: command parser =
  let* _ = reserved "Neg" in
  return Neg

let quit: command parser =
  let* _ = reserved "Quit" in
  return Quit

let cat: command parser =
  let* _ = reserved "Cat" in
  return Cat

let and': command parser =
  let* _ = reserved "And" in
  return And

let or': command parser =
  let* _ = reserved "Or" in
  return Or

let not': command parser =
  let* _ = reserved "Not" in
  return Not

let eq: command parser =
  let* _ = reserved "Eq" in
  return Eq

let lte: command parser =
  let* _ = reserved "Lte" in
  return Lte

let lt: command parser =
  let* _ = reserved "Lt" in
  return Lt

let gte: command parser =
  let* _ = reserved "Gte" in
  return Gte

let gt: command parser =
  let* _ = reserved "Gt" in
  return Gt

let bnd: command parser =
  let* _ = reserved "Bnd" in
  return Bnd

let command () =
  choice
    [ push; swap; pop;
      add; sub; mul; div; rem; neg;
      quit; cat; and'; or'; not'; eq;
      lte; lt; gte; gt; bnd]

let rec beginend (): command parser =
  let* _ = reserved "Begin" in 
  let* coms = many1 (choice [command(); ifthenelse(); beginend()]) in
  let* _ = reserved "End" in 
  return (BeginEnd coms)

and ifthenelse (): command parser = 
  let* _ = reserved "If" in
  let* coms1 = many1 (choice [command(); ifthenelse(); beginend()]) in
  let* _ = reserved "Then" in
  let* coms2 = many1 (choice [command(); ifthenelse(); beginend()]) in
  let* _ = reserved "Else" in
  let* coms3 = many1 (choice [command(); ifthenelse(); beginend()]) in
  let* _ = reserved "EndIf" in 
  return (IfThenElse [coms1; coms2; coms3])

let commands () =
  many1 (choice [command (); ifthenelse(); beginend()])

(* environment *)

let add_to_env lst (n: name) (v: value) = (n, v)::lst

let store n v env = 
  match env with
  | Root (stack, lst) -> Root (stack, add_to_env lst n v)
  | Child (env', stack, lst) -> Child (env', stack, add_to_env lst n v)

(* let update_env s env = 
   match env with
   | Root (_, lst) -> Root (s, lst)
   | Child (env', _, lst) -> Child (env', s, lst) *)

let rec get (n: name) (env: environment) =
  match env with 
  | Root (_, lst) -> List.assoc_opt n lst
  | Child (env', _, lst) -> (match List.assoc_opt n lst with
      | Some v -> (match v with 
          | N n' -> get n' env
          | _ -> Some v )
      | None -> get n env' )

let get_int x env =
  match x with
  | I i -> Some i
  | N n -> (match get n env with
      | Some I i -> Some i
      | _ -> None)
  | _ -> None

let get_bool x env =
  match x with
  | B b -> Some b
  | N n -> (
      match get n env with
      | Some B b -> Some b
      | _ -> None )
  | _ -> None

let get_string x env =
  match x with
  | S s -> Some s
  | N n -> ( match get n env with
      | Some S s -> Some s
      | _ -> None )
  | _ -> None

(* evaluation *)

let rec eval coms stack (env: environment) =
  match coms, stack with
  | Push v :: coms, _ -> eval coms (v :: stack) env
  | Swap :: coms, x :: y :: stack -> eval coms (y :: x :: stack) env
  | Pop :: coms, x :: stack -> eval coms stack env
  | Bnd :: coms, [] -> eval coms (E :: stack) env
  | Bnd :: coms, x :: y :: stack' -> 
    (match x, y with
     | N x', y -> ( match y with
         | E -> eval coms (E :: stack) env
         | _ -> eval coms (U :: stack') (store x' y env) )
     | _, _ -> eval coms (E :: stack) env )
  | Bnd :: coms, x :: [] -> eval coms (E :: stack) env
  | BeginEnd com :: coms, _ -> ( match eval com [] (Child (env, stack, [])) with
      | frame::_ -> eval coms (frame :: stack) env
      | [] -> stack)
  | IfThenElse com :: coms, _ -> (match com with
      | _if::_then::_else::_ -> ( match eval _if [] (Child (env, stack, [])) with
          | frame::_ -> (match get_bool frame env with
              | Some true -> (match eval _then [] (Child (env, stack, [])) with
                  | frame'::_ -> eval coms (frame' :: stack) env
                  | [] -> stack )
              | Some false -> (match eval _else [] (Child (env, stack, [])) with
                  | frame'::_ -> eval coms (frame' :: stack) env
                  | [] -> stack )
              | error -> eval coms (E :: stack) env )
          | _ -> eval coms (E :: stack) env )
      | _ -> eval coms stack env)
  | EndIf :: coms, _ -> eval coms stack env
  | Add :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (I (x + y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Sub :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (I (x - y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Mul :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (I (x * y) :: stack') env
     | error ->
       eval coms (E :: stack) env )
  | Div :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some 0 -> eval coms (E :: stack) env
     | Some x, Some y -> eval coms (I (x / y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Rem :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some 0 -> eval coms (E :: stack) env
     | Some x, Some y -> eval coms (I (x mod y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Neg :: coms, x :: stack' ->
    (match get_int x env with
     | Some x -> eval coms (I (-x) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Cat :: coms, x :: y :: stack' -> 
    (match get_string x env, get_string y env with
     | Some x, Some y -> eval coms (S(x^y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | And :: coms, x :: y :: stack' ->
    (match get_bool x env, get_bool y env with
     | Some x, Some y -> eval coms (B(x&&y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Or :: coms, x :: y :: stack' ->
    (match get_bool x env, get_bool y env with
     | Some x, Some y -> eval coms (B(x||y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Not :: coms, x :: stack' ->
    (match get_bool x env with
     | Some x -> eval coms (B(not x) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Eq :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (B (x = y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Lte :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (B (x <= y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Lt :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (B (x < y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Gte :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (B (x >= y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Gt :: coms, x :: y :: stack' ->
    (match get_int x env, get_int y env with
     | Some x, Some y -> eval coms (B (x > y) :: stack') env
     | error -> eval coms (E :: stack) env )
  | Quit :: coms, _ -> stack
  | [], _ -> stack
  | _ :: coms, _ -> eval coms (E :: stack) env

(* testing *)

let parse fname =
  let strs = readlines fname in
  let css = List.map explode strs in
  let cs = List.fold_right (fun cs acc -> cs @ ['\n'] @ acc) css [] in
  match (ws >> commands ()) cs with
  | Some coms, [] -> coms
  | _, cs -> failwith (implode cs)

let interpreter (inputFile : string) (outputFile : string) =
  let coms = parse inputFile in
  let oc = open_out outputFile in
  let stack = eval coms [] (Root ([], [])) in
  let _ = fprint_stack oc stack in
  close_out oc

let main() = 
  interpreter "./part2-public/input/input1.txt" "./part2-public/test/test1.txt";
  interpreter "./part2-public/input/input2.txt" "./part2-public/test/test2.txt";
  interpreter "./part2-public/input/input3.txt" "./part2-public/test/test3.txt";
  interpreter "./part2-public/input/input4.txt" "./part2-public/test/test4.txt";
  interpreter "./part2-public/input/input5.txt" "./part2-public/test/test5.txt";
  interpreter "./part2-public/input/input6.txt" "./part2-public/test/test6.txt";
  interpreter "./part2-public/input/input7.txt" "./part2-public/test/test7.txt";
  interpreter "./part2-public/input/input8.txt" "./part2-public/test/test8.txt";
  interpreter "./part2-public/input/input9.txt" "./part2-public/test/test9.txt";
  interpreter "./part2-public/input/input10.txt" "./part2-public/test/test10.txt";
  interpreter "./part2-public/input/input11.txt" "./part2-public/test/test11.txt";
  interpreter "./part2-public/input/input12.txt" "./part2-public/test/test12.txt";
  interpreter "./part2-public/input/input13.txt" "./part2-public/test/test13.txt";
  interpreter "./part2-public/input/input14.txt" "./part2-public/test/test14.txt";
  interpreter "./part2-public/input/input15.txt" "./part2-public/test/test15.txt";
  interpreter "./part2-public/input/input16.txt" "./part2-public/test/test16.txt";
  interpreter "./part2-public/input/input17.txt" "./part2-public/test/test17.txt";
  interpreter "./part2-public/input/input18.txt" "./part2-public/test/test18.txt";
  interpreter "./part2-public/input/input19.txt" "./part2-public/test/test19.txt";
  interpreter "./part2-public/input/input20.txt" "./part2-public/test/test20.txt";