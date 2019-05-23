type const = I of int | S of string | E  | B of bool | U
| N of string | C of const * com list * (const * const) list list

and com = Pushi of const | Pushb of const | Pushs of const | Pushn of const
| Push of const | Add  | Sub  | Mul  | Div  | Rem  | Neg | Quit
| Swap | Pop | Bind | Let | End | Cat | And | Or | Not | Lessthan | Equal | If | Func of const * const
| Funend | Call | Return

let rec getClosure stack code =
  match stack with
    | s::xs -> (match s with
                    | (Funend) -> (code, Funend::xs)
                    | _ -> getClosure xs (s::code))
    | _ -> (code, stack)

let rec fetch m name =
  match m, name with
    | (N s2, x)::ms, N s1 -> if s1 = s2 then Some x
                             else fetch ms name
    | ([], n) -> None
    | _ -> None

let rec bigFetch m name =
  match m, name with
    | m::ms, N n -> let find = (fetch m (N n)) in (match find with
                                                    | Some x -> Some x
                                                    | None ->  bigFetch ms (N n))
    | ([], n) -> None
    | _ -> None

let cat stack m =
  match stack with
    | (S s1)::(S s2)::xs ->  (S (s2^s1))::xs
    | (S s1)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                  | Some (S s2) -> (S (s2^s1))::xs
                                                                  | None -> (E)::stack
                                                                  | _ -> (E)::stack)
    | (N n)::(S s2)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                  | Some (S s1) -> (S (s2^s1))::xs
                                                                  | None -> (E)::stack
                                                                  | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                      | Some (S s1), Some (S s2) -> (S (s2^s1))::xs
                                                                                                      | None, None -> (E)::stack
                                                                                                      | _ -> (E)::stack)
    | _ -> (E)::stack

let log_and stack m =
  match stack with
    | (B b1)::(B b2)::xs -> if (b1 && b2) then (B true)::xs
                            else (B false)::xs
    | (B b1)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                  | Some (B b2) -> if (b1 && b2) then (B true)::xs
                                                                                   else (B false)::xs
                                                                  | None -> (E)::stack
                                                                  | _ -> (E)::stack)
    | (N n)::(B b2)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                  | Some (B b1) -> if (b1 && b2) then (B true)::xs
                                                                                   else (B false)::xs
                                                                  | None -> (E)::stack
                                                                  | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (B b1), Some (B b2) -> if (b1 && b2) then (B true)::xs
                                                                                                                                      else (B false)::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (E)::stack)
    | _ -> (E)::stack

let log_or stack m =
  match stack with
    | (B b1)::(B b2)::xs -> if (b1 || b2) then (B true)::xs
                            else (B false)::xs
    | (B b1)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                  | Some (B b2) -> if (b1 || b2) then (B true)::xs
                                                                                   else (B false)::xs
                                                                  | None -> (E)::stack
                                                                  | _ -> (E)::stack)
    | (N n)::(B b2)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                  | Some (B b1) -> if (b1 || b2) then (B true)::xs
                                                                                   else (B false)::xs
                                                                  | None -> (E)::stack
                                                                  | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (B b1), Some (B b2) -> if (b1 || b2) then (B true)::xs
                                                                                                                                      else (B false)::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (E)::stack)
    | _ -> (E)::stack

let log_not stack m =
  match stack with
    | (B b)::xs -> if b then (B false)::xs
                   else (B true)::xs
    | (N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                        | Some (B b) -> if b then (B false)::xs
                                                                        else (B true)::xs
                                                        | None -> (E)::stack
                                                        | _ -> (E)::stack)
    | _ -> (E)::stack

let lessThan stack m =
  match stack with
    | (I x)::(I y)::xs -> if y < x then (B true)::xs
                          else (B false)::xs
    | (I x)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> if i < x then (B true)::xs
                                                                                else (B false)::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> if x < i then (B true)::xs
                                                                                else (B false)::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (I i), Some (I i2) -> if i2 < i then (B true)::xs
                                                                                                                                     else (B false)::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (E)::stack)
    | _ -> (E)::stack

let equal stack m =
  match stack with
    | (I x)::(I y)::xs -> if y = x then (B true)::xs
                          else (B false)::xs
    | (I x)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> if i = x then (B true)::xs
                                                                                else (B false)::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> if x = i then (B true)::xs
                                                                                else (B false)::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (I i), Some (I i2) -> if i2 = i then (B true)::xs
                                                                                                                                     else (B false)::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (E)::stack)
    | _ -> (E)::stack


let log_if stack m =
  match stack with
    | x::y::(B b)::xs -> if b then x::xs
                         else y::xs
    | x::y::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                              | Some (B b) -> if b then x::xs
                                                                              else y::xs
                                                              | None -> (E)::stack
                                                              | _ -> (E)::stack)
    | _ -> (E)::stack


let add stack m =
  match stack with
    | (I x)::(I y)::xs -> (I(x+y))::xs
    | (I x)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> (I(i+x))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> (I(i+x))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                      | Some (I i), Some (I q) -> (I(i+q))::xs
                                                                                                      | None, None -> (E)::stack
                                                                                                      | _ -> (E)::stack)
    | _ -> (E)::stack

let sub stack m =
  match stack with
    | (I x)::(I y)::xs -> (I(y-x))::xs
    | (I x)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> (I(i-x))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> (I(x-i))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                      | Some (I i), Some (I q) -> (I(q-i))::xs
                                                                                                      | None, None -> (E)::stack
                                                                                                      | _ -> (E)::stack)
    | _ -> (E::stack)

let div stack m =
  match stack with
    | (I x)::(I y)::xs -> if x = 0 then (E)::stack
                          else (I(y/x))::xs
    | (I x)::(N n)::xs -> if x = 0 then (E)::stack
                          else let newbind = (bigFetch m (N n)) in (match newbind with
                                                                      | Some (I i) -> (I(i/x))::xs
                                                                      | None -> (E)::stack
                                                                      | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> if i = 0 then (E)::stack
                                                                                else (I(x/i))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (I i), Some (I q) -> if i = 0 then (E)::stack
                                                                                                                                    else (I(q/i))::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (E)::stack)
    | _ -> (E)::stack

let mul stack m =
  match stack with
    | (I x)::(I y)::xs -> (I(x*y))::xs
    | (I x)::(N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> (I(x*i))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> (I(x*i))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (I i), Some (I q) -> (I(q*i))::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (print_endline "unbound names");(E)::stack)
    | _ -> (E)::stack

let pop stack =
  match stack with
    | x::xs -> xs
    | _ -> (E)::stack

let rem stack m =
  match stack with
    | (I x)::(I y)::xs -> if x = 0 then (E)::stack
                          else (I(y mod x))::xs
    | (I x)::(N n)::xs -> if x = 0 then (E)::stack
                          else let newbind = (bigFetch m (N n)) in (match newbind with
                                                                    | Some (I i) -> (I(i mod x))::xs
                                                                    | None -> (E)::stack
                                                                    | _ -> (E)::stack)
    | (N n)::(I x)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                                | Some (I i) -> if i = 0 then (E)::stack
                                                                                else (I(x mod i))::xs
                                                                | None -> (E)::stack
                                                                | _ -> (E)::stack)
    | (N n)::(N n1)::xs -> let newbind = (bigFetch m (N n)) in let newbind1 = (bigFetch m (N n1)) in (match newbind, newbind1 with
                                                                                                        | Some (I i), Some (I q) -> if i = 0 then (E)::stack
                                                                                                                                    else (I(q mod i))::xs
                                                                                                        | None, None -> (E)::stack
                                                                                                        | _ -> (E)::stack)
    | _ -> (E)::stack

let neg stack m =
  match stack with
    | (I x)::xs -> (I(x -(2*x)))::xs
    | (N n)::xs -> let newbind = (bigFetch m (N n)) in (match newbind with
                                                      | Some (I i) -> (I(i -(2*i)))::xs
                                                      | None -> (E)::stack
                                                      | _ -> (E)::stack)
    | _ -> (E)::stack

let swap stack =
  match stack with
    | x::y::xs -> y::x::xs
    | _ -> (E)::stack

let bind stack (m : (const * const) list list) =
  match stack, m with
    | (I i)::(N n)::xs, m::ms -> (U::xs, (((N n, I i)::m)::ms) )
    | (S s)::(N n)::xs, m::ms -> (U::xs, ((N n, S s )::m)::ms)
    | (B b)::(N n)::xs, m::ms -> (U::xs, ((N n, B b)::m)::ms)
    | U::(N n)::xs, m::ms -> (U::xs, ((N n, U)::m)::ms)
    | (N n)::(N ns)::xs, m::ms -> let newbind = (bigFetch (m::ms) (N n)) in (match newbind with
                                                                              | Some y-> (U::xs, ((N ns, y)::m)::ms)
                                                                              | None  -> (E::stack, m::ms))
    | _ -> (E::stack, m)

let bindarg name value m =
  match name, value with
    | (N n),(value) -> (N n, I value)::m

let newBind name param clist (m : (const * const) list list) : (const * const) list list =
  match name, param, clist, m with
    | name, param, clist, m1::ms -> ((name, C (param, clist, m))::m1)::ms
    | _ -> m

let log_end stack m =
  match (stack, m) with
    | (x::x1::xs, m::ms) -> (match x with
                              | y::ys -> ((y::x1)::xs, ms)
                              | [] -> (x1::xs, ms))
    | _ -> (stack, m)


let rec print_out stack oc =
  match stack with
    | (I i)::xs -> let int_string = string_of_int i in Printf.fprintf oc "%s\n" int_string; print_out xs oc
    | (B b)::xs -> (match b with
                    | true -> Printf.fprintf oc "%s\n" ":true:"; print_out xs oc
                    | false -> Printf.fprintf oc "%s\n" ":false:"; print_out xs oc)

    | (S s)::xs -> Printf.fprintf oc "%s\n" s; print_out xs oc
    | (N n)::xs -> Printf.fprintf oc "%s\n" n; print_out xs oc
    | E::xs -> Printf.fprintf oc "%s\n" ":error:"; print_out xs oc
    | U::xs -> Printf.fprintf oc "%s\n" ":unit:"; print_out xs oc
    | [] -> close_out oc

let interpreter ((inFile : string), (outFile : string)) : unit =

  let ic = open_in inFile in

  let oc = open_out outFile in
  (* Helper function: file input function. It reads file line by line
       and return the result as a list of string.  *)
  let rec loop_read acc =

    try
        let l = input_line ic in loop_read (l::acc)
    with
    | End_of_file -> List.rev acc in


  let ls_str = loop_read [] in

  let rec to_comlist ls_str ls =
    match ls_str with
      | [] -> List.rev ls
      | x::xs -> let x' = (String.split_on_char ' ' x) in match x' with
                                                          | "pushi"::y::ys -> let int_opt =  (int_of_string_opt y) in (match int_opt with
                                                                                                                      | Some i -> to_comlist xs ((Pushi (I i))::ls)
                                                                                                                      | None -> to_comlist xs ((Push (E))::ls))

                                                          | "pushb"::y::ys -> if y = ":true:" then to_comlist xs ((Pushb (B true))::ls)
                                                                              else if y = ":false:" then to_comlist xs ((Pushb (B false))::ls)
                                                                              else to_comlist xs ((Push (E))::ls)
                                                          | "pushs"::y::ys -> if y.[0] = '"' then let new_str = String.sub x 7 ((String.length x) - 8) in to_comlist xs ((Pushs (S new_str))::ls)
                                                                              else to_comlist xs ((Push(E))::ls)
                                                          | "add"::ys -> to_comlist xs (Add::ls)
                                                          | "sub"::ys -> to_comlist xs (Sub::ls)
                                                          | "mul"::ys -> to_comlist xs (Mul::ls)
                                                          | "div"::ys -> to_comlist xs (Div::ls)
                                                          | "push"::y::ys -> if y = ":unit:" then to_comlist xs ((Push(U))::ls) else to_comlist xs ((Push(E))::ls)
                                                          | "pushn"::y::ys -> let fchar = y.[0] in (match fchar with
                                                                                                    | 'a' .. 'z' -> to_comlist xs ((Pushn (N y))::ls)
                                                                                                    | 'A' .. 'Z' -> to_comlist xs ((Pushn (N y))::ls)
                                                                                                    | '_' -> to_comlist xs ((Pushn(N y))::ls)
                                                                                                    | _ -> to_comlist xs ((Push(E))::ls))

                                                          | "pop"::y -> to_comlist xs (Pop::ls)
                                                          | "rem"::y -> to_comlist xs (Rem::ls)
                                                          | "neg"::y -> to_comlist xs (Neg::ls)
                                                          | "swap"::y -> to_comlist xs (Swap::ls)
                                                          | "quit"::y -> to_comlist xs (Quit::ls)
                                                          | "bind"::y -> to_comlist xs (Bind::ls)
                                                          | "let"::y -> to_comlist xs (Let::ls)
                                                          | "end"::y -> to_comlist xs (End::ls)
                                                          | "cat"::y -> to_comlist xs (Cat::ls)
                                                          | "and"::y -> to_comlist xs (And::ls)
                                                          | "or"::y -> to_comlist xs (Or::ls)
                                                          | "not"::y -> to_comlist xs (Not::ls)
                                                          | "equal"::y -> to_comlist xs (Equal::ls)
                                                          | "if"::y -> to_comlist xs (If::ls)
                                                          | "lessThan"::y -> to_comlist xs (Lessthan::ls)
                                                          | "fun"::fs::fp::y -> to_comlist xs ((Func(N fs, N fp))::ls)
                                                          | "funEnd"::y -> to_comlist xs (Funend::ls)
                                                          | "call"::y -> to_comlist xs (Call::ls)
                                                          | "return"::y -> to_comlist xs (Return::ls)
                                                          | [] -> to_comlist xs ls
                                                          | _ -> to_comlist xs ls
                                                          in

  let mem = [[]] in
  let stack = [[]] in

  let rec process com_list stack (m : (const * const) list list)  =
    match com_list, stack, m with
      | (Add::xs, s::ss, m) -> process xs ((add s m)::ss) (m)
      | (Sub::xs, s::ss, m) -> process xs ((sub s m)::ss) (m)
      | (Div::xs, s::ss, m) -> process xs ((div s m)::ss) (m)
      | (Mul::xs, s::ss, m) -> process xs ((mul s m)::ss) (m)
      | (Rem::xs, s::ss, m) -> process xs ((rem s m)::ss) (m)
      | (Neg::xs, s::ss, m) -> process xs ((neg s m)::ss) (m)
      | (Swap::xs, s::ss, m) -> process xs ((swap s)::ss) (m)
      | (Pop::xs, s::ss, m) -> process xs ((pop s)::ss) (m)
      | (Quit::xs, s::ss, m) -> (s, m)
      | (Pushi (I i)::xs, s::ss, m) -> process xs (((I i)::s)::ss) (m)
      | (Pushs (S s)::xs, l::ss, m) -> process xs (((S s)::l)::ss) (m)
      | (Pushn (N n)::xs, s::ss, m) -> process xs (((N n)::s)::ss) (m)
      | (Push (e)::xs, s::ss, m) -> process xs (((e)::s)::ss) (m)
      | (Pushb (B b)::xs, s::ss, m) -> process xs (((B b)::s)::ss) (m)
      | (Let::xs, s, m) -> process xs ([]::s) ([]::m)
      | (End::xs, s, m)-> let end1 = (log_end s m) in (match end1 with
                                                          | (s, m1) -> process xs s m1)
      | (Cat::xs, s::ss, m) -> process xs ((cat s m)::ss) (m)
      | (And::xs, s::ss, m) -> process xs ((log_and s m)::ss) (m)
      | (Or::xs, s::ss, m) -> process xs ((log_or s m)::ss) (m)
      | (Not::xs, s::ss, m) -> process xs ((log_not s m)::ss) (m)
      | (Lessthan::xs, s::ss, m) -> process xs ((lessThan s m)::ss) (m)
      | (Equal::xs, s::ss, m) -> process xs ((equal s m)::ss) (m)
      | (If::xs, s::ss, m) -> process xs ((log_if s m)::ss) (m)
      | (Bind::xs, s::ss, m) -> let (newstack, newenv) = (bind s m) in process xs ((newstack)::ss) (newenv)
      | ((Func (N n1, N n2))::xs, s, m) -> let body = (getClosure xs [] ) in (match body with
                                                                                        | (code, cmnds) -> process cmnds (s) (newBind (N n1) ( N n2) (List.rev code) m))
      | (Funend::xs, s::ls, m) -> process xs ((U::s)::ls) m
      | (Call::xs, (s)::ss, m::ms) -> (match s with
                                        | (I arg)::(N name)::ts -> let isbound = (fetch m (N name)) in (match isbound, arg with
                                                                                                          | Some y, arg -> (match y, arg with
                                                                                                                              | (C (param, cmlist, mem)), arg ->  process (cmlist@xs) (([])::ts::ss) ((bindarg param arg m )::ms)
                                                                                                                              | _ -> (print_endline "closure not found"; process xs (((E)::s)::ss) (m::ms)))
                                                                                                          | None, arg -> process xs (((E)::s)::ss) (m::ms)
                                                                                                          )
                                        | (N arg)::(N name)::ts -> let argbound = (fetch m (N arg)) in let isbound = (fetch m (N name)) in (match isbound, argbound with
                                                                                                                                  | Some y, Some arg -> (match y, arg with
                                                                                                                                                            | (C (param, cmlist, mem)), (I arg) -> process (cmlist@xs) (([])::s::ss) ((bindarg param arg m )::ms)
                                                                                                                                                            | _ -> process xs (((E)::s)::ss) (m::ms))
                                                                                                                                  | None, None -> process xs (((E)::s)::ss) (m::ms)
                                                                                                                                  )
                                        | _ -> process xs (((E)::s)::ss) (m::ms)
                                      )
      | (Return::xs, s1::s2::ls, m::ms) -> (match s1, m with
                                            | z::ts, m -> process xs ((z::s2)::ls) (ms)
                                            |_ -> process xs (s2::ls) (ms))

      | (_, s::xs, m) -> (s, m)
      in

  let print_stack = (to_comlist ls_str []) in
  let procc = process (print_stack) (stack) (mem) in
  match procc with
    | (stack, mem) -> print_out (stack) oc
    | _ -> ();;
