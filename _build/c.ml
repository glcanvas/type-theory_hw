open Tree;;
(*
let out_buffer = Buffer.create 2048;;
let in_buffer = Buffer.create 2048;;
let rec  write_to_buffer buffer expression=
    let token = expression in
        match token with
            | Application (a,b) ->      Buffer.add_char buffer '(';
                                        write_to_buffer buffer a;
                                        Buffer.add_char buffer ' ';
                                        write_to_buffer buffer b;
                                        Buffer.add_char buffer ')'

            | Abstraction (a,b) ->      Buffer.add_string buffer (String.concat "" ["(\\";a;"."]);
                                        write_to_buffer buffer b;
                                        Buffer.add_char buffer ')';

            | Variable(a)       ->      Buffer.add_string buffer a;;
 write_to_buffer out_buffer d;;
 Buffer.add_char out_buffer '\n';;
 print_string (Buffer.contents out_buffer);;
*)

module AlgebraMap = Map.Make(String);;
module AbstractVar = Map.Make(String);;
exception MatchEquation of string

type algebra =  Var of string (* constant *)
            |   Func of string * algebra * algebra (* for expression like -> smth smth *);;
let common_variable = "a";;

let custom_merge a b = (*AlgebraMap.fold AlgebraMap.add a b;;*)
        List.rev_append a b;;

let rec algebra_to_string expression =
    let token = expression in
        match token with
            | Var(a) -> a
            | Func(a, b , c) -> String.concat "" [a ; " (" ; (algebra_to_string b) ; " " ; (algebra_to_string c); ")"];;



let update_variable var =
    let last = (String.length var) - 1 in
        let symb = String.get var last in
            match symb with
                | 'z'   ->   var ^ "a"
                | _     ->   let new_var = String.sub var 0 last  in
                                let new_var = new_var ^ Char.escaped (Char.chr ((Char.code symb) + 1) ) in
                                    new_var;;

 let rec build_system expression free_var abstaction_name =
    let token = expression in
        match token with
            | Application (a, b) ->  let union_a, term_a, last_map_a, last_var_a =  build_system a free_var abstaction_name in
                                        let  union_b, term_b, last_map_b, last_var_b = build_system b last_var_a abstaction_name in
                                            let new_var = update_variable last_var_b in
                                                let merged_equation = custom_merge union_a union_b in
                                                    let merged_map = AbstractVar.fold AbstractVar.add last_map_a last_map_b in
                                                            let added_equation = merged_equation @ [(term_a, (Func ("->", term_b, Var(new_var))))] in
                                                        (added_equation, Var(new_var), merged_map, new_var)

            | Abstraction (a, b) ->     let new_free_var = update_variable free_var in
                                            let updated_map = AbstractVar.add a new_free_var abstaction_name in
                                                    let union_b, term_b, last_map_b, last_var_b = build_system b new_free_var updated_map in
                                                        let new_var = update_variable last_var_b in
                                                            (union_b, Func ("->", Var(new_free_var), term_b), last_map_b, new_var)

            | Variable (a)       ->     let contains_variable = AbstractVar.mem a abstaction_name in
                                            if contains_variable then
                                                let variable_name = AbstractVar.find a abstaction_name in
                                                    (  [], Var(variable_name), abstaction_name, free_var)
                                            else
                                                let new_var = update_variable free_var in
                                                    (  [], Var(new_var), abstaction_name, new_var) ;;




let is_var equation =
    match  equation with
        | Var(a) -> true
        | _ -> false;;

let second_action item =
    if (not (is_var (fst item))) && (not (is_var (snd item))) then
        match item with
        | Func(a, b, c), Func(d, e, f) ->   [(b, e); (c, f)]
        | _ -> []
    else
        [item];;

(*
define triple values x y z
from conspect
*)
let rec help_calculate_num_of_vars expr mp =
    match expr with
    | Var(a) -> if AbstractVar.mem a mp then
                    let num = AbstractVar.find a mp in
                        AbstractVar.add a (num + 1) mp
                else
                    AbstractVar.add a 1 mp
    | Func(a, b, c) -> let result_b = help_calculate_num_of_vars b mp in
                            let result_c = help_calculate_num_of_vars c result_b in
                                result_c;;

(* first number *)
let calculate_first item =
    let first = fst item in
    let emp_mp = AbstractVar.empty in
        let result = help_calculate_num_of_vars first emp_mp in
            let ok_vars = AbstractVar.filter (fun a b -> b > 1) result in
                AbstractVar.cardinal ok_vars;;
(*end first number*)

(*second number*)
let rec help_calc_second exp =
        match exp with
            | Var(a) -> 0
            | Func(a, b, c) -> (help_calc_second b) + (help_calc_second c) + 1;;

let calculate_second item =
        let f = help_calc_second (fst item) in
            let s = help_calc_second (snd item) in
               f + s;;
(*end second number*)

(*third number*)
let calculate_third item =
    match item with
    | Var(a), Var(b) -> if a == b then 1 else 0
    | Func(b, c, d), Var(a) -> 1
    | _ -> 0;;
(*end third number*)

let calculate_statement equations =
       let n1 = ref 0 in
            let n2 = ref 0 in
                let n3 = ref 0 in

                    let array_of_tuple = List.map
                        (fun it-> (calculate_first it) + (calculate_second it) + (calculate_third it))
                            equations in

       (n1,n2,n3);;


let solve_equations equations  =
    let can_update = ref true in

        while !can_update do
            can_update := false;
            (*term = var -> var = term*)
            let first = List.map (fun item -> if (not (is_var (fst item))) && (is_var (snd item)) then ((snd item), (fst item)) else item) equations in
                (*term = term -> [equiv_1..equiv_n]*)
                let second = List.fold_left (fun a b -> a @ b) [] (List.map second_action first) in

                    can_update := false
        done;;

(*
\f.\x.(f(f x))
\f.(\x. f (x x)) (\x. f (x x))
*)
let e = Lexing.from_string "(\x.x)(\y.y)";;
let d =(Parser.lambdaParser Lexer.main)  e;;




let empty_bounded_names = AbstractVar.empty;;
let equations, lambda_type, bounded_names, last_free_name = build_system d common_variable empty_bounded_names;;

List.iter (fun a -> print_string ((algebra_to_string (fst a)) ^ " = ");
                               print_string ((algebra_to_string (snd a)  ) ^ "\n")) equations;;
print_string "=======\n";;
AbstractVar.iter (fun a b ->  print_string ("key: " ^ a ^ " value: " ^ b ^ "\n")) bounded_names;;
print_string "==========\n";;
print_string ((algebra_to_string lambda_type) ^ "\n");;
