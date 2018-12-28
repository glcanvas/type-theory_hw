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
exception MatchEquation of string;;

type algebra =  Var of string (* constant *)
            |   Func of string * algebra * algebra (* for expression like -> smth smth *);;
let common_variable = "a";;

let custom_merge a b = List.rev_append a b;;

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

let encure_array eq_system =
    let double_list = List.map (fun x-> (x,(fst x, snd x))) eq_system in
        let la, lb = List.split double_list in
            List.rev_append la lb;;

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

let rec num_of_vars equation map_of_vars =
    match equation with
    | Var(a) -> if AbstractVar.mem a map_of_vars then
                            let num  = AbstractVar.find a map_of_vars in
                                    AbstractVar.add a (num + 1) map_of_vars
                        else AbstractVar.add a 1 map_of_vars
    | Func(a, b, c) -> let left_map = num_of_vars b map_of_vars in
                            let right_map = num_of_vars c left_map in
                                right_map;;
let available_map equations =
    List.filter (fun x -> let left, right  = x in
                    match left with
                    | Var(a) -> true
                    | _ -> false) equations;;

let rec replace_var_in_expression expression variable template =
    match expression with
    | Var(a) -> if Var (a) = variable then template else Var(a)
    | Func(a,b,c) -> let left_replace = if b = variable then template else replace_var_in_expression b variable template in
                        let right_replace = if c = variable then template else replace_var_in_expression c variable template in
                               Func(a,left_replace,right_replace)
                               ;;

let fourth_action_replace variable template equations =
    List.map (fun item ->
                    let left, right = item in
                        if left = variable && right = template then
                            item
                        else
                            (replace_var_in_expression left variable template,
                             replace_var_in_expression right variable template)
             ) equations;;

let fourth_action equations =
    let current_map = AbstractVar.empty in
        let tmp_map_list = List.map (fun item ->
                                        let em_map = AbstractVar.empty in
                                            let left_map = num_of_vars (fst item) em_map in
                                                let right_map = num_of_vars (snd item) left_map in
                                                        right_map
                                    ) equations in
                let result_map = List.fold_left (fun a b -> AbstractVar.merge (fun _ k1 k2 -> match k1, k2 with
                                                                                | Some v, Some u -> Some(u + v)
                                                                                | None, None -> None
                                                                                | None, k2 -> k2
                                                                                | k1, None -> k1
                                                                            ) a b) (AbstractVar.empty) tmp_map_list in
                                                  (*AbstractVar.iter (fun k v -> Printf.printf "%s <=> %d\n" k v) result_map; for debug *)
                    let filtered_map = AbstractVar.filter (fun k v -> v > 1) result_map in
                        let list_of_vars_term = available_map equations in
                        (*List.iter (fun it -> Printf.printf "var = %s term = %s \n" (algebra_to_string (fst it)) (algebra_to_string(snd it))) list_of_vars_term);*)
                            let filtered_list = List.filter (fun item -> let lft, rght = item in
                                                                match lft with
                                                                | Var(a) -> AbstractVar.mem a filtered_map
                                                                | _ -> false
                                                            ) list_of_vars_term in
                                            let num_of_can_vars = List.length filtered_list in
                                                match num_of_can_vars with
                                                | 0 -> equations
                                                | _ -> let var, template = List.hd filtered_list in
                                                            fourth_action_replace var template equations;;
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
    | Var(a), Var(b) -> if a = b then  1 else 0
    | Func(b, c, d), Var(a) -> 1
    | _ -> 0;;
(*end third number*)
(*
let calculate_statement equations =
                    let array_of_tuple = List.map
                        (fun it-> (calculate_first it, calculate_second it, calculate_third it))
                            equations in
                    let result_tuple = List.fold_left (fun a b -> let n1, n2, n3 = b in
                                                                    let a1, a2, a3 = a in
                                                                         (n1 + a1, n2 + a2, n3 + a3))
                                                                            (0,0,0) array_of_tuple in
       result_tuple;;
*)
let rec is_solved_form equations var_map =
    match equations with
    | [] -> true
    | _  -> let head = List.hd equations in
                let  tail = List.tl equations in
                    (*Printf.printf "head = %s | %s\n" (algebra_to_string (fst head)) (algebra_to_string (snd head)); for debug*)
                    let left, right = head in
                        match left with
                        | Var(a) -> let contains = AbstractVar.mem a var_map in
                                        if contains then
                                            false
                                        else
                                            is_solved_form tail (AbstractVar.add a 1 var_map)
                        | Func(a, b, c) -> false;;

let rec solve_equations equations =
    List.iter (fun it -> Printf.printf "%s | %s \n" (algebra_to_string (fst it)) (algebra_to_string (snd it))) equations;
    print_string "!!!!\n";
    (*term = var -> var = term*)
    let first = List.map (fun item -> if (not (is_var (fst item))) && (is_var (snd item)) then ((snd item), (fst item)) else item) equations in
        (*term = term -> [equiv_1..equiv_n]*)
        let second = List.fold_left (fun a b -> a @ b) [] (List.map second_action first) in
            (* if Var(a) = Var(b) -> remove them *)
            let delete_equal = List.filter
                (
                    fun item -> match item with
                        | Var(a), Var(b) -> if a=b then false else true
                        | _ -> true
                ) second in
                    (* replace all occur variable more than one time*)
                    let fourth = fourth_action delete_equal in
                        let compare = is_solved_form fourth (AbstractVar.empty) in
                            match compare with
                                | false -> solve_equations fourth
                                | true -> fourth;;

(*
\f.\x.(f(f x))
\f.(\x. f (x x)) (\x. f (x x))
(\x.x)(\y.y)(\x.x)(\x.x)(\x.x)(\x.x)(\x.x)(\x.x)(\x.x)(\x.x)(\x.x)(\x.x)
*)

let e = Lexing.from_string "\f.\x. f (f x)";;
let d =(Parser.lambdaParser Lexer.main)  e;;




let empty_bounded_names = AbstractVar.empty;;
let my_equitatins, lambda_type, bounded_names, last_free_name = build_system d common_variable empty_bounded_names;;

List.iter (fun a -> print_string ((algebra_to_string (fst a)) ^ " = ");
                               print_string ((algebra_to_string (snd a)  ) ^ "\n")) my_equitatins;;
print_string "=======\n";;
AbstractVar.iter (fun a b ->  print_string ("key: " ^ a ^ " value: " ^ b ^ "\n")) bounded_names;;
print_string "==========\n";;
print_string ((algebra_to_string lambda_type) ^ "\n");;


let eq =  encure_array [
(Var("d"), Var("c"));
(Var("e"), Var("d"));
](*my_equitatins*) (*[

(Var("a"),Var("b"));
(Var("c"), Func("->", Var("a"), Var("e")));
(Func("->", Var("a"), Var("b")), Var("a"));
(Func("->", Var("a"), Var("b")), Func("->", Var("a"), Var("b")));
(Var("a"), Var("a"));
(Func("->", Var("b"), Func("->", Var("a"), Var("a"))), Var("a"));
(Var("f"),Var("b"));
(Var("c"), Func("->", Var("a"), Var("e")));
]*);;

let tmp_eq = fourth_action eq;;
let tmp_eq =fourth_action tmp_eq;;
let tmp_eq =fourth_action tmp_eq;;
let tmp_eq =fourth_action tmp_eq;;
print_string "=====|||==\n";;
List.iter (fun a -> print_string ((algebra_to_string (fst a)) ^ " = ");
                                         print_string ((algebra_to_string (snd a)  ) ^ "\n")) tmp_eq;;
(*
let n1,n2,n3 = calculate_statement eq;;
Printf.printf "%d %d %d" n1 n2 n3;;
*)
