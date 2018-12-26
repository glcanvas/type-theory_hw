open Tree;;
(*
let out_buffer = Buffer.create 2048;;

let in_buffer = Buffer.create 2048;;

let b = Lexing.from_string "\a. b";;
let d =(Parser.lambdaParser Lexer.main)  b;;


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
*)
(*
 write_to_buffer out_buffer d;;
 Buffer.add_char out_buffer '\n';;
 print_string (Buffer.contents out_buffer);;
 *)

module AlgebraMap = Map.Make(String);;
module AbstractVar = Map.Make(String);;

let custom_merge a b = (*AlgebraMap.fold AlgebraMap.add a b;;*)
        List.rev_append a b;;

type algebra =  Var of string (* constant *)
            |   Func of string * algebra * algebra (* for expression like -> smth smth *);;

let rec algebra_to_string expression =
    let token = expression in
        match token with
            | Var(a) -> a
            | Func(a, b , c) -> String.concat "" [a ; " (" ; (algebra_to_string b) ; " " ; (algebra_to_string c); ")"];;


let common_variable = "a";;

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
(*
\f.\x.(f(f x))
\f.(\x. f (x x)) (\x. f (x x))
*)
let e = Lexing.from_string "\f.\x.(f(f x))";;
let d =(Parser.lambdaParser Lexer.main)  e;;

let f a = print_string ((algebra_to_string (fst a)) ^ " = ");
                print_string ((algebra_to_string (snd a)  ) ^ "\n");;

let f1 a b =  print_string ("key: " ^ a ^ " value: " ^ b ^ "\n");;

let empty_bounded_names = AbstractVar.empty;;
let equations, lambda_type, bounded_names, last_free_name = build_system d common_variable empty_bounded_names;;

List.iter f equations;;
print_string "=======\n";;
AbstractVar.iter f1 bounded_names;;
print_string "==========\n";;
print_string ((algebra_to_string lambda_type) ^ "\n");;

