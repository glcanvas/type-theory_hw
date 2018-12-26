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

let custom_merge a b = (*AlgebraMap.fold AlgebraMap.add a b;;*)
        List.rev_append a b;;

type algebra =  Var of string (* constant *)
            |   Func of string * algebra * algebra (* for expression like -> smth smth *);;

let rec algebra_to_string expression =
    let token = expression in
        match token with
            | Var(a) -> a
            | Func(a, b , c) -> String.concat "" [a ; " (" ; (algebra_to_string b) ; " " ; (algebra_to_string c); ")"];;


let common_variable = "_a";;

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
            | Application (a, b) ->  let union_a, term_a, last_var_a =  build_system a free_var in
                                        let  union_b, term_b, last_var_b = build_system b last_var_a in

                                            let new_var = update_variable last_var_b in

                                                let merged_map = custom_merge union_a union_b in
                                                    (*let added_map = AlgebraMap.add last_var_a (Func ("->", term_b, Var(new_var))) merged_map in*)
                                                            let added_map = merged_map @ [(last_var_a, (Func ("->", term_b, Var(new_var))))] in
                                                        (added_map,
                                                        Var(new_var),
                                                        new_var)


            | Abstraction (a, b) -> let union_b, term_b, last_var_b = build_system b free_var in
                                        let new_var = update_variable last_var_b in
                                            (union_b, Func ("->", Var(new_var), term_b), new_var)

            | Variable (a)       -> let new_var = update_variable free_var in
                                            (*AlgebraMap.empty*)
                                        (  [], Var(new_var), new_var) ;;
(*let e = Lexing.from_string "(\x.x)(\y.y)";;
let d =(Parser.lambdaParser Lexer.main)  e;;

let f a = print_string ((fst a) ^ " ");
                print_string ((algebra_to_string (snd a)  ) ^ "\n");;

let a,b,c = build_system d common_variable;;

List.iter f a;;
(*
AlgebraMap.iter f a;;
*)
print_string ((algebra_to_string b) ^ "\n");;
print_string (c ^ "\n");;
*)
