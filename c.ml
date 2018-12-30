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

let rec  write_to_string expression =
    let token = expression in
        match token with
            | Application (a,b) ->      "(" ^ (write_to_string a) ^ " " ^ (write_to_string b) ^ ")"

            | Abstraction (a,b) ->      (String.concat "" ["(\\";a;"."]) ^ (write_to_string b) ^ ")"

            | Variable(a)       ->      a;;

module AlgebraMap = Map.Make(String);;

module AbstractVar = Map.Make(String);;

exception MatchEquation of string;;

type algebra =  Var of string (* constant *)
            |   Func of string * algebra * algebra (* for expression like -> smth smth *);;

type tmp_derivation =   BuildTypeVar of algebra
                        | BuildTypeAbstr of algebra * algebra * tmp_derivation
                        | BuildTypeAppl of algebra * algebra * algebra * tmp_derivation * tmp_derivation ;;

let common_variable = "a";;

let custom_merge a b = List.rev_append a b;;

let rec algebra_to_string expression =
    let token = expression in
        match token with
            | Var(a) -> a
            | Func(a, b , c) -> String.concat "" ["(" ; (algebra_to_string b) ; a ; (algebra_to_string c); ")"];;



let update_variable var =
    let last = (String.length var) - 1 in
        let symb = String.get var last in
            match symb with
                | 'z'   ->   var ^ "a"
                | _     ->   let new_var = String.sub var 0 last  in
                                let new_var = new_var ^ Char.escaped (Char.chr ((Char.code symb) + 1) ) in
                                    new_var;;

 let rec build_system expression free_var abstaction_name unbound_names =
    let token = expression in
        match token with
            | Application (a, b) ->  let union_a, term_a, last_map_a, last_unbound_map_a, last_var_a, derivation_a =  build_system a free_var abstaction_name unbound_names in
                                        let  union_b, term_b, last_map_b, last_unbound_map_b, last_var_b, derivation_b = build_system b last_var_a abstaction_name last_unbound_map_a in
                                            let new_var = update_variable last_var_b in
                                                let merged_equation = custom_merge union_a union_b in
                                                    let merged_map = AbstractVar.fold AbstractVar.add last_map_a last_map_b in
                                                        let algebra_type = Func ("->", term_b, Var(new_var)) in
                                                            let derivation = BuildTypeAppl(term_a, term_b, Var new_var, derivation_a, derivation_b) in
                                                                let added_equation = merged_equation @ [(term_a, algebra_type)] in
                                                                    (added_equation, Var(new_var), merged_map, last_unbound_map_b, new_var, derivation)

            | Abstraction (a, b) ->     let new_free_var = update_variable free_var in
                                            let updated_map = AbstractVar.add a new_free_var abstaction_name in
                                                let union_b, term_b, last_map_b, last_unbound_map_b, last_var_b, deriavtion_b = build_system b new_free_var updated_map unbound_names in
                                                    let new_var = update_variable last_var_b in
                                                        let algebra_type = Func ("->", Var new_free_var, term_b) in
                                                            let derivation = BuildTypeAbstr(Var new_free_var, term_b, deriavtion_b) in
                                                                (union_b, algebra_type, last_map_b, last_unbound_map_b, new_var, derivation)

            | Variable (a)       ->     let contains_variable = AbstractVar.mem a abstaction_name in
                                            if contains_variable then
                                                let variable_name = AbstractVar.find a abstaction_name in
                                                    let algebra_type = Var(variable_name) in
                                                        ([], algebra_type, abstaction_name, unbound_names, free_var, BuildTypeVar algebra_type)
                                            else
                                                let unbound_var = AbstractVar.mem a unbound_names in
                                                    match unbound_var with
                                                    | true -> let var_name = AbstractVar.find a unbound_names in
                                                                let algebra_type = Var var_name in
                                                                    ([], algebra_type, abstaction_name, unbound_names, free_var, BuildTypeVar algebra_type)
                                                    | false -> let new_var = update_variable free_var in
                                                                    let added_bound_names = AbstractVar.add a new_var unbound_names in
                                                                            let algebra_type = Var(new_var) in
                                                                                ([], algebra_type, abstaction_name, added_bound_names, new_var, BuildTypeVar algebra_type);;

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

let rec check_exist_recursion variable equations =
    match equations with
    | Var(a) -> Var(a) = variable
    | Func(a,b,c) -> let left = check_exist_recursion variable b in
                        let right = check_exist_recursion variable c in
                            left || right;;

let rec check_same_derivation equations =
    match equations with
    | [] -> true
    | _ -> let left,right = List.hd equations in
                let tail = List.tl equations in
                    match left with
                    | Var(a) -> let result = check_exist_recursion (Var a) right in
                                    if  result then false else check_same_derivation tail
                    | _ -> check_same_derivation tail;;

let rec help_delete_repeat left right equations =
    match equations with
    | [] -> []
    | _ -> let head_left, head_right =  List.hd equations in
                let tail = List.tl equations in
                    if head_left = left && head_right = right then
                        help_delete_repeat left right tail
                    else
                        [(head_left, head_right)] @ (help_delete_repeat left right tail);;

let rec delete_repeat equations =
    match equations with
    | [] -> []
    | _ -> let head_left, head_right =  List.hd equations in
                let tail = List.tl equations in
                    let result_delete = help_delete_repeat head_left head_right tail in
                        [(head_left, head_right)] @ (delete_repeat result_delete);;

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
                    let filtered_map = AbstractVar.filter (fun k v -> v > 1) result_map in
                        let list_of_vars_term = available_map equations in
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


let rec help_is_solved_form expression right_var =
    match expression with
    | Var(a) -> AbstractVar.add a 1 right_var
    | Func(a, b, c) -> let left = help_is_solved_form b right_var in
                            let right = help_is_solved_form c left in
                                right;;

let rec is_solved_form equations var_map num_of_var_in_right =
    match equations with
    | [] -> true
    | _  -> let head = List.hd equations in
                let  tail = List.tl equations in
                    let left, right = head in
                        let calc_right_var = help_is_solved_form right num_of_var_in_right in
                            match left with
                            | Var(a) -> let contains = AbstractVar.mem a var_map in
                                            if contains then
                                                false
                                            else
                                                let exist_in_right = AbstractVar.mem a calc_right_var in
                                                    if exist_in_right then
                                                        false
                                                    else
                                                        is_solved_form tail (AbstractVar.add a 1 var_map) calc_right_var
                            | Func(a, b, c) -> false;;

let rec solve_equations equations =
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
                    let exist_recursion = check_same_derivation delete_equal in
                        if not exist_recursion then
                            (false, delete_equal)
                        else
                            let deleted_repeat = delete_repeat delete_equal in
                            let fourth = fourth_action deleted_repeat in
                                let compare = is_solved_form fourth (AbstractVar.empty) (AbstractVar.empty) in
                                    match compare with
                                        | false ->  solve_equations fourth
                                        | true ->   (true, fourth);;

let make_map_from_list solved_equations =
    List.fold_left (fun mp it->
                    let left, right = it in
                    match left with
                    | Var(a) -> AbstractVar.add a right mp
                   ) AbstractVar.empty solved_equations;;

let rec replace_in_type map_solved_equations expression_type =
    match expression_type with
    | Var(a) -> if AbstractVar.mem a map_solved_equations then
                    AbstractVar.find a map_solved_equations
                else
                    Var a
    | Func(a, b, c) -> let left = replace_in_type map_solved_equations b in
                            let right = replace_in_type map_solved_equations c in
                                Func (a, left, right);;

let repeat_stars n =
    String.concat "" (Array.to_list (Array.make n "*   "));;


let rec constuct_type map_solved_equations unbounded_names expression derivation bounded_names depth =
    let unbounded = AbstractVar.fold (fun k v lst -> lst @ [(k ^ " : " ^ (algebra_to_string v))] ) unbounded_names [] in
    let bounded = AbstractVar.fold (fun k v lst -> lst @ [(k ^ " : " ^ (algebra_to_string v))] ) bounded_names unbounded in
    let list_of_left = String.concat ", " bounded in
        print_string (repeat_stars depth);
        print_string list_of_left;
        print_string " |- ";
        match expression, derivation with
        | Variable(a), BuildTypeVar(tp) -> (let exist = AbstractVar.mem a unbounded_names in
                                                match exist with
                                                | true ->   let right = AbstractVar.find a unbounded_names in
                                                    print_string (a ^ " : " ^ (algebra_to_string right));
                                                | false ->  let right = replace_in_type map_solved_equations tp in
                                                    print_string (a ^ " : " ^ (algebra_to_string right));
                                            );
                                            print_string " [rule #1]\n"

        | Abstraction(a, b), BuildTypeAbstr(tp_a, tp_b, tp_inner) -> let tp_a_repl = replace_in_type map_solved_equations tp_a in
                                                                        let tp_b_repl = replace_in_type map_solved_equations tp_b in
                                                                            let abstraction = Func("->",tp_a_repl, tp_b_repl) in
                                                                                let abst_string = write_to_string (Abstraction(a,b)) in
                                                                                    print_string (abst_string ^ " : " ^ (algebra_to_string abstraction));
                                                                                    print_string " [rule #3]\n";
                                                                                    constuct_type map_solved_equations unbounded_names b tp_inner (AbstractVar.add a tp_a_repl bounded_names) (depth + 1)
        | Application(a, b), BuildTypeAppl(tp_a, tp_b, tp_c, tp_in_a, tp_in_b)  -> let tp_a_repl = replace_in_type map_solved_equations tp_a in
                                                                                        let tp_b_repl = replace_in_type map_solved_equations tp_b in
                                                                                            let tp_c_repl = replace_in_type map_solved_equations tp_c in
                                                                                                let appl_string = write_to_string (Application (a,b)) in
                                                                                                    print_string (appl_string ^ " : " ^ (algebra_to_string tp_c_repl));
                                                                                                    print_string " [rule #2]\n";
                                                                                                    constuct_type map_solved_equations unbounded_names a tp_in_a bounded_names (depth + 1);
                                                                                                    constuct_type map_solved_equations unbounded_names b tp_in_b bounded_names (depth + 1);;

let e = Lexing.from_channel stdin;;(*Lexing.from_string "\x.\y. x";;*)
let d = (Parser.lambdaParser Lexer.main)  e;;


let empty_bounded_names = AbstractVar.empty;;
let emplty_unbounded_names = AbstractVar.empty;;
let my_equitatins, lambda_type, bounded_names, unbounded_names, last_free_name, result_derivation = build_system d common_variable empty_bounded_names emplty_unbounded_names;;

let ok,eq =  solve_equations my_equitatins;;

match ok with
    | true ->
                 let maped_eq = make_map_from_list eq in
                 let solved_unbound_variabes = AbstractVar.map (fun v -> replace_in_type maped_eq (Var v))  unbounded_names in
                    constuct_type maped_eq solved_unbound_variabes d result_derivation (AbstractVar.empty) 0

    | false ->  Printf.printf "Expression has no type\n"
;;
