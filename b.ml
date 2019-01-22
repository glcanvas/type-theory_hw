open Tree;;

module StringMap = Map.Make(String);;
module Table = Hashtbl;;
(*
let common_variable = "za"   ;;

let rec  write_to_string expression =
    let token = expression in
        match token with
            | Application (a,b) ->      "(" ^ (write_to_string a) ^ " " ^ (write_to_string b) ^ ")"

            | Abstraction (a,b) ->      (String.concat "" ["(\\";a;"."]) ^ (write_to_string b) ^ ")"

            | Variable(a)       ->      a;;


let update_variable var =
    let last = (String.length var) - 1 in
        let symb = String.get var last in
            match symb with
                | 'z'   ->   var ^ "a"
                | _     ->   let new_var = String.sub var 0 last  in
                                let new_var = new_var ^ Char.escaped (Char.chr ((Char.code symb) + 1) ) in
                                    new_var;;

let rec rename_variable expression free_var bounded_var =
    match expression with
    | Application (a,b) ->  let expr_a, a_free_var = rename_variable a free_var bounded_var  in
                                let expr_b, b_free_var = rename_variable b a_free_var bounded_var  in
                                    (Application(expr_a, expr_b), b_free_var)

    | Abstraction (a,b) ->  let new_free_var = update_variable free_var in
                                let a_bound_var = StringMap.add a new_free_var bounded_var in
                                    let expr_b, b_free_var = rename_variable b new_free_var a_bound_var  in
                                        (Abstraction(new_free_var, expr_b), b_free_var)

    | Variable (a)      ->  let is_bounded  = StringMap.mem a bounded_var in
                                match is_bounded with
                                    true        ->  let bound_name = StringMap.find a bounded_var in
                                                        (Variable bound_name, free_var)
                                    | false     ->  (Variable a, free_var);;


let rec replace_in_expr expression right_part variable =
    match expression with
    | Application (a, b) -> Application (replace_in_expr a right_part variable,
                                            replace_in_expr b right_part variable)
    | Abstraction (a, b) -> Abstraction (a, replace_in_expr b right_part variable)

    | Variable(x) ->    if x = variable then right_part else Variable(x);;


let rec reduction expression start_var =
    match expression with
    | Application (Abstraction(v, c), b)    ->  let renamed_expr, free_var = rename_variable b start_var (StringMap.empty) in
                                                    ((replace_in_expr c renamed_expr v), true, free_var)

    | Application (a, b) -> let inner_a, need_a, var_a = reduction a start_var in
                                let inner_b, need_b, var_b = reduction b var_a in
                                    (Application(inner_a, inner_b), need_a || need_b, var_b)

    | Abstraction (a, b)    -> let inner, need, var_b = reduction b start_var in
                                    (Abstraction (a, inner), need, var_b)
    | Variable (a)          -> (Variable (a), false, start_var);;


let rec recursion_loop expression start_var =
    let expr, need, free_var = reduction expression start_var in
        match need with
        | false -> expr
        | true -> recursion_loop expr free_var;;

*)

(*
let x, y = rename_variable d common_variable (StringMap.empty);;

let result = recursion_loop x y;;
print_string (write_to_string result);;
*)


type bruijn = DeApplication of bruijn * bruijn
    |   DeAbstraction of bruijn
    |   DeVariable of int
;;

let toBruijn expression =
    let begin_index = ref 228 in
        let boundedVars = (Table.create 100_000 : (string, int) Table.t) in
            let unboundedVars = StringMap.empty in
                let intNameT = (Table.create 100_000 : (int, string) Table.t) in
                    let rec inner_func level = function
                            | Application (a, b)    ->      let left = inner_func (level + 1) a in
                                                                let right = inner_func (level + 1) b  in
                                                                    DeApplication (left, right)

                            | Abstraction (a, b)    ->      Table.add boundedVars a level;
                                                            (*
                                                            Printf.printf "!!!!\n";
                                                            Table.iter (fun k v -> Printf.printf "%s %d " k v) boundedVars;
                                                            *)
                                                            let right = inner_func (level + 1) b in
                                                                Table.remove boundedVars a;
                                                                DeAbstraction right

                            | Variable (a)          ->      let isBound = Table.mem boundedVars a in
                                                                if isBound = true then
                                                                    let var_level = Table.find boundedVars a in
                                                                        DeVariable var_level
                                                                else
                                                                    let existInFree = Table.mem boundedVars a in
                                                                        if existInFree = true then
                                                                            let freeLvl = StringMap.find a unboundedVars in
                                                                                DeVariable (level + freeLvl)
                                                                        else
                                                                            begin
                                                                                begin_index := !begin_index + 1;
                                                                                StringMap.add a (!begin_index) unboundedVars;
                                                                                Table.add intNameT (!begin_index) a;
                                                                                DeVariable (level + (!begin_index))
                                                                            end
                    in
                        (inner_func 0 expression, intNameT);;

let intToString number =
    Printf.sprintf "var%d" number;;

let bruijnToString expression maped =
    let rec inner level = function
        | DeApplication (a, b)  ->      let left = inner (level + 1) a in
                                            let right = inner (level + 1) b in
                                                "(" ^ left ^ " " ^ right ^ ")"
        | DeAbstraction (a)     ->      let right = inner (level + 1) a in
                                            (String.concat "" ["(\\";(intToString level);"."]) ^ right ^ ")"
        | DeVariable (a)        ->      if a < level then
                                            intToString a
                                        else
                                            let cur_var = a - level in
                                            Table.find maped cur_var
    in inner 0 expression
    ;;

let b = (*Lexing.from_channel stdin;; *) Lexing.from_string "(\x.x x y z)(\y.\z. z z z y z)";;
let d = (Parser.lambdaParser Lexer.main)  b;;

let b_ex, vars = toBruijn d;;
let res = bruijnToString b_ex vars;;
Printf.printf "%s" res ;;

