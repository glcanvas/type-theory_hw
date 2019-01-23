open Tree;;

module Table = Hashtbl;;

type bruijn = DeApplication of bruijn * bruijn
    |   DeAbstraction of bruijn
    |   DeVariable of int
;;

let toBruijn expression =
    let begin_index = ref 1488 in
        let boundedVars = (Table.create 148_800 : (string, int) Table.t) in
            let unboundedVars = (Table.create 148_800 : (string, int) Table.t) in
                let intNameT = (Table.create 148_800 : (int, string) Table.t) in
                    let rec inner_func exp level =
                            (match exp with
                            | Application (a, b)    ->      let left = inner_func a (level) in
                                                                let right = inner_func b (level) in
                                                                    DeApplication (left, right)

                            | Abstraction (a, b)    ->      Table.add boundedVars a (level + 1);
                                                            let right = inner_func b (level + 1) in
                                                                Table.remove boundedVars a;
                                                                DeAbstraction right

                            | Variable (a)          ->      let isBound = Table.mem boundedVars a in
                                                                (match isBound with
                                                                    |true ->    let var_level = level - (Table.find boundedVars a) in
                                                                                    DeVariable var_level

                                                                    |false ->   let existInFree = Table.mem boundedVars a in
                                                                                    (
                                                                                        match existInFree with
                                                                                            |true  ->   let freeLvl = Table.find unboundedVars a in
                                                                                                            DeVariable freeLvl
                                                                                            |false ->   begin_index := !begin_index + 1;
                                                                                                        Table.add unboundedVars a (!begin_index);
                                                                                                        Table.add intNameT (!begin_index) a;
                                                                                                        DeVariable (!begin_index)

                                                                                    )
                                                                )
                            )
                            in
                                (inner_func expression 0, intNameT);;

let intToString number =
    Printf.sprintf "v%d" number;;

let bruijnToString expression maped =
    let lambdaTable = (Table.create 148_800 : (int, string) Table.t) in
        let rec inner expr level =
            (match expr with
            | DeApplication (a, b)  ->      let left = inner a level in
                                                let right = inner b level in
                                                    "(" ^ left ^ " " ^ right ^ ")"
            | DeAbstraction (a)     ->      Table.add lambdaTable (level + 1) (intToString (level + 1));
                                            let right = inner a (level + 1) in
                                                (String.concat "" ["(\\";(intToString (level + 1));"."]) ^ right ^ ")"

            | DeVariable (a)        ->      (
                                                match (a < level) with
                                                    | true  ->      Table.find lambdaTable (level - a)
                                                    | false ->      Table.find maped a
                                            )
            )
        in inner expression 0
;;
(*— количество абстракций в дереве разбора, на которое нужно подняться, чтобы найти ту лямбду, с которой данная переменная связана*)
let rec addLevel expression level added_level =
    match  expression with
    | DeApplication(a, b) ->    let left = addLevel a level added_level in
                                    let right = addLevel b level added_level in
                                        DeApplication (left, right)

    | DeAbstraction(a) ->       let right = addLevel a (level + 1) added_level in
                                    DeAbstraction right

    | DeVariable(a) ->          (match a >= level with
                                    | true  ->     DeVariable (a + added_level)
                                    | false ->     DeVariable a
                                )
;;

let rec replace expression expr const_level =
    match  expression with
        | DeApplication(a, b) ->    let left  = replace a expr const_level in
                                        let right = replace b expr const_level in
                                            DeApplication (left, right)

        | DeAbstraction(a) ->       let right = replace a expr (const_level + 1) in
                                        DeAbstraction right

        | DeVariable(a) ->          (
                                        match a = const_level with
                                            | true ->   addLevel expr 0 a
                                            | false ->  (
                                                            match a < const_level || a >= 1488 with
                                                                | true  ->      DeVariable a
                                                                | false ->      DeVariable (a - 1)
                                                        )
                                    )
;;

let rec reduction expr =
    match expr with
        | DeApplication(DeAbstraction (a), b) ->    let call = replace a b 0 in
                                                        (call, true)

        | DeApplication(a, b) ->    let in_a, need_a = reduction a in
                                        (
                                            match need_a with
                                                | true ->   (DeApplication(in_a, b), true)
                                                | false ->  let in_b, need_b = reduction b in
                                                                (DeApplication (in_a, in_b), need_b)
                                        )
        | DeAbstraction(a) ->   let right, need_b = reduction a in
                                    (DeAbstraction right, need_b)

        | DeVariable(a) -> (DeVariable(a), false)
;;


let rec reductionLoop expression =
     let exp, need = reduction expression in
        match need with
        | true ->   reductionLoop exp
        | false ->  exp
;;


let b = Lexing.from_channel stdin;;
let d = (Parser.lambdaParser Lexer.main)  b;;

let b_ex, vars = toBruijn d;;

let redu = reductionLoop b_ex;;
Printf.printf "%s" (bruijnToString redu vars);;
