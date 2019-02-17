open Tree;;

let rec  write_to_string expression =
    let token = expression in
        match token with
            | Application (a,b) ->      "(" ^ (write_to_string a) ^ " " ^ (write_to_string b) ^ ")"

            | Abstraction (a,b) ->      (String.concat "" ["(\\";a;"."]) ^ (write_to_string b) ^ ")"

            | Variable(a)       ->      a;;

let s = Abstraction("f", Abstraction("g", Abstraction("x", Application(Application(Variable "f", Variable "x"), Application(Variable "g", Variable "x")))));;
let k = Abstraction("a", Abstraction("b", Variable "a"));;

let rec pretty_print expression =
    match  expression with
    | Abstraction("f", Abstraction("g", Abstraction("x", Application(Application(Variable "f", Variable "x"), Application(Variable "g", Variable "x"))))) -> "s"
    | Abstraction("a", Abstraction("b", Variable "a")) -> "k"
    | Application(a, b) -> let left = pretty_print a in
                                let right = pretty_print b in
                                     String.concat " " ["(" ^ left; right ^ ")"]
    | Variable(a) -> a
    | Abstraction(a, b) -> (String.concat "" ["(\\";a;"."]) ^ (pretty_print b) ^ ")"
    ;;

let is_combinator exp =
    match exp with
        |   Abstraction(f, Abstraction(g, Abstraction(x, Application(Application(Variable f1, Variable x1), Application(Variable g1, Variable x2))))) ->
                if (f = f1) && (g = g1) && (x = x1 && x = x2 && x1 = x2) then
                    true
                else
                    false
        |   Abstraction(a, Abstraction(b, Variable a1)) -> if a = a1 then
                                                                true
                                                           else
                                                                false
        | _ -> false
    ;;

let rec f_tunc expression =
    match expression with
    | Variable (x)                          -> Variable x

    | Application (a, b)                    -> let left_ok = if is_combinator a then a else f_tunc a in
                                                        let right_ok = if is_combinator b then b else f_tunc b in
                                                            Application(left_ok, right_ok)

    | Abstraction (x, Abstraction(y, p))    -> if is_combinator (Abstraction(y, p)) then
                                                    Application (k, Abstraction(y, p))
                                               else
                                                    begin
                                                            let inner = Abstraction (y, p) in
                                                                let inner_ok = if is_combinator inner then inner else f_tunc inner in
                                                                       let result = Abstraction (x, inner_ok) in
                                                                            let result_ok = if is_combinator result then result else f_tunc result in
                                                                                result_ok
                                                    end

    | Abstraction (x, Variable y)           -> if x = y then
                                                    begin
                                                    Application(Application(s, k), k)
                                                    end
                                               else
                                                    begin
                                                    Application (k, Variable y)
                                                    end

    | Abstraction (x, Application(p, q))    -> let left = Abstraction (x, p) in
                                                        let right = Abstraction (x, q) in
                                                            let left_ok = if is_combinator left then left else f_tunc left in
                                                                let right_ok = if is_combinator right then right else f_tunc right in
                                                                    Application (Application (s, left_ok), right_ok)

    | Abstraction (x, p)                    -> let inner = if is_combinator p then p else f_tunc p in
                                                        Application (k, inner)
    ;;


let b = Lexing.from_channel stdin;;
let d = (Parser.lambdaParser Lexer.main)  b;;

print_string (pretty_print (f_tunc d));;