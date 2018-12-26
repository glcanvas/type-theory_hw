open Tree;;
let out_buffer = Buffer.create 2048;;

let in_buffer = Buffer.create 2048;;

let b = Lexing.from_channel stdin;;
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

(*
 write_to_buffer out_buffer d;;
 Buffer.add_char out_buffer '\n';;
 print_string (Buffer.contents out_buffer);;
 *)

 let rec beta_reduction expression =
    let token = expression in
        match token with
            | Application (a, b) ->

            | Abstraction (a, b) ->

            | Variable (a)       -> ;;