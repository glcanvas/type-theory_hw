type token =
  | VAR of (string)
  | SLASH
  | DOT
  | OPEN
  | CLOSE
  | EOF

val lambdaParser :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree
