%{
    open Tree;;
 %}

%token <string> VAR
%token SLASH
%token DOT
%token OPEN
%token CLOSE
%token EOF
%start lambdaParser
%type <Tree.tree> lambdaParser
%%

lambdaParser:
        b EOF { $1 }

b:
        p SLASH VAR DOT b { Application($1, Abstraction($3, $5)) }
    |   SLASH VAR DOT b {Abstraction($2, $4)}
    |   p {$1}

p:
        p a {Application($1, $2)}
    |   a {$1}

a:      OPEN b CLOSE {$2}
    |   VAR {Variable($1)}
