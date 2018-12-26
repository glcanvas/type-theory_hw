{
open Parser

}

let variable = ['a' - 'z'] ['a' - 'z' '0' - '9' '\'']*
let white = [' ' '\t' '\r' '\n']+

rule main = parse
	| variable as v {VAR(v)}
	| "(" {OPEN}
	| ")" {CLOSE}
	| "\\" {SLASH}
	| "." {DOT}
	| white { main lexbuf }
	| eof {EOF}

