type tree =
    Application of tree * tree
    | Abstraction of string * tree
    | Variable of string;;