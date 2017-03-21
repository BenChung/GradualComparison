module AST

type Type =
| Any
| Class of string

type Expr =
| Var of string
| This
| That
| NewExn of string * (Expr list)
| GetF of Expr * string 
| SetF of Expr * string * Expr
| Call of Expr * Type * Type * string * Expr
| DynCall of Expr * string * Expr
| Cast of Type * Expr
| Seq of Expr list

type md = 
| MDef of string * string * Type * Type * Expr
| SDef of string * string * Type * Expr
| GDef of string * Type * Expr

type fd =
| FDef of string * Type

type k =
| ClassDef of string * md list * fd list