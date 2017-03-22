module AST

type Type =
| Any
| Class of string
 override x.ToString() = sprintf "%A" x

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
 override x.ToString() = sprintf "%A" x

type md = 
| MDef of string * string * Type * Type * Expr
| SDef of string * string * Type * Expr
| GDef of string * Type * Expr
 override x.ToString() = sprintf "%A" x

type fd =
| FDef of string * Type
 override x.ToString() = sprintf "%A" x

type k =
| ClassDef of string * fd list * md list
 override x.ToString() = sprintf "%A" x

type prog =
| Program of k list * Expr
 override x.ToString() = sprintf "%A" x