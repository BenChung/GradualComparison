module AST

type Type =
| Any
| Class of string
 override x.ToString() = sprintf "%A" x

type Expr =
| Var of string
| This
| That
| Thisfd
| NewExn of string * (Expr list)
| GetF of Expr * string
| SetF of Expr * string * Expr
| Call of Expr * Type * Type * string * Expr
| DynCall of Expr * string * Expr
| SubCast of Type * Expr
| BehCast of Type * Expr
 override x.ToString() = sprintf "%A" x

let rec subst(n:string, wth : Expr)(ine:Expr) = 
    match ine with
    | Var np -> if np = n then wth else Var np
    | This -> This
    | That -> That
    | NewExn(name, exprs) -> NewExn(name, List.map (subst(n, wth)) exprs)
    | GetF(recr, f) -> GetF(subst(n, wth)(recr), f)
    | SetF(recr, f, v) -> SetF(subst(n,wth)(recr), f, subst(n,wth)(v))
    | Call(recr, t1, t2, m, arg) -> Call(subst(n,wth) recr, t1, t2, m, subst(n,wth) arg)
    | DynCall(recr, m, arg) -> DynCall(subst(n,wth) recr, m, subst(n,wth) arg)
    | SubCast(t, e) -> SubCast(t, subst(n,wth) e)
    | BehCast(t, e) -> BehCast(t, subst(n,wth) e)

type md = 
| MDef of string * string * Type * Type * Expr list
| SDef of string * string * Type * Expr list
| GDef of string * Type * Expr list
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