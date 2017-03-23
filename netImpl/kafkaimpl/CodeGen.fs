module CodeGen
open AST
open CGAST

let toCsType(t:Type) : string = 
    match t with
    | Any -> "dynamic"
    | Class c -> c

let rec genExpr(ex:Expr) : string =
    match ex with
    | Var n -> n
    | This -> "this"
    | That -> "this.that"
    | NewExn(c, exprs) -> "new " + c + "(" + (String.concat "," (List.map genExpr exprs)) + ")"
    | GetF(rece, f) -> (genExpr rece) + "." + f
    | SetF(rece, f, v) -> (genExpr rece) + "." + f + " = " + (genExpr v)
    | Call(rece, tp, t, m, arg) -> (genExpr rece) + "." + m + "(" + (genExpr arg) + ")"
    | DynCall(rece, m, arg) -> (genExpr rece) + "," + m + "(" + (genExpr arg) + ")"
    | Cast(t, expr) -> "(" + (toCsType t) + ")" + (genExpr expr)
    
let genBody(ex:Expr list) : string = Seq.fold (fun acc x -> acc + x + ";\n") "" (List.map genExpr ex)

let genDef(md:cgmd) : string =
    match md with
    | CMDef(name, var, vtype, rtype, body) -> "public " + toCsType(rtype) + " " + name + "(" + toCsType(vtype) + " " + var + ")" + "{\n" + genBody(body) + "}\n" 


let genGet(getter:cggd option) : string =
    match getter with
    | Some(CGDef(body)) -> "get {\n" + genBody(body) + "}\n"
    | None -> ""

let genSet(setter: cgsd option) : string =
    match setter with
    | Some(CSDef(var, body)) -> "set {\n" + genBody(List.map (subst(var, Var "value")) body) + "}\n"
    | None -> ""

let genFd(fd:cgfd) : string =
    match fd with
    | CFDef(name, tpe) -> "public " + toCsType(tpe) + " " + name + ";"
    | CPDef(name, tpe, get, set) -> "public " + toCsType(tpe) + " " + name + "{\n" + genGet(get) + genSet(set) + "}"

let genClass(k:cgk) : string =
    match k with
    | CClassDef(name, fds, mds) -> "class " + name + " {\n" + (String.concat "\n" (List.map genFd fds)) + "\n" + (String.concat "\n" (List.map genDef mds)) + "\n}"

let genProg(p:Cprog) : string =
    match p with
    | CProgram(ks, expr) -> (String.concat "\n" (List.map genClass ks)) + "\n" + "class Main { \n static void Main(string[] args) { \n" + genExpr(expr) + ";\n}\n}"