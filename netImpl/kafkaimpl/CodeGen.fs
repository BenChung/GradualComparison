module CodeGen
open AST
open CGAST
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.Formatting

let toCsType(t:Type) : string = 
    match t with
    | Any -> "dynamic"
    | Class c -> "I" + c

let rec genExpr(ex:Expr) : string =
    match ex with
    | Var n -> n
    | This -> "this"
    | That -> "this.that"
    | NewExn(c, exprs) -> "new " + c + "(" + (String.concat "," (List.map genExpr exprs)) + ")"
    | GetF(rece, f) -> (genExpr rece) + "." + f
    | SetF(rece, f, v) -> (genExpr rece) + "." + f + " = " + (genExpr v)
    | Call(rece, tp, t, m, arg) -> (genExpr rece) + "." + m + "(" + (genExpr arg) + ")"
    | DynCall(rece, m, arg) -> (genExpr rece) + "." + m + "(" + (genExpr arg) + ")"
    | SubCast(t, expr) -> "(" + (toCsType t) + ")" + (genExpr expr)
    | BehCast(t, expr) -> match t with
                          | Class C -> "Runtime.tyWrapper<" + toCsType(t) + ">(" + genExpr(expr) + ")"
                          | Any -> "Runtime.dyWrapper(" + genExpr(expr) + ")"
    
let genBody(ex:Expr list) : string = Seq.fold (fun acc x -> acc + x + ";\n") "" (List.mapi (fun i expr -> if i = (List.length ex) - 1 then "return " + expr else expr) (List.map genExpr ex))

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
    | CFDef(name, tpe) -> "public " + toCsType(tpe) + " " + name + " {get; set;}"
    | CPDef(name, tpe, get, set) -> "public " + toCsType(tpe) + " " + name + "{\n" + genGet(get) + genSet(set) + "}"

let genConstructor(name:string, fds: cgfd list) : string =
    let cfds = (Seq.choose(fun (fd : cgfd) -> match fd with
                                              | CFDef(name,tpe) -> Some(name,tpe)
                                              | _ -> None) fds)
    "public " + name + "(" + (String.concat(", ")(Seq.map (fun (name, tpe) -> toCsType(tpe) + " " + name) cfds)) + ") { \n" +
                             (String.concat "\n" (Seq.map (fun (name, tpe) -> "this." + name + " = " + name + ";") cfds)) + "\n}"
                             
let genIfd: cgfd -> string = function
|   CFDef(name, tpe) -> toCsType(tpe) + " " + name + " {get; set;}"
|   CPDef(name, tpe, get, set) -> toCsType(tpe) + " " + name + "{\n" + match get with Some(_) -> "get;" | None -> "" + match set with Some(_) -> "set;" | None -> "" + "}"

let genImd : cgmd -> string = function
|   CMDef(name, x, t1, t2, body) -> toCsType(t2) + " " + name + "(" + toCsType(t1) + " " + x + ");"

let genInterface(k:cgk) : string =
    match k with
    | CClassDef(name, fds, mds) -> "public interface I" + name + "{\n"+ (String.concat "\n" (List.append (List.map genIfd fds) (List.map genImd mds))) + "\n}"  
    
exception ThisShouldntHappenException of string
let genClass(env:Map<string, string list>)(k:cgk) : string =
    match k with
    | CClassDef(name, fds, mds) -> 
        let interfaces = match env.TryFind name with
                         |  Some(n) -> n
                         |  None -> raise (ThisShouldntHappenException "wtf")
        let ifacestring = String.concat ", " (List.map (fun tpe -> toCsType(Class tpe)) interfaces)
        "public class " + name + " : " + ifacestring + " {\n" + (String.concat "\n" (genConstructor(name, fds) :: (List.append (List.map genFd fds) (List.map genDef mds)))) + "\n}"

let genProg(p:Cprog, pretty:bool) : string =
    match p with
    | CProgram(ks, env, expr) -> 
        let generated = "using Kafka;\nnamespace Kafka {\n" + (String.concat "\n" 
                                                        (List.append (List.map (genInterface) ks) 
                                                                     (List.map (genClass env) ks))) + "\n" + 
                                                                        "public class Program { \n public static dynamic Main(string[] args) { \n return " + genExpr(expr) + ";\n}\n}\n}"
        if pretty then
            use ws = new AdhocWorkspace()
            let ast = CSharpSyntaxTree.ParseText(generated)
            Formatter.Format(ast.GetRoot(), ws).ToFullString()
        else
            generated