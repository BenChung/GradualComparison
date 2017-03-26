module Typechecker
open AST

type mtd =
| MD of string * Type * Type
| G of string
| S of string

type mt =
| MDT of string * Type * Type
| GT of string * Type
| ST of string * Type

exception ClassNotFound of string*Map<string, k>
exception TypeNotFound of Type*Map<string, k>
exception VariableNotFound of string*Map<string,Type>
exception IncompatibleType of Type*Expr*Expr
exception FieldAccessOnAny of Expr
exception MethodCallOnAny of Expr
exception IncompatibleMethodFound of mtd*Expr*string
exception FieldOrMethodNotFound of string*Expr*string
exception IncompatibleReturnValue of Type*Expr
exception EmptyMethodBody of string
exception MalformedMethod of md
exception MethodExistsException of string

let orElse<'a>(a: 'a option) (b: 'a option) : 'a option = 
    match a with
    | Some a' -> Some a'
    | None -> b

let inmtypes (m:mtd) (c:string) (K: Map<string, k>) : mt option =
    match K.TryFind c with
    | None -> raise (ClassNotFound(c, K))
    | Some (ClassDef(name, fds, mds)) -> match m with
                | MD(name, t1, t2) -> List.tryPick (fun md -> match md with 
                                                      | (MDef(mp, x, t1p, t2p, expr)) -> 
                                                        if mp = name && t1 = t1p && t2 = t2p then
                                                           Some(MDT(name, t1p, t2p))
                                                        else
                                                           None
                                                      | _ -> None) mds  
                | G(name) -> orElse(List.tryPick (fun md -> match md with
                                                        | (GDef(mp, t1p, expr)) -> if mp = name then Some(GT(name, t1p)) else None
                                                        | _ -> None) mds)
                                   (List.tryPick (fun (FDef(f,tp)) -> if f = name then Some(GT(f, tp)) else None ) fds)
                | S(name) -> orElse(List.tryPick (fun md -> match md with
                                                        | (SDef(mp, xp, t1p, expr)) -> if mp = name then Some(ST(name, t1p)) else None
                                                        | _ -> None) mds)
                                   (List.tryPick (fun (FDef(f,tp)) -> if f = name then Some(ST(f, tp)) else None) fds)
                                   

let rec syntype(env : Map<string, Type>) (K: Map<string, k>) (expr: Expr) : Type =
    match expr with
    | Var x -> match env.TryFind x with
               | Some tpe -> tpe
               | None -> raise (VariableNotFound(x, env))
    | This -> match env.TryFind "this" with
               | Some tpe -> tpe
               | None -> raise (VariableNotFound("this", env))
    | That -> raise (VariableNotFound("that", env))
    | NewExn(C, exps) -> match K.TryFind C with
                         | Some (ClassDef(name, fds, mds)) -> 
                            let sel = (fun (FDef(name, tpe)) expr -> anatype env K expr tpe)
                            if (List.forall2 sel fds exps) then
                               Class(C)
                            else
                               let (FDef(name, reqt),arg) = List.find (fun (x,y) -> not (sel x y)) (List.zip fds exps)
                               raise (IncompatibleType(reqt, arg, expr))
                         | None -> raise (ClassNotFound(C, K))
    | GetF(rece, f) -> match syntype env K rece with
                       | Any -> raise (FieldAccessOnAny(rece))
                       | Class C -> 
                        match inmtypes(G(f))(C)(K) with
                        | Some(GT(n,t)) -> t
                        | Some(_) -> raise (IncompatibleMethodFound(G(f), rece, C))
                        | None -> raise (FieldOrMethodNotFound(f, rece, C))
    | SetF(rece, f, valu) -> match syntype env K rece with
                       | Any -> raise (FieldAccessOnAny(rece))
                       | Class C -> 
                        match inmtypes(S(f))(C)(K) with
                        | Some(ST(n,t)) -> if anatype env K valu t then t else raise (IncompatibleType(t,valu,rece))
                        | Some(_) -> raise (IncompatibleMethodFound(S(f), rece, C))
                        | None -> raise (FieldOrMethodNotFound(f, rece, C))
    | Call(rece, t1, t2, m, arg) -> match syntype env K rece with
                       | Any -> raise (MethodCallOnAny(rece))
                       | Class C -> 
                        match inmtypes(MD(m, t1, t2)) C K with
                        | Some(MDT(mp, t1p, t2p)) -> if anatype env K arg t1p then t2p else raise (IncompatibleType(t1p,arg,rece))
                        | Some(_) -> raise (IncompatibleMethodFound(MD(m, t1, t2), rece, C))
                        | None -> raise (FieldOrMethodNotFound(m, rece, C))
    | DynCall(rece, m, arg) -> match anatype env K rece Any, anatype env K arg Any with
                               | true, true -> Any
                               | _, _ -> raise (IncompatibleType(Any,rece,arg))
    | Cast(t, e) -> match syntype env K e with
                    | tp -> t 
                       
and anatype(env : Map<string, Type>) (K: Map<string, k>) (expr: Expr) (against: Type) : bool = 
    let it = syntype env K expr
    it = against

let wftype (K:Map<string, k>) (t : Type) = match t with
| Any -> true
| Class C -> K.ContainsKey C

let wffield (K:Map<string, k>) (f: fd) = match f with
| FDef(name, tpe) -> wftype K tpe

let rec private butlast<'a,'b,'c>(f1 : 'a -> 'b)(f2 : 'a -> 'c)(l:'a list) : 'c option = match l with
| e1 :: e2 :: r -> let _ = f1(e1)
                   butlast(f1)(f2)r
| e2 :: nil -> Some(f2(e2))
| nil -> None

let wfmeth (env:Map<string, Type>) (K:Map<string, k>) (def : md) : bool = 
 match def with
 | MDef(name, x, Any, Any, body) -> 
   let ienv = Map.add x Any env
   match butlast (syntype ienv K) (fun e -> anatype ienv K e Any) body with
   | Some(true) -> true
   | Some(_) -> raise (IncompatibleReturnValue(Any, List.last body))
   | None -> raise (EmptyMethodBody(name))
 | MDef(name, x, Class C1, Class C2, body) -> 
   let ienv = Map.add x (Class C1) env
   if not (wftype K (Class C1)) then raise (ClassNotFound(C1, K))
   if not (wftype K (Class C2)) then raise (ClassNotFound(C2, K))
   match butlast (syntype ienv K) (fun e -> anatype ienv K e (Class C2)) body with
   | Some(true) -> true
   | Some(_) -> raise (IncompatibleReturnValue(Any, List.last body))
   | None -> raise (EmptyMethodBody(name))
 | SDef(name, x, t, body) -> 
   let ienv = Map.add x t env
   if not (wftype K t) then raise (TypeNotFound(t, K))
   match butlast (syntype ienv K) (fun e -> anatype ienv K e t) body with
   | Some(true) -> true
   | Some(_) -> raise (IncompatibleReturnValue(Any, List.last body))
   | None -> raise (EmptyMethodBody(name))
 | GDef(name, t, body) -> 
   if not (wftype K t) then raise (TypeNotFound(t, K))
   match butlast (syntype env K) (fun e -> anatype env K e t) body with
   | Some(true) -> true
   | Some(_) -> raise (IncompatibleReturnValue(Any, List.last body))
   | None -> raise (EmptyMethodBody(name))
 | _  -> raise (MalformedMethod(def))

let rec private names : md list -> string list = function 
|               ((MDef(name, _, _, _, _)) :: mds : md list) -> name :: (names mds)
|               ((GDef(name, _, _)) :: mds : md list) -> name :: (names mds)
|               ((SDef(name, _, _, _)) :: mds : md list) -> name :: (names mds)
|               ([]) -> []

type private Seen =
| Property of bool * bool
| Method 

let private Nand a b = 
    match a, b with
    | true, true -> false
    | _, _ -> true

let private mexists(map:Map<string,Seen>) (name:string) : Seen -> Map<string,Seen> = function
|   Property(b1,b2) -> 
    match map.TryFind name with
    |   Some(Property(b1p, b2p)) -> 
        if (Nand b1 b1p) && (Nand b2 b2p) then 
            Map.add(name)(Property(b1 || b1p, b2 || b2p)) map
        else
            raise (MethodExistsException(name))
    |   Some(Method) -> raise (MethodExistsException(name))
    |   None -> Map.add(name)(Property(b1, b2)) map
|   Method -> 
    match map.TryFind name with
    |   Some(_) -> raise (MethodExistsException(name))
    |   None -> Map.add(name)(Method) map

let rec private overloading : Map<string,Seen> -> fd list -> md list -> unit = fun seen -> function
|   (FDef(name, t)) :: fds -> fun mds -> overloading (mexists seen name (Property(true, true))) fds mds
|   [] -> function
    |   (MDef(name, x, t1, t2, body)) :: rest -> overloading (mexists seen name (Method)) [] rest
    |   (GDef(name, t, body)) :: rest -> overloading (mexists seen name (Property(true, false))) [] rest
    |   (SDef(name, x, t, body)) :: rest -> overloading (mexists seen name (Property(false, true))) [] rest
    |   [] -> ()

let wfclass (K: Map<string,k>) (ClassDef(name, fds, mds)) : unit =
    let _ = overloading (Map.empty) fds mds
    let _ = List.map (wffield K) fds
    let _ = List.map (wfmeth (Map[("this", Class(name))]) K) mds
    ()

let wfprog (Program(ks, expr)) : unit = 
    let K = Map.ofList (List.map (fun k -> match k with (ClassDef(name, fds, mds)) -> (name,k)) ks)
    let _ = List.map (wfclass K) ks
    let _ = syntype (Map.empty) K expr
    ()
// let wfclass\]