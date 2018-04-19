module Translations
open AST
open Typechecker

let rec private butlast<'a,'b>(f1 : 'a -> 'b)(f2 : 'a -> 'b)(l:'a list) : 'b list = 
    match l with
    | e1 :: e2 :: r -> f1(e1) :: butlast(f1)(f2)r
    | e2 :: nil -> [f2(e2)]
    | nil -> []

let rec private ts_syntrans(K:Map<string,k>)(env:Map<string,Type>) : Expr -> Expr * Type = function
|   That -> raise (VariableNotFound("that", env))
|   This -> This, match env.TryFind "this" with Some(t) -> t | None -> raise (VariableNotFound("this", env))
|   Var(x) -> Var(x), match env.TryFind x with Some(t) -> t | None -> raise (VariableNotFound(x, env))
|   Call(receiver, t1, t2, method, argument) -> 
    let epr,tr = ts_syntrans K env receiver
    match tr with
    |   Class(C) -> match inmtypes (MD(method, t1, t2)) C K with
                    |   Some(MDT(_,_,_)) ->
                        let ep = ts_anatrans K env argument t1
                        DynCall(SubCast(Any,epr), method, SubCast(Any, ep)), t2
                    |   _ -> raise (FieldOrMethodNotFound(method, receiver, ""))
    |   Any -> 
        let ep = ts_anatrans K env argument Any
        DynCall(SubCast(Any, epr), method, SubCast(Any, ep)), Any
|   DynCall(receiver, method, argument) -> 
        let epr = ts_anatrans K env receiver Any
        let epa = ts_anatrans K env argument Any
        DynCall(epr, method, epa), Any
|   GetF(field) -> 
    let epr,tr = ts_syntrans K env This
    match tr with
    |   Class(C) -> match inmtypes (G(field)) C K with
                    |   Some(GT(_,t)) ->
                        GetF(field), t
                    |   _ -> raise (FieldOrMethodNotFound(field, epr, ""))
    |   Any -> (raise (FieldAccessOnAny(This)))
|   SetF(field, value) ->
    let epr,tr = ts_syntrans K env This
    match tr with
    |   Class(C) -> match inmtypes (S(field)) C K with
                    |   Some(ST(_,t)) ->
                        let ep = ts_anatrans K env value t
                        SetF(field, ep), t
                    |   _ -> raise (FieldOrMethodNotFound(field, epr, ""))
    |   Any -> (raise (FieldAccessOnAny(This)))
|   SubCast(target, expr) ->
    let epr, tr = ts_syntrans K env expr
    epr, target
|   BehCast(target, expr) ->
    let epr, tr = ts_syntrans K env expr
    BehCast(target, epr), target
|   NewExn(C, exprs) ->
    let fdts = match K.TryFind C with
               |   None -> raise (ClassNotFound(C, K))
               |   Some(ClassDef(_,fds,_)) -> List.map (function (FDef(name, tpe)) -> tpe) fds
    let tns = List.map2 (ts_anatrans K env) exprs fdts
    SubCast(Any, NewExn(C, tns)), Class(C)
and private ts_anatrans(K:Map<string,k>)(env:Map<string,Type>)(expr:Expr) : Type -> Expr = function
|   Class(C) -> 
    let epr, tr = ts_syntrans K env expr
    match subtype K (Set.empty) tr (Class(C)) with
    |   true -> epr
    |   false -> match tr with
                 |   Class(D) -> raise (NotSubtype((Class C), (Class D)))
                 |   Any -> epr
|   Any -> 
    let epr, tr = ts_syntrans K env expr
    epr


let private ts_methtrans(K:Map<string,k>)(C:string) : md -> md = function
|   MDef(name, var, t1, t2, body) ->
    let env = (Map[ ("this", Class C) ; ("x", t1) ])
    match butlast (fun exp -> match ts_syntrans K env exp with (epr,tr) -> epr) 
                  (fun exp -> SubCast(Any, ts_anatrans K env exp t2)) body with
    |   [] -> raise (EmptyMethodBody(name))
    |   body -> MDef(name, var, Any, Any, body)

let private ts_classtrans(K:Map<string,k>) : k -> k = function
|   ClassDef(name, fds, mds) ->
    ClassDef(name, List.map (function FDef(name,tpe) -> FDef(name, Any)) fds, List.map (ts_methtrans K name) mds)

let ts_progtrans : prog -> prog = function
|   Program(ks, exp) -> 
    let K = makek(ks)
    let expp, outt = ts_syntrans K (Map.empty) exp
    Program(List.map (ts_classtrans K) ks, expp)