﻿module Parser
open FParsec
open AST

let parse (prog:string) = 
    let (<!>) (p: Parser<_,_>) label : Parser<_,_> =
        fun stream ->
            printfn "%A: Entering %s" stream.Position label
            let reply = p stream
            printfn "%A: Leaving %s (%A)" stream.Position label reply.Status
            reply
    let ws = spaces <|> (skipMany skipNewline)
    let str_ws s = pstring s .>> ws
    let id = identifier (IdentifierOptions(isAsciiIdStart = isAsciiLetter, isAsciiIdContinue = fun c -> isAsciiLetter c || isDigit c))
    let tpe = (pstring "any" |>> fun x -> Any) <|> (id |>> fun x -> Class x)
    let term, termImpl = createParserForwardedToRef()
    let expr = (pstring "this" |>> fun x -> This) <|> 
               (pstring "that" |>> fun x -> That) <|> 
               (pipe2 (pstring "new" >>. ws >>. id .>> ws .>> pstring "(")
                     ((sepBy (ws >>. term) (ws >>. pstring ",")) .>> pstring ")")
                     (fun className args -> NewExn(className, args))) <|>
               (attempt (pipe2 (pstring "<|" >>. ws >>. tpe .>> ws .>> pstring "|>") (ws >>. term) (fun t e -> BehCast(t,e)))) <|> 
               (pipe2 (pstring "<" >>. ws >>. tpe .>> ws .>> pstring ">") (ws >>. term) (fun t e -> SubCast(t,e))) <|> 
               ((pstring "(" >>. ws >>. term .>> ws .>> pstring ")") |>> (fun e -> e)) <|> 
               (id |>> fun x -> Var x)
    let callExpr = (attempt (pstring "." >>. (attempt ((id .>> ws .>> pstring "(" .>> ws .>> pstring ")") |>> (fun name -> fun exp -> GetF(exp,name))) <|>
                                             attempt (pipe2 (id .>> ws .>> pstring "(" .>> ws) (term .>> ws .>> pstring ")") (fun name arg -> fun exp -> SetF(exp, name, arg))) <|>
                                             attempt (pipe4 (id .>> ws .>> pstring ":" .>> ws) (tpe .>> ws .>> pstring "->" .>> ws) (tpe .>> ws .>> pstring "(" .>> ws) (term .>> ws .>> pstring ")") (fun name t1 t2 arg -> fun exp -> Call(exp,t1,t2,name,arg)))))) <|>
                   (attempt (pipe2 (pstring "@" >>. id .>> ws .>> pstring "(" .>> ws) (term .>> ws .>> pstring ")") (fun name arg -> fun exp -> DynCall(exp, name, arg)))) 
    do termImpl := (attempt (pipe2 expr (many callExpr) (fun e l -> List.fold (fun acc f -> f acc) e l))) <|> expr
    let term = termImpl.Value
    let body = (sepBy1 term (attempt (ws >>. pstring ";" >>. ws)))
    let fd = pipe2 (id .>> ws .>> pstring ":" .>> ws) tpe (fun name tpe -> FDef(name, tpe))
    let md = pipe5 (id .>> pstring "(") 
                   (ws >>. id) 
                   (ws .>> pstring ":" >>. ws >>. tpe .>> pstring ")" .>> ws .>> pstring ":" .>> ws) 
                   (tpe .>> ws .>> pstring "{" .>> ws) 
                   ( body .>> ws .>> pstring "}")
                   (fun name var tp t body -> MDef(name, var, tp, t, body)) 
    let sd = pipe4 (id .>> pstring "(") 
                   (ws >>. id .>> ws .>> pstring ")" .>> ws .>> pstring ":" .>> ws) 
                   (tpe .>> ws .>> pstring "{" .>> ws) 
                   ( body .>> ws .>> pstring "}")
                   (fun name var t body -> SDef(name, var, t, body)) 
    let gd = pipe3 (id .>> pstring "(" .>> ws .>> pstring ")" ) 
                   (ws >>. pstring ":" >>. ws >>. tpe .>> ws) 
                   (pstring "{" >>. ws >>. body .>> ws .>> pstring "}") 
                   (fun name tpe expr -> GDef(name, tpe, expr))
    let clazz = pipe3 (ws >>. str_ws "class" >>. ws >>. id .>> ws .>> pstring "{") (sepEndBy (attempt (ws >>. fd)) ws) ((sepEndBy (ws >>. (attempt sd <|> attempt md <|> attempt gd)) ws) .>> pstring "}") (fun name fds mds -> ClassDef(name, fds, mds))
    let program = pipe2 ((sepEndBy clazz ws) .>> ws) (term .>> ws) (fun c t -> Program(c,t))
    match run program prog with
    | Success(result, _, _) -> Some(result)
    | Failure(errorMsg, _, _) -> printfn "Failure %s" errorMsg; None