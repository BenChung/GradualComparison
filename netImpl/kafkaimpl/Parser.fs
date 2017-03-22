module Parser
open FParsec
open AST

let parse (prog:string) = 
    let ws = spaces <|> (skipMany skipNewline)
    let str_ws s = pstring s .>> ws
    let id = many1Chars asciiLetter
    let tpe = (pstring "any" |>> fun x -> Any) <|> (id |>> fun x -> Class x)
    let term, termImpl = createParserForwardedToRef()
    let expr = (pstring "this" |>> fun x -> This) <|> 
               (pstring "that" |>> fun x -> That) <|> 
               (pipe2 (pstring "new" >>. ws >>. id .>> ws .>> pstring "(")
                     ((sepBy (ws >>. term) (ws >>. pstring ",")) .>> pstring ")")
                     (fun className args -> NewExn(className, args))) <|>
               (pipe2 (pstring "<" >>. ws >>. tpe .>> ws .>> pstring ">") (ws >>. term) (fun t e -> Cast(t,e))) <|> 
               ((pstring "(" >>. ws >>. term .>> ws .>> pstring ")") |>> (fun e -> e)) <|> 
               (id |>> fun x -> Var x)
    let callExpr = (attempt (pstring "." >>. (attempt ((id .>> ws .>> pstring "(" .>> ws .>> pstring ")") |>> (fun name -> fun exp -> GetF(exp,name))) <|>
                                             attempt (pipe2 (id .>> ws .>> pstring "(" .>> ws) (term .>> ws .>> pstring ")") (fun name arg -> fun exp -> SetF(exp, name, arg))) <|>
                                             attempt (pipe4 (id .>> ws .>> pstring ":" .>> ws) (tpe .>> ws .>> pstring "->" .>> ws) (tpe .>> ws .>> pstring "(" .>> ws) (term .>> ws .>> pstring ")") (fun name t1 t2 arg -> fun exp -> Call(exp,t1,t2,name,arg)))))) <|>
                   (attempt (pipe2 (pstring "@" >>. id .>> ws .>> pstring "(" .>> ws) (term .>> ws .>> pstring ")") (fun name arg -> fun exp -> DynCall(exp, name, arg)))) 
    do termImpl := (attempt (pipe2 expr (many callExpr) (fun e l -> List.fold (fun acc f -> f acc) e l))) <|> expr
    let term = termImpl.Value
    let fd = id .>> pstring ":" .>>. tpe
    let md = pipe5 (id .>> pstring "(") 
                   (ws >>. id) 
                   (ws .>> pstring ":" >>. ws >>. tpe .>> pstring ")" .>> ws .>> pstring ":" .>> ws) 
                   (tpe .>> ws .>> pstring "{" .>> ws) 
                   ( term .>> ws .>> pstring "}")
                   (fun name var tp t body -> MDef(name, var, tp, tp, body)) 
    let gd = (id .>> pstring "(" .>> ws .>> pstring ")" 
        .>> ws .>> pstring ":" .>> ws .>>. tpe .>> ws
        .>> pstring "{" .>> ws .>>. term .>> ws .>> pstring "}")
    
    let clazz = ws >>. str_ws "class" >>. ws >>. id .>> ws .>> pstring "{" .>>. (sepEndBy (attempt (ws >>. fd)) skipNewline) .>>. (sepEndBy (ws >>. md) skipNewline) .>> pstring "}"
    let program = (sepEndBy clazz skipNewline) .>> ws .>>. term .>> ws
    run program prog