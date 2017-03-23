// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System
open Parser
open AST
open CGAST
open CodeGen

[<EntryPoint>]
let main argv = 
    let res = Parser.parse @"
class D {
    f:D
    m(x:any):any { this }
}
new D()"
    let trans = CGAST.transp(res.Value)
    let outp = CodeGen.genProg(trans)
    printfn "%A" argv
    0 // return an integer exit code
