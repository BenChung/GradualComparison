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
class A {
    m(x:any):any { this } }
class I {
    n(x:any):any { this } }
class T {
    s(x:any):any { this }
    t(x:any):any { this.s : any -> any (x) }
}
new T()@t(new A())
"
    let trans = CGAST.transp(res.Value)
    let outp = CodeGen.genProg(trans)
    printfn "%A" argv
    0 // return an integer exit code
