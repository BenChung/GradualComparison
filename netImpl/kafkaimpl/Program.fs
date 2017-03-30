// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System
open Parser
open AST
open CGAST
open CodeGen

(**
@"
class A {
    m(x:any):any { this } }
class I {
    n(x:any):any { this } }
class T {
    s(x:any):any { this }
    t(x:any):any { this@s(x) }
}
new T()@t(new A())"
*)
[<EntryPoint>]
let main argv = 
    
    let res = Parser.parse @"
class A {
    m(x:A) : A { this } }
class I {
    m(x:C) : I { this } }
class T {
    s(x : I) : T { this } 
    t(x : any) : any { <any>(this.s : I -> T ( <I> x)) } }
class C {
    n(x:C):C { this } }
(<any>new T())@t(<|any|>new A())
"
    let tsv = Translations.ts_progtrans res.Value
    let _ = Typechecker.wfprog tsv
    let trans = CGAST.transp(tsv)
    let outp = CodeGen.genProg(trans, true)
    let evaluated = Executor.execute(outp)
    
    printfn "%A" evaluated
    0 // return an integer exit code
