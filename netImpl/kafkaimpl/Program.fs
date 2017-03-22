// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System
open Parser

[<EntryPoint>]
let main argv = 
    let res = Parser.parse @"
class B {
    f:D
    m(x:any):any { new B(x, y, z) }
    m(x:any):any { too.bar() }
    m(x:any):any { too.bar(baz) }
}
class D {}
hello"
    printfn "%A" argv
    0 // return an integer exit code
